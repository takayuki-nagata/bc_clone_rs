// SPDX-License-Identifier: MIT

//! Kani bounded model checking harnesses for `bc_core`.
//!
//! Cross-verifies the `dual_verified!` kernels in `verified_kernels.rs` using
//! bit-precise CBMC symbolic execution (`kani::any()`) and verifies multi-step
//! state-machine invariants without heap allocation state explosion.

use crate::verified_kernels::*;

/// Bit-precise verification of `verified_hex_char_val` across all 256 possible `u8` values.
#[kani::proof]
fn proof_verified_char_parsers() {
    let c: u8 = kani::any();

    let hex_val = verified_hex_char_val(c);
    assert!(hex_val <= 15);
    if c.is_ascii_digit() {
        assert_eq!(hex_val, (c - b'0') as usize);
    } else if (b'A'..=b'F').contains(&c) {
        assert_eq!(hex_val, (c - b'A') as usize + 10);
    } else if (b'a'..=b'f').contains(&c) {
        assert_eq!(hex_val, (c - b'a') as usize + 10);
    } else {
        assert_eq!(hex_val, 0);
    }
}

/// Bit-precise verification of POSIX scale calculation kernels (`add`, `sub`, `mul`, `div`, `sqrt`, `pow`).
#[kani::proof]
fn proof_verified_posix_scale_rules() {
    let a: usize = kani::any();
    let b: usize = kani::any();
    let g: usize = kani::any();

    // 1. verified_add_sub_scales works for any usize without precondition
    let (sr_add, shift_a, shift_b) = verified_add_sub_scales(a, b);
    assert!(sr_add >= a && sr_add >= b);
    assert_eq!(a + shift_a, sr_add);
    assert_eq!(b + shift_b, sr_add);
    assert!(shift_a == 0 || shift_b == 0);

    // 2. Bounded scale preconditions for mul, div, sqrt, pow
    kani::assume(a <= MAX_VERIFIED_SCALE);
    kani::assume(b <= MAX_VERIFIED_SCALE);
    kani::assume(g <= MAX_VERIFIED_SCALE);

    let (sr_mul, diff_mul) = verified_mul_scale_and_shift(a, b, g);
    assert!(sr_mul <= a + b);
    assert!(sr_mul >= a || sr_mul >= b);
    assert_eq!(sr_mul + diff_mul, a + b);

    let (sr_div, shift_div) = verified_div_scale_and_shift(a, b, g);
    assert_eq!(sr_div, g);
    assert_eq!(shift_div, (b as i64) - (a as i64) + (g as i64));

    let (sr_sqrt, shift_sqrt) = verified_sqrt_scale_and_shift(a, g);
    assert!(sr_sqrt >= a && sr_sqrt >= g);
    assert_eq!(a + shift_sqrt, 2 * sr_sqrt);

    let (sr_pow, diff_pow) = verified_pow_scale_and_shift(a, b, g);
    assert!(sr_pow <= a);
    assert_eq!(sr_pow + diff_pow, a);
}

/// Bit-precise verification of `verified_bcnum_length` and `verified_bessel_negative_order_parity`.
#[kani::proof]
fn proof_verified_length_and_bessel_parity() {
    let is_zero: bool = kani::any();
    let digits: usize = kani::any();
    let scale: usize = kani::any();
    kani::assume(digits <= MAX_VERIFIED_SCALE);
    kani::assume(scale <= MAX_VERIFIED_SCALE);
    if !is_zero {
        kani::assume(digits >= 1);
    }

    let len = verified_bcnum_length(is_zero, digits, scale);
    assert!(len >= 1 && len >= scale);
    if is_zero {
        assert_eq!(len, if scale >= 1 { scale } else { 1 });
    } else {
        assert_eq!(len, digits + scale);
    }

    let n_i64: i64 = kani::any();
    kani::assume(n_i64 > i64::MIN);
    let (n_abs, sign) = verified_bessel_negative_order_parity(n_i64);
    assert!(n_abs >= 0);
    assert!(sign == 1 || sign == -1);
    if n_i64 >= 0 {
        assert_eq!(n_abs, n_i64);
        assert_eq!(sign, 1);
    } else {
        assert_eq!(n_abs, -n_i64);
        assert_eq!(sign, if (n_abs % 2) == 1 { -1 } else { 1 });
    }
}

/// Bit-precise verification of `verified_wrapped_stdout_step` and `verified_relational_scale_shifts`.
#[kani::proof]
fn proof_verified_stdout_step_and_relational_shifts() {
    let col: usize = kani::any();
    let is_nl: bool = kani::any();
    kani::assume(col <= POSIX_WRAP_COL_LIMIT);

    let (next_col, should_wrap) = verified_wrapped_stdout_step(col, is_nl);
    assert!(next_col <= POSIX_WRAP_COL_LIMIT);
    if is_nl {
        assert_eq!(next_col, 0);
        assert!(!should_wrap);
    } else if col == POSIX_WRAP_COL_LIMIT {
        assert_eq!(next_col, 1);
        assert!(should_wrap);
    } else {
        assert_eq!(next_col, col + 1);
        assert!(!should_wrap);
    }

    let l_scale: usize = kani::any();
    let r_scale: usize = kani::any();
    kani::assume(l_scale <= MAX_VERIFIED_SCALE);
    kani::assume(r_scale <= MAX_VERIFIED_SCALE);
    let (shift_l, shift_r) = verified_relational_scale_shifts(l_scale, r_scale);
    assert_eq!(l_scale + shift_l, r_scale + shift_r);
    assert!(shift_l == 0 || shift_r == 0);
}

/// Bit-precise verification of `verified_clamp_register` for the `scale`, `ibase`, and `obase`
/// ranges across all `usize` magnitudes and both signs.
#[kani::proof]
fn proof_verified_register_clamping() {
    let magnitude: usize = kani::any();
    let negative: bool = kani::any();

    for (min, max) in [(0, BC_SCALE_MAX), (2, IBASE_MAX), (2, BC_BASE_MAX)] {
        let (v, kind) = verified_clamp_register(magnitude, negative, min, max);
        assert!(min <= v && v <= max);
        if negative {
            assert!(kind == -2 && v == min);
        } else if magnitude < min {
            assert!(kind == -1 && v == min);
        } else if magnitude > max {
            assert!(kind == 1 && v == max);
        } else {
            assert!(kind == 0 && v == magnitude);
        }
    }
    // The clamped scale satisfies the precondition of every scale kernel.
    let (scale, _) = verified_clamp_register(magnitude, negative, 0, BC_SCALE_MAX);
    assert!(scale <= MAX_VERIFIED_SCALE);
}

/// Bit-precise verification of lexer & parser helper kernels (`verified_is_bc_digit`,
/// `verified_is_ident_continue`, `verified_lexer_peek_token_index`, `verified_lexer_peek_char_index`,
/// `verified_lexer_advance_step`, `verified_pratt_next_min_prec`, `verified_pratt_infix_info`).
#[kani::proof]
fn proof_verified_lexer_and_parser_kernels() {
    let b: u32 = kani::any();
    let is_digit = verified_is_bc_digit(b);
    assert_eq!(is_digit, (48..=57).contains(&b) || (65..=70).contains(&b));

    let is_ident = verified_is_ident_continue(b);
    assert_eq!(
        is_ident,
        (97..=122).contains(&b) || (48..=57).contains(&b) || b == 95
    );

    let buf_len: usize = kani::any();
    let offset: usize = kani::any();
    kani::assume(buf_len >= 1);
    let tok_idx = verified_lexer_peek_token_index(buf_len, offset);
    assert!(tok_idx < buf_len);

    let text_len: usize = kani::any();
    let pos: usize = kani::any();
    kani::assume(text_len <= MAX_VERIFIED_SCALE);
    kani::assume(pos <= text_len);
    kani::assume(offset <= MAX_VERIFIED_SCALE);
    let (in_bounds, valid_idx) = verified_lexer_peek_char_index(text_len, pos, offset);
    if in_bounds {
        assert!(valid_idx < text_len);
        assert_eq!(valid_idx, pos + offset);
    } else {
        assert_eq!(valid_idx, 0);
    }

    let line: usize = kani::any();
    let is_nl: bool = kani::any();
    kani::assume(pos < 1_000_000_000);
    kani::assume(line <= 1_000_000_000);
    let (next_pos, next_line) = verified_lexer_advance_step(pos, line, is_nl);
    assert_eq!(next_pos, pos + 1);
    assert_eq!(next_line, if is_nl { line + 1 } else { line });

    let tok_kind: u8 = kani::any();
    let (op_prec, right_assoc, next_min_prec) = verified_pratt_infix_info(tok_kind);
    if (1..=4).contains(&tok_kind) {
        assert!((1..=4).contains(&op_prec));
        if right_assoc {
            assert_eq!(next_min_prec, op_prec);
        } else {
            assert_eq!(next_min_prec, op_prec + 1);
        }
    } else {
        assert_eq!(op_prec, -1);
        assert!(!right_assoc);
        assert_eq!(next_min_prec, 0);
    }
}

/// Bit-precise verification of `obase` padding, transcendental guard precision, Decimal shift,
/// control-flow flags, C-FFI buffer capacity, and Zephyr character classification.
#[kani::proof]
fn proof_verified_math_eval_ffi_and_zephyr_kernels() {
    let dw: usize = kani::any();
    let rl: usize = kani::any();
    let pad = verified_multi_digit_obase_pad_zeros(dw, rl);
    if dw > rl {
        assert_eq!(pad + rl, dw);
    } else {
        assert_eq!(pad, 0);
    }

    let xs: usize = kani::any();
    let gs: usize = kani::any();
    let ep: usize = kani::any();
    kani::assume(xs <= MAX_VERIFIED_SCALE);
    kani::assume(gs <= MAX_VERIFIED_SCALE);
    kani::assume(ep <= MAX_VERIFIED_SCALE);
    let gprec = verified_transcendental_guard_prec(xs, gs, ep);
    assert!(gprec >= 15 && gprec >= xs + ep + 15 && gprec >= gs + ep + 15);

    let (shift_digits, should_mul) = verified_decimal_scale_shift(dw, rl);
    if rl >= dw {
        assert!(should_mul);
        assert_eq!(dw + shift_digits, rl);
    } else {
        assert!(!should_mul);
        assert_eq!(rl + shift_digits, dw);
    }

    let bf: bool = kani::any();
    let rf: bool = kani::any();
    let qf: bool = kani::any();
    let abort = verified_should_abort_execution(bf, rf, qf);
    let (exit_loop, next_bf) = verified_loop_post_body_action(bf, rf, qf);
    assert_eq!(abort, exit_loop);
    assert!(!next_bf);

    let cap_ok = verified_c_ffi_check_buf_capacity(dw, rl);
    if cap_ok {
        assert!(rl >= 1 && dw <= rl - 1);
    }

    let ch: u8 = kani::any();
    let z_class = verified_zephyr_classify_char(ch);
    assert!(z_class <= 4);

    let line_len: usize = kani::any();
    let max_line: usize = kani::any();
    let action = verified_zephyr_repl_action(ch, line_len, max_line);
    assert!(action <= 4);
    assert_eq!(action == REPL_ACTION_EVAL_LINE, z_class == 1);
    assert_eq!(
        action == REPL_ACTION_BACKSPACE,
        z_class == 2 && line_len > 0
    );
    assert_eq!(action == REPL_ACTION_CTRL_C, z_class == 3);
    assert_eq!(
        action == REPL_ACTION_APPEND_CHAR,
        z_class == 4 && line_len < max_line
    );
}

/// Bit-precise verification of CLI argument classification and initial scale across symbolic slices.
#[kani::proof]
fn proof_verified_cli_kernels() {
    let math_enabled: bool = kani::any();
    let init_scale = verified_cli_initial_scale(math_enabled);
    assert_eq!(init_scale, if math_enabled { 20 } else { 0 });

    let buf: [u8; 10] = kani::any();
    let len: usize = kani::any();
    kani::assume(len <= 10);
    let slice = &buf[..len];

    let options_ended: bool = kani::any();
    let kind = verified_cli_classify_arg(slice, options_ended);
    if options_ended || len < 2 || slice[0] != b'-' {
        assert_eq!(kind, CLI_ARG_FILE);
    } else if len == 2 && slice[1] == b'-' {
        assert_eq!(kind, CLI_ARG_END_OF_OPTIONS);
    } else if slice == b"--version" {
        assert_eq!(kind, CLI_ARG_OPT_VERSION);
    } else if slice[1] == b'-' {
        assert_eq!(kind, CLI_ARG_OPT_INVALID);
    } else {
        assert_eq!(kind, CLI_ARG_OPT_CLUSTER);
    }

    let c: u32 = kani::any();
    let letter = verified_cli_classify_option_char(c);
    match char::from_u32(c) {
        Some('l') => assert_eq!(letter, CLI_ARG_OPT_L),
        Some('s') => assert_eq!(letter, CLI_ARG_OPT_S),
        Some('w') => assert_eq!(letter, CLI_ARG_OPT_W),
        Some('v') => assert_eq!(letter, CLI_ARG_OPT_VERSION),
        _ => assert_eq!(letter, CLI_ARG_OPT_INVALID),
    }
}

/// `verified_cli_parse_options` over symbolic command lines of up to 5 entries, against a
/// direct statement of its rules: the first invalid option or `-v` ends the reading, `-l`
/// enables the math library, `-s` wins over `-w`, and nothing else changes the state.
#[kani::proof]
#[kani::unwind(7)]
fn proof_verified_cli_parse_options() {
    let buf: [u8; 5] = kani::any();
    let len: usize = kani::any();
    kani::assume(len <= 5);
    let kinds = &buf[..len];
    let (outcome, stop, math, policy) = verified_cli_parse_options(kinds);

    let first_stop = kinds
        .iter()
        .position(|&k| k == CLI_ARG_OPT_INVALID || k == CLI_ARG_OPT_VERSION);
    let read = &kinds[..first_stop.unwrap_or(len)];
    match first_stop {
        None => assert!(outcome == CLI_PARSE_RUN && stop == len),
        Some(i) => {
            assert_eq!(stop, i);
            let expected = if kinds[i] == CLI_ARG_OPT_INVALID {
                CLI_PARSE_ERROR
            } else {
                CLI_PARSE_VERSION
            };
            assert_eq!(outcome, expected);
        }
    }
    assert_eq!(math, read.contains(&CLI_ARG_OPT_L));
    let expected_policy = if read.contains(&CLI_ARG_OPT_S) {
        CLI_POLICY_REJECT
    } else if read.contains(&CLI_ARG_OPT_W) {
        CLI_POLICY_WARN
    } else {
        CLI_POLICY_ALLOW
    };
    assert_eq!(policy, expected_policy);
}

/// Bit-precise bounded model checking of `verified_repl_block_completeness` over arbitrary
/// 8-byte symbolic sequences ($256^8$ combinations of `/*`, `*/`, `"`, `\`, `\r`, `\n`, `{`, `}`).
#[kani::proof]
#[kani::unwind(9)]
fn proof_verified_repl_block_completeness_symbolic() {
    let buf: [u8; 8] = kani::any();
    let len: usize = kani::any();
    kani::assume(len <= 8);
    let slice = &buf[..len];

    let (count, is_incomplete) = verified_repl_block_completeness(slice);
    assert!(count >= -(len as i32) && count <= (len as i32));
    if count > 0 {
        assert!(is_incomplete);
    }
}

/// Resuming the block scan after a line that ends in a newline gives the result of scanning the
/// whole text, which is what lets `UnitAccumulator::push_line` scan each line once.
#[kani::proof]
#[kani::unwind(9)]
fn proof_verified_repl_block_scan_resumes_at_a_line_end() {
    let buf: [u8; 8] = kani::any();
    let len: usize = kani::any();
    let split: usize = kani::any();
    kani::assume(len <= 8 && 0 < split && split <= len);
    kani::assume(buf[split - 1] == b'\n');
    let start = (0, false, false);
    let whole = verified_repl_block_scan(&buf[..len], 0, start);
    let first = verified_repl_block_scan(&buf[..split], 0, start);
    assert_eq!(verified_repl_block_scan(&buf[..len], split, first), whole);
}

/// Verifies multi-step execution of `WrappedStdout` column state machine and `Lexer` cursor/line
/// advancement across arbitrary 8-byte streams without heap allocation overhead.
#[kani::proof]
#[kani::unwind(9)]
fn proof_multi_step_wrapped_stdout_and_lexer_cursor() {
    let raw: [u8; 8] = kani::any();
    let mut col: usize = kani::any();
    kani::assume(col <= POSIX_WRAP_COL_LIMIT);

    let mut pos: usize = 0;
    let mut line: usize = 1;

    for i in 0..8 {
        let is_nl = raw[i] == b'\n';
        let (next_col, should_wrap) = verified_wrapped_stdout_step(col, is_nl);
        assert!(next_col <= POSIX_WRAP_COL_LIMIT);
        if should_wrap {
            assert_eq!(col, POSIX_WRAP_COL_LIMIT);
            assert!(!is_nl);
        }
        col = next_col;

        let (in_bounds, valid_idx) = verified_lexer_peek_char_index(8, pos, 0);
        assert!(in_bounds && valid_idx == i);
        let (next_pos, next_line) = verified_lexer_advance_step(pos, line, is_nl);
        pos = next_pos;
        line = next_line;
    }
    assert_eq!(pos, 8);
    assert!((1..=9).contains(&line));
}

/// `verified_nesting_within_limit` decides `depth + height <= max_depth` without overflowing,
/// for all `usize` inputs.
#[kani::proof]
fn proof_verified_nesting_within_limit() {
    let depth: usize = kani::any();
    let height: usize = kani::any();
    let max_depth: usize = kani::any();
    let expected = (depth as u128) + (height as u128) <= (max_depth as u128);
    assert_eq!(
        verified_nesting_within_limit(depth, height, max_depth),
        expected
    );
}

/// `verified_unit_within_limit` is the comparison with `BC_UNIT_MAX`, for all `usize` inputs.
#[kani::proof]
fn proof_verified_unit_within_limit() {
    let len: usize = kani::any();
    assert_eq!(verified_unit_within_limit(len), len <= BC_UNIT_MAX);
}

/// `verified_utf8_char_len` (with `verified_utf8_second_ok`) agrees with `core`'s UTF-8 encoder
/// on every byte string of up to four bytes: it returns `k >= 2` exactly when the `k` bytes at
/// `pos` are the encoding of a `char`, and 1 otherwise. (`core::str::from_utf8` is not used as
/// the reference: its word-at-a-time loop does not unwind under a symbolic length.)
#[kani::proof]
#[kani::unwind(6)]
fn proof_verified_utf8_char_len() {
    let text: [u8; 4] = kani::any();
    let len: usize = kani::any();
    let pos: usize = kani::any();
    kani::assume(len <= 4);
    kani::assume(pos < len);
    let n = verified_utf8_char_len(&text[..len], pos);
    assert!((1..=4).contains(&n) && pos + n <= len);
    // Whether the `k` bytes at `pos` (2 <= k <= 4) encode a `char`: decode the payload bits and
    // check that encoding the result gives the same bytes back.
    let encodes = |k: usize| {
        if pos + k > len {
            return false;
        }
        let b = &text[pos..pos + k];
        let lead_bits = u32::from(b[0]) & (0x7f >> k);
        let cp = b[1..]
            .iter()
            .fold(lead_bits, |acc, &c| (acc << 6) | (u32::from(c) & 0x3f));
        let mut buf = [0u8; 4];
        char::from_u32(cp).is_some_and(|ch| ch.encode_utf8(&mut buf).as_bytes() == b)
    };
    if n >= 2 {
        assert!(encodes(n));
    }
    for k in 2..=4 {
        if k != n {
            assert!(!encodes(k));
        }
    }
}
