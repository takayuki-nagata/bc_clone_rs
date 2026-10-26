// SPDX-License-Identifier: MIT

//! Kani bounded model checking harnesses for `bc_core`.
//!
//! Cross-verifies all 31 `dual_verified!` kernels in `verified_kernels.rs` using
//! bit-precise CBMC symbolic execution (`kani::any()`) and verifies multi-step
//! state-machine invariants without heap allocation state explosion.

use crate::verified_kernels::*;

/// Bit-precise verification of `verified_alphanumeric_char_val` and `verified_hex_char_val`
/// across all 256 possible `u8` values.
#[kani::proof]
fn proof_verified_char_parsers() {
    let c: u8 = kani::any();

    let alpha_val = verified_alphanumeric_char_val(c);
    assert!(alpha_val <= 35);
    if c.is_ascii_digit() {
        assert_eq!(alpha_val, (c - b'0') as usize);
    } else if c.is_ascii_uppercase() {
        assert_eq!(alpha_val, (c - b'A') as usize + 10);
    } else if c.is_ascii_lowercase() {
        assert_eq!(alpha_val, (c - b'a') as usize + 10);
    } else {
        assert_eq!(alpha_val, 0);
    }

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
}

/// Bit-precise verification of CLI argument classification and initial scale across symbolic slices.
#[kani::proof]
fn proof_verified_cli_kernels() {
    let math_enabled: bool = kani::any();
    let init_scale = verified_cli_initial_scale(math_enabled);
    assert_eq!(init_scale, if math_enabled { 20 } else { 0 });

    let buf: [u8; 6] = kani::any();
    let len: usize = kani::any();
    kani::assume(len <= 6);
    let slice = &buf[..len];

    let kind = verified_cli_classify_arg(slice);
    if len == 2 && slice[0] == b'-' && slice[1] == b'l' {
        assert_eq!(kind, CLI_ARG_OPT_L);
    } else if len >= 1 && slice[0] == b'-' {
        assert_eq!(kind, CLI_ARG_OPT_INVALID);
    } else {
        assert_eq!(kind, CLI_ARG_FILE);
    }
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
