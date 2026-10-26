// SPDX-License-Identifier: MIT

//! Dual-mode formally verified kernels shared directly between Verus SMT verification
//! and production `#![no_std]` execution across `math.rs`, `eval.rs`, `parser.rs`, and `bc_cli`.
//!
//! Every function in this module is a **Single Source of Truth**:
//! - When compiled under Verus (`#[cfg(verus_keep_ghost)]`), `dual_verified!` expands inside
//!   `verus! { ... }` with full `requires` and `ensures` contracts checked by Z3.
//! - When compiled under standard Cargo / `rustc` (`#[cfg(not(verus_keep_ghost))]`),
//!   `dual_verified!` strips only the ghost specification clauses and compiles the exact
//!   same function body as an `#[inline]` `#![no_std]` Rust function.

#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
macro_rules! dual_verified {
    (
        $(
            pub const $cname:ident : $cty:ty = $cval:expr;
        )*
        $(
            $(#[$meta:meta])*
            pub fn $name:ident( $($arg:ident : $arg_ty:ty),* $(,)? ) -> ($ret_name:ident : $ret_ty:ty)
                $(requires [ $($req:tt)* ])?
                ensures [ $($ens:tt)* ]
            $body:block
        )+
    ) => {
        verus! {
            $(
                pub const $cname : $cty = $cval;
            )*
            $(
                $(#[$meta])*
                pub fn $name( $($arg : $arg_ty),* ) -> ($ret_name : $ret_ty)
                    $(requires $($req)*)?
                    ensures $($ens)*
                $body
            )+
        }
    };
}

#[cfg(not(verus_keep_ghost))]
macro_rules! dual_verified {
    (
        $(
            pub const $cname:ident : $cty:ty = $cval:expr;
        )*
        $(
            $(#[$meta:meta])*
            pub fn $name:ident( $($arg:ident : $arg_ty:ty),* $(,)? ) -> ($ret_name:ident : $ret_ty:ty)
                $(requires [ $($req:tt)* ])?
                ensures [ $($ens:tt)* ]
            $body:block
        )+
    ) => {
        $(
            pub const $cname : $cty = $cval;
        )*
        $(
            $(#[$meta])*
            #[inline]
            #[allow(
                clippy::manual_range_contains,
                clippy::manual_clamp,
                clippy::implicit_saturating_sub
            )]
            pub fn $name( $($arg : $arg_ty),* ) -> $ret_ty
            $body
        )+
    };
}

dual_verified! {
    pub const MAX_VERIFIED_SCALE: usize = 1_000_000_000;
    // `BC_SCALE_MAX` (`docs/COMPATIBILITY.md` §2): every `BCNum` scale stays within this bound,
    // which establishes the `MAX_VERIFIED_SCALE` preconditions of the scale kernels.
    pub const BC_SCALE_MAX: usize = MAX_VERIFIED_SCALE;
    // `BC_BASE_MAX`: the largest valid `obase`.
    pub const BC_BASE_MAX: usize = 2_147_483_647;
    // `BC_DIM_MAX`: array subscripts range over `0..BC_DIM_MAX`.
    pub const BC_DIM_MAX: usize = 16_777_216;
    // Largest valid `ibase` (POSIX).
    pub const IBASE_MAX: usize = 16;
    pub const POSIX_WRAP_COL_LIMIT: usize = 68;
    pub const TOK_ASSIGN_OP: u8 = 1;
    pub const TOK_PLUS_MINUS: u8 = 2;
    pub const TOK_MUL_OP: u8 = 3;
    pub const TOK_EXP_OP: u8 = 4;
    pub const CLI_ARG_OPT_L: u8 = 1;
    pub const CLI_ARG_OPT_INVALID: u8 = 2;
    pub const CLI_ARG_FILE: u8 = 3;
    /// Verified alphanumeric digit parser (`math.rs:BCNum::from_string`).
    ///
    /// Proves that any ASCII byte maps to a bounded value in $0..=35$, with exact mappings
    /// for `'0'..='9'` ($0..=9$) and `'A'..='Z'` / `'a'..='z'` ($10..=35$).
    pub fn verified_alphanumeric_char_val(c: u8) -> (res: usize)
        ensures [
            res <= 35,
            (b'0' <= c && c <= b'9') ==> res == (c - b'0') as usize,
            (b'A' <= c && c <= b'Z') ==> res == (c - b'A') as usize + 10,
            (b'a' <= c && c <= b'z') ==> res == (c - b'a') as usize + 10,
            !((b'0' <= c && c <= b'9') || (b'A' <= c && c <= b'Z') || (b'a' <= c && c <= b'z'))
                ==> res == 0,
        ]
    {
        if c >= b'0' && c <= b'9' {
            (c - b'0') as usize
        } else if c >= b'A' && c <= b'Z' {
            (c - b'A') as usize + 10
        } else if c >= b'a' && c <= b'z' {
            (c - b'a') as usize + 10
        } else {
            0
        }
    }

    /// Verified hexadecimal digit parser (`eval.rs:AssignOp` for `ibase`/`obase`).
    ///
    /// Proves that any ASCII byte maps to a bounded value in $0..=15$, with exact mappings
    /// for `'0'..='9'`, `'A'..='F'`, and `'a'..='f'`.
    pub fn verified_hex_char_val(c: u8) -> (res: usize)
        ensures [
            res <= 15,
            (b'0' <= c && c <= b'9') ==> res == (c - b'0') as usize,
            (b'A' <= c && c <= b'F') ==> res == (c - b'A') as usize + 10,
            (b'a' <= c && c <= b'f') ==> res == (c - b'a') as usize + 10,
            !((b'0' <= c && c <= b'9') || (b'A' <= c && c <= b'F') || (b'a' <= c && c <= b'f'))
                ==> res == 0,
        ]
    {
        if c >= b'0' && c <= b'9' {
            (c - b'0') as usize
        } else if c >= b'A' && c <= b'F' {
            (c - b'A') as usize + 10
        } else if c >= b'a' && c <= b'f' {
            (c - b'a') as usize + 10
        } else {
            0
        }
    }

    /// Verified POSIX scale and shift calculation for `BCNum::add` and `BCNum::sub`.
    pub fn verified_add_sub_scales(
        self_scale: usize,
        other_scale: usize,
    ) -> (res: (usize, usize, usize))
        ensures [
            res.0 == if self_scale >= other_scale { self_scale } else { other_scale },
            res.1 == res.0 - self_scale,
            res.2 == res.0 - other_scale,
            res.0 >= self_scale && res.0 >= other_scale,
            (res.1 == 0 || res.2 == 0),
        ]
    {
        let sr = if self_scale >= other_scale {
            self_scale
        } else {
            other_scale
        };
        let shift_a = sr - self_scale;
        let shift_b = sr - other_scale;
        (sr, shift_a, shift_b)
    }

    /// Verified POSIX scale and non-negative truncation shift calculation for `BCNum::mul`.
    ///
    /// POSIX IEEE Std 1003.1 mandates:
    /// `scale(a * b) = min(scale(a) + scale(b), max(scale, scale(a), scale(b)))`.
    /// Formally proves that `exact_scale >= sr` always holds (i.e., `diff = exact_scale - sr >= 0`).
    pub fn verified_mul_scale_and_shift(
        self_scale: usize,
        other_scale: usize,
        global_scale: usize,
    ) -> (res: (usize, usize))
        requires [
            self_scale <= MAX_VERIFIED_SCALE,
            other_scale <= MAX_VERIFIED_SCALE,
            global_scale <= MAX_VERIFIED_SCALE,
        ]
        ensures [
            // res = (sr, truncation_diff)
            res.0 <= self_scale + other_scale,
            res.0 >= self_scale || res.0 >= other_scale,
            res.1 == (self_scale + other_scale) - res.0,
            res.0 as int == (if self_scale + other_scale <= (if global_scale >= (if self_scale >= other_scale { self_scale } else { other_scale }) { global_scale } else { if self_scale >= other_scale { self_scale } else { other_scale } }) {
                self_scale + other_scale
            } else {
                (if global_scale >= (if self_scale >= other_scale { self_scale } else { other_scale }) { global_scale } else { if self_scale >= other_scale { self_scale } else { other_scale } }) as int
            }),
        ]
    {
        let max_ab = if self_scale >= other_scale {
            self_scale
        } else {
            other_scale
        };
        let max_all = if global_scale >= max_ab {
            global_scale
        } else {
            max_ab
        };
        let exact_scale = self_scale + other_scale;
        let sr = if exact_scale <= max_all {
            exact_scale
        } else {
            max_all
        };
        let diff = exact_scale - sr;
        (sr, diff)
    }

    /// Verified POSIX scale and signed decimal shift calculation for `BCNum::div`.
    pub fn verified_div_scale_and_shift(
        self_scale: usize,
        other_scale: usize,
        global_scale: usize,
    ) -> (res: (usize, i64))
        requires [
            self_scale <= MAX_VERIFIED_SCALE,
            other_scale <= MAX_VERIFIED_SCALE,
            global_scale <= MAX_VERIFIED_SCALE,
        ]
        ensures [
            res.0 == global_scale,
            res.1 == (other_scale as int) - (self_scale as int) + (global_scale as int),
        ]
    {
        let sr = global_scale;
        let shift: i64 = (other_scale as i64) - (self_scale as i64) + (sr as i64);
        (sr, shift)
    }

    /// Verified POSIX scale and radicand shift calculation for `BCNum::sqrt`.
    ///
    /// Proves that `2 * sr >= self.scale` always holds without underflow.
    pub fn verified_sqrt_scale_and_shift(
        self_scale: usize,
        global_scale: usize,
    ) -> (res: (usize, usize))
        requires [
            self_scale <= MAX_VERIFIED_SCALE,
            global_scale <= MAX_VERIFIED_SCALE,
        ]
        ensures [
            res.0 == if self_scale >= global_scale { self_scale } else { global_scale },
            res.0 >= self_scale,
            res.0 >= global_scale,
            res.1 == 2 * res.0 - self_scale,
            self_scale + res.1 == 2 * res.0,
        ]
    {
        let sr = if self_scale >= global_scale {
            self_scale
        } else {
            global_scale
        };
        let shift = 2 * sr - self_scale;
        (sr, shift)
    }

    /// Verified POSIX `length(x)` significant digit count calculation (`math.rs:BCNum::length`).
    pub fn verified_bcnum_length(
        int_part_is_zero: bool,
        int_part_digits: usize,
        scale: usize,
    ) -> (res: usize)
        requires [
            scale <= MAX_VERIFIED_SCALE,
            int_part_digits <= MAX_VERIFIED_SCALE,
            !int_part_is_zero ==> int_part_digits >= 1,
        ]
        ensures [
            res >= 1,
            res >= scale,
            int_part_is_zero ==> res == (if scale >= 1 { scale } else { 1 }),
            !int_part_is_zero ==> res == int_part_digits + scale,
        ]
    {
        if int_part_is_zero {
            if scale >= 1 {
                scale
            } else {
                1
            }
        } else {
            int_part_digits + scale
        }
    }

    /// Verified Bessel function negative-order parity identity $J_{-n}(x) = (-1)^n J_n(x)$
    /// (`math.rs:bc_bessel`).
    pub fn verified_bessel_negative_order_parity(n_i64: i64) -> (res: (i64, i64))
        requires [
            n_i64 > i64::MIN,
        ]
        ensures [
            // res = (n_abs, sign)
            res.0 >= 0,
            res.0 == if n_i64 < 0 { -(n_i64 as int) } else { n_i64 as int },
            res.1 == 1 || res.1 == -1,
            n_i64 >= 0 ==> res.1 == 1,
            (n_i64 < 0 && (-(n_i64 as int)) % 2 == 1) ==> res.1 == -1,
            (n_i64 < 0 && (-(n_i64 as int)) % 2 == 0) ==> res.1 == 1,
        ]
    {
        if n_i64 < 0 {
            let neg_n: i64 = -n_i64;
            let neg_n_u64: u64 = neg_n as u64;
            let rem: u64 = neg_n_u64 % 2;
            let sign: i64 = if rem == 1 { -1 } else { 1 };
            (neg_n, sign)
        } else {
            (n_i64, 1)
        }
    }

    /// Verified single-character state transition for `WrappedStdout` (`eval.rs`).
    ///
    /// Returns `(next_col, should_emit_backslash_newline_before_char)`.
    pub fn verified_wrapped_stdout_step(col: usize, is_newline: bool) -> (res: (usize, bool))
        requires [
            col <= POSIX_WRAP_COL_LIMIT,
        ]
        ensures [
            res.0 <= POSIX_WRAP_COL_LIMIT,
            is_newline ==> (res.0 == 0 && !res.1),
            (!is_newline && col < POSIX_WRAP_COL_LIMIT) ==> (res.0 == col + 1 && !res.1),
            (!is_newline && col == POSIX_WRAP_COL_LIMIT) ==> (res.0 == 1 && res.1 && col + 2 <= 70),
        ]
    {
        if is_newline {
            (0, false)
        } else if col >= POSIX_WRAP_COL_LIMIT {
            (1, true)
        } else {
            (col + 1, false)
        }
    }

    /// Verified exponent shift calculation for relational operators (`eval.rs`).
    pub fn verified_relational_scale_shifts(
        l_scale: usize,
        r_scale: usize,
    ) -> (res: (usize, usize))
        requires [
            l_scale <= MAX_VERIFIED_SCALE,
            r_scale <= MAX_VERIFIED_SCALE,
        ]
        ensures [
            l_scale > r_scale ==> (res.0 == 0 && res.1 == l_scale - r_scale),
            l_scale < r_scale ==> (res.0 == r_scale - l_scale && res.1 == 0),
            l_scale == r_scale ==> (res.0 == 0 && res.1 == 0),
            l_scale + res.0 == r_scale + res.1,
        ]
    {
        let diff: i64 = (l_scale as i64) - (r_scale as i64);
        if diff > 0 {
            (0, (diff as usize))
        } else if diff < 0 {
            ((-diff) as usize, 0)
        } else {
            (0, 0)
        }
    }

    /// Verified check for valid bc numeric literal characters (`0..=9` or `A..=F`) (`parser.rs`).
    pub fn verified_is_bc_digit(b: u32) -> (res: bool)
        ensures [
            res == ((48 <= b && b <= 57) || (65 <= b && b <= 70)),
        ]
    {
        (b >= 48 && b <= 57) || (b >= 65 && b <= 70)
    }

    /// Verified `Lexer::peek_token` buffer index clamping (`parser.rs`).
    pub fn verified_lexer_peek_token_index(buffer_len: usize, offset: usize) -> (res: usize)
        requires [
            buffer_len >= 1,
        ]
        ensures [
            res < buffer_len,
            offset < buffer_len ==> res == offset,
            offset >= buffer_len ==> res == buffer_len - 1,
        ]
    {
        let last_idx = buffer_len - 1;
        if offset <= last_idx {
            offset
        } else {
            last_idx
        }
    }

    /// Verified Pratt parser `next_min_prec` calculation (`parser.rs`).
    pub fn verified_pratt_next_min_prec(op_prec: i8, right_assoc: bool) -> (res: i8)
        requires [
            1 <= op_prec && op_prec <= 10,
        ]
        ensures [
            right_assoc ==> res == op_prec,
            !right_assoc ==> (res == op_prec + 1 && res > op_prec),
        ]
    {
        if right_assoc {
            op_prec
        } else {
            op_prec + 1
        }
    }

    /// Verified POSIX `pow` target scale `sr` and non-negative truncation shift `diff` (`math.rs:BCNum::pow`).
    pub fn verified_pow_scale_and_shift(
        res_scale: usize,
        a_scale: usize,
        global_scale: usize,
    ) -> (res: (usize, usize))
        requires [
            res_scale <= MAX_VERIFIED_SCALE,
            a_scale <= MAX_VERIFIED_SCALE,
            global_scale <= MAX_VERIFIED_SCALE,
        ]
        ensures [
            // res = (sr, diff)
            res.0 <= res_scale,
            res.0 <= if global_scale >= a_scale { global_scale } else { a_scale },
            res.1 == res_scale - res.0,
            res.0 + res.1 == res_scale,
            res.0 == (if res_scale <= (if global_scale >= a_scale { global_scale } else { a_scale }) {
                res_scale
            } else {
                if global_scale >= a_scale { global_scale } else { a_scale }
            }),
        ]
    {
        let max_g_a = if global_scale >= a_scale {
            global_scale
        } else {
            a_scale
        };
        let sr = if res_scale <= max_g_a {
            res_scale
        } else {
            max_g_a
        };
        let diff = res_scale - sr;
        (sr, diff)
    }

    /// Verified zero-padding count for multi-digit `obase > 16` formatting (`math.rs:format_obase`).
    pub fn verified_multi_digit_obase_pad_zeros(digit_width: usize, rem_len: usize) -> (res: usize)
        ensures [
            digit_width > rem_len ==> (res == digit_width - rem_len && res + rem_len == digit_width),
            digit_width <= rem_len ==> res == 0,
        ]
    {
        if digit_width > rem_len {
            digit_width - rem_len
        } else {
            0
        }
    }

    /// Verified internal guard precision calculation for transcendental functions (`math.rs`).
    pub fn verified_transcendental_guard_prec(
        x_scale: usize,
        global_scale: usize,
        extra_prec: usize,
    ) -> (res: usize)
        requires [
            x_scale <= MAX_VERIFIED_SCALE,
            global_scale <= MAX_VERIFIED_SCALE,
            extra_prec <= MAX_VERIFIED_SCALE,
        ]
        ensures [
            res >= 15,
            res >= x_scale + extra_prec + 15,
            res >= global_scale + extra_prec + 15,
            res == (if x_scale >= global_scale { x_scale } else { global_scale }) + extra_prec + 15,
        ]
    {
        let base_prec = if x_scale >= global_scale {
            x_scale
        } else {
            global_scale
        };
        base_prec + extra_prec + 15
    }

    /// Verified control-flow short-circuit check (`eval.rs:Evaluator::execute`).
    pub fn verified_should_abort_execution(
        break_flag: bool,
        return_flag: bool,
        quit_flag: bool,
    ) -> (res: bool)
        ensures [
            res == (break_flag || return_flag || quit_flag),
        ]
    {
        break_flag || return_flag || quit_flag
    }

    /// Verified post-body loop flag transition for `while` and `for` loops (`eval.rs`).
    ///
    /// Returns `(should_exit_loop, next_break_flag)`.
    pub fn verified_loop_post_body_action(
        break_flag: bool,
        return_flag: bool,
        quit_flag: bool,
    ) -> (res: (bool, bool))
        ensures [
            // res = (should_exit_loop, next_break_flag)
            res.0 == (break_flag || return_flag || quit_flag),
            !res.1,
        ]
    {
        (break_flag || return_flag || quit_flag, false)
    }

    /// Verified single-character cursor and line advancement (`parser.rs:Lexer::advance_char`).
    pub fn verified_lexer_advance_step(
        pos: usize,
        line: usize,
        is_newline: bool,
    ) -> (res: (usize, usize))
        requires [
            pos < 1_000_000_000,
            line <= 1_000_000_000,
        ]
        ensures [
            res.0 == pos + 1,
            is_newline ==> res.1 == line + 1,
            !is_newline ==> res.1 == line,
        ]
    {
        let next_line = if is_newline { line + 1 } else { line };
        (pos + 1, next_line)
    }

    /// Verified C-FFI output buffer capacity check (`crates/bc_c_api/src/lib.rs`).
    ///
    /// Proves that when `res == true`, `buf_size >= 1` and `output_len < buf_size`,
    /// guaranteeing that copying `output_len` bytes and writing a trailing NUL (`0u8`)
    /// at index `output_len` is strictly within `0..buf_size` without integer overflow.
    pub fn verified_c_ffi_check_buf_capacity(output_len: usize, buf_size: usize) -> (res: bool)
        ensures [
            res == (output_len < buf_size),
            res ==> (buf_size >= 1 && output_len <= buf_size - 1),
        ]
    {
        output_len < buf_size
    }

    /// Verified character classification for the Zephyr RTOS interactive serial REPL
    /// (`crates/bc_zephyr/src/lib.rs:run_repl_with`).
    ///
    /// Returns:
    /// - `1`: Newline (`\r` or `\n`)
    /// - `2`: Backspace / Delete (`0x08` or `0x7F`)
    /// - `3`: Ctrl+C interrupt (`0x03`)
    /// - `4`: Printable ASCII (`0x20..=0x7E`)
    /// - `0`: Ignored control/non-ASCII byte
    pub fn verified_zephyr_classify_char(b: u8) -> (res: u8)
        ensures [
            res <= 4,
            (b == 13 || b == 10) <==> res == 1,
            (b == 8 || b == 127) <==> res == 2,
            (b == 3) <==> res == 3,
            (32 <= b && b <= 126) <==> res == 4,
        ]
    {
        if b == 13 || b == 10 {
            1
        } else if b == 8 || b == 127 {
            2
        } else if b == 3 {
            3
        } else if b >= 32 && b <= 126 {
            4
        } else {
            0
        }
    }

    /// Verified unsigned decimal shift and direction `(shift_digits, should_multiply)`
    /// for fixed-point scale conversions (`math.rs:Decimal::from_bc_num` / `Decimal::to_bc_num`).
    pub fn verified_decimal_scale_shift(
        src_scale: usize,
        dst_scale: usize,
    ) -> (res: (usize, bool))
        ensures [
            dst_scale >= src_scale ==> (res.1 && res.0 == dst_scale - src_scale && src_scale + res.0 == dst_scale),
            dst_scale < src_scale ==> (!res.1 && res.0 == src_scale - dst_scale && dst_scale + res.0 == src_scale),
        ]
    {
        if dst_scale >= src_scale {
            (dst_scale - src_scale, true)
        } else {
            (src_scale - dst_scale, false)
        }
    }

    /// Verified register clamping with warning classification for `scale`, `ibase`, and
    /// `obase` assignments (`eval.rs`, `docs/COMPATIBILITY.md` §3.3).
    ///
    /// `magnitude` is the absolute value of the integer part saturated to `usize::MAX`, and
    /// `negative` is the sign of the assigned value. Returns `(clamped, warning_kind)`:
    /// - `-2`: the value is negative ("negative <reg>, set to <min>")
    /// - `-1`: `magnitude < min` ("<reg> too small, set to <min>")
    /// - `1`: `magnitude > max` ("<reg> too large, set to <max>")
    /// - `0`: in range (no warning)
    pub fn verified_clamp_register(
        magnitude: usize,
        negative: bool,
        min: usize,
        max: usize,
    ) -> (res: (usize, i8))
        requires [
            min <= max,
        ]
        ensures [
            min <= res.0 && res.0 <= max,
            negative <==> (res.1 == -2 && res.0 == min),
            (!negative && magnitude < min) <==> (res.1 == -1 && res.0 == min),
            (!negative && magnitude > max) <==> (res.1 == 1 && res.0 == max),
            (!negative && min <= magnitude && magnitude <= max) <==> (res.1 == 0 && res.0 == magnitude),
        ]
    {
        if negative {
            (min, -2)
        } else if magnitude < min {
            (min, -1)
        } else if magnitude > max {
            (max, 1)
        } else {
            (magnitude, 0)
        }
    }

    /// Verified Pratt parser infix operator precedence, associativity, and `next_min_prec`
    /// (`parser.rs:Parser::get_infix_info`).
    ///
    /// Returns `(op_prec, right_assoc, next_min_prec)`.
    pub fn verified_pratt_infix_info(tok_kind: u8) -> (res: (i8, bool, i8))
        ensures [
            tok_kind == TOK_ASSIGN_OP ==> (res.0 == 1 && res.1 && res.2 == 1),
            tok_kind == TOK_PLUS_MINUS ==> (res.0 == 2 && !res.1 && res.2 == 3),
            tok_kind == TOK_MUL_OP ==> (res.0 == 3 && !res.1 && res.2 == 4),
            tok_kind == TOK_EXP_OP ==> (res.0 == 4 && res.1 && res.2 == 4),
            (tok_kind < 1 || tok_kind > 4) ==> (res.0 == -1 && !res.1 && res.2 == 0),
            res.0 >= 1 ==> (if res.1 { res.2 == res.0 } else { res.2 == res.0 + 1 && res.2 > res.0 }),
        ]
    {
        let (op_prec, right_assoc): (i8, bool) = if tok_kind == TOK_ASSIGN_OP {
            (1, true)
        } else if tok_kind == TOK_PLUS_MINUS {
            (2, false)
        } else if tok_kind == TOK_MUL_OP {
            (3, false)
        } else if tok_kind == TOK_EXP_OP {
            (4, true)
        } else {
            (-1, false)
        };

        let next_min_prec: i8 = if op_prec < 0 {
            0
        } else {
            verified_pratt_next_min_prec(op_prec, right_assoc)
        };

        (op_prec, right_assoc, next_min_prec)
    }

    /// Verified bounds-safe lookahead index calculation for `Lexer::peek_char` (`parser.rs`).
    ///
    /// Returns `(in_bounds, valid_idx)`.
    pub fn verified_lexer_peek_char_index(
        text_len: usize,
        pos: usize,
        offset: usize,
    ) -> (res: (bool, usize))
        requires [
            pos <= text_len,
            text_len <= MAX_VERIFIED_SCALE,
            offset <= MAX_VERIFIED_SCALE,
        ]
        ensures [
            (pos + offset < text_len) ==> (res.0 && res.1 == pos + offset && res.1 < text_len),
            (pos + offset >= text_len) ==> (!res.0 && res.1 == 0),
        ]
    {
        let idx = pos + offset;
        if idx < text_len {
            (true, idx)
        } else {
            (false, 0)
        }
    }

    /// Verified identifier continuation character check (`a..=z`, `0..=9`, or `_`) (`parser.rs`).
    pub fn verified_is_ident_continue(b: u32) -> (res: bool)
        ensures [
            res == ((97 <= b && b <= 122) || (48 <= b && b <= 57) || b == 95),
        ]
    {
        (b >= 97 && b <= 122) || (b >= 48 && b <= 57) || b == 95
    }

    /// Verified CLI argument classification (`crates/bc_cli/src/main.rs:run_app`).
    ///
    /// Returns:
    /// - `CLI_ARG_OPT_L` (`1`): `"-l"`
    /// - `CLI_ARG_OPT_INVALID` (`2`): any other argument starting with `'-'`
    /// - `CLI_ARG_FILE` (`3`): filename operand
    pub fn verified_cli_classify_arg(bytes: &[u8]) -> (res: u8)
        ensures [
            (bytes@.len() == 2 && bytes@[0] == 45 && bytes@[1] == 108) <==> res == CLI_ARG_OPT_L,
            (bytes@.len() >= 1 && bytes@[0] == 45 && !(bytes@.len() == 2 && bytes@[1] == 108))
                <==> res == CLI_ARG_OPT_INVALID,
            (bytes@.len() == 0 || bytes@[0] != 45) <==> res == CLI_ARG_FILE,
        ]
    {
        let len = bytes.len();
        if len >= 1 && bytes[0] == 45 {
            if len == 2 && bytes[1] == 108 {
                CLI_ARG_OPT_L
            } else {
                CLI_ARG_OPT_INVALID
            }
        } else {
            CLI_ARG_FILE
        }
    }

    /// Verified POSIX `bc` initial `scale` register value (`20` when `-l` is enabled, `0` otherwise).
    pub fn verified_cli_initial_scale(math_enabled: bool) -> (res: usize)
        ensures [
            math_enabled ==> res == 20,
            !math_enabled ==> res == 0,
        ]
    {
        if math_enabled {
            20
        } else {
            0
        }
    }
}

#[cfg(verus_keep_ghost)]
macro_rules! dual_verified_repl_scanner {
    (
        $(#[$meta:meta])*
        pub fn $name:ident($arg:ident : $arg_ty:ty) -> ($ret_name:ident : $ret_ty:ty)
            requires [ $($req:tt)* ]
            ensures [ $($ens:tt)* ]
            locals [ $($loc_tt:tt)* ]
            while ($cond:expr)
                invariant [ $($inv:tt)* ]
                decreases ($dec:expr)
            $loop_body:block
            return $ret_expr:expr;
    ) => {
        verus! {
            $(#[$meta])*
            pub fn $name($arg : $arg_ty) -> ($ret_name : $ret_ty)
                requires $($req)*
                ensures $($ens)*
            {
                $($loc_tt)*
                while $cond
                    invariant $($inv)*
                    decreases $dec
                $loop_body
                $ret_expr
            }
        }
    };
}

#[cfg(not(verus_keep_ghost))]
macro_rules! dual_verified_repl_scanner {
    (
        $(#[$meta:meta])*
        pub fn $name:ident($arg:ident : $arg_ty:ty) -> ($ret_name:ident : $ret_ty:ty)
            requires [ $($req:tt)* ]
            ensures [ $($ens:tt)* ]
            locals [ $($loc_tt:tt)* ]
            while ($cond:expr)
                invariant [ $($inv:tt)* ]
                decreases ($dec:expr)
            $loop_body:block
            return $ret_expr:expr;
    ) => {
        $(#[$meta])*
        #[inline]
        #[allow(clippy::assign_op_pattern)]
        pub fn $name($arg : $arg_ty) -> $ret_ty {
            $($loc_tt)*
            while $cond $loop_body
            $ret_expr
        }
    };
}

dual_verified_repl_scanner! {
    /// Verified CLI REPL `count_open_braces` & `is_block_incomplete` state machine
    /// (`crates/bc_cli/src/main.rs`).
    ///
    /// Scans an arbitrary byte slice tracking `/* ... */` comments, `"..."` strings
    /// (including `\\\n` and `\\\r\n` continuations), and `{` / `}` brace nesting depth.
    pub fn verified_repl_block_completeness(text: &[u8]) -> (res: (i32, bool))
        requires [
            text@.len() <= 1_000_000_000,
        ]
        ensures [
            // res = (open_brace_count, is_incomplete)
            -(text@.len() as int) <= (res.0 as int) && (res.0 as int) <= (text@.len() as int),
            res.0 > 0 ==> res.1,
        ]
        locals [
            let mut count: i32 = 0;
            let mut in_comment: bool = false;
            let mut in_string: bool = false;
            let mut i: usize = 0;
            let len: usize = text.len();
        ]
        while (i < len)
            invariant [
                0 <= i <= len,
                len == text@.len(),
                len <= 1_000_000_000,
                !(in_comment && in_string),
                -(i as int) <= (count as int) && (count as int) <= (i as int),
            ]
            decreases (len - i)
        {
            let c = text[i];
            if in_comment {
                if c == b'*' && len - i >= 2 && text[i + 1] == b'/' {
                    in_comment = false;
                    i = i + 2;
                } else {
                    i = i + 1;
                }
            } else if in_string {
                if c == b'"' {
                    in_string = false;
                    i = i + 1;
                } else if c == b'\\' && len - i >= 2 && text[i + 1] == b'\n' {
                    i = i + 2;
                } else if c == b'\\' && len - i >= 3 && text[i + 1] == b'\r' && text[i + 2] == b'\n' {
                    i = i + 3;
                } else {
                    i = i + 1;
                }
            } else if c == b'/' && len - i >= 2 && text[i + 1] == b'*' {
                in_comment = true;
                i = i + 2;
            } else if c == b'"' {
                in_string = true;
                i = i + 1;
            } else if c == b'{' {
                count = count + 1;
                i = i + 1;
            } else if c == b'}' {
                count = count - 1;
                i = i + 1;
            } else {
                i = i + 1;
            }
        }
        return (count, count > 0 || in_comment || in_string);
}
