// SPDX-License-Identifier: MIT

//! Dual-mode formally verified kernels shared directly between Verus SMT verification
//! and production `#![no_std]` execution across `math.rs`, `eval/`, `parser/`, and `bc_cli`.
//!
//! Every function in this module is a **Single Source of Truth**:
//! - When compiled under Verus (`#[cfg(verus_keep_ghost)]`), `dual_verified!` expands inside
//!   `verus! { ... }` with full `requires` and `ensures` contracts checked by Z3.
//! - When compiled under standard Cargo / `rustc` (`#[cfg(not(verus_keep_ghost))]`),
//!   `dual_verified!` strips only the ghost specification clauses and compiles the exact
//!   same function body as an `#[inline]` `#![no_std]` Rust function.
//!
//! The integer casts in the kernel bodies are lossless: each kernel's `ensures` clause states
//! the result over mathematical integers, so Verus proves that no cast wraps or truncates for
//! inputs that satisfy its `requires` clause (and Kani re-checks them bit-precisely).
//!
//! The `requires` clauses are not checked at run time, so a kernel is `pub` only if a front
//! end calls it; the others are `pub(crate)`, called only by verified code or by the callers
//! that AGENTS.md lists. Of the public kernels, only `verified_repl_block_completeness` has a
//! precondition.
#![allow(
    clippy::cast_possible_truncation,
    clippy::cast_sign_loss,
    clippy::cast_possible_wrap,
    reason = "proved lossless by the Verus contracts (see the module documentation)"
)]

#[cfg(not(verus_keep_ghost))]
use verus_builtin_macros::verus;
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
            pub $(($scope:tt))? fn $name:ident( $($arg:ident : $arg_ty:ty),* $(,)? ) -> ($ret_name:ident : $ret_ty:ty)
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
                pub $(($scope))? fn $name( $($arg : $arg_ty),* ) -> ($ret_name : $ret_ty)
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
            pub $(($scope:tt))? fn $name:ident( $($arg:ident : $arg_ty:ty),* $(,)? ) -> ($ret_name:ident : $ret_ty:ty)
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
            pub $(($scope))? fn $name( $($arg : $arg_ty),* ) -> $ret_ty
            $body
        )+
    };
}

dual_verified! {
    pub const MAX_VERIFIED_SCALE: usize = 1_000_000_000;
    // `BC_SCALE_MAX` (`docs/COMPATIBILITY.md` §2): every `BCNum` scale stays within this bound,
    // which establishes the `MAX_VERIFIED_SCALE` preconditions of the scale kernels.
    pub const BC_SCALE_MAX: usize = MAX_VERIFIED_SCALE;
    // The longest input unit (`docs/COMPATIBILITY.md` §2), which establishes the length
    // preconditions of the lexer kernels and of `verified_repl_block_completeness`.
    pub const BC_UNIT_MAX: usize = 1_000_000_000;
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
    pub const CLI_ARG_OPT_S: u8 = 4;
    pub const CLI_ARG_OPT_W: u8 = 5;
    pub const CLI_ARG_END_OF_OPTIONS: u8 = 6;
    pub const CLI_ARG_OPT_CLUSTER: u8 = 7;

    /// Verified hexadecimal digit parser (`eval/` assignments to `ibase`/`obase`).
    ///
    /// Proves that any ASCII byte maps to a bounded value in $0..=15$, with exact mappings
    /// for `'0'..='9'`, `'A'..='F'`, and `'a'..='f'`.
    pub(crate) fn verified_hex_char_val(c: u8) -> (res: usize)
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
    pub(crate) fn verified_add_sub_scales(
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
    pub(crate) fn verified_mul_scale_and_shift(
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
    pub(crate) fn verified_div_scale_and_shift(
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
    pub(crate) fn verified_sqrt_scale_and_shift(
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
    pub(crate) fn verified_bcnum_length(
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
    pub(crate) fn verified_bessel_negative_order_parity(n_i64: i64) -> (res: (i64, i64))
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

    /// Verified single-character state transition for `WrappedStdout` (`format::wrap_output`).
    ///
    /// Returns `(next_col, should_emit_backslash_newline_before_char)`.
    pub(crate) fn verified_wrapped_stdout_step(col: usize, is_newline: bool) -> (res: (usize, bool))
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

    /// Verified exponent shift calculation for relational operators (`BCNum::cmp_val`).
    pub(crate) fn verified_relational_scale_shifts(
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

    /// Verified check for valid bc numeric literal characters (`0..=9` or `A..=F`) (`parser/lexer.rs`).
    pub(crate) fn verified_is_bc_digit(b: u32) -> (res: bool)
        ensures [
            res == ((48 <= b && b <= 57) || (65 <= b && b <= 70)),
        ]
    {
        (b >= 48 && b <= 57) || (b >= 65 && b <= 70)
    }

    /// Verified `Lexer::try_peek_token` buffer index clamping (`parser/lexer.rs`).
    pub(crate) fn verified_lexer_peek_token_index(buffer_len: usize, offset: usize) -> (res: usize)
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

    /// Verified Pratt parser `next_min_prec` calculation (`parser/parse.rs`).
    pub(crate) fn verified_pratt_next_min_prec(op_prec: i8, right_assoc: bool) -> (res: i8)
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
    pub(crate) fn verified_pow_scale_and_shift(
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
    pub(crate) fn verified_multi_digit_obase_pad_zeros(digit_width: usize, rem_len: usize) -> (res: usize)
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
    pub(crate) fn verified_transcendental_guard_prec(
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

    /// Verified nesting-limit check (`parser/parse.rs` and `eval/`): whether `depth` enclosing
    /// levels plus `height` more stay within `max_depth`, computed without overflow.
    pub(crate) fn verified_nesting_within_limit(depth: usize, height: usize, max_depth: usize) -> (res: bool)
        ensures [
            res == ((depth as int) + (height as int) <= (max_depth as int)),
        ]
    {
        height <= max_depth && depth <= max_depth - height
    }

    /// Whether an input unit of `len` bytes is within `BC_UNIT_MAX`.
    pub fn verified_unit_within_limit(len: usize) -> (res: bool)
        ensures [
            res == (len <= BC_UNIT_MAX),
        ]
    {
        len <= BC_UNIT_MAX
    }

    /// Verified control-flow short-circuit check (`eval/machine/stmt.rs`,
    /// `eval/machine/quick.rs`, `eval/leaf.rs`).
    pub(crate) fn verified_should_abort_execution(
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

    /// Verified post-body loop flag transition for `while` and `for` loops (`eval/machine.rs`,
    /// `eval/machine/quick.rs`).
    ///
    /// Returns `(should_exit_loop, next_break_flag)`.
    pub(crate) fn verified_loop_post_body_action(
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

    /// Verified single-character cursor and line advancement (`parser/lexer.rs:Lexer::advance_char`).
    pub(crate) fn verified_lexer_advance_step(
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
    /// for fixed-point scale conversions (`mathlib::ball::Ball::from_bcnum`).
    pub(crate) fn verified_decimal_scale_shift(
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
    /// `obase` assignments (`eval/ops.rs`; `eval/mod.rs` for `set_scale`;
    /// `docs/COMPATIBILITY.md` §3.3).
    ///
    /// `magnitude` is the absolute value of the integer part saturated to `usize::MAX`, and
    /// `negative` is the sign of the assigned value. Returns `(clamped, warning_kind)`:
    /// - `-2`: the value is negative ("negative <reg>, set to <min>")
    /// - `-1`: `magnitude < min` ("<reg> too small, set to <min>")
    /// - `1`: `magnitude > max` ("<reg> too large, set to <max>")
    /// - `0`: in range (no warning)
    pub(crate) fn verified_clamp_register(
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
    /// (`parser/parse.rs:Parser::get_infix_info`).
    ///
    /// Returns `(op_prec, right_assoc, next_min_prec)`.
    pub(crate) fn verified_pratt_infix_info(tok_kind: u8) -> (res: (i8, bool, i8))
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

    /// Verified bounds-safe lookahead index calculation for `Lexer::peek_char` (`parser/lexer.rs`).
    ///
    /// Returns `(in_bounds, valid_idx)`.
    pub(crate) fn verified_lexer_peek_char_index(
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

    /// Verified identifier continuation character check (`a..=z`, `0..=9`, or `_`) (`parser/lexer.rs`).
    pub(crate) fn verified_is_ident_continue(b: u32) -> (res: bool)
        ensures [
            res == ((97 <= b && b <= 122) || (48 <= b && b <= 57) || b == 95),
        ]
    {
        (b >= 97 && b <= 122) || (b >= 48 && b <= 57) || b == 95
    }

    /// Verified test of the second byte of a UTF-8 sequence led by `lead` (`parser/lexer.rs`): the
    /// specification's `second_ok` (no overlong forms, surrogates or code points above
    /// U+10FFFF).
    pub(crate) fn verified_utf8_second_ok(lead: u8, b: u8) -> (res: bool)
        ensures [
            res == bc_spec::lexer::second_ok(lead, b),
        ]
    {
        if lead == 0xe0 {
            0xa0 <= b && b <= 0xbf
        } else if lead == 0xed {
            0x80 <= b && b <= 0x9f
        } else if lead == 0xf0 {
            0x90 <= b && b <= 0xbf
        } else if lead == 0xf4 {
            0x80 <= b && b <= 0x8f
        } else {
            0x80 <= b && b <= 0xbf
        }
    }

    /// Verified length of the character at `text[pos]` for an `illegal character` diagnostic
    /// (`parser/lexer.rs`): the length of the well-formed UTF-8 sequence that starts there, or 1 if
    /// none does (the specification's `utf8_len`).
    pub(crate) fn verified_utf8_char_len(text: &[u8], pos: usize) -> (n: usize)
        requires [
            pos < text@.len(),
        ]
        ensures [
            1 <= n <= 4,
            pos + n <= text@.len(),
            n == bc_spec::lexer::utf8_len(text@.subrange(pos as int, text@.len() as int)),
        ]
    {
        let c = text[pos];
        let rem = text.len() - pos;
        if 0xc2 <= c && c <= 0xdf && rem >= 2 && 0x80 <= text[pos + 1] && text[pos + 1] <= 0xbf {
            2
        } else if 0xe0 <= c && c <= 0xef && rem >= 3 && verified_utf8_second_ok(c, text[pos + 1])
            && 0x80 <= text[pos + 2] && text[pos + 2] <= 0xbf
        {
            3
        } else if 0xf0 <= c && c <= 0xf4 && rem >= 4 && verified_utf8_second_ok(c, text[pos + 1])
            && 0x80 <= text[pos + 2] && text[pos + 2] <= 0xbf
            && 0x80 <= text[pos + 3] && text[pos + 3] <= 0xbf
        {
            4
        } else {
            1
        }
    }

    /// Verified CLI argument classification (`crates/bc_cli/src/main.rs:run_app`), following
    /// the XBD 12.2 Utility Syntax Guidelines that POSIX requires of `bc`.
    ///
    /// Returns:
    /// - `CLI_ARG_FILE` (`3`): a file operand. After `--` (`options_ended`) every argument is
    ///   an operand; so are `-` and the empty string (Guideline 13 leaves `-` to the utility).
    /// - `CLI_ARG_END_OF_OPTIONS` (`6`): `"--"`, which ends the options (Guideline 10)
    /// - `CLI_ARG_OPT_INVALID` (`2`): a long option `--name`, which `bc_clone` does not support
    /// - `CLI_ARG_OPT_CLUSTER` (`7`): `-` followed by one or more option letters, possibly
    ///   grouped (`-ls`, Guideline 5); each letter is classified by
    ///   `verified_cli_classify_option_char`
    pub fn verified_cli_classify_arg(bytes: &[u8], options_ended: bool) -> (res: u8)
        ensures [
            (options_ended || bytes@.len() < 2 || bytes@[0] != 45) <==> res == CLI_ARG_FILE,
            (!options_ended && bytes@.len() == 2 && bytes@[0] == 45 && bytes@[1] == 45)
                <==> res == CLI_ARG_END_OF_OPTIONS,
            (!options_ended && bytes@.len() > 2 && bytes@[0] == 45 && bytes@[1] == 45)
                <==> res == CLI_ARG_OPT_INVALID,
            (!options_ended && bytes@.len() >= 2 && bytes@[0] == 45 && bytes@[1] != 45)
                <==> res == CLI_ARG_OPT_CLUSTER,
        ]
    {
        let len = bytes.len();
        if options_ended || len < 2 || bytes[0] != 45 {
            CLI_ARG_FILE
        } else if bytes[1] == 45 {
            if len == 2 {
                CLI_ARG_END_OF_OPTIONS
            } else {
                CLI_ARG_OPT_INVALID
            }
        } else {
            CLI_ARG_OPT_CLUSTER
        }
    }

    /// Verified classification of one option letter inside a `CLI_ARG_OPT_CLUSTER` argument:
    /// `CLI_ARG_OPT_L` for `l`, `CLI_ARG_OPT_S` for `s` (reject extensions), `CLI_ARG_OPT_W`
    /// for `w` (warn about extensions), and `CLI_ARG_OPT_INVALID` for any other character.
    pub fn verified_cli_classify_option_char(c: u32) -> (res: u8)
        ensures [
            c == 108 <==> res == CLI_ARG_OPT_L,
            c == 115 <==> res == CLI_ARG_OPT_S,
            c == 119 <==> res == CLI_ARG_OPT_W,
            (c != 108 && c != 115 && c != 119) <==> res == CLI_ARG_OPT_INVALID,
        ]
    {
        if c == 108 {
            CLI_ARG_OPT_L
        } else if c == 115 {
            CLI_ARG_OPT_S
        } else if c == 119 {
            CLI_ARG_OPT_W
        } else {
            CLI_ARG_OPT_INVALID
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

verus! {

/// The state machine of `verified_repl_block_completeness`, resumed at `start` in the state
/// `state` = (open brace count, in a comment, in a string).
pub(crate) fn verified_repl_block_scan(text: &[u8], start: usize, state: (i32, bool, bool)) -> (res: (i32, bool, bool))
    requires
        text@.len() <= 1_000_000_000,
        start <= text@.len(),
        -(start as int) <= (state.0 as int) && (state.0 as int) <= (start as int),
        !(state.1 && state.2),
    ensures
        -(text@.len() as int) <= (res.0 as int) && (res.0 as int) <= (text@.len() as int),
        !(res.1 && res.2),
        (bc_spec::lexer::BlockScan { count: res.0 as i64, in_comment: res.1, in_string: res.2 })
            == bc_spec::lexer::block_scan(text@.skip(start as int), bc_spec::lexer::BlockScan { count: state.0 as i64, in_comment: state.1, in_string: state.2 }),
{
    let mut count: i32 = state.0;
    let mut in_comment: bool = state.1;
    let mut in_string: bool = state.2;
    let mut i: usize = start;
    let len: usize = text.len();
    while i < len
        invariant
            0 <= i <= len,
            len == text@.len(),
            len <= 1_000_000_000,
            !(in_comment && in_string),
            -(i as int) <= (count as int) && (count as int) <= (i as int),
            bc_spec::lexer::block_scan(text@.skip(i as int), bc_spec::lexer::BlockScan { count: count as i64, in_comment, in_string })
                == bc_spec::lexer::block_scan(text@.skip(start as int), bc_spec::lexer::BlockScan { count: state.0 as i64, in_comment: state.1, in_string: state.2 }),
        decreases len - i
    {
        let c = text[i];
        proof {
            let t = text@.skip(i as int);
            assert(t[0] == c);
            assert(t.drop_first() =~= text@.skip(i + 1));
            if i + 1 < len {
                assert(t[1] == text@[i + 1]);
                assert(text@.skip(i + 1).drop_first() =~= text@.skip(i + 2));
            }
            if i + 2 < len {
                assert(t[2] == text@[i + 2]);
                assert(text@.skip(i + 2).drop_first() =~= text@.skip(i + 3));
            }
        }
        if in_comment {
            if c == b'*' && len - i >= 2 && text[i + 1] == b'/' {
                in_comment = false;
                i += 2;
            } else {
                i += 1;
            }
        } else if in_string {
            if c == b'"' {
                in_string = false;
                i += 1;
            } else if c == b'\\' && len - i >= 2 && text[i + 1] == b'\n' {
                i += 2;
            } else if c == b'\\' && len - i >= 3 && text[i + 1] == b'\r' && text[i + 2] == b'\n' {
                i += 3;
            } else {
                i += 1;
            }
        } else if c == b'/' && len - i >= 2 && text[i + 1] == b'*' {
            in_comment = true;
            i += 2;
        } else if c == b'"' {
            in_string = true;
            i += 1;
        } else if c == b'{' {
            count += 1;
            i += 1;
        } else if c == b'}' {
            count -= 1;
            i += 1;
        } else {
            i += 1;
        }
    }
    proof {
        assert(text@.skip(i as int).len() == 0);
    }
    (count, in_comment, in_string)
}

} // verus!

dual_verified! {
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
    {
        let (count, in_comment, in_string) = verified_repl_block_scan(text, 0, (0, false, false));
        (count, count > 0 || in_comment || in_string)
    }
}
