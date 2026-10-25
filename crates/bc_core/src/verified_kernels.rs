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
            #[allow(clippy::manual_range_contains, clippy::manual_clamp)]
            pub fn $name( $($arg : $arg_ty),* ) -> $ret_ty
            $body
        )+
    };
}

dual_verified! {
    pub const MAX_VERIFIED_SCALE: usize = 1_000_000_000;
    pub const POSIX_WRAP_COL_LIMIT: usize = 68;
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

    /// Verified `ibase` register clamping (`eval.rs`).
    pub fn verified_clamp_ibase(reg_val: usize) -> (res: usize)
        ensures [
            2 <= res && res <= 16,
            (2 <= reg_val && reg_val <= 16) ==> res == reg_val,
            reg_val < 2 ==> res == 2,
            reg_val > 16 ==> res == 16,
        ]
    {
        if reg_val < 2 {
            2
        } else if reg_val > 16 {
            16
        } else {
            reg_val
        }
    }

    /// Verified `obase` register clamping (`eval.rs`).
    pub fn verified_clamp_obase(reg_val: usize) -> (res: usize)
        ensures [
            res >= 2,
            reg_val >= 2 ==> res == reg_val,
            reg_val < 2 ==> res == 2,
        ]
    {
        if reg_val < 2 {
            2
        } else {
            reg_val
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
