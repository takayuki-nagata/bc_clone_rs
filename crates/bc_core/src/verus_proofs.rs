// SPDX-License-Identifier: MIT

//! Formal verification specifications, lemmas, and verified core algorithms for `bc_core` using Verus.
//!
//! This module is verified by the Verus SMT prover (`scripts/run_verus_verification.sh`)
//! and compiled only under `#[cfg(verus_keep_ghost)]`, ensuring zero overhead or coverage impact
//! on standard `#![no_std]` and embedded target builds.

use vstd::prelude::*;

verus! {

// ============================================================================
// Target 1: POSIX `bc` Scale Rules, Shift Calculations & Fixed-Point Arithmetic
// ============================================================================

/// Maximum verified scale bound to prevent `usize` / `i64` arithmetic overflow
/// during scale and exponent shift calculations.
pub const MAX_VERIFIED_SCALE: usize = 1_000_000_000;

/// Mathematical specification of $10^n$ over arbitrary-precision natural numbers.
pub open spec fn pow10(n: nat) -> int
    decreases n,
{
    if n == 0 {
        1
    } else {
        10 * pow10((n - 1) as nat)
    }
}

/// Lemma: $10^n \ge 1$ for all $n \ge 0$.
pub proof fn lemma_pow10_pos(n: nat)
    ensures
        pow10(n) >= 1,
    decreases n,
{
    if n > 0 {
        lemma_pow10_pos((n - 1) as nat);
    }
}

/// Lemma: $10^{a + b} == 10^a \cdot 10^b$ for all $a, b \ge 0$.
pub proof fn lemma_pow10_add(a: nat, b: nat)
    ensures
        pow10(a + b) == pow10(a) * pow10(b),
    decreases a,
{
    if a == 0 {
        assert(0 + b == b);
        assert(pow10(0) == 1);
    } else {
        lemma_pow10_add((a - 1) as nat, b);
        assert((a - 1) as nat + b == (a + b - 1) as nat);
        assert(pow10(a) * pow10(b) == (10 * pow10((a - 1) as nat)) * pow10(b));
        assert((10 * pow10((a - 1) as nat)) * pow10(b) == 10 * (pow10((a - 1) as nat) * pow10(b)))
            by (nonlinear_arith);
    }
}

/// Abstract specification model of `BCNum` representing $\text{coeff} \times 10^{-\text{scale}}$.
pub ghost struct SpecBCNum {
    pub coeff: int,
    pub scale: nat,
}

impl SpecBCNum {
    /// Returns the numerator when normalized to `target_scale` ($\ge \text{self.scale}$).
    pub open spec fn scaled_coeff(self, target_scale: nat) -> int
        recommends
            target_scale >= self.scale,
    {
        self.coeff * pow10((target_scale - self.scale) as nat)
    }

    /// Mathematical specification of `BCNum::add`.
    pub open spec fn spec_add(self, other: SpecBCNum) -> SpecBCNum {
        let sr = if self.scale >= other.scale { self.scale } else { other.scale };
        SpecBCNum {
            coeff: self.scaled_coeff(sr) + other.scaled_coeff(sr),
            scale: sr,
        }
    }

    /// Mathematical specification of `BCNum::sub`.
    pub open spec fn spec_sub(self, other: SpecBCNum) -> SpecBCNum {
        let sr = if self.scale >= other.scale { self.scale } else { other.scale };
        SpecBCNum {
            coeff: self.scaled_coeff(sr) - other.scaled_coeff(sr),
            scale: sr,
        }
    }
}

/// Proof that `BCNum` addition is commutative and subtraction is the exact inverse of addition
/// when scales match or are bounded by `other.scale <= self.scale`.
pub proof fn lemma_bcnum_add_sub_properties(a: SpecBCNum, b: SpecBCNum)
    ensures
        a.spec_add(b) == b.spec_add(a),
        a.scale >= b.scale ==> a.spec_add(b).spec_sub(b) == a,
{
    let sr = if a.scale >= b.scale { a.scale } else { b.scale };
    if a.scale >= b.scale {
        assert(sr == a.scale);
        assert((sr - a.scale) as nat == 0);
        assert(pow10(0) == 1);
        assert(a.scaled_coeff(sr) == a.coeff);
        let sum = a.spec_add(b);
        assert(sum.scale == a.scale);
        assert(sum.scaled_coeff(sr) == sum.coeff);
    }
}

/// Verified POSIX scale and shift calculation for `BCNum::add` and `BCNum::sub`.
///
/// Mirrors `crates/bc_core/src/math.rs` (`BCNum::add` / `BCNum::sub`).
pub fn verified_add_sub_scales(self_scale: usize, other_scale: usize) -> (res: (usize, usize, usize))
    ensures
        res.0 == if self_scale >= other_scale { self_scale } else { other_scale },
        res.1 == res.0 - self_scale,
        res.2 == res.0 - other_scale,
        res.0 >= self_scale && res.0 >= other_scale,
        (res.1 == 0 || res.2 == 0),
{
    let sr = if self_scale >= other_scale { self_scale } else { other_scale };
    let shift_a = sr - self_scale;
    let shift_b = sr - other_scale;
    (sr, shift_a, shift_b)
}

/// POSIX specification for multiplication scale:
/// $\min(a + b, \max(\text{global\_scale}, \max(a, b)))$.
pub open spec fn spec_posix_mul_scale(a: nat, b: nat, global_scale: nat) -> nat {
    let max_ab = if a >= b { a } else { b };
    let max_all = if global_scale >= max_ab { global_scale } else { max_ab };
    if a + b <= max_all {
        a + b
    } else {
        max_all
    }
}

/// Verified POSIX scale and truncation shift calculation for `BCNum::mul`.
///
/// POSIX IEEE Std 1003.1 mandates:
/// `scale(a * b) = min(scale(a) + scale(b), max(scale, scale(a), scale(b)))`.
/// Furthermore, proves that `exact_scale >= sr` always holds (i.e., `diff >= 0`),
/// guaranteeing that multiplication never requires negative truncation shifts.
pub fn verified_mul_scale_and_shift(
    self_scale: usize,
    other_scale: usize,
    global_scale: usize,
) -> (res: (usize, usize, usize))
    requires
        self_scale <= MAX_VERIFIED_SCALE,
        other_scale <= MAX_VERIFIED_SCALE,
        global_scale <= MAX_VERIFIED_SCALE,
    ensures
        // res = (sr, exact_scale, truncation_diff)
        res.1 == self_scale + other_scale,
        res.0 <= res.1,
        res.0 >= self_scale || res.0 >= other_scale,
        res.2 == res.1 - res.0,
        // Exact match with POSIX specification:
        res.0 as nat == spec_posix_mul_scale(
            self_scale as nat,
            other_scale as nat,
            global_scale as nat,
        ),
{
    let max_ab = if self_scale >= other_scale { self_scale } else { other_scale };
    let max_all = if global_scale >= max_ab { global_scale } else { max_ab };
    let exact_scale = self_scale + other_scale;
    let sr = if exact_scale <= max_all { exact_scale } else { max_all };
    let diff = exact_scale - sr;
    (sr, exact_scale, diff)
}

/// Verified POSIX scale and signed decimal shift calculation for `BCNum::div`.
///
/// Mirrors `crates/bc_core/src/math.rs` (`BCNum::div`):
/// `sr = global_scale`, `shift = other.scale - self.scale + sr`.
pub fn verified_div_scale_and_shift(
    self_scale: usize,
    other_scale: usize,
    global_scale: usize,
) -> (res: (usize, i64))
    requires
        self_scale <= MAX_VERIFIED_SCALE,
        other_scale <= MAX_VERIFIED_SCALE,
        global_scale <= MAX_VERIFIED_SCALE,
    ensures
        res.0 == global_scale,
        res.1 == (other_scale as int) - (self_scale as int) + (global_scale as int),
{
    let sr = global_scale;
    let shift: i64 = (other_scale as i64) - (self_scale as i64) + (sr as i64);
    (sr, shift)
}

/// Verified POSIX scale and radicand shift calculation for `BCNum::sqrt`.
///
/// Mirrors `crates/bc_core/src/math.rs` (`BCNum::sqrt`):
/// `sr = max(self.scale, global_scale)`, `shift = 2 * sr - self.scale`.
/// Proves that `2 * sr >= self.scale` always holds without underflow, and that
/// shifting the radicand by `shift` yields an exact square scale `self.scale + shift == 2 * sr`.
pub fn verified_sqrt_scale_and_shift(
    self_scale: usize,
    global_scale: usize,
) -> (res: (usize, usize))
    requires
        self_scale <= MAX_VERIFIED_SCALE,
        global_scale <= MAX_VERIFIED_SCALE,
    ensures
        res.0 == if self_scale >= global_scale { self_scale } else { global_scale },
        res.0 >= self_scale,
        res.0 >= global_scale,
        res.1 == 2 * res.0 - self_scale,
        self_scale + res.1 == 2 * res.0,
{
    let sr = if self_scale >= global_scale { self_scale } else { global_scale };
    let shift = 2 * sr - self_scale;
    (sr, shift)
}

/// Proof of POSIX `bc` modulo identity and truncation error bound:
/// When `q = (a * 10^shift) / b` (integer truncating division for `a >= 0, b > 0`),
/// the remainder `r = a * 10^shift - q * b` satisfies `0 <= r < b`.
pub proof fn lemma_truncating_div_mod_bounds(num: int, den: int)
    requires
        num >= 0,
        den > 0,
    ensures
        0 <= num - (num / den) * den,
        num - (num / den) * den < den,
        (num / den) * den + (num % den) == num,
{
    assert((num / den) * den + (num % den) == num) by (nonlinear_arith)
        requires
            num >= 0,
            den > 0,
    ;
    assert(0 <= num % den && num % den < den) by (nonlinear_arith)
        requires
            num >= 0,
            den > 0,
    ;
}

// ============================================================================
// Target 2: Non-Decimal `obase` Fractional Digit Count Termination & Minimality
// ============================================================================

/// Mathematical specification of $\text{base}^{\text{exp}}$ over natural numbers.
pub open spec fn pow_base(base: nat, exp: nat) -> nat
    decreases exp,
{
    if exp == 0 {
        1
    } else {
        base * pow_base(base, (exp - 1) as nat)
    }
}

/// Lemma: For $\text{base} \ge 1$, $\text{base}^{\text{exp}} \ge 1$.
pub proof fn lemma_pow_base_pos(base: nat, exp: nat)
    requires
        base >= 1,
    ensures
        pow_base(base, exp) >= 1,
    decreases exp,
{
    if exp > 0 {
        lemma_pow_base_pos(base, (exp - 1) as nat);
        assert(base * pow_base(base, (exp - 1) as nat) >= 1 * 1) by (nonlinear_arith)
            requires
                base >= 1,
                pow_base(base, (exp - 1) as nat) >= 1,
        ;
    }
}

/// Lemma: For $\text{base} \ge 2$, $\text{base}^{\text{exp} + 1} > \text{base}^{\text{exp}}$.
pub proof fn lemma_pow_base_strictly_increasing(base: nat, exp: nat)
    requires
        base >= 2,
    ensures
        pow_base(base, exp + 1) == base * pow_base(base, exp),
        pow_base(base, exp + 1) > pow_base(base, exp),
{
    lemma_pow_base_pos(base, exp);
    let p = pow_base(base, exp);
    assert(pow_base(base, exp + 1) == base * p);
    assert(base * p >= 2 * p) by (nonlinear_arith)
        requires
            base >= 2,
            p >= 1,
    ;
}

/// Verified calculation of the minimum fractional digit count $k$ in base `obase`
/// such that $\text{obase}^k \ge \text{target}$ (where $\text{target} = 10^{\text{scale}}$).
///
/// Mirrors the `#![no_std]` floating-point-free loop in `crates/bc_core/src/math.rs` (`format_obase`):
/// proves both loop termination (`decreases target - current`) and exact minimality of $k$:
/// $\text{obase}^k \ge \text{target}$ and ($k > 0 \implies \text{obase}^{k-1} < \text{target}$).
pub fn verified_obase_frac_digits(obase: u64, target: u64, max_bound: u64) -> (res: (usize, u64))
    requires
        obase >= 2,
        target >= 1,
        // Ensure `current * obase` will not overflow u64 before reaching `target`
        target <= max_bound,
        max_bound <= usize::MAX as u64,
        max_bound * (obase as int) <= u64::MAX as int,
    ensures
        res.1 as nat == pow_base(obase as nat, res.0 as nat),
        res.1 >= target,
        pow_base(obase as nat, res.0 as nat) >= target as nat,
        res.0 > 0 ==> pow_base(obase as nat, (res.0 - 1) as nat) < target as nat,
        res.0 == 0 <==> target == 1,
{
    let mut k: usize = 0;
    let mut current: u64 = 1;

    while current < target
        invariant
            obase >= 2,
            target >= 1,
            target <= max_bound,
            max_bound <= usize::MAX as u64,
            max_bound * (obase as int) <= u64::MAX as int,
            current >= 1,
            current as nat == pow_base(obase as nat, k as nat),
            (k as int) < (current as int),
            k > 0 ==> pow_base(obase as nat, (k - 1) as nat) < target as nat,
            k == 0 <==> current == 1,
        decreases
            if current < target {
                target - current
            } else {
                0
            },
    {
        let prev_current = current;
        let prev_k = k;

        proof {
            lemma_pow_base_strictly_increasing(obase as nat, prev_k as nat);
            assert((prev_current as int) * (obase as int) <= (max_bound as int) * (obase as int))
                by (nonlinear_arith)
                requires
                    prev_current < target,
                    target <= max_bound,
                    obase >= 2,
            ;
            assert((prev_current as int) * (obase as int) >= (prev_current as int) * 2)
                by (nonlinear_arith)
                requires
                    prev_current >= 1,
                    obase >= 2,
            ;
            assert((prev_k as int) + 1 < (prev_current as int) * (obase as int))
                by (nonlinear_arith)
                requires
                    (prev_k as int) < (prev_current as int),
                    prev_current >= 1,
                    (prev_current as int) * (obase as int) >= (prev_current as int) * 2,
            ;
        }

        current = current * obase;
        k = k + 1;
    }

    proof {
        if k > 0 {
            lemma_pow_base_pos(obase as nat, (k - 1) as nat);
        }
    }

    (k, current)
}

// ============================================================================
// Target 3: POSIX 70-Char Line Wrapping (`WrappedStdout`) & `Lexer` Safety
// ============================================================================

/// Maximum column index before POSIX `bc` emits a `\\\n` continuation (68 chars + `\` + `\n` = 70 chars).
pub const POSIX_WRAP_COL_LIMIT: usize = 68;

/// Verified single-character state transition for `WrappedStdout` (`crates/bc_core/src/eval.rs`).
///
/// Returns `(next_col, emitted_backslash_newline)`.
/// Proves that if `col <= 68`, then `next_col <= 68` holds unconditionally, and whenever
/// a line wrap (`\\\n`, 2 characters) is emitted, the line length including `\\\n` is at most 70.
pub fn verified_wrapped_stdout_step(col: usize, is_newline: bool) -> (res: (usize, bool))
    requires
        col <= POSIX_WRAP_COL_LIMIT,
    ensures
        res.0 <= POSIX_WRAP_COL_LIMIT,
        is_newline ==> (res.0 == 0 && !res.1),
        (!is_newline && col < POSIX_WRAP_COL_LIMIT) ==> (res.0 == col + 1 && !res.1),
        (!is_newline && col == POSIX_WRAP_COL_LIMIT) ==> (res.0 == 1 && res.1 && col + 2 <= 70),
{
    if is_newline {
        (0, false)
    } else if col >= POSIX_WRAP_COL_LIMIT {
        // Emits "\\\n" (resets column to 0), then emits the character (col becomes 1)
        (1, true)
    } else {
        (col + 1, false)
    }
}

/// Verified multi-character stream processing loop for `WrappedStdout::write_str`.
///
/// Proves that across an arbitrary input slice `bytes`, the column counter invariant
/// `col <= 68` is preserved at every iteration and upon return, and the total number
/// of line-wrap continuations emitted is bounded by the input length.
pub fn verified_wrapped_stdout_write_bytes(initial_col: usize, bytes: &[u8]) -> (res: (usize, usize))
    requires
        initial_col <= POSIX_WRAP_COL_LIMIT,
    ensures
        res.0 <= POSIX_WRAP_COL_LIMIT,
        res.1 <= bytes@.len(),
{
    let mut col: usize = initial_col;
    let mut wrap_count: usize = 0;
    let mut i: usize = 0;
    let len: usize = bytes.len();

    while i < len
        invariant
            0 <= i <= len,
            len == bytes@.len(),
            col <= POSIX_WRAP_COL_LIMIT,
            wrap_count <= i,
        decreases len - i,
    {
        let b = bytes[i];
        let (next_col, wrapped) = verified_wrapped_stdout_step(col, b == b'\n');
        col = next_col;
        if wrapped {
            wrap_count = wrap_count + 1;
        }
        i = i + 1;
    }

    (col, wrap_count)
}

/// Verified bounds-safe lookahead `Lexer::peek_char` (`crates/bc_core/src/parser.rs`).
///
/// Proves absence of out-of-bounds slice indexing and arithmetic overflow when peeking ahead.
pub fn verified_lexer_peek_byte(text: &[u8], pos: usize, offset: usize) -> (res: u8)
    requires
        pos <= text@.len(),
        offset <= usize::MAX - pos,
    ensures
        pos + offset >= text@.len() ==> res == 0u8,
        pos + offset < text@.len() ==> res == text@[pos + offset],
{
    let idx = pos + offset;
    if idx >= text.len() {
        0u8
    } else {
        text[idx]
    }
}

/// Verified cursor and line advancement `Lexer::advance_char` (`crates/bc_core/src/parser.rs`).
///
/// Proves that:
/// 1. Slice indexing `text[pos]` never panics (out-of-bounds is impossible).
/// 2. `pos` advances monotonically to `min(initial_pos + steps, text.len())`.
/// 3. `line` increases monotonically and never overflows `usize`.
pub fn verified_lexer_advance_bytes(
    text: &[u8],
    initial_pos: usize,
    initial_line: usize,
    steps: usize,
) -> (res: (usize, usize))
    requires
        initial_pos <= text@.len(),
        initial_line >= 1,
        initial_line <= usize::MAX - text@.len(),
    ensures
        res.0 <= text@.len(),
        res.0 >= initial_pos,
        res.0 == if initial_pos + steps <= text@.len() {
            (initial_pos + steps) as usize
        } else {
            text@.len() as usize
        },
        res.1 >= initial_line,
        res.1 <= initial_line + (res.0 - initial_pos),
{
    let mut pos: usize = initial_pos;
    let mut line: usize = initial_line;
    let mut s: usize = 0;
    let len: usize = text.len();

    while s < steps
        invariant
            0 <= s <= steps,
            len == text@.len(),
            initial_pos <= pos <= len,
            initial_line <= usize::MAX - len,
            pos == if initial_pos + s <= len {
                (initial_pos + s) as usize
            } else {
                len
            },
            line >= initial_line,
            line <= initial_line + (pos - initial_pos),
        decreases steps - s,
    {
        if pos < len {
            if text[pos] == b'\n' {
                line = line + 1;
            }
            pos = pos + 1;
        }
        s = s + 1;
    }

    (pos, line)
}

} // verus!
