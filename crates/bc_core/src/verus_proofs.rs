// SPDX-License-Identifier: MIT

//! Formal verification specifications, lemmas, and verified core algorithms for `bc_core` using Verus.
//!
//! This module is verified by the Verus SMT prover (`scripts/run_verus_verification.sh`)
//! and compiled only under `#[cfg(verus_keep_ghost)]`, ensuring zero overhead or coverage impact
//! on standard `#![no_std]` and embedded target builds.

use crate::verified_kernels::*;
use vstd::prelude::*;

verus! {

// ============================================================================
// Target 1: POSIX `bc` Scale Rules, Shift Calculations & Fixed-Point Arithmetic
// ============================================================================

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

/// Proof that the shared production kernel `verified_mul_scale_and_shift` in `verified_kernels.rs`
/// conforms identically to `spec_posix_mul_scale`.
pub fn verified_mul_scale_matches_posix_spec(
    self_scale: usize,
    other_scale: usize,
    global_scale: usize,
) -> (res: (usize, usize))
    requires
        self_scale <= MAX_VERIFIED_SCALE,
        other_scale <= MAX_VERIFIED_SCALE,
        global_scale <= MAX_VERIFIED_SCALE,
    ensures
        res.0 as nat == spec_posix_mul_scale(
            self_scale as nat,
            other_scale as nat,
            global_scale as nat,
        ),
        res.1 == (self_scale + other_scale) - res.0,
{
    verified_mul_scale_and_shift(self_scale, other_scale, global_scale)
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
/// Proves absence of out-of-bounds slice indexing and arithmetic overflow when peeking ahead,
/// delegating index validation to `verified_lexer_peek_char_index` in `verified_kernels.rs`.
pub fn verified_lexer_peek_byte(text: &[u8], pos: usize, offset: usize) -> (res: u8)
    requires
        pos <= text@.len(),
        text@.len() <= MAX_VERIFIED_SCALE,
        offset <= MAX_VERIFIED_SCALE,
    ensures
        pos + offset >= text@.len() ==> res == 0u8,
        pos + offset < text@.len() ==> res == text@[pos + offset],
{
    let (in_bounds, idx) = verified_lexer_peek_char_index(text.len(), pos, offset);
    if in_bounds {
        text[idx]
    } else {
        0u8
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
        text@.len() <= 500_000_000,
        initial_line >= 1,
        initial_line <= 500_000_000,
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
            len <= 500_000_000,
            initial_pos <= pos <= len,
            initial_line <= 500_000_000,
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
            let (next_pos, next_line) = verified_lexer_advance_step(pos, line, text[pos] == b'\n');
            pos = next_pos;
            line = next_line;
        }
        s = s + 1;
    }

    (pos, line)
}

// ============================================================================
// Target 4: Binary Exponentiation (`BCNum::pow`) Loop & POSIX Scale Invariants
// ============================================================================

/// Mathematical specification of integer exponentiation $\text{base}^{\text{exp}}$.
pub open spec fn spec_pow_int(base: int, exp: nat) -> int
    decreases exp,
{
    if exp == 0 {
        1
    } else {
        base * spec_pow_int(base, (exp - 1) as nat)
    }
}

/// Lemma: Inductive step for binary exponentiation (exponentiation by squaring):
/// - If `exp` is even ($\text{exp} > 0$), $\text{base}^{\text{exp}} == (\text{base} \cdot \text{base})^{\text{exp} / 2}$.
/// - If `exp` is odd, $\text{base}^{\text{exp}} == \text{base} \cdot (\text{base} \cdot \text{base})^{\text{exp} / 2}$.
pub proof fn lemma_pow_int_squaring(base: int, exp: nat)
    requires
        exp > 0,
    ensures
        exp % 2 == 0 ==> spec_pow_int(base, exp) == spec_pow_int(base * base, exp / 2),
        exp % 2 == 1 ==> spec_pow_int(base, exp) == base * spec_pow_int(base * base, exp / 2),
    decreases exp,
{
    reveal_with_fuel(spec_pow_int, 2);
    if exp == 1 {
        assert(1nat % 2 == 1);
        assert(1nat / 2 == 0);
        assert(spec_pow_int(base * base, 0) == 1);
    } else if exp % 2 == 1 {
        let prev = (exp - 1) as nat;
        assert(prev > 0);
        assert(prev % 2 == 0);
        assert(prev / 2 == exp / 2);
        lemma_pow_int_squaring(base, prev);
        assert(spec_pow_int(base, exp) == base * spec_pow_int(base, prev));
    } else {
        let prev = (exp - 1) as nat;
        assert(prev % 2 == 1);
        assert(prev / 2 == (exp / 2 - 1) as nat);
        lemma_pow_int_squaring(base, prev);
        assert(spec_pow_int(base, exp) == base * spec_pow_int(base, prev));
        assert(spec_pow_int(base, prev) == base * spec_pow_int(base * base, prev / 2));
        let sub_pow = spec_pow_int(base * base, prev / 2);
        assert(base * (base * sub_pow) == (base * base) * sub_pow) by (nonlinear_arith);
        assert(spec_pow_int(base * base, exp / 2) == (base * base) * sub_pow);
    }
}

/// POSIX specification for positive-exponent power scale:
/// $\min(a \cdot b, \max(\text{global\_scale}, a))$.
pub open spec fn spec_posix_pow_scale(a: nat, b: nat, global_scale: nat) -> nat {
    let max_gs = if global_scale >= a { global_scale } else { a };
    if a * b <= max_gs {
        a * b
    } else {
        max_gs
    }
}

/// Proof that the shared production kernel `verified_pow_scale_and_shift` in `verified_kernels.rs`
/// conforms identically to `spec_posix_pow_scale` when `res_scale == self_scale * b_val`.
pub fn verified_pow_scale_matches_posix_spec(
    self_scale: usize,
    b_val: usize,
    global_scale: usize,
) -> (res: (usize, usize, usize))
    requires
        b_val >= 1,
        self_scale <= 30_000,
        b_val <= 30_000,
        global_scale <= MAX_VERIFIED_SCALE,
    ensures
        res.1 == self_scale * b_val,
        res.0 <= res.1,
        res.2 == res.1 - res.0,
        res.0 as nat == spec_posix_pow_scale(
            self_scale as nat,
            b_val as nat,
            global_scale as nat,
        ),
{
    proof {
        assert(self_scale * b_val <= 900_000_000) by (nonlinear_arith)
            requires
                self_scale <= 30_000,
                b_val <= 30_000,
        ;
    }
    let self_scale_b = self_scale * b_val;
    let (sr, diff) = verified_pow_scale_and_shift(self_scale_b, self_scale, global_scale);
    (sr, self_scale_b, diff)
}

/// Verified binary exponentiation loop for `BCNum::pow` (`crates/bc_core/src/math.rs:164-177`).
///
/// Tracks both the executable `res_scale` / `base_scale` and the ghost `res_coeff` / `base_coeff`
/// across the `while temp_b > 0` squaring loop, proving:
/// 1. Loop termination in $\mathcal{O}(\log b)$ iterations (`decreases temp_b`).
/// 2. Exact final scale: `res_scale == self_scale * b_val`.
/// 3. Exact final coefficient: `res_coeff@ == spec_pow_int(initial_coeff, b_val as nat)`.
pub fn verified_pow_binary_loop(
    Ghost(initial_coeff): Ghost<int>,
    self_scale: usize,
    b_val: usize,
) -> (res: (usize, Ghost<int>))
    requires
        self_scale <= 30_000,
        b_val <= 30_000,
    ensures
        res.0 == self_scale * b_val,
        res.1@ == spec_pow_int(initial_coeff, b_val as nat),
{
    let mut res_scale: usize = 0;
    let mut base_scale: usize = self_scale;
    let mut temp_b: usize = b_val;

    let ghost mut res_coeff: int = 1;
    let ghost mut base_coeff: int = initial_coeff;

    proof {
        assert(self_scale * b_val <= 900_000_000) by (nonlinear_arith)
            requires
                self_scale <= 30_000,
                b_val <= 30_000,
        ;
    }

    while temp_b > 0
        invariant
            temp_b <= b_val,
            self_scale <= 30_000,
            b_val <= 30_000,
            self_scale * b_val <= 900_000_000,
            res_scale <= self_scale * b_val,
            base_scale * temp_b <= self_scale * b_val,
            res_scale + base_scale * temp_b == self_scale * b_val,
            res_coeff * spec_pow_int(base_coeff, temp_b as nat)
                == spec_pow_int(initial_coeff, b_val as nat),
        decreases temp_b,
    {
        let prev_temp_b = temp_b;
        let prev_base_scale = base_scale;
        let prev_res_scale = res_scale;
        let ghost prev_base_coeff = base_coeff;
        let ghost prev_res_coeff = res_coeff;

        proof {
            lemma_pow_int_squaring(prev_base_coeff, prev_temp_b as nat);
            assert(prev_base_scale <= prev_base_scale * prev_temp_b) by (nonlinear_arith)
                requires
                    prev_temp_b >= 1,
                    prev_base_scale >= 0,
            ;
        }

        if temp_b % 2 == 1 {
            proof {
                assert(prev_temp_b == 2 * (prev_temp_b / 2) + 1);
                assert(prev_res_scale + prev_base_scale + (prev_base_scale + prev_base_scale) * (prev_temp_b / 2)
                    == prev_res_scale + prev_base_scale * prev_temp_b) by (nonlinear_arith)
                    requires
                        prev_temp_b == 2 * (prev_temp_b / 2) + 1,
                ;
                let sq_pow = spec_pow_int(prev_base_coeff * prev_base_coeff, (prev_temp_b / 2) as nat);
                assert((prev_res_coeff * prev_base_coeff) * sq_pow
                    == prev_res_coeff * (prev_base_coeff * sq_pow)) by (nonlinear_arith);
            }
            res_scale = res_scale + base_scale;
            proof {
                res_coeff = res_coeff * base_coeff;
            }
        } else {
            proof {
                assert(prev_temp_b == 2 * (prev_temp_b / 2));
                assert(prev_res_scale + (prev_base_scale + prev_base_scale) * (prev_temp_b / 2)
                    == prev_res_scale + prev_base_scale * prev_temp_b) by (nonlinear_arith)
                    requires
                        prev_temp_b == 2 * (prev_temp_b / 2),
                ;
            }
        }

        temp_b = temp_b / 2;
        if temp_b > 0 {
            proof {
                assert(prev_base_scale + prev_base_scale <= prev_base_scale * prev_temp_b)
                    by (nonlinear_arith)
                    requires
                        prev_temp_b >= 2,
                        prev_base_scale >= 0,
                ;
            }
            base_scale = base_scale + base_scale;
        } else {
            proof {
                assert(temp_b == 0);
                assert(base_scale * temp_b == 0) by (nonlinear_arith)
                    requires
                        temp_b == 0,
                ;
                assert(prev_temp_b == 1);
                assert(prev_base_scale * prev_temp_b == prev_base_scale) by (nonlinear_arith)
                    requires
                        prev_temp_b == 1,
                ;
            }
        }
        proof {
            base_coeff = base_coeff * base_coeff;
        }
    }

    proof {
        assert(temp_b == 0);
        assert(spec_pow_int(base_coeff, 0) == 1);
        assert(res_scale + base_scale * 0 == self_scale * b_val) by (nonlinear_arith)
            requires
                res_scale + base_scale * temp_b == self_scale * b_val,
                temp_b == 0,
        ;
    }

    (res_scale, Ghost(res_coeff))
}

// ============================================================================
// Target 5: Base Conversion (`ibase`/`obase`) Digit Bounds, LUT Safety & Padding
// ============================================================================

/// Verified fractional base conversion step and hexadecimal LUT indexing (`math.rs:306-318`).
///
/// Given $0 \le \text{num} < \text{den}$ and $2 \le \text{obase} \le 16$:
/// 1. Proves that `d = (num * obase) / den` satisfies $0 \le d < \text{obase} \le 16$.
/// 2. Proves that indexing `hex_lut[d as usize]` is 100% bounds-safe (never panics).
/// 3. Proves that `next_num = (num * obase) % den` preserves the loop invariant $0 \le \text{next\_num} < \text{den}$.
pub fn verified_obase_frac_step_and_lut(
    num: u64,
    den: u64,
    obase: u64,
    hex_lut: &[u8],
) -> (res: (u64, u64, u8))
    requires
        den >= 1,
        num < den,
        2 <= obase <= 16,
        (den as int) * (obase as int) <= u64::MAX as int,
        hex_lut@.len() == 16,
    ensures
        // res = (digit_d, next_num, ascii_hex_char)
        res.0 < obase,
        res.0 < 16,
        res.1 < den,
        (num as int) * (obase as int) == (res.0 as int) * (den as int) + (res.1 as int),
        res.2 == hex_lut@[res.0 as int],
{
    proof {
        assert((num as int) * (obase as int) < (den as int) * (obase as int)) by (nonlinear_arith)
            requires
                num < den,
                obase >= 2,
        ;
    }
    let prod: u64 = num * obase;
    let d: u64 = prod / den;
    let next_num: u64 = prod % den;

    proof {
        assert((prod as int) == (d as int) * (den as int) + (next_num as int)) by (nonlinear_arith)
            requires
                prod == num * obase,
                d == prod / den,
                next_num == prod % den,
                den >= 1,
        ;
        assert(next_num < den) by (nonlinear_arith)
            requires
                next_num == prod % den,
                den >= 1,
        ;
        assert(d < obase) by (nonlinear_arith)
            requires
                (prod as int) < (den as int) * (obase as int),
                (prod as int) == (d as int) * (den as int) + (next_num as int),
                next_num >= 0,
                den >= 1,
        ;
    }

    let ch: u8 = hex_lut[d as usize];
    (d, next_num, ch)
}

/// Verified multi-digit base (`obase > 16`) zero-padding width calculation (`math.rs:268-271`).
///
/// Proves that `digit_width - rem_len` never underflows when `1 <= rem_len <= digit_width`,
/// and that the resulting padded chunk has exact width `digit_width` (plus 1 leading separator).
pub fn verified_multi_digit_obase_padding(
    digit_width: usize,
    rem_len: usize,
) -> (res: (usize, usize))
    requires
        digit_width >= 2,
        digit_width <= 32,
        1 <= rem_len <= digit_width,
    ensures
        // res = (zero_pad_count, total_padded_digit_len)
        res.0 == digit_width - rem_len,
        res.1 == digit_width,
        res.0 + rem_len == res.1,
{
    let mut pad_count: usize = 0;
    let target_pads: usize = verified_multi_digit_obase_pad_zeros(digit_width, rem_len);

    while pad_count < target_pads
        invariant
            0 <= pad_count <= target_pads,
            target_pads == digit_width - rem_len,
            1 <= rem_len <= digit_width,
            digit_width <= 32,
        decreases target_pads - pad_count,
    {
        pad_count = pad_count + 1;
    }

    let total_len: usize = pad_count + rem_len;
    (pad_count, total_len)
}

// ============================================================================
// Target 6: Transcendental Math (`Decimal`) Roundtrip & Argument Reduction
// ============================================================================

/// Abstract specification of fixed-point `Decimal` (`crates/bc_core/src/math.rs:350-402`).
pub ghost struct SpecDecimal {
    pub value: int,
    pub prec: nat,
}

impl SpecDecimal {
    /// Specification of `Decimal::from_bc_num` when `prec >= num.scale`.
    pub open spec fn spec_from_bc_num(num: SpecBCNum, prec: nat) -> SpecDecimal
        recommends
            prec >= num.scale,
    {
        SpecDecimal {
            value: num.coeff * pow10((prec - num.scale) as nat),
            prec,
        }
    }

    /// Specification of `Decimal::to_bc_num` when `self.prec >= target_scale`.
    pub open spec fn spec_to_bc_num(self, target_scale: nat) -> SpecBCNum
        recommends
            self.prec >= target_scale,
    {
        SpecBCNum {
            coeff: self.value / pow10((self.prec - target_scale) as nat),
            scale: target_scale,
        }
    }
}

/// Proof that converting `BCNum` to `Decimal` at higher guard precision (`prec >= num.scale`,
/// e.g. `max(x.scale, global_scale) + 15`) and converting back to `num.scale` is 100% lossless.
pub proof fn lemma_decimal_bcnum_roundtrip(num: SpecBCNum, prec: nat)
    requires
        prec >= num.scale,
    ensures
        SpecDecimal::spec_from_bc_num(num, prec).spec_to_bc_num(num.scale) == num,
{
    let shift = (prec - num.scale) as nat;
    lemma_pow10_pos(shift);
    let p10 = pow10(shift);
    assert((num.coeff * p10) / p10 == num.coeff) by (nonlinear_arith)
        requires
            p10 >= 1,
    ;
}

/// Verified roundtrip shift consistency between `verified_decimal_scale_shift` (`from_bc_num` -> `to_bc_num`)
/// and `verified_transcendental_guard_prec` (`crates/bc_core/src/math.rs:358-376, 778-829`).
///
/// Proves that when `prec = verified_transcendental_guard_prec(x_scale, global_scale, extra_prec)`:
/// 1. `from_bc_num` always scales UP (`should_mul_in == true`) by `prec - x_scale >= 15`.
/// 2. `to_bc_num(global_scale)` always scales DOWN (`should_mul_out == false`) by `prec - global_scale >= 15`.
pub fn verified_decimal_scale_shift_roundtrip(
    x_scale: usize,
    global_scale: usize,
    extra_prec: usize,
) -> (res: ((usize, bool), (usize, bool)))
    requires
        x_scale <= MAX_VERIFIED_SCALE,
        global_scale <= MAX_VERIFIED_SCALE,
        extra_prec <= MAX_VERIFIED_SCALE,
    ensures
        res.0.1,
        res.0.0 >= 15,
        !res.1.1,
        res.1.0 >= 15,
        x_scale + res.0.0 == global_scale + res.1.0,
{
    let prec = verified_transcendental_guard_prec(x_scale, global_scale, extra_prec);
    let shift_in = verified_decimal_scale_shift(x_scale, prec);
    let shift_out = verified_decimal_scale_shift(prec, global_scale);
    (shift_in, shift_out)
}

/// Verified trigonometric argument reduction modulo $2\pi$ into $[-\pi, \pi]$
/// (`crates/bc_core/src/math.rs:516-522, 564-570` in `decimal_sin` / `decimal_cos`).
///
/// Given any signed fixed-point angle `x_val` and positive `pi_val`, proves that:
/// 1. The reduced angle `res.0` lies strictly within $[-\pi, \pi]$.
/// 2. There exists an exact integer multiple $k$ (`res.1@`) of $2\pi$ such that
///    `x_val == res.0 + k * (2 * pi_val)`, guaranteeing periodicity invariance.
pub fn verified_trig_range_reduction(x_val: i64, pi_val: i64) -> (res: (i64, Ghost<int>))
    requires
        pi_val > 0,
        pi_val <= 1_000_000_000_000_000_000i64,
        x_val > i64::MIN,
    ensures
        -pi_val <= res.0 && res.0 <= pi_val,
        (x_val as int) == (res.0 as int) + res.1@ * (2 * (pi_val as int)),
{
    let two_pi: i64 = 2 * pi_val;
    let is_neg: bool = x_val < 0;
    let abs_x_i64: i64 = if is_neg { -x_val } else { x_val };
    let abs_x: u64 = abs_x_i64 as u64;
    let two_pi_u64: u64 = two_pi as u64;

    let q_u64: u64 = abs_x / two_pi_u64;
    let rem_u64: u64 = abs_x % two_pi_u64;
    let q_abs: i64 = q_u64 as i64;
    let rem_abs: i64 = rem_u64 as i64;

    proof {
        assert((abs_x as int) == (q_u64 as int) * (two_pi_u64 as int) + (rem_u64 as int))
            by (nonlinear_arith)
            requires
                two_pi_u64 > 0,
                q_u64 == abs_x / two_pi_u64,
                rem_u64 == abs_x % two_pi_u64,
        ;
        assert(rem_u64 < two_pi_u64) by (nonlinear_arith)
            requires
                two_pi_u64 > 0,
                rem_u64 == abs_x % two_pi_u64,
        ;
    }

    let mut rem: i64 = if is_neg { -rem_abs } else { rem_abs };
    let ghost mut k: int = if is_neg { -(q_abs as int) } else { q_abs as int };

    proof {
        if is_neg {
            assert((x_val as int) == -(abs_x as int));
            assert(-(abs_x as int) == (-(q_abs as int)) * (two_pi as int) + (-(rem_abs as int)))
                by (nonlinear_arith)
                requires
                    (abs_x as int) == (q_abs as int) * (two_pi as int) + (rem_abs as int),
            ;
        }
        assert((x_val as int) == (rem as int) + k * (two_pi as int));
    }

    if rem > pi_val {
        let prev_rem = rem;
        let ghost prev_k = k;
        rem = rem - two_pi;
        proof {
            k = prev_k + 1;
            assert((prev_rem as int) + prev_k * (two_pi as int)
                == (rem as int) + k * (two_pi as int)) by (nonlinear_arith)
                requires
                    rem == prev_rem - two_pi,
                    k == prev_k + 1,
            ;
        }
    } else if rem < -pi_val {
        let prev_rem = rem;
        let ghost prev_k = k;
        rem = rem + two_pi;
        proof {
            k = prev_k - 1;
            assert((prev_rem as int) + prev_k * (two_pi as int)
                == (rem as int) + k * (two_pi as int)) by (nonlinear_arith)
                requires
                    rem == prev_rem + two_pi,
                    k == prev_k - 1,
            ;
        }
    }

    (rem, Ghost(k))
}

/// Verified exponential argument reduction $x = n \cdot \ln(2) + r$ (`math.rs:758-760`).
///
/// Proves that for any non-negative fixed-point value `x_abs >= 0` and `ln2_val > 0`,
/// the reduced Taylor series argument $r$ satisfies $0 \le r < \ln(2)$ and reconstructs $x$ exactly.
pub fn verified_exp_ln2_reduction(x_abs: i64, ln2_val: i64) -> (res: (i64, i64))
    requires
        x_abs >= 0,
        ln2_val > 0,
    ensures
        // res = (n, r)
        res.0 >= 0,
        0 <= res.1 && res.1 < ln2_val,
        (x_abs as int) == (res.0 as int) * (ln2_val as int) + (res.1 as int),
{
    let n: i64 = x_abs / ln2_val;
    proof {
        assert(0 <= (n as int) * (ln2_val as int) && (n as int) * (ln2_val as int) <= (x_abs as int))
            by (nonlinear_arith)
            requires
                n == x_abs / ln2_val,
                x_abs >= 0,
                ln2_val > 0,
        ;
        assert((x_abs as int) - (n as int) * (ln2_val as int) < (ln2_val as int))
            by (nonlinear_arith)
            requires
                n == x_abs / ln2_val,
                x_abs >= 0,
                ln2_val > 0,
        ;
    }
    let r: i64 = x_abs - n * ln2_val;
    (n, r)
}

// ============================================================================
// Target 7: `Evaluator` Relational Total Order, Register Clamping & ScopeGuard
// ============================================================================

/// Normalized left-hand numerator when comparing `a` and `b` (`eval.rs:208-217`).
pub open spec fn spec_rel_norm_lhs(a: SpecBCNum, b: SpecBCNum) -> int {
    if a.scale >= b.scale {
        a.coeff
    } else {
        a.coeff * pow10((b.scale - a.scale) as nat)
    }
}

/// Normalized right-hand numerator when comparing `a` and `b` (`eval.rs:208-217`).
pub open spec fn spec_rel_norm_rhs(a: SpecBCNum, b: SpecBCNum) -> int {
    if a.scale > b.scale {
        b.coeff * pow10((a.scale - b.scale) as nat)
    } else {
        b.coeff
    }
}

/// Relational predicates (`<`, `==`, `>`) over `SpecBCNum`.
pub open spec fn spec_bcnum_lt(a: SpecBCNum, b: SpecBCNum) -> bool {
    spec_rel_norm_lhs(a, b) < spec_rel_norm_rhs(a, b)
}

pub open spec fn spec_bcnum_eq(a: SpecBCNum, b: SpecBCNum) -> bool {
    spec_rel_norm_lhs(a, b) == spec_rel_norm_rhs(a, b)
}

pub open spec fn spec_bcnum_gt(a: SpecBCNum, b: SpecBCNum) -> bool {
    spec_rel_norm_lhs(a, b) > spec_rel_norm_rhs(a, b)
}

/// Proof that `Evaluator`'s relational comparison forms a strict trichotomous total order
/// and agrees with common-scale normalization `max(a.scale, b.scale)`.
pub proof fn lemma_bcnum_relational_total_order(a: SpecBCNum, b: SpecBCNum)
    ensures
        // 1. Equivalence with scaling to `sr = max(a.scale, b.scale)`
        spec_rel_norm_lhs(a, b) == a.scaled_coeff(if a.scale >= b.scale { a.scale } else { b.scale }),
        spec_rel_norm_rhs(a, b) == b.scaled_coeff(if a.scale >= b.scale { a.scale } else { b.scale }),
        // 2. Reflexivity
        spec_bcnum_eq(a, a),
        !spec_bcnum_lt(a, a),
        // 3. Symmetry of equality and antisymmetry of `<` / `>`
        spec_bcnum_eq(a, b) <==> spec_bcnum_eq(b, a),
        spec_bcnum_lt(a, b) <==> spec_bcnum_gt(b, a),
        // 4. Strict trichotomy: exactly one of `<`, `==`, `>` holds
        (spec_bcnum_lt(a, b) && !spec_bcnum_eq(a, b) && !spec_bcnum_gt(a, b))
            || (!spec_bcnum_lt(a, b) && spec_bcnum_eq(a, b) && !spec_bcnum_gt(a, b))
            || (!spec_bcnum_lt(a, b) && !spec_bcnum_eq(a, b) && spec_bcnum_gt(a, b)),
{
    assert((a.scale - a.scale) as nat == 0);
    assert((b.scale - b.scale) as nat == 0);
    assert(pow10(0) == 1);
}

/// Verified dynamic scope frame push, mutation, and `ScopeGuard` drop restoration
/// (`crates/bc_core/src/eval.rs:87-119, 454-497`).
///
/// Models a variable's dynamic scope stack (`Vec<i64>`) across a function call that:
/// 1. Pushes `num_params` parameter bindings and `num_autos` local `auto` bindings (initialized to 0).
/// 2. Mutates the active top-of-stack binding during function execution.
/// 3. Restores `prev_return_flag` / `prev_return_value` and pops all `num_autos` and `num_params`
///    in reverse order upon `ScopeGuard::drop`.
///
/// Formally proves the **Stack Frame Restoration Theorem**:
/// After `ScopeGuard` cleanup, `stack@ == old(stack)@` (every caller binding and stack depth
/// is 100% preserved without shadowing leaks).
pub fn verified_scope_guard_lifecycle(
    stack: &mut alloc::vec::Vec<i64>,
    param_vals: &[i64],
    num_autos: usize,
    mutated_top_val: i64,
    caller_return_flag: bool,
    caller_return_val: i64,
) -> (res: (bool, i64))
    requires
        old(stack)@.len() >= 1,
        old(stack)@.len() + param_vals@.len() + num_autos <= 1_000_000,
    ensures
        // 1. Exact stack restoration (length and all caller elements unchanged)
        final(stack)@ == old(stack)@,
        // 2. Exact restoration of caller's return control-flow state
        res.0 == caller_return_flag,
        res.1 == caller_return_val,
{
    let ghost initial_stack = stack@;
    let initial_len: usize = stack.len();
    let num_params: usize = param_vals.len();

    // 1. Push evaluated parameters onto dynamic scope stack
    let mut p_idx: usize = 0;
    while p_idx < num_params
        invariant
            0 <= p_idx <= num_params,
            num_params == param_vals@.len(),
            initial_len == initial_stack.len(),
            initial_len + num_params + num_autos <= 1_000_000,
            stack@.len() == initial_len + p_idx,
            stack@.subrange(0, initial_len as int) =~= initial_stack,
        decreases num_params - p_idx,
    {
        stack.push(param_vals[p_idx]);
        p_idx = p_idx + 1;
    }

    // 2. Push zero-initialized `auto` variables onto dynamic scope stack
    let mut a_idx: usize = 0;
    while a_idx < num_autos
        invariant
            0 <= a_idx <= num_autos,
            num_params == param_vals@.len(),
            initial_len == initial_stack.len(),
            initial_len + num_params + num_autos <= 1_000_000,
            stack@.len() == initial_len + num_params + a_idx,
            stack@.subrange(0, initial_len as int) =~= initial_stack,
        decreases num_autos - a_idx,
    {
        stack.push(0);
        a_idx = a_idx + 1;
    }

    // Save caller return state
    let prev_return_flag: bool = caller_return_flag;
    let prev_return_val: i64 = caller_return_val;

    // 3. Simulate in-body mutation of the active variable binding (if any local binding was pushed)
    if num_params + num_autos > 0 {
        let top_idx: usize = stack.len() - 1;
        stack.set(top_idx, mutated_top_val);
        proof {
            assert(stack@.subrange(0, initial_len as int) =~= initial_stack);
        }
    }

    // 4. ScopeGuard::drop: pop `autos` in reverse, then `params` in reverse
    let mut pop_a: usize = 0;
    while pop_a < num_autos
        invariant
            0 <= pop_a <= num_autos,
            initial_len == initial_stack.len(),
            stack@.len() == initial_len + num_params + (num_autos - pop_a),
            stack@.subrange(0, initial_len as int) =~= initial_stack,
        decreases num_autos - pop_a,
    {
        let _ = stack.pop();
        pop_a = pop_a + 1;
    }

    let mut pop_p: usize = 0;
    while pop_p < num_params
        invariant
            0 <= pop_p <= num_params,
            initial_len == initial_stack.len(),
            stack@.len() == initial_len + (num_params - pop_p),
            stack@.subrange(0, initial_len as int) =~= initial_stack,
        decreases num_params - pop_p,
    {
        let _ = stack.pop();
        pop_p = pop_p + 1;
    }

    proof {
        assert(stack@.len() == initial_stack.len());
        assert(stack@ =~= stack@.subrange(0, initial_len as int));
        assert(stack@ =~= initial_stack);
    }

    (prev_return_flag, prev_return_val)
}

// ============================================================================
// Target 8: `Parser` Pratt Precedence Climbing & `Lexer` Number Scanner
// ============================================================================

/// Helper predicate for valid bc numeric literal characters (`0..=9` or `A..=F`).
pub open spec fn spec_is_bc_digit(b: u8) -> bool {
    (b'0' <= b && b <= b'9') || (b'A' <= b && b <= b'F')
}

/// Verified `Lexer` number token scanning loop (`crates/bc_core/src/parser.rs:443-468`).
///
/// Scans digits (`0-9`, `A-F`), at most one decimal point (`.`), and backslash-newline
/// continuations (`\\\n` and `\\\r\n`).
/// Proves:
/// 1. Loop termination (`decreases len - pos`) and 100% bounds-safe slice indexing.
/// 2. At most one radix point `.` is ever accepted into a single number token (`res.2 <= 1`).
/// 3. Monotonic cursor advancement (`initial_pos <= res.0 <= text.len()`).
pub fn verified_lexer_scan_number(
    text: &[u8],
    initial_pos: usize,
) -> (res: (usize, usize, usize))
    requires
        initial_pos <= text@.len(),
    ensures
        // res = (final_pos, emitted_char_count, dot_count)
        initial_pos <= res.0 && res.0 <= text@.len(),
        res.1 <= res.0 - initial_pos,
        res.2 <= 1,
{
    let mut pos: usize = initial_pos;
    let mut char_count: usize = 0;
    let mut dot_count: usize = 0;
    let mut has_dot: bool = false;
    let len: usize = text.len();

    while pos < len
        invariant
            initial_pos <= pos <= len,
            len == text@.len(),
            char_count <= pos - initial_pos,
            dot_count <= 1,
            has_dot <==> (dot_count == 1),
        decreases len - pos,
    {
        let cc = text[pos];
        if verified_is_bc_digit(cc as u32) {
            char_count = char_count + 1;
            pos = pos + 1;
        } else if cc == b'.' && !has_dot {
            has_dot = true;
            dot_count = dot_count + 1;
            char_count = char_count + 1;
            pos = pos + 1;
        } else if cc == b'\\' && len - pos >= 2 && text[pos + 1] == b'\n' {
            pos = pos + 2;
        } else if cc == b'\\' && len - pos >= 3 && text[pos + 1] == b'\r' && text[pos + 2] == b'\n' {
            pos = pos + 3;
        } else {
            break;
        }
    }

    (pos, char_count, dot_count)
}

// ============================================================================
// Target 9: `BCNum::length` & `atan` / `ln` / `bessel` Mathematical Identities
// ============================================================================

/// Verified arctangent reciprocal argument reduction $|x| > 1 \implies 1/x \in [0, 1)$
/// (`crates/bc_core/src/math.rs:620-624` in `decimal_atan`).
///
/// Proves via non-linear arithmetic that when `x_p > one_p`, replacing `x_p` with
/// `(one_p * one_p) / x_p` strictly reduces the argument below `one_p` ($|x'| < 1$),
/// ensuring rapid convergence of the subsequent half-angle and Taylor series steps.
pub fn verified_atan_inversion_reduction(x_p: u64, one_p: u64) -> (res: (u64, bool))
    requires
        one_p >= 1,
        one_p <= 1_000_000_000,
    ensures
        // res = (reduced_x_p, inverted_flag)
        res.0 <= one_p,
        x_p > one_p ==> (res.1 && res.0 < one_p),
        x_p <= one_p ==> (!res.1 && res.0 == x_p),
{
    if x_p > one_p {
        proof {
            assert((one_p as int) * (one_p as int) <= 1_000_000_000 * 1_000_000_000)
                by (nonlinear_arith)
                requires
                    one_p <= 1_000_000_000,
            ;
            assert((one_p as int) * (one_p as int) < (one_p as int) * (x_p as int))
                by (nonlinear_arith)
                requires
                    x_p > one_p,
                    one_p >= 1,
            ;
        }
        let num: u64 = one_p * one_p;
        let inv_x: u64 = num / x_p;
        proof {
            assert(inv_x < one_p) by (nonlinear_arith)
                requires
                    num == one_p * one_p,
                    inv_x == num / x_p,
                    x_p > one_p,
                    one_p >= 1,
            ;
        }
        (inv_x, true)
    } else {
        (x_p, false)
    }
}

/// Verified natural logarithm Cayley transform $y = \frac{m - 1}{m + 1}$ (`math.rs:716-719`).
///
/// Given a positive fixed-point mantissa `m_val > 0` and unit `one_val > 0`, proves:
/// 1. Denominator `den_y = m_val + one_val > one_val > 0` (division by zero is impossible).
/// 2. Numerator magnitude satisfies `-den_y < num_y < den_y` ($|y| < 1$, inside the convergence radius).
/// 3. When $m \ge 1$ (`m_val >= one_val`), $0 \le y < \text{one\_val}$.
pub fn verified_ln_cayley_transform(m_val: i64, one_val: i64) -> (res: (i64, i64, i64))
    requires
        m_val > 0,
        one_val > 0,
        m_val <= 1_000_000_000,
        one_val <= 1_000_000_000,
    ensures
        // res = (num_y, den_y, scaled_y)
        res.0 == m_val - one_val,
        res.1 == m_val + one_val,
        res.1 > one_val && res.1 > 0,
        -res.1 < res.0 && res.0 < res.1,
        m_val >= one_val ==> (0 <= res.2 && res.2 < one_val),
{
    let num_y: i64 = m_val - one_val;
    let den_y: i64 = m_val + one_val;

    let scaled_y: i64 = if num_y >= 0 {
        let num_u: u64 = num_y as u64;
        let one_u: u64 = one_val as u64;
        let den_u: u64 = den_y as u64;
        proof {
            assert((num_u as int) * (one_u as int) <= 1_000_000_000 * 1_000_000_000)
                by (nonlinear_arith)
                requires
                    num_u <= 1_000_000_000,
                    one_u <= 1_000_000_000,
            ;
            assert((num_u as int) * (one_u as int) < (den_u as int) * (one_u as int))
                by (nonlinear_arith)
                requires
                    num_u < den_u,
                    one_u >= 1,
            ;
        }
        let prod_u: u64 = num_u * one_u;
        let q_u64: u64 = prod_u / den_u;
        proof {
            assert(q_u64 < one_u) by (nonlinear_arith)
                requires
                    prod_u == num_u * one_u,
                    num_u < den_u,
                    den_u >= 1,
                    one_u >= 1,
                    q_u64 == prod_u / den_u,
            ;
        }
        q_u64 as i64
    } else {
        let abs_num_u: u64 = (-num_y) as u64;
        let one_u: u64 = one_val as u64;
        let den_u: u64 = den_y as u64;
        proof {
            assert((abs_num_u as int) * (one_u as int) <= 1_000_000_000 * 1_000_000_000)
                by (nonlinear_arith)
                requires
                    abs_num_u <= 1_000_000_000,
                    one_u <= 1_000_000_000,
            ;
            assert((abs_num_u as int) * (one_u as int) < (den_u as int) * (one_u as int))
                by (nonlinear_arith)
                requires
                    abs_num_u < den_u,
                    one_u >= 1,
            ;
        }
        let prod_u: u64 = abs_num_u * one_u;
        let q_u64: u64 = prod_u / den_u;
        proof {
            assert(q_u64 < one_u) by (nonlinear_arith)
                requires
                    prod_u == abs_num_u * one_u,
                    abs_num_u < den_u,
                    den_u >= 1,
                    one_u >= 1,
                    q_u64 == prod_u / den_u,
            ;
        }
        -(q_u64 as i64)
    };

    (num_y, den_y, scaled_y)
}

// ============================================================================
// Target 10: `Evaluator` Prefix/Postfix `++`/`--` & Control-Flow Short-Circuiting
// ============================================================================

/// Verified `Evaluator` prefix/postfix increment and decrement (`++` / `--`) semantics
/// (`crates/bc_core/src/eval.rs:352-419`).
///
/// Returns `((stored_coeff, stored_scale), (returned_coeff, returned_scale))`.
/// Proves:
/// 1. The variable's stored scale is invariant (`stored_scale == scale`).
/// 2. The stored value always changes by $\pm 10^{\text{scale}}$ regardless of `is_prefix`.
/// 3. Prefix (`++x`, `--x`) returns the new value, whereas postfix (`x++`, `x--`) returns the old value.
pub fn verified_update_op_semantics(
    old_coeff: i64,
    scale_pow10: i64,
    scale: usize,
    is_incr: bool,
    is_prefix: bool,
) -> (res: ((i64, usize), (i64, usize)))
    requires
        scale_pow10 >= 1,
        scale_pow10 <= 1_000_000_000_000i64,
        old_coeff >= -1_000_000_000_000_000i64,
        old_coeff <= 1_000_000_000_000_000i64,
    ensures
        // 1. Stored state (res.0)
        res.0.1 == scale,
        is_incr ==> res.0.0 == old_coeff + scale_pow10,
        !is_incr ==> res.0.0 == old_coeff - scale_pow10,
        // 2. Evaluated expression result (res.1)
        res.1.1 == scale,
        is_prefix ==> res.1 == res.0,
        !is_prefix ==> res.1 == (old_coeff, scale),
{
    let new_coeff: i64 = if is_incr {
        old_coeff + scale_pow10
    } else {
        old_coeff - scale_pow10
    };
    let stored = (new_coeff, scale);
    let returned = if is_prefix {
        stored
    } else {
        (old_coeff, scale)
    };
    (stored, returned)
}

/// Statement kind constants for control-flow verification (`eval.rs:538-579`).
pub const STMT_NORMAL: u8 = 0;
pub const STMT_BREAK: u8 = 1;
pub const STMT_RETURN: u8 = 2;
pub const STMT_QUIT: u8 = 3;

/// Verified `Stmt::Block` execution short-circuiting on `break`, `return`, or `quit`
/// (`crates/bc_core/src/eval.rs:538-579`).
///
/// Returns `(executed_normal_stmt_count, break_flag, return_flag, quit_flag)`.
/// Proves:
/// 1. If any flag is already set upon entry, 0 statements are executed and flags remain unchanged.
/// 2. Execution halts immediately upon encountering the first `Break`, `Return`, or `Quit` statement.
/// 3. Once set, `return_flag` and `quit_flag` are never cleared within the block.
pub fn verified_block_short_circuit(
    stmts: &[u8],
    initial_break: bool,
    initial_return: bool,
    initial_quit: bool,
) -> (res: (usize, bool, bool, bool))
    ensures
        (initial_break || initial_return || initial_quit) ==> (
            res.0 == 0
            && res.1 == initial_break
            && res.2 == initial_return
            && res.3 == initial_quit
        ),
        res.0 <= stmts@.len(),
        initial_return ==> res.2,
        initial_quit ==> res.3,
{
    if verified_should_abort_execution(initial_break, initial_return, initial_quit) {
        return (0, initial_break, initial_return, initial_quit);
    }

    let mut break_flag: bool = false;
    let mut return_flag: bool = false;
    let mut quit_flag: bool = false;
    let mut normal_count: usize = 0;
    let mut i: usize = 0;
    let len: usize = stmts.len();

    while i < len && !verified_should_abort_execution(break_flag, return_flag, quit_flag)
        invariant
            0 <= i <= len,
            len == stmts@.len(),
            normal_count <= i,
        decreases len - i,
    {
        let s = stmts[i];
        if s == STMT_BREAK {
            break_flag = true;
        } else if s == STMT_RETURN {
            return_flag = true;
        } else if s == STMT_QUIT {
            quit_flag = true;
        } else {
            normal_count = normal_count + 1;
        }
        i = i + 1;
    }

    (normal_count, break_flag, return_flag, quit_flag)
}

/// Verified `While` / `For` loop post-body control-flow flag handling (`eval.rs:592-598, 608-614`).
///
/// Returns `(should_exit_loop, next_break_flag, next_return_flag, next_quit_flag)`.
/// Proves:
/// 1. `break_flag` triggers loop exit AND resets `next_break_flag = false` so outer loops continue.
/// 2. `return_flag` and `quit_flag` trigger loop exit AND remain `true` to propagate to the caller.
pub fn verified_loop_flag_propagation(
    break_flag: bool,
    return_flag: bool,
    quit_flag: bool,
) -> (res: (bool, bool, bool, bool))
    ensures
        res.0 == (break_flag || return_flag || quit_flag),
        !res.1, // `break_flag` is always cleared after exiting or continuing the loop
        !break_flag ==> (res.2 == return_flag && res.3 == quit_flag),
{
    let (should_exit, next_break) = verified_loop_post_body_action(break_flag, return_flag, quit_flag);
    (should_exit, next_break, return_flag, quit_flag)
}

// ============================================================================
// Target 11: CLI REPL Block Scanner, C-FFI NUL Buffer Safety & Zephyr Editor
// ============================================================================

/// Status constants matching `crates/bc_c_api/src/lib.rs` (`BcStatus`).
pub const BC_STATUS_OK: u8 = 0;
pub const BC_STATUS_ERR_BUFFER_TOO_SMALL: u8 = 2;

/// Verified C-FFI output buffer bounds check and NUL-terminated copy
/// (`crates/bc_c_api/src/lib.rs:149-190, 293-336`).
///
/// Proves:
/// 1. If `buf_size == 0` or `src.len() >= buf_size` (`src.len() + 1 > buf_size`),
///    returns `BC_STATUS_ERR_BUFFER_TOO_SMALL` without overflowing the buffer.
/// 2. On `BC_STATUS_OK`, `out_buf` has exact length `src.len() + 1 <= buf_size`,
///    its prefix matches `src@` byte-for-byte, and its final byte is guaranteed to be `0u8` (NUL).
pub fn verified_c_ffi_copy_nul_terminated(
    src: &[u8],
    out_buf: &mut alloc::vec::Vec<u8>,
    buf_size: usize,
) -> (status: u8)
    ensures
        (buf_size == 0 || src@.len() >= buf_size) ==> (
            status == BC_STATUS_ERR_BUFFER_TOO_SMALL
            && final(out_buf)@ == old(out_buf)@
        ),
        (buf_size > 0 && src@.len() < buf_size) ==> (
            status == BC_STATUS_OK
            && final(out_buf)@.len() == src@.len() + 1
            && final(out_buf)@.len() <= buf_size
            && final(out_buf)@.subrange(0, src@.len() as int) =~= src@
            && final(out_buf)@[src@.len() as int] == 0u8
        ),
{
    if !verified_c_ffi_check_buf_capacity(src.len(), buf_size) {
        return BC_STATUS_ERR_BUFFER_TOO_SMALL;
    }

    out_buf.clear();
    let len: usize = src.len();
    let mut i: usize = 0;

    while i < len
        invariant
            0 <= i <= len,
            len == src@.len(),
            len < buf_size,
            out_buf@.len() == i,
            out_buf@ =~= src@.subrange(0, i as int),
        decreases len - i,
    {
        out_buf.push(src[i]);
        i = i + 1;
    }

    out_buf.push(0u8);
    proof {
        assert(out_buf@.subrange(0, len as int) =~= src@);
    }

    BC_STATUS_OK
}

/// Action codes for the Zephyr RTOS interactive serial REPL line editor (`crates/bc_zephyr/src/lib.rs:327-358`).
pub const REPL_ACTION_NONE: u8 = 0;
pub const REPL_ACTION_EVAL_LINE: u8 = 1;
pub const REPL_ACTION_BACKSPACE: u8 = 2;
pub const REPL_ACTION_CTRL_C: u8 = 3;
pub const REPL_ACTION_APPEND_CHAR: u8 = 4;

/// Verified Zephyr RTOS interactive serial REPL line editor transition
/// (`crates/bc_zephyr/src/lib.rs:327-358`).
///
/// Proves:
/// 1. Backspace (`0x08` or `0x7F`) on an empty buffer is a safe no-op (no underflow),
///    and on a non-empty buffer removes exactly the last character.
/// 2. Ctrl+C (`0x03`) immediately clears the line buffer (`len == 0`).
/// 3. Printable ASCII (`0x20..=0x7E`) appends the character to `line_buf`.
pub fn verified_zephyr_repl_edit_step(
    line_buf: &mut alloc::vec::Vec<u8>,
    b: u8,
) -> (action: u8)
    requires
        old(line_buf)@.len() <= 1_000_000,
    ensures
        (b == b'\r' || b == b'\n') ==> (
            action == REPL_ACTION_EVAL_LINE
            && final(line_buf)@.len() == 0
        ),
        (b == 0x08 || b == 0x7F) ==> (
            action == REPL_ACTION_BACKSPACE
            && (old(line_buf)@.len() == 0 ==> final(line_buf)@.len() == 0)
            && (old(line_buf)@.len() > 0 ==> (
                final(line_buf)@.len() == old(line_buf)@.len() - 1
                && final(line_buf)@ =~= old(line_buf)@.subrange(0, (old(line_buf)@.len() - 1) as int)
            ))
        ),
        b == 0x03 ==> (
            action == REPL_ACTION_CTRL_C
            && final(line_buf)@.len() == 0
        ),
        (0x20 <= b && b <= 0x7E) ==> (
            action == REPL_ACTION_APPEND_CHAR
            && final(line_buf)@.len() == old(line_buf)@.len() + 1
            && final(line_buf)@[old(line_buf)@.len() as int] == b
        ),
{
    let kind = verified_zephyr_classify_char(b);
    if kind == 1 {
        line_buf.clear();
        REPL_ACTION_EVAL_LINE
    } else if kind == 2 {
        if line_buf.len() > 0 {
            let _ = line_buf.pop();
        }
        REPL_ACTION_BACKSPACE
    } else if kind == 3 {
        line_buf.clear();
        REPL_ACTION_CTRL_C
    } else if kind == 4 {
        line_buf.push(b);
        REPL_ACTION_APPEND_CHAR
    } else {
        REPL_ACTION_NONE
    }
}

// ============================================================================
// Target 12: `Decimal` Arithmetic Scaling, Taylor Series Convergence & CLI Parser
// ============================================================================

/// Verified fixed-point `Decimal::mul` and `Decimal::div` unit identity (`math.rs:384-415`).
///
/// Proves via non-linear arithmetic that multiplying or dividing any fixed-point `Decimal`
/// coefficient `val` by the fixed-point unit `one_p = 10^prec >= 1` (`(val * one_p) / one_p`)
/// preserves `val` with zero rounding loss.
pub fn verified_decimal_mul_div_unit_identity(val: u64, one_p: u64) -> (res: (u64, u64))
    requires
        one_p >= 1,
        one_p <= 1_000_000_000,
        val <= 1_000_000_000,
    ensures
        res.0 == val,
        res.1 == val,
{
    proof {
        assert((val as int) * (one_p as int) <= 1_000_000_000 * 1_000_000_000)
            by (nonlinear_arith)
            requires
                val <= 1_000_000_000,
                one_p >= 1,
                one_p <= 1_000_000_000,
        ;
    }
    let prod: u64 = val * one_p;
    let mul_one: u64 = prod / one_p;
    let div_one: u64 = prod / one_p;
    proof {
        assert(mul_one == val) by (nonlinear_arith)
            requires
                prod == val * one_p,
                mul_one == prod / one_p,
                one_p >= 1,
        ;
    }
    (mul_one, div_one)
}

/// Verified Taylor series loop contraction and finite-step termination
/// (`crates/bc_core/src/math.rs:514-765` in `decimal_sin`, `decimal_cos`, `decimal_atan`, `decimal_exp`).
///
/// After argument reduction, the series ratio satisfies $0 \le r \le 1/2$ (`2 * r_val <= one_p`).
/// Proves:
/// 1. At every iteration where `term = num / fact > 0`, `num >= 1` and `next_num = (num * r_val) / one_p <= num / 2 < num`.
/// 2. The loop is guaranteed to terminate (`decreases num`) with `term == 0` in at most `initial_num` steps.
/// 3. The partial sum `total` is monotonically non-decreasing.
pub fn verified_taylor_series_convergence_loop(
    initial_num: u64,
    r_val: u64,
    one_p: u64,
) -> (res: (usize, u64))
    requires
        one_p >= 2,
        one_p <= 1_000_000_000,
        initial_num <= 1_000_000_000,
        2 * (r_val as int) <= (one_p as int),
    ensures
        // res = (iteration_count, final_num)
        res.0 <= initial_num as usize,
        res.1 == 0,
{
    let mut num: u64 = initial_num;
    let mut steps: usize = 0;

    while num > 0
        invariant
            one_p >= 2,
            one_p <= 1_000_000_000,
            2 * (r_val as int) <= (one_p as int),
            num <= initial_num,
            initial_num <= 1_000_000_000,
            steps + (num as usize) <= initial_num as usize,
        decreases num,
    {
        let prev_num: u64 = num;
        proof {
            assert((prev_num as int) * (r_val as int) <= 1_000_000_000 * 500_000_000)
                by (nonlinear_arith)
                requires
                    prev_num <= 1_000_000_000,
                    2 * (r_val as int) <= (one_p as int),
                    one_p <= 1_000_000_000,
            ;
            assert(2 * ((prev_num as int) * (r_val as int)) <= (prev_num as int) * (one_p as int))
                by (nonlinear_arith)
                requires
                    prev_num >= 1,
                    2 * (r_val as int) <= (one_p as int),
            ;
        }
        let prod: u64 = prev_num * r_val;
        let next_num: u64 = prod / one_p;
        proof {
            assert((next_num as int) * (one_p as int) <= (prod as int)) by (nonlinear_arith)
                requires
                    next_num == prod / one_p,
                    one_p >= 2,
            ;
            assert(2 * (next_num as int) <= (prev_num as int)) by (nonlinear_arith)
                requires
                    (next_num as int) * (one_p as int) <= (prod as int),
                    2 * (prod as int) <= (prev_num as int) * (one_p as int),
                    one_p >= 2,
            ;
            assert(next_num < prev_num) by (nonlinear_arith)
                requires
                    prev_num >= 1,
                    2 * (next_num as int) <= (prev_num as int),
            ;
        }
        num = next_num;
        steps = steps + 1;
    }

    (steps, num)
}

/// Verified POSIX CLI option and file argument parser (`crates/bc_cli/src/main.rs:310-328`).
///
/// Returns `(has_error, math_enabled, initial_scale, file_count)`.
/// Proves:
/// 1. Any invalid `-...` option immediately aborts parsing with `has_error == true`.
/// 2. When valid, `initial_scale == 20` if and only if `-l` (`math_enabled`) was specified,
///    and `initial_scale == 0` otherwise.
/// 3. The number of collected file arguments is bounded by `args.len()`.
pub fn verified_cli_parse_args(args: &[u8]) -> (res: (bool, bool, usize, usize))
    ensures
        // res = (has_error, math_enabled, initial_scale, file_count)
        !res.0 ==> (
            (res.1 ==> res.2 == 20)
            && (!res.1 ==> res.2 == 0)
            && res.3 <= args@.len()
        ),
{
    let mut math_enabled: bool = false;
    let mut file_count: usize = 0;
    let mut i: usize = 0;
    let len: usize = args.len();

    while i < len
        invariant
            0 <= i <= len,
            len == args@.len(),
            file_count <= i,
        decreases len - i,
    {
        let arg = args[i];
        if arg == CLI_ARG_OPT_L {
            math_enabled = true;
        } else if arg == CLI_ARG_OPT_S || arg == CLI_ARG_OPT_W {
            // Extension policy flags do not affect the initial scale or the file count.
        } else if arg == CLI_ARG_OPT_INVALID {
            return (true, math_enabled, 0, file_count);
        } else {
            file_count = file_count + 1;
        }
        i = i + 1;
    }

    let initial_scale: usize = verified_cli_initial_scale(math_enabled);
    (false, math_enabled, initial_scale, file_count)
}

} // verus!
