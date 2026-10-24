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

} // verus!
