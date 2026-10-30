// SPDX-License-Identifier: MIT

//! Mathematical (L0) specification of `bc` numbers over the unbounded integers.
//!
//! These definitions are the meaning of every number in the executable specification and the
//! reference point for the refinement proofs of `bc_core`, which uses them through
//! `bc_core::spec_num`.

use vstd::prelude::*;

verus! {

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

/// Truncation toward zero of `a / b` for `b > 0` (Verus's `/` floors for a positive divisor).
pub open spec fn trunc_div(a: int, b: int) -> int {
    if a >= 0 {
        a / b
    } else {
        -((-a) / b)
    }
}

/// The floor quotient is unique: `q·d <= n < q·d + d` determines `n / d`.
pub proof fn lemma_floor_div_unique(n: int, d: int, q: int)
    requires
        d > 0,
        q * d <= n,
        n < q * d + d,
    ensures
        n / d == q,
{
    assert((n / d) * d + n % d == n && 0 <= n % d && n % d < d) by (nonlinear_arith)
        requires
            d > 0,
    ;
    let q2 = n / d;
    assert(q2 == q) by (nonlinear_arith)
        requires
            d > 0,
            q * d <= n,
            n < q * d + d,
            q2 * d <= n,
            n < q2 * d + d,
    ;
}

/// Truncating integer division (toward zero), as `BigInt` `/` computes it, for any nonzero `b`.
pub open spec fn spec_tdiv(a: int, b: int) -> int {
    let q = (if a >= 0 { a } else { -a }) / (if b >= 0 { b } else { -b });
    if (a < 0) != (b < 0) { -q } else { q }
}

/// `a * b` truncated toward zero to the POSIX multiplication scale (`BCNum::mul`).
pub open spec fn spec_mul(a: SpecBCNum, b: SpecBCNum, global_scale: nat) -> SpecBCNum {
    let sr = spec_posix_mul_scale(a.scale, b.scale, global_scale);
    SpecBCNum {
        coeff: spec_tdiv(a.coeff * b.coeff, pow10((a.scale + b.scale - sr) as nat)),
        scale: sr,
    }
}

/// `a / b` for `b != 0`: the quotient truncated toward zero at `global_scale` digits.
pub open spec fn spec_div(a: SpecBCNum, b: SpecBCNum, global_scale: nat) -> SpecBCNum {
    let shift = b.scale + global_scale - a.scale;
    SpecBCNum {
        coeff: if shift >= 0 {
            spec_tdiv(a.coeff * pow10(shift as nat), b.coeff)
        } else {
            spec_tdiv(a.coeff, b.coeff * pow10((-shift) as nat))
        },
        scale: global_scale,
    }
}

/// `a % b` for `b != 0`: `a - (a / b) * b`, where the product keeps its exact scale.
pub open spec fn spec_mod(a: SpecBCNum, b: SpecBCNum, global_scale: nat) -> SpecBCNum {
    let q = spec_div(a, b, global_scale);
    a.spec_sub(SpecBCNum { coeff: q.coeff * b.coeff, scale: q.scale + b.scale })
}

/// The integer part of `b`, truncated toward zero (the exponent of `^`).
pub open spec fn spec_int_part(b: SpecBCNum) -> int {
    spec_tdiv(b.coeff, pow10(b.scale))
}

/// `a ^ b` when no error applies (`BCNum::try_pow`): the exact power of the coefficient has
/// scale `scale(a) * |n|`; a non-negative power is truncated to the POSIX power scale, and a
/// negative one is `1 / a^|n|` at `scale`.
pub open spec fn spec_pow(a: SpecBCNum, b: SpecBCNum, global_scale: nat) -> SpecBCNum {
    let e = spec_int_part(b);
    let n = (if e >= 0 { e } else { -e }) as nat;
    let r = spec_pow_int(a.coeff, n);
    let exact = a.scale * n;
    if e >= 0 {
        let sr = spec_posix_pow_scale(a.scale, n, global_scale);
        SpecBCNum { coeff: spec_tdiv(r, pow10((exact - sr) as nat)), scale: sr }
    } else {
        spec_div(SpecBCNum { coeff: 1, scale: 0 }, SpecBCNum { coeff: r, scale: exact }, global_scale)
    }
}

/// `r` is the integer square root of `n`.
pub open spec fn is_isqrt(n: int, r: int) -> bool {
    r >= 0 && r * r <= n && n < (r + 1) * (r + 1)
}

/// `k` is the number of decimal digits of `n > 0`.
pub open spec fn is_digit_count(n: int, k: nat) -> bool {
    k >= 1 && pow10((k - 1) as nat) <= n && n < pow10(k)
}

/// The value of big-endian digits `ds` in `base`, continuing from `acc`.
pub open spec fn spec_horner(acc: int, ds: Seq<u8>, base: int) -> int
    decreases ds.len(),
{
    if ds.len() == 0 {
        acc
    } else {
        spec_horner(acc * base + ds[0], ds.drop_first(), base)
    }
}

} // verus!
