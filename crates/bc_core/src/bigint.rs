// SPDX-License-Identifier: MIT

//! The `BigInt` operations that verified code uses: the trusted primitives of
//! `trusted_bigint.rs`, re-exported, and the operations derived from them here, in verified
//! code, with the same kind of contract over the mathematical integers (`big_view`).
//!
//! Callers import every `big_*` function from this module, so whether an operation is trusted
//! or derived is decided here alone.

#[cfg(verus_keep_ghost)]
use crate::spec_num::*;
#[cfg(verus_keep_ghost)]
pub use crate::trusted_bigint::{axiom_bigint_size, big_view};
pub use crate::trusted_bigint::{
    big_add, big_bits, big_clone, big_cmp, big_from_u64, big_mul, big_sub, big_tdiv_rem, big_to_i64,
};
#[cfg(verus_keep_ghost)]
use bc_spec::power::{lemma_pow_add, lemma_pow_mul, lemma_pow_positive};
use core::cmp::Ordering;
use num_bigint::BigInt;
#[cfg(not(verus_keep_ghost))]
use verus_builtin_macros::verus;
#[cfg(verus_keep_ghost)]
use vstd::arithmetic::div_mod::{
    lemma_fundamental_div_mod, lemma_fundamental_div_mod_converse, lemma_mod_pos_bound,
};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

verus! {

pub fn big_zero() -> (r: BigInt)
    ensures
        big_view(&r) == 0,
{
    big_from_u64(0)
}

pub fn big_from_usize(n: usize) -> (r: BigInt)
    ensures
        big_view(&r) == n,
{
    big_from_u64(n as u64)
}

#[allow(
    clippy::cast_sign_loss,
    clippy::cast_possible_truncation,
    reason = "Verus proves both casts exact: n >= 0 in the first, 0 < -n <= 2^63 in the second"
)]
pub fn big_from_i64(n: i64) -> (r: BigInt)
    ensures
        big_view(&r) == n,
{
    if n >= 0 {
        big_from_u64(n as u64)
    } else {
        let m = big_from_u64((-(n as i128)) as u64);
        big_sub(&big_zero(), &m)
    }
}

pub fn big_neg(a: &BigInt) -> (r: BigInt)
    ensures
        big_view(&r) == -big_view(a),
{
    big_sub(&big_zero(), a)
}

pub fn big_is_zero(a: &BigInt) -> (r: bool)
    ensures
        r == (big_view(a) == 0),
{
    matches!(big_cmp(a, &big_zero()), Ordering::Equal)
}

pub fn big_is_negative(a: &BigInt) -> (r: bool)
    ensures
        r == (big_view(a) < 0),
{
    matches!(big_cmp(a, &big_zero()), Ordering::Less)
}

pub fn big_abs(a: &BigInt) -> (r: BigInt)
    ensures
        big_view(&r) == (if big_view(a) >= 0 { big_view(a) } else { -big_view(a) }),
{
    if big_is_negative(a) {
        big_neg(a)
    } else {
        big_clone(a)
    }
}

/// The sign of `a`: 1, 0 or −1.
pub fn big_signum(a: &BigInt) -> (r: BigInt)
    ensures
        big_view(&r) == (if big_view(a) > 0 {
            1int
        } else if big_view(a) < 0 {
            -1int
        } else {
            0int
        }),
{
    match big_cmp(a, &big_zero()) {
        Ordering::Greater => big_from_i64(1),
        Ordering::Less => big_from_i64(-1),
        Ordering::Equal => big_zero(),
    }
}

/// `a / b`, truncated toward zero.
pub fn big_tdiv(a: &BigInt, b: &BigInt) -> (r: BigInt)
    requires
        big_view(b) != 0,
    ensures
        big_view(&r) == spec_tdiv(big_view(a), big_view(b)),
{
    let (q, _) = big_tdiv_rem(a, b);
    q
}

/// `a / d`, truncated toward zero, for a machine-word divisor.
pub fn big_tdiv_u64(a: &BigInt, d: u64) -> (r: BigInt)
    requires
        d > 0,
    ensures
        big_view(&r) == spec_tdiv(big_view(a), d as int),
{
    big_tdiv(a, &big_from_u64(d))
}

/// For a positive divisor, the remainder of truncating division is in `(-d, d)` and has the
/// sign of the dividend.
proof fn lemma_trem_bounds(x: int, d: int)
    requires
        d > 0,
    ensures
        -d < x - spec_tdiv(x, d) * d < d,
        x >= 0 ==> x - spec_tdiv(x, d) * d >= 0,
        x < 0 ==> x - spec_tdiv(x, d) * d <= 0,
{
    let m = if x >= 0 { x } else { -x };
    lemma_fundamental_div_mod(m, d);
    lemma_mod_pos_bound(m, d);
    let (q, r) = (m / d, m % d);
    assert(m - q * d == r) by (nonlinear_arith)
        requires
            m == d * q + r,
    ;
    if x >= 0 {
        assert(spec_tdiv(x, d) == q);
    } else {
        assert(spec_tdiv(x, d) == -q);
        assert(x - spec_tdiv(x, d) * d == -(m - q * d)) by (nonlinear_arith)
            requires
                x == -m,
                spec_tdiv(x, d) == -q,
        ;
    }
}

/// The floor quotient and remainder for a positive divisor; Verus's `/` and `%` are the floor
/// quotient and the nonnegative remainder for a positive divisor.
pub fn big_div_mod_floor(a: &BigInt, b: &BigInt) -> (r: (BigInt, BigInt))
    requires
        big_view(b) > 0,
    ensures
        big_view(&r.0) == big_view(a) / big_view(b),
        big_view(&r.1) == big_view(a) % big_view(b),
{
    let ghost (x, d) = (big_view(a), big_view(b));
    let (q, r) = big_tdiv_rem(a, b);
    proof {
        lemma_trem_bounds(x, d);
    }
    if big_is_negative(&r) {
        let q1 = big_sub(&q, &big_from_u64(1));
        let r1 = big_add(&r, b);
        proof {
            let t = spec_tdiv(x, d);
            assert(x == (t - 1) * d + (x - t * d + d)) by (nonlinear_arith);
            lemma_fundamental_div_mod_converse(x, d, t - 1, x - t * d + d);
        }
        (q1, r1)
    } else {
        proof {
            let t = spec_tdiv(x, d);
            assert(x == t * d + (x - t * d)) by (nonlinear_arith);
            lemma_fundamental_div_mod_converse(x, d, t, x - t * d);
        }
        (q, r)
    }
}

/// The value of a non-negative `BigInt` below `2^32`.
#[allow(clippy::cast_sign_loss, reason = "Verus proves x >= 0 from the precondition")]
pub fn big_to_u64_small(a: &BigInt) -> (r: u64)
    requires
        0 <= big_view(a) < 0x1_0000_0000,
    ensures
        r == big_view(a),
{
    match big_to_i64(a) {
        Some(x) => x as u64,
        // Unreachable: the precondition puts the value in the range of `i64`.
        None => 0,
    }
}

/// `a + d` for a small `d`.
pub fn big_add_i64(a: BigInt, d: i64) -> (r: BigInt)
    ensures
        big_view(&r) == big_view(&a) + d,
{
    big_add(&a, &big_from_i64(d))
}

/// `a·m + d`, for one step of a base conversion.
pub fn big_mul_add_small(a: BigInt, m: usize, d: usize) -> (r: BigInt)
    ensures
        big_view(&r) == big_view(&a) * m + d,
{
    big_add(&big_mul(&a, &big_from_usize(m)), &big_from_usize(d))
}

/// `b^e`, by binary exponentiation (the last squaring is skipped: it would be discarded).
#[allow(clippy::assign_op_pattern, reason = "the code keeps the form that the proof reasons about")]
pub fn big_pow(b: &BigInt, e: u64) -> (r: BigInt)
    ensures
        big_view(&r) == spec_pow_int(big_view(b), e as nat),
{
    let ghost b0 = big_view(b);
    let mut acc = big_from_u64(1);
    let mut base = big_clone(b);
    let mut k = e;
    proof {
        assert(spec_pow_int(b0, e as nat) == 1 * spec_pow_int(big_view(&base), k as nat));
    }
    while k > 0
        invariant
            spec_pow_int(b0, e as nat) == big_view(&acc) * spec_pow_int(big_view(&base), k as nat),
        decreases k,
    {
        let ghost (a0, x, k0) = (big_view(&acc), big_view(&base), k);
        proof {
            lemma_pow_halve(x, k0 as nat);
        }
        if k % 2 == 1 {
            acc = big_mul(&acc, &base);
        }
        k = k / 2;
        if k > 0 {
            base = big_mul(&base, &base);
        }
        proof {
            let h = (k0 / 2) as nat;
            if k0 % 2 == 1 {
                assert(spec_pow_int(x, k0 as nat) == x * spec_pow_int(x * x, h));
                assert(a0 * (x * spec_pow_int(x * x, h)) == (a0 * x) * spec_pow_int(x * x, h))
                    by (nonlinear_arith);
            }
            if k == 0 {
                assert(spec_pow_int(x * x, 0) == 1);
                assert(spec_pow_int(big_view(&base), 0) == 1);
            }
        }
    }
    acc
}

/// `x^k = x^(k mod 2) · (x²)^(k div 2)`.
proof fn lemma_pow_halve(x: int, k: nat)
    ensures
        k % 2 == 0 ==> spec_pow_int(x, k) == spec_pow_int(x * x, k / 2),
        k % 2 == 1 ==> spec_pow_int(x, k) == x * spec_pow_int(x * x, k / 2),
{
    let h = k / 2;
    lemma_pow_mul(x, 2, h);
    assert(spec_pow_int(x, 2) == x * x) by {
        assert(spec_pow_int(x, 1) == x * spec_pow_int(x, 0));
    }
    if k % 2 == 1 {
        assert(k == 1 + 2 * h);
        lemma_pow_add(x, 1, 2 * h);
        assert(spec_pow_int(x, 1) == x * spec_pow_int(x, 0));
    } else {
        assert(k == 2 * h);
    }
}

/// `b^e`.
pub fn big_pow_usize(b: usize, e: usize) -> (r: BigInt)
    ensures
        big_view(&r) == spec_pow_int(b as int, e as nat),
{
    big_pow(&big_from_usize(b), e as u64)
}

/// `10^n`.
pub fn big_pow10(n: u32) -> (r: BigInt)
    ensures
        big_view(&r) == pow10(n as nat),
{
    let r = big_pow(&big_from_u64(10), n as u64);
    proof {
        lemma_pow10_is_pow(n as nat);
    }
    r
}

proof fn lemma_pow10_is_pow(n: nat)
    ensures
        pow10(n) == spec_pow_int(10, n),
    decreases n,
{
    if n > 0 {
        lemma_pow10_is_pow((n - 1) as nat);
    }
}

/// `a·2^n`.
pub fn big_shl(a: &BigInt, n: u64) -> (r: BigInt)
    ensures
        big_view(&r) == big_view(a) * spec_pow_int(2, n as nat),
{
    big_mul(a, &big_pow(&big_from_u64(2), n))
}

/// `⌊a / 2^n⌋`.
pub fn big_shr(a: &BigInt, n: u64) -> (r: BigInt)
    ensures
        big_view(&r) == big_view(a) / spec_pow_int(2, n as nat),
{
    let p = big_pow(&big_from_u64(2), n);
    proof {
        lemma_pow_positive(2, n as nat);
    }
    let (q, _) = big_div_mod_floor(a, &p);
    q
}


/// `b^m <= b^n` for `b >= 1` and `m <= n`.
proof fn lemma_pow_mono(b: int, m: nat, n: nat)
    requires
        b >= 1,
        m <= n,
    ensures
        spec_pow_int(b, m) <= spec_pow_int(b, n),
{
    lemma_pow_add(b, m, (n - m) as nat);
    lemma_pow_positive(b, m);
    lemma_pow_positive(b, (n - m) as nat);
    let (x, y) = (spec_pow_int(b, m), spec_pow_int(b, (n - m) as nat));
    assert(x <= x * y) by (nonlinear_arith)
        requires
            x > 0,
            y >= 1,
    ;
}

/// `2^k <= 10^k`.
proof fn lemma_pow2_le_pow10(k: nat)
    ensures
        spec_pow_int(2, k) <= pow10(k),
    decreases k,
{
    if k > 0 {
        lemma_pow2_le_pow10((k - 1) as nat);
        lemma_pow_positive(2, (k - 1) as nat);
    }
}

/// A Newton step from `x > 0` toward the integer square root of `n`, with `q = ⌊n/x⌋` and
/// `y = ⌊(x + q)/2⌋`, does not go below it: `n < (y+1)²`.
proof fn lemma_newton_above(n: int, x: int, q: int, y: int)
    requires
        x > 0,
        x * q <= n < x * q + x,
        2 * y <= x + q <= 2 * y + 1,
    ensures
        n < (y + 1) * (y + 1),
{
    let t = y + 1;
    // x·(q+1) > n, and q + 1 <= 2t − x, so n < x·(2t − x) = t² − (t − x)² <= t².
    assert(n < x * (q + 1)) by (nonlinear_arith)
        requires
            n < x * q + x,
    ;
    assert(x * (q + 1) <= x * (2 * t - x)) by (nonlinear_arith)
        requires
            x > 0,
            q + 1 <= 2 * t - x,
    ;
    assert(x * (2 * t - x) == t * t - (t - x) * (t - x)) by (nonlinear_arith);
    assert((t - x) * (t - x) >= 0) by (nonlinear_arith);
}

/// The Newton step stops decreasing only at the root: `y >= x` implies `x² <= n`.
proof fn lemma_newton_stop(n: int, x: int, q: int, y: int)
    requires
        x > 0,
        x * q <= n,
        2 * y <= x + q,
        y >= x,
    ensures
        x * x <= n,
{
    assert(q >= x);
    assert(x * x <= x * q) by (nonlinear_arith)
        requires
            x > 0,
            q >= x,
    ;
}

/// The integer square root, by Newton's method from `2^⌈b/2⌉` (`b` the bit length), which is
/// above the root; the iterates decrease strictly until the root.
pub fn big_isqrt(n: &BigInt) -> (r: BigInt)
    requires
        big_view(n) >= 0,
    ensures
        is_isqrt(big_view(n), big_view(&r)),
{
    let ghost nv = big_view(n);
    if big_is_zero(n) {
        proof {
            assert(is_isqrt(0, 0)) by (nonlinear_arith);
        }
        return big_zero();
    }
    let b = big_bits(n);
    let h = b / 2 + b % 2;
    let mut x = big_shl(&big_from_u64(1), h);
    proof {
        lemma_pow_add(2, h as nat, h as nat);
        lemma_pow_mono(2, b as nat, (h + h) as nat);
        lemma_pow_positive(2, h as nat);
        let xv = big_view(&x);
        assert(xv == spec_pow_int(2, h as nat));
        assert(nv < (xv + 1) * (xv + 1)) by (nonlinear_arith)
            requires
                nv < xv * xv,
                xv > 0,
        ;
    }
    let mut done = false;
    while !done
        invariant
            nv == big_view(n),
            nv >= 1,
            big_view(&x) > 0,
            nv < (big_view(&x) + 1) * (big_view(&x) + 1),
            done ==> big_view(&x) * big_view(&x) <= nv,
        decreases 2 * big_view(&x) + (if done { 0int } else { 1int }),
    {
        let ghost xv = big_view(&x);
        let q = big_tdiv(n, &x);
        let y = big_tdiv_u64(&big_add(&x, &q), 2);
        let ghost (qv, yv) = (big_view(&q), big_view(&y));
        proof {
            lemma_fundamental_div_mod(nv, xv);
            lemma_mod_pos_bound(nv, xv);
            assert(qv == nv / xv);
            assert(xv * qv <= nv < xv * qv + xv) by (nonlinear_arith)
                requires
                    nv == xv * qv + nv % xv,
                    0 <= nv % xv < xv,
            ;
            assert(qv >= 0) by (nonlinear_arith)
                requires
                    xv > 0,
                    nv >= 0,
                    nv < xv * qv + xv,
            ;
            lemma_fundamental_div_mod(xv + qv, 2);
            lemma_mod_pos_bound(xv + qv, 2);
            assert(yv == (xv + qv) / 2);
            lemma_newton_above(nv, xv, qv, yv);
        }
        if matches!(big_cmp(&y, &x), Ordering::Less) {
            proof {
                assert(yv >= 1) by (nonlinear_arith)
                    requires
                        nv >= 1,
                        nv < (yv + 1) * (yv + 1),
                        2 * yv >= xv + qv - 1,
                        xv > 0,
                        qv >= 0,
                ;
            }
            x = y;
        } else {
            proof {
                lemma_newton_stop(nv, xv, qv, yv);
            }
            done = true;
        }
    }
    x
}

/// The number of decimal digits of `a > 0`. It is below the bit length, so it fits in a `u64`
/// (not always in a `usize` on 32-bit targets). The bit length gives an estimate from below
/// (`log10 2 > 0.30102999566`), and the loops correct it.
#[allow(
    clippy::cast_possible_truncation,
    reason = "Verus proves est <= b - 1, so the u128 quotient fits in a u64"
)]
#[allow(clippy::assign_op_pattern, reason = "the code keeps the form that the proof reasons about")]
pub fn big_decimal_digits(a: &BigInt) -> (r: u64)
    requires
        big_view(a) > 0,
    ensures
        is_digit_count(big_view(a), r as nat),
{
    let ghost av = big_view(a);
    let b = big_bits(a);
    let x = (b - 1) as u128;
    let est = (x * 30102999566u128 / 100000000000u128) as u64;
    proof {
        assert(x * 30102999566 / 100000000000 <= x) by (nonlinear_arith)
            requires
                x >= 0,
        ;
    }
    let ten = big_from_u64(10);
    let mut p = big_pow(&ten, est);
    let mut k = est + 1;
    proof {
        lemma_pow10_is_pow(est as nat);
    }
    // Down to `10^(k-1) <= a` (the estimate is from below, so this does not run in practice).
    let mut above = matches!(big_cmp(&p, a), Ordering::Greater);
    while above
        invariant
            av == big_view(a),
            av >= 1,
            k >= 1,
            big_view(&p) == pow10((k - 1) as nat),
            above == (big_view(&p) > av),
        decreases k,
    {
        proof {
            // pow10(0) = 1 <= a, so k >= 2.
            assert(k >= 2);
            let m = pow10((k - 2) as nat);
            assert(pow10((k - 1) as nat) == 10 * m);
            lemma_pow10_pos((k - 2) as nat);
            lemma_fundamental_div_mod_converse(10 * m, 10, m, 0);
        }
        p = big_tdiv_u64(&p, 10);
        k = k - 1;
        above = matches!(big_cmp(&p, a), Ordering::Greater);
    }
    // Up to `a < 10^k`.
    let mut q = big_mul(&p, &ten);
    let mut fits = matches!(big_cmp(&q, a), Ordering::Greater);
    while !fits
        invariant
            av == big_view(a),
            k >= 1,
            big_view(&p) == pow10((k - 1) as nat),
            big_view(&p) <= av,
            big_view(&q) == pow10(k as nat),
            fits == (big_view(&q) > av),
            big_view(&ten) == 10,
            b >= 1,
            av < spec_pow_int(2, b as nat),
        decreases av - big_view(&p),
    {
        proof {
            // 2^k <= 10^k <= a < 2^b, so k < b <= u64::MAX.
            lemma_pow2_le_pow10(k as nat);
            if k >= b {
                lemma_pow_mono(2, b as nat, k as nat);
            }
            lemma_pow10_pos((k - 1) as nat);
        }
        p = q;
        q = big_mul(&p, &ten);
        k = k + 1;
        proof {
            assert(pow10(k as nat) == 10 * pow10((k - 1) as nat));
        }
        fits = matches!(big_cmp(&q, a), Ordering::Greater);
    }
    k
}

} // verus!

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::string::ToString;
    use proptest::prelude::*;

    fn big(x: i128) -> BigInt {
        BigInt::from(x)
    }

    /// Truncating division over `i128`, written out like `spec_tdiv`.
    fn tdiv(a: i128, b: i128) -> i128 {
        let q = a.abs() / b.abs();
        if (a < 0) != (b < 0) { -q } else { q }
    }

    // The derived operations are proved; these tests check the proofs' setting (that the
    // contracts say what the callers expect) on a few values.
    proptest! {
        #[test]
        fn derived_operations(a in -(1i128 << 60)..(1i128 << 60), b in -(1i128 << 60)..(1i128 << 60), v in any::<i64>(), x in any::<u32>(), n in any::<usize>(), m in 0usize..=36, d in 0usize..=35) {
            prop_assert_eq!(big_neg(&big(a)), big(-a));
            prop_assert_eq!(big_is_zero(&big(a)), a == 0);
            prop_assert_eq!(big_is_negative(&big(a)), a < 0);
            prop_assert_eq!(big_abs(&big(a)), big(a.abs()));
            prop_assert_eq!(big_signum(&big(a)), big(a.signum()));
            if b != 0 {
                prop_assert_eq!(big_tdiv(&big(a), &big(b)), big(tdiv(a, b)));
                prop_assert_eq!(big_tdiv_u64(&big(a), b.unsigned_abs() as u64), big(tdiv(a, b.abs())));
            }
            if b > 0 {
                prop_assert_eq!(big_div_mod_floor(&big(a), &big(b)), (big(a.div_euclid(b)), big(a.rem_euclid(b))));
            }
            prop_assert_eq!(big_from_i64(v), big(i128::from(v)));
            prop_assert_eq!(big_add_i64(big(a), v), big(a + i128::from(v)));
            prop_assert_eq!(big_to_u64_small(&big(i128::from(x))), u64::from(x));
            prop_assert_eq!(big_from_usize(n), BigInt::from(n));
            prop_assert_eq!(big_mul_add_small(big(a), m, d), big(a * m as i128 + d as i128));
        }

        #[test]
        fn isqrt_and_digit_count(a in 0i128..(1i128 << 100)) {
            let r = big_isqrt(&big(a));
            prop_assert!(&r * &r <= big(a) && big(a) < (&r + 1) * (&r + 1));
            if a > 0 {
                let k = big_decimal_digits(&big(a));
                prop_assert_eq!(k, a.to_string().len() as u64);
            }
        }

        #[test]
        fn powers_and_shifts(a in -(1i128 << 60)..(1i128 << 60), n in 0u64..60, m in 0usize..=36, e in 0usize..=20) {
            prop_assert_eq!(big_pow_usize(m, e), BigInt::from(m).pow(e as u32));
            prop_assert_eq!(big_shl(&big(a), n), big(a * (1i128 << n)));
            prop_assert_eq!(big_shr(&big(a), n), big(a.div_euclid(1i128 << n)));
        }
    }

    #[test]
    fn edges() {
        assert_eq!(big_zero(), big(0));
        assert_eq!(big_from_i64(i64::MIN), big(i128::from(i64::MIN)));
        assert!(!big_is_negative(&big_neg(&big(0))));
        let mut p = 1i128;
        for n in 0..=38u32 {
            assert_eq!(big_pow10(n), big(p));
            p = p.saturating_mul(10);
        }
        assert_eq!(big_pow(&big(-3), 0), big(1));
        assert_eq!(big_pow(&big(-3), 5), big(-243));
    }
}
