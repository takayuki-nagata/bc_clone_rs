// SPDX-License-Identifier: MIT

//! The trusted interface to `num-bigint`: every `BigInt` operation that verified code uses.
//!
//! Verus does not verify `num-bigint`. Each function here is a one-line wrapper around a
//! `BigInt` operation, marked `#[verifier::external_body]`: Verus assumes its `ensures` clause
//! and does not check the body. The clauses state the operation over the mathematical integers
//! (`big_view`), using the L0 definitions of `spec_num` (e.g. truncating division is
//! `spec_tdiv`). These assumptions are part of the trusted computing base of the refinement
//! proofs (proved versions would replace them); the tests below check each one against
//! independent `i128` arithmetic.
//!
//! Keep every wrapper this small, so that its clause is evidently what the `num-bigint`
//! operation computes, and add a test for each new one.

#[cfg(verus_keep_ghost)]
use crate::spec_num::*;
use alloc::string::ToString;
#[cfg(verus_keep_ghost)]
use bc_spec::convert::value_bits;
use core::cmp::Ordering;
use num_bigint::BigInt;
use num_traits::{Signed, ToPrimitive, Zero};
#[cfg(not(verus_keep_ghost))]
use verus_builtin_macros::verus;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

verus! {

#[cfg(verus_keep_ghost)]
#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExBigInt(BigInt);

/// The integer a `BigInt` denotes.
pub uninterp spec fn big_view(b: &BigInt) -> int;

/// Every `BigInt` has fewer than 2^60 bits (128 PiB): it is below `2^value_bits()` in absolute
/// value, the bound under which the specification's digit counts are proved.
pub axiom fn axiom_bigint_size(b: &BigInt)
    ensures
        -spec_pow_int(2, value_bits()) < big_view(b) < spec_pow_int(2, value_bits()),
;

#[verifier::external_body]
pub fn big_zero() -> (r: BigInt)
    ensures
        big_view(&r) == 0,
{
    BigInt::zero()
}

#[verifier::external_body]
pub fn big_add(a: &BigInt, b: &BigInt) -> (r: BigInt)
    ensures
        big_view(&r) == big_view(a) + big_view(b),
{
    a + b
}

#[verifier::external_body]
pub fn big_sub(a: &BigInt, b: &BigInt) -> (r: BigInt)
    ensures
        big_view(&r) == big_view(a) - big_view(b),
{
    a - b
}

#[verifier::external_body]
pub fn big_neg(a: &BigInt) -> (r: BigInt)
    ensures
        big_view(&r) == -big_view(a),
{
    -a
}

#[verifier::external_body]
pub fn big_mul(a: &BigInt, b: &BigInt) -> (r: BigInt)
    ensures
        big_view(&r) == big_view(a) * big_view(b),
{
    a * b
}

/// `a / b`, truncated toward zero (`BigInt`'s `/`).
#[verifier::external_body]
pub fn big_tdiv(a: &BigInt, b: &BigInt) -> (r: BigInt)
    requires
        big_view(b) != 0,
    ensures
        big_view(&r) == spec_tdiv(big_view(a), big_view(b)),
{
    a / b
}

#[verifier::external_body]
pub fn big_cmp(a: &BigInt, b: &BigInt) -> (r: Ordering)
    ensures
        (r == Ordering::Less) == (big_view(a) < big_view(b)),
        (r == Ordering::Equal) == (big_view(a) == big_view(b)),
        (r == Ordering::Greater) == (big_view(a) > big_view(b)),
{
    a.cmp(b)
}

/// `a % b`, the remainder of truncating division (`BigInt`'s `%`).
#[verifier::external_body]
pub fn big_trem(a: &BigInt, b: &BigInt) -> (r: BigInt)
    requires
        big_view(b) != 0,
    ensures
        big_view(&r) == big_view(a) - spec_tdiv(big_view(a), big_view(b)) * big_view(b),
{
    a % b
}

/// The value of a non-negative `BigInt` below `2^32` (its only 32-bit limb, or none for 0).
#[verifier::external_body]
pub fn big_to_u64_small(a: &BigInt) -> (r: u64)
    requires
        0 <= big_view(a) < 0x1_0000_0000,
    ensures
        r == big_view(a),
{
    a.iter_u32_digits().next().map_or(0, u64::from)
}

#[verifier::external_body]
pub fn big_is_zero(a: &BigInt) -> (r: bool)
    ensures
        r == (big_view(a) == 0),
{
    a.is_zero()
}

#[verifier::external_body]
pub fn big_from_usize(n: usize) -> (r: BigInt)
    ensures
        big_view(&r) == n,
{
    BigInt::from(n)
}

#[verifier::external_body]
pub fn big_is_negative(a: &BigInt) -> (r: bool)
    ensures
        r == (big_view(a) < 0),
{
    a.is_negative()
}

#[verifier::external_body]
pub fn big_abs(a: &BigInt) -> (r: BigInt)
    ensures
        big_view(&r) == (if big_view(a) >= 0 { big_view(a) } else { -big_view(a) }),
{
    a.abs()
}

/// The integer square root (`BigInt::sqrt`, which panics on a negative argument).
#[verifier::external_body]
pub fn big_isqrt(a: &BigInt) -> (r: BigInt)
    requires
        big_view(a) >= 0,
    ensures
        is_isqrt(big_view(a), big_view(&r)),
{
    a.sqrt()
}

/// The number of decimal digits of a positive integer (the length of its decimal text).
#[verifier::external_body]
pub fn big_decimal_digits(a: &BigInt) -> (r: usize)
    requires
        big_view(a) > 0,
    ensures
        is_digit_count(big_view(a), r as nat),
{
    a.to_string().len()
}

#[verifier::external_body]
pub fn big_clone(a: &BigInt) -> (r: BigInt)
    ensures
        big_view(&r) == big_view(a),
{
    a.clone()
}

/// The value as an `i64`, if it fits.
#[verifier::external_body]
pub fn big_to_i64(a: &BigInt) -> (r: Option<i64>)
    ensures
        match r {
            Some(x) => x as int == big_view(a),
            None => big_view(a) < i64::MIN || big_view(a) > i64::MAX,
        },
{
    a.to_i64()
}

/// `a·m + d`, for one step of a base conversion.
#[verifier::external_body]
pub fn big_mul_add_small(a: BigInt, m: usize, d: usize) -> (r: BigInt)
    ensures
        big_view(&r) == big_view(&a) * m + d,
{
    a * m + d
}

/// `b^e`.
#[verifier::external_body]
pub fn big_pow_usize(b: usize, e: usize) -> (r: BigInt)
    ensures
        big_view(&r) == spec_pow_int(b as int, e as nat),
{
    num_traits::pow(BigInt::from(b), e)
}

/// `10^n`.
#[verifier::external_body]
pub fn big_pow10(n: u32) -> (r: BigInt)
    ensures
        big_view(&r) == pow10(n as nat),
{
    BigInt::from(10).pow(n)
}

#[verifier::external_body]
pub fn big_from_i64(n: i64) -> (r: BigInt)
    ensures
        big_view(&r) == n,
{
    BigInt::from(n)
}

#[verifier::external_body]
pub fn big_from_u64(n: u64) -> (r: BigInt)
    ensures
        big_view(&r) == n,
{
    BigInt::from(n)
}

/// `a / d`, truncated toward zero, for a machine-word divisor.
#[verifier::external_body]
pub fn big_tdiv_u64(a: &BigInt, d: u64) -> (r: BigInt)
    requires
        d > 0,
    ensures
        big_view(&r) == spec_tdiv(big_view(a), d as int),
{
    a / d
}

/// The number of bits of |a| (`BigInt::bits`). Only a heuristic of `mathlib::ln_ball` uses it,
/// so nothing is assumed about its value.
#[verifier::external_body]
pub fn big_bits(a: &BigInt) -> u64 {
    a.bits()
}

/// The sign of `a`: 1, 0 or −1.
#[verifier::external_body]
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
    a.signum()
}

/// `a + d` for a small `d`, reusing `a`'s storage.
#[verifier::external_body]
pub fn big_add_i64(a: BigInt, d: i64) -> (r: BigInt)
    ensures
        big_view(&r) == big_view(&a) + d,
{
    a + d
}

/// `a·2^n` (`<<`).
#[verifier::external_body]
pub fn big_shl(a: &BigInt, n: u64) -> (r: BigInt)
    ensures
        big_view(&r) == big_view(a) * spec_pow_int(2, n as nat),
{
    a << n
}

/// `⌊a / 2^n⌋` (`>>`, which rounds toward negative infinity on a `BigInt`).
#[verifier::external_body]
pub fn big_shr(a: &BigInt, n: u64) -> (r: BigInt)
    ensures
        big_view(&r) == big_view(a) / spec_pow_int(2, n as nat),
{
    a >> n
}

/// The floor quotient and remainder (`Integer::div_mod_floor`) for a positive divisor; Verus's
/// `/` and `%` are the floor quotient and the nonnegative remainder for a positive divisor.
#[verifier::external_body]
pub fn big_div_mod_floor(a: &BigInt, b: &BigInt) -> (r: (BigInt, BigInt))
    requires
        big_view(b) > 0,
    ensures
        big_view(&r.0) == big_view(a) / big_view(b),
        big_view(&r.1) == big_view(a) % big_view(b),
{
    num_integer::Integer::div_mod_floor(a, b)
}

} // verus!

// Not under Miri: the specification's arithmetic is too slow there, and the cases are pure
// `num-bigint` arithmetic.
#[cfg(all(test, not(miri)))]
mod oracle_tests;

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    fn big(x: i128) -> BigInt {
        BigInt::from(x)
    }

    /// Truncating division over `i128`, written out like `spec_tdiv`.
    fn tdiv(a: i128, b: i128) -> i128 {
        let q = a.abs() / b.abs();
        if (a < 0) != (b < 0) { -q } else { q }
    }

    proptest! {
        #[test]
        fn wrappers_match_integer_arithmetic(a in -(1i128 << 60)..(1i128 << 60), b in -(1i128 << 60)..(1i128 << 60)) {
            prop_assert_eq!(big_add(&big(a), &big(b)), big(a + b));
            prop_assert_eq!(big_sub(&big(a), &big(b)), big(a - b));
            prop_assert_eq!(big_mul(&big(a), &big(b)), big(a * b));
            prop_assert_eq!(big_neg(&big(a)), big(-a));
            prop_assert_eq!(big_is_zero(&big(a)), a == 0);
            if b != 0 {
                prop_assert_eq!(big_tdiv(&big(a), &big(b)), big(tdiv(a, b)));
            }
            prop_assert_eq!(big_is_negative(&big(a)), a < 0);
            prop_assert_eq!(big_cmp(&big(a), &big(b)), a.cmp(&b));
            if b != 0 {
                prop_assert_eq!(big_trem(&big(a), &big(b)), big(a - tdiv(a, b) * b));
            }
            prop_assert_eq!(big_abs(&big(a)), big(a.abs()));
        }

        #[test]
        fn isqrt_and_digit_count(a in 0i128..(1i128 << 100)) {
            let r = big_isqrt(&big(a));
            prop_assert!(&r * &r <= big(a) && big(a) < (&r + 1) * (&r + 1));
            if a > 0 {
                let k = big_decimal_digits(&big(a));
                prop_assert!(k >= 1 && 10i128.pow(k as u32 - 1) <= a && (k >= 39 || a < 10i128.pow(k as u32)));
            }
        }

        #[test]
        fn clone_and_to_i64(a in any::<i64>(), wide in any::<i128>()) {
            prop_assert_eq!(big_clone(&big(i128::from(a))), big(i128::from(a)));
            prop_assert_eq!(big_to_i64(&big(i128::from(a))), Some(a));
            let fits = i128::from(i64::MIN) <= wide && wide <= i128::from(i64::MAX);
            prop_assert_eq!(big_to_i64(&big(wide)).is_some(), fits);
        }

        #[test]
        fn small_steps(a in -(1i128 << 60)..(1i128 << 60), m in 0usize..=36, d in 0usize..=35, e in 0usize..=20) {
            prop_assert_eq!(big_mul_add_small(big(a), m, d), big(a * m as i128 + d as i128));
            prop_assert_eq!(big_pow_usize(m, e), BigInt::from(m).pow(e as u32));
        }

        #[test]
        fn small_values(x in any::<u32>()) {
            prop_assert_eq!(big_to_u64_small(&big(i128::from(x))), u64::from(x));
        }

        #[test]
        fn from_usize(n in any::<usize>()) {
            prop_assert_eq!(big_from_usize(n), BigInt::from(n));
        }
    }

    /// Floor division and remainder over `i128`, for a positive divisor.
    fn floor_div_mod(a: i128, b: i128) -> (i128, i128) {
        (a.div_euclid(b), a.rem_euclid(b))
    }

    proptest! {
        #[test]
        fn shifts_and_floor_division(a in -(1i128 << 60)..(1i128 << 60), b in 1i128..(1i128 << 60), n in 0u64..60, v in any::<i64>()) {
            prop_assert_eq!(big_from_i64(v), big(i128::from(v)));
            prop_assert_eq!(big_add_i64(big(a), v), big(a + i128::from(v)));
            prop_assert_eq!(big_from_u64(v.unsigned_abs()), big(i128::from(v.unsigned_abs())));
            prop_assert_eq!(big_signum(&big(a)), big(a.signum()));
            prop_assert_eq!(big_bits(&big(a)), u64::from(128 - a.unsigned_abs().leading_zeros()));
            let d = b.unsigned_abs() as u64;
            prop_assert_eq!(big_tdiv_u64(&big(a), d), big(tdiv(a, i128::from(d))));
            prop_assert_eq!(big_shl(&big(a), n), big(a * (1i128 << n)));
            prop_assert_eq!(big_shr(&big(a), n), big(floor_div_mod(a, 1i128 << n).0));
            let (q, r) = floor_div_mod(a, b);
            prop_assert_eq!(big_div_mod_floor(&big(a), &big(b)), (big(q), big(r)));
        }
    }

    #[test]
    fn zero_and_powers_of_ten() {
        assert_eq!(big_zero(), big(0));
        let mut p = 1i128;
        for n in 0..=38u32 {
            assert_eq!(big_pow10(n), big(p));
            p = p.saturating_mul(10);
        }
    }
}
