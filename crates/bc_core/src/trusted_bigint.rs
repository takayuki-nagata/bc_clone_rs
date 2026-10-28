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

/// `10^n`.
#[verifier::external_body]
pub fn big_pow10(n: u32) -> (r: BigInt)
    ensures
        big_view(&r) == pow10(n as nat),
{
    BigInt::from(10).pow(n)
}

} // verus!

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
            prop_assert_eq!(big_is_zero(&big(a)), a == 0);
            if b != 0 {
                prop_assert_eq!(big_tdiv(&big(a), &big(b)), big(tdiv(a, b)));
            }
            prop_assert_eq!(big_is_negative(&big(a)), a < 0);
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
        fn from_usize(n in any::<usize>()) {
            prop_assert_eq!(big_from_usize(n), BigInt::from(n));
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
