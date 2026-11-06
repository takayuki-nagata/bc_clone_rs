// SPDX-License-Identifier: MIT

//! The trusted interface to `num-bigint`: the primitive `BigInt` operations that the other
//! operations are built on.
//!
//! Verus does not verify `num-bigint`. Each function here is a one-line wrapper around a
//! `BigInt` operation, marked `#[verifier::external_body]`: Verus assumes its `ensures` clause
//! and does not check the body. The clauses state the operation over the mathematical integers
//! (`big_view`), using the L0 definitions of `spec_num` (e.g. truncating division is
//! `spec_tdiv`). These assumptions are part of the trusted computing base of the proofs. The
//! other operations (sign tests, floor division, powers, shifts, the integer square root, the
//! decimal digit count, ...) are derived from these in verified code in `bigint.rs`, which is
//! also where callers import them from.
//!
//! The tests below check each wrapper against `i128` arithmetic, and `oracle_tests` checks them
//! on multi-limb values against the executable decimal arithmetic of the specification, which
//! is proved and does not use `num-bigint`.
//!
//! Keep every wrapper this small, so that its clause is evidently what the `num-bigint`
//! operation computes, and add a test for each new one. Add a wrapper only for an operation that
//! cannot be derived from these at a reasonable cost.

#[cfg(verus_keep_ghost)]
use crate::spec_num::*;
#[cfg(verus_keep_ghost)]
use bc_spec::convert::value_bits;
use core::cmp::Ordering;
use num_bigint::BigInt;
use num_traits::ToPrimitive;
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

/// The truncating quotient and its remainder (`Integer::div_rem`, which is `BigInt`'s `/` and
/// `%` computed at once).
#[verifier::external_body]
pub fn big_tdiv_rem(a: &BigInt, b: &BigInt) -> (r: (BigInt, BigInt))
    requires
        big_view(b) != 0,
    ensures
        big_view(&r.0) == spec_tdiv(big_view(a), big_view(b)),
        big_view(&r.1) == big_view(a) - spec_tdiv(big_view(a), big_view(b)) * big_view(b),
{
    num_integer::Integer::div_rem(a, b)
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

#[verifier::external_body]
pub fn big_from_u64(n: u64) -> (r: BigInt)
    ensures
        big_view(&r) == n,
{
    BigInt::from(n)
}

/// The number of bits of |a| (`BigInt::bits`): 0 for 0, otherwise the `r` with
/// `2^(r-1) <= |a| < 2^r`.
#[verifier::external_body]
pub fn big_bits(a: &BigInt) -> (r: u64)
    ensures
        big_view(a) == 0 ==> r == 0,
        big_view(a) != 0 ==> r >= 1 && spec_pow_int(2, (r - 1) as nat) <= (if big_view(a) >= 0 {
            big_view(a)
        } else {
            -big_view(a)
        }) < spec_pow_int(2, r as nat),
{
    a.bits()
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
            if b != 0 {
                prop_assert_eq!(big_tdiv_rem(&big(a), &big(b)), (big(tdiv(a, b)), big(a - tdiv(a, b) * b)));
            }
            prop_assert_eq!(big_cmp(&big(a), &big(b)), a.cmp(&b));
        }

        #[test]
        fn clone_and_to_i64(a in any::<i64>(), wide in any::<i128>()) {
            prop_assert_eq!(big_clone(&big(i128::from(a))), big(i128::from(a)));
            prop_assert_eq!(big_to_i64(&big(i128::from(a))), Some(a));
            let fits = i128::from(i64::MIN) <= wide && wide <= i128::from(i64::MAX);
            prop_assert_eq!(big_to_i64(&big(wide)).is_some(), fits);
        }

        #[test]
        fn bits_and_from_u64(a in -(1i128 << 60)..(1i128 << 60), v in any::<u64>()) {
            prop_assert_eq!(big_from_u64(v), big(i128::from(v)));
            prop_assert_eq!(big_bits(&big(a)), u64::from(128 - a.unsigned_abs().leading_zeros()));
        }
    }
}
