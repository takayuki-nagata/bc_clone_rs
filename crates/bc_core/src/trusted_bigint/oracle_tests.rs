// SPDX-License-Identifier: MIT

//! Checks the trusted `num-bigint` wrappers on multi-limb values against the executable decimal
//! arithmetic of the specification (`bc_spec::num`), which is proved to compute the integer
//! operations and does not use `num-bigint`.
//!
//! Values are built from 32-bit limbs (`BigInt::from_slice`) and read back with
//! `to_u32_digits`, and the conversion between limbs and decimal digits is done here, so the
//! check does not go through `num-bigint`'s own radix conversion. The specification's
//! arithmetic is quadratic in the number of digits per addition, so the operands stay at a few
//! hundred digits; larger operands are checked against identities instead.

use super::*;
use crate::bigint::{big_abs, big_decimal_digits, big_is_negative, big_is_zero, big_isqrt};
use alloc::vec;
use alloc::vec::Vec;
use bc_spec::num::{exec_add_mag, exec_cmp_mag, exec_divmod_mag, exec_mul_mag, exec_sub_mag};
use num_bigint::Sign;
use proptest::prelude::*;

/// Little-endian decimal digits of the little-endian 32-bit limbs `limbs` (no leading zeros).
fn limbs_to_mag(limbs: &[u32]) -> Vec<u8> {
    let mut mag: Vec<u8> = Vec::new();
    for &limb in limbs.iter().rev() {
        // mag = mag · 2^32 + limb, one decimal digit at a time.
        let mut carry = u64::from(limb);
        for d in mag.iter_mut() {
            let t = u64::from(*d) * (1u64 << 32) + carry;
            *d = (t % 10) as u8;
            carry = t / 10;
        }
        while carry > 0 {
            mag.push((carry % 10) as u8);
            carry /= 10;
        }
    }
    mag
}

/// Drops the leading zeros (at the end) of a magnitude.
fn trim(mut m: Vec<u8>) -> Vec<u8> {
    while m.last() == Some(&0) {
        m.pop();
    }
    m
}

/// A signed value as the specification sees it: sign (`true` for negative) and magnitude.
fn view(b: &BigInt) -> (bool, Vec<u8>) {
    let (sign, limbs) = b.to_u32_digits();
    (sign == Sign::Minus, limbs_to_mag(&limbs))
}

fn make(neg: bool, limbs: &[u32]) -> BigInt {
    BigInt::from_slice(if neg { Sign::Minus } else { Sign::Plus }, limbs)
}

/// `±m` normalized: zero is never negative, magnitudes have no leading zeros.
fn signed(neg: bool, m: Vec<u8>) -> (bool, Vec<u8>) {
    let m = trim(m);
    (neg && !m.is_empty(), m)
}

/// `a + b` over signed magnitudes, with the specification's `add_mag`, `sub_mag` and `cmp_mag`.
fn spec_add(a: &(bool, Vec<u8>), b: &(bool, Vec<u8>)) -> (bool, Vec<u8>) {
    if a.0 == b.0 {
        signed(a.0, exec_add_mag(&a.1, &b.1, 0))
    } else if exec_cmp_mag(&a.1, &b.1) >= 0 {
        signed(a.0, exec_sub_mag(&a.1, &b.1, 0).0)
    } else {
        signed(b.0, exec_sub_mag(&b.1, &a.1, 0).0)
    }
}

fn neg_of(a: &(bool, Vec<u8>)) -> (bool, Vec<u8>) {
    signed(!a.0, a.1.clone())
}

/// One 32-bit limb, biased toward the patterns that select special cases of long division
/// (all ones, only the top bit, zero, one).
fn limb() -> impl Strategy<Value = u32> {
    prop_oneof![
        4 => any::<u32>(),
        1 => Just(u32::MAX),
        1 => Just(0x8000_0000),
        1 => Just(0),
        1 => Just(1),
    ]
}

/// A signed value of 1 to `max` limbs.
fn value(max: usize) -> impl Strategy<Value = BigInt> {
    (any::<bool>(), prop::collection::vec(limb(), 1..=max)).prop_map(|(n, l)| make(n, &l))
}

/// The limbs of the operands checked against the specification: up to 12 (about 115 digits).
const ORACLE_LIMBS: usize = 12;

proptest! {
    #![proptest_config(ProptestConfig::with_cases(128))]

    #[test]
    fn ring_operations_match_the_specification(a in value(ORACLE_LIMBS), b in value(ORACLE_LIMBS)) {
        let (va, vb) = (view(&a), view(&b));
        prop_assert_eq!(view(&big_add(&a, &b)), spec_add(&va, &vb));
        prop_assert_eq!(view(&big_sub(&a, &b)), spec_add(&va, &neg_of(&vb)));
        prop_assert_eq!(view(&big_mul(&a, &b)), signed(va.0 != vb.0, exec_mul_mag(&va.1, &vb.1)));
        let c = exec_cmp_mag(&va.1, &vb.1);
        let want = match (va.0, vb.0) {
            (false, true) => Ordering::Greater,
            (true, false) => Ordering::Less,
            (false, false) => c.cmp(&0),
            (true, true) => 0.cmp(&c),
        };
        prop_assert_eq!(big_cmp(&a, &b), want);
        prop_assert_eq!(view(&big_clone(&a)), va);
    }

    /// Truncating division: the quotient's sign is the product of the signs and the remainder
    /// has the dividend's sign (`spec_tdiv`). Dividends near a multiple of the divisor reach the
    /// correction steps of long division.
    #[test]
    fn division_matches_the_specification(
        b in value(ORACLE_LIMBS / 2),
        q in value(ORACLE_LIMBS / 2),
        delta in -2i64..=2,
        free in value(ORACLE_LIMBS),
        near in any::<bool>(),
    ) {
        let a = if near { big_add(&big_mul(&b, &q), &BigInt::from(delta)) } else { free };
        let (va, vb) = (view(&a), view(&b));
        prop_assume!(!vb.1.is_empty());
        let (sq, sr) = exec_divmod_mag(&va.1, &vb.1);
        let (q, r) = big_tdiv_rem(&a, &b);
        prop_assert_eq!(view(&q), signed(va.0 != vb.0, sq));
        prop_assert_eq!(view(&r), signed(va.0, sr));
    }

    #[test]
    fn sizes_match_the_limbs(neg in any::<bool>(), limbs in prop::collection::vec(limb(), 1..=40)) {
        let a = make(neg, &limbs);
        let top = limbs.iter().rposition(|&l| l != 0);
        let bits = top.map_or(0, |i| 32 * i as u64 + u64::from(32 - limbs[i].leading_zeros()));
        prop_assert_eq!(big_bits(&a), bits);
        let digits = limbs_to_mag(&limbs).len();
        if digits > 0 {
            prop_assert_eq!(big_decimal_digits(&big_abs(&a)), digits as u64);
        }
    }

    #[test]
    fn isqrt_matches_the_specification(limbs in prop::collection::vec(limb(), 1..=ORACLE_LIMBS)) {
        let a = make(false, &limbs);
        let r = big_isqrt(&a);
        let (vr, va) = (view(&r).1, view(&a).1);
        let r1 = exec_add_mag(&vr, &[1], 0);
        prop_assert!(exec_cmp_mag(&exec_mul_mag(&vr, &vr), &va) <= 0);
        prop_assert!(exec_cmp_mag(&exec_mul_mag(&r1, &r1), &va) > 0);
    }

    /// Operands too long for the specification's arithmetic: division is checked by
    /// `a = q·b + r` with `|r| < |b|` and `r` of the dividend's sign, and the square root by
    /// `r² <= a < (r+1)²`.
    #[test]
    fn long_division_and_isqrt_identities(a in value(64), b in value(40)) {
        prop_assume!(!big_is_zero(&b));
        let (q, r) = big_tdiv_rem(&a, &b);
        prop_assert_eq!(big_add(&big_mul(&q, &b), &r), a.clone());
        prop_assert_eq!(big_cmp(&big_abs(&r), &big_abs(&b)), Ordering::Less);
        prop_assert!(big_is_zero(&r) || big_is_negative(&r) == big_is_negative(&a));
        let m = big_abs(&a);
        let s = big_isqrt(&m);
        let s1 = big_add(&s, &BigInt::from(1));
        prop_assert!(big_cmp(&big_mul(&s, &s), &m) != Ordering::Greater);
        prop_assert_eq!(big_cmp(&big_mul(&s1, &s1), &m), Ordering::Greater);
    }
}

/// `to_i64` at the edges of the `i64` range, built from limbs.
#[test]
fn to_i64_at_the_edges() {
    let cases: [(bool, &[u32], Option<i64>); 6] = [
        (false, &[u32::MAX, 0x7FFF_FFFF], Some(i64::MAX)),
        (false, &[0, 0x8000_0000], None),
        (true, &[0, 0x8000_0000], Some(i64::MIN)),
        (true, &[1, 0x8000_0000], None),
        (false, &[0, 0, 1], None),
        (true, &[0], Some(0)),
    ];
    for (neg, limbs, want) in cases {
        assert_eq!(big_to_i64(&make(neg, limbs)), want, "{neg} {limbs:?}");
    }
    assert_eq!(limbs_to_mag(&[0, 1]), vec![6, 9, 2, 7, 6, 9, 4, 9, 2, 4]);
}
