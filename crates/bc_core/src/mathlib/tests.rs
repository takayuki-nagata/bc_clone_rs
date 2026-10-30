// SPDX-License-Identifier: MIT

use super::*;
use alloc::vec::Vec;
use num_traits::Signed;
use proptest::prelude::*;

/// A decimal literal, optionally negative (`BCNum::from_string` takes digits only).
fn num(s: &str) -> BCNum {
    match s.strip_prefix('-') {
        Some(digits) => {
            let v = BCNum::from_string(digits, 10);
            BCNum::new(-v.coeff, v.scale)
        }
        None => BCNum::from_string(s, 10),
    }
}

/// The truncation toward zero of v / 10^k, by integer arithmetic.
fn trunc_div(v: &BigInt, k: usize) -> BigInt {
    v / pow10_within(k)
}

proptest! {
    /// `certified_trunc` never accepts a ball whose values truncate differently, and the
    /// value it returns is their common truncation (checked for every integer in the ball).
    #[test]
    fn certified_trunc_is_sound(mid in -5000i64..5000, rad in 0i64..40, k in 0usize..3) {
        let ball = Ball { mid: BigInt::from(mid), rad: BigInt::from(rad), prec: k };
        let truncs: Vec<BigInt> =
            (mid - rad..=mid + rad).map(|v| trunc_div(&BigInt::from(v), k)).collect();
        let all_same = truncs.iter().all(|t| *t == truncs[0]);
        match certified_trunc(&ball, 0) {
            Some(q) => prop_assert!(all_same && q == truncs[0]),
            // A ball touching a multiple of 10^k is rejected even when the truncations
            // agree, because the true value may be any real in it.
            None => prop_assert!(!all_same || rad > 0 || (mid % 10i64.pow(k as u32) == 0)),
        }
    }

    /// Ball arithmetic contains the exact results: for exact operands a/10^p and b/10^p
    /// with radius 0, the true product, quotient and square root lie in the balls.
    #[test]
    fn ball_operations_contain_exact_results(a in 1i64..10_000_000, b in 1i64..10_000_000) {
        let p = 4;
        let ba = Ball::exact(BigInt::from(a), p);
        let bb = Ball::exact(BigInt::from(b), p);
        let scale = BigInt::from(10_000);
        // a·b / 10^p in ulps is a·b/10^4: check |mid·10^4 − a·b| <= rad·10^4.
        let prod = ba.mul(&bb);
        prop_assert!((&prod.mid * &scale - a * b).abs() <= &prod.rad * &scale);
        // a/b in ulps is a·10^4/b: check |mid·b − a·10^4| <= rad·b.
        let quot = ba.div(&bb).unwrap();
        prop_assert!((&quot.mid * b - BigInt::from(a) * &scale).abs() <= &quot.rad * b);
        // √(a·10^4) in ulps: (mid − rad)² <= a·10^4 <= (mid + rad)².
        let root = ba.sqrt().unwrap();
        let v = BigInt::from(a) * &scale;
        prop_assert!((&root.mid - &root.rad).pow(2) <= v && v <= (&root.mid + &root.rad).pow(2));
    }
}

#[test]
fn constants_contain_their_true_values() {
    // π and ln 2 to 60 digits.
    let pi60 = "3141592653589793238462643383279502884197169399375105820974944";
    let ln2_60 = "0693147180559945309417232121458176568075500134360255254120680";
    for (ball, digits) in [(pi(60), pi60), (ln2(60), ln2_60)] {
        let truth = BigInt::parse_bytes(digits.as_bytes(), 10).unwrap();
        // `truth` is truncated, so the true value is in [truth, truth + 1].
        prop_assert_ok(&ball, &truth);
    }

    fn prop_assert_ok(ball: &Ball, truth: &BigInt) {
        assert!(&ball.mid - &ball.rad <= *truth && *truth < &ball.mid + &ball.rad);
        // About 2 ulps per series term (43 terms for atan(1/5) at 60 digits), times 16.
        assert!(ball.rad < BigInt::from(4000));
    }
}

#[test]
fn exact_results_are_returned_without_series() {
    assert_eq!(bc_sin(&num("0"), 5).unwrap(), exact_result(0, 5));
    assert_eq!(bc_cos(&num("0.000"), 5).unwrap(), exact_result(1, 5));
    assert_eq!(bc_atan(&num("0"), 3).unwrap(), exact_result(0, 3));
    assert_eq!(bc_ln(&num("1.000"), 4).unwrap(), exact_result(0, 4));
    assert_eq!(bc_exp(&num("0"), 2).unwrap(), exact_result(1, 2));
    assert_eq!(
        bc_bessel(&num("0"), &num("0"), 2).unwrap(),
        exact_result(1, 2)
    );
    assert_eq!(
        bc_bessel(&num("3"), &num("0"), 2).unwrap(),
        exact_result(0, 2)
    );
}

#[test]
fn results_are_truncated_toward_zero() {
    // Reference values truncated by hand from 30-digit expansions.
    let cases: [(&str, BCNum); 8] = [
        (".84147098480789650665", bc_sin(&num("1"), 20).unwrap()),
        ("-.84147098480789650665", bc_sin(&num("-1"), 20).unwrap()),
        (".54030230586813971740", bc_cos(&num("1"), 20).unwrap()),
        (".78539816339744830961", bc_atan(&num("1"), 20).unwrap()),
        ("-1.56079666010823138", bc_atan(&num("-100"), 17).unwrap()),
        ("-.69314718055994530941", bc_ln(&num("0.5"), 20).unwrap()),
        ("2.71828182845904523536", bc_exp(&num("1"), 20).unwrap()),
        (
            ".76519768655796655144",
            bc_bessel(&num("0"), &num("1"), 20).unwrap(),
        ),
    ];
    for (expected, actual) in cases {
        assert_eq!(actual.format_obase(10), expected);
    }
}
