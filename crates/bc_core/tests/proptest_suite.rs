// SPDX-License-Identifier: MIT

//! Property-based tests (`proptest`) for `bc_core`.
//!
//! Arithmetic results are checked against an exact reference: each operand is the rational
//! `coeff / 10^scale`, the reference computes the exact result with `BigInt`, and then truncates
//! it toward zero to the POSIX result scale (`docs/COMPATIBILITY.md` §1.4). The suite also checks
//! base-conversion round trips and that the parser and evaluator never panic.

#![cfg(not(miri))]

use bc_core::verified_kernels::BC_SCALE_MAX;
use bc_core::{BCNum, Evaluator, Lexer, Parser, RuntimeError, STDIN_SOURCE};
use num_bigint::BigInt;
use num_traits::{Signed, Zero};
use proptest::prelude::*;

fn pow10(n: usize) -> BigInt {
    BigInt::from(10).pow(n as u32)
}

/// Truncates the rational `num / den` toward zero to `scale` decimal places, as a `BCNum`.
/// `BigInt` division truncates toward zero, which is the POSIX rounding rule.
fn truncate(num: BigInt, den: BigInt, scale: usize) -> BCNum {
    BCNum::new(num * pow10(scale) / den, scale)
}

/// Compares numeric value and scale (the coefficient representation must match exactly).
fn same(actual: &BCNum, expected: &BCNum) -> bool {
    actual.scale == expected.scale && actual.coeff == expected.coeff
}

fn arb_bcnum() -> impl Strategy<Value = BCNum> {
    (
        prop_oneof![
            -1_000i128..=1_000i128,
            -1_000_000_000_000_000_000_000_000i128..=1_000_000_000_000_000_000_000_000i128,
        ],
        0usize..=30usize,
    )
        .prop_map(|(c, scale)| BCNum::new(BigInt::from(c), scale))
}

fn arb_nonzero_bcnum() -> impl Strategy<Value = BCNum> {
    arb_bcnum().prop_filter("non-zero", |n| !n.coeff.is_zero())
}

fn arb_global_scale() -> impl Strategy<Value = usize> {
    0usize..=40usize
}

/// Programs mixing every statement kind with bounded loops, recursion, arrays, registers, and
/// runtime errors.
fn arb_bounded_bc_program() -> impl Strategy<Value = String> {
    (
        0usize..=8usize,
        -1_000i64..=1_000i64,
        -1_000i64..=1_000i64,
        -100i64..=100i64,
        -4i32..=4i32,
        prop::sample::select(vec!["+", "-", "*", "/", "%", "^"]),
        prop::sample::select(vec!["==", "!=", "<=", ">=", "<", ">"]),
        0u32..=12u32,
        2usize..=20usize,
    )
        .prop_map(
            |(scale, a, b, c, exp, arith_op, rel_op, depth, obase)| {
                format!(
                    "scale = {scale}\n\
                     x = ({a}) {arith_op} ({b}); y = ({c}) ^ ({exp}); z = sqrt({a})\n\
                     if (({a}) {rel_op} ({b})) x\n\
                     define f(n) {{\nauto t[]\nt[n] = n\nif (n <= 0) return (t[n])\nreturn (n + f(n - 1))\n}}\n\
                     f({depth})\n\
                     for (i = 0; i < {depth}; i++) {{ q[i] = i * x; if (i == 5) break }}\n\
                     obase = {obase}; x + y + z; q[{depth} % 6]; obase = 10\n\
                     ({a}) / ({b} - {b})\n"
                )
            },
        )
}

proptest! {
    #![proptest_config(ProptestConfig {
        cases: 256,
        fork: false,
        .. ProptestConfig::default()
    })]

    #[test]
    fn prop_add_sub_exact(a in arb_bcnum(), b in arb_bcnum()) {
        let s = a.scale.max(b.scale);
        let (ca, cb) = (&a.coeff * pow10(s - a.scale), &b.coeff * pow10(s - b.scale));
        prop_assert!(same(&a.add(&b), &BCNum::new(&ca + &cb, s)));
        prop_assert!(same(&a.sub(&b), &BCNum::new(&ca - &cb, s)));
        prop_assert!(same(&a.add(&b), &b.add(&a)));
    }

    #[test]
    fn prop_mul_truncates_to_posix_scale(a in arb_bcnum(), b in arb_bcnum(), g in arb_global_scale()) {
        let r = (a.scale + b.scale).min(g.max(a.scale).max(b.scale));
        let expected = truncate(&a.coeff * &b.coeff, pow10(a.scale + b.scale), r);
        prop_assert!(same(&a.mul(&b, g), &expected));
        prop_assert!(same(&a.mul(&b, g), &b.mul(&a, g)));
    }

    #[test]
    fn prop_div_truncates_to_scale(a in arb_bcnum(), b in arb_nonzero_bcnum(), g in arb_global_scale()) {
        // a / b = (ca / 10^sa) / (cb / 10^sb) = (ca * 10^sb) / (cb * 10^sa)
        let expected = truncate(&a.coeff * pow10(b.scale), &b.coeff * pow10(a.scale), g);
        prop_assert!(same(&a.try_div(&b, g).unwrap(), &expected));
        prop_assert_eq!(a.try_div(&BCNum::zero(), g), Err(RuntimeError::DivideByZero));
    }

    #[test]
    fn prop_mod_matches_posix_definition(a in arb_bcnum(), b in arb_nonzero_bcnum(), g in arb_global_scale()) {
        let r = a.try_mod_op(&b, g).unwrap();
        prop_assert_eq!(r.scale, (g + b.scale).max(a.scale));
        // POSIX: a % b = a - (a / b) * b, with a / b computed at `scale` and the product exact.
        let q = truncate(&a.coeff * pow10(b.scale), &b.coeff * pow10(a.scale), g);
        let exact = a.sub(&BCNum::new(&q.coeff * &b.coeff, g + b.scale));
        prop_assert!(same(&r, &exact));
        // The remainder is smaller than |b| * 10^-scale and has the sign of a (or is zero).
        let s = r.scale;
        let bound = b.coeff.abs() * pow10(s - b.scale);
        prop_assert!(r.coeff.abs() * pow10(g) < bound);
        prop_assert!(r.coeff.is_zero() || r.coeff.is_negative() == a.coeff.is_negative());
        prop_assert_eq!(a.try_mod_op(&BCNum::zero(), g), Err(RuntimeError::ModuloByZero));
    }

    #[test]
    fn prop_sqrt_is_floor_at_posix_scale(a in arb_bcnum(), g in arb_global_scale()) {
        if a.coeff.is_negative() {
            prop_assert_eq!(a.try_sqrt(g), Err(RuntimeError::NegativeSqrt));
            return Ok(());
        }
        let z = a.try_sqrt(g).unwrap();
        let r = g.max(a.scale);
        prop_assert_eq!(z.scale, r);
        // z = floor(sqrt(a) * 10^r): z^2 <= a * 10^(2r) < (z + 1)^2
        let target = &a.coeff * pow10(2 * r - a.scale);
        prop_assert!(&z.coeff * &z.coeff <= target);
        prop_assert!(target < (&z.coeff + 1) * (&z.coeff + 1));
    }

    #[test]
    fn prop_pow_truncates_exact_power(a in arb_bcnum(), e in -6i64..=12i64, g in arb_global_scale()) {
        let exp = BCNum::new(BigInt::from(e), 0);
        let n = e.unsigned_abs() as usize;
        let exact_num = a.coeff.pow(n as u32);
        let exact_scale = a.scale * n;
        let result = a.try_pow(&exp, g);
        if e >= 0 {
            let r = exact_scale.min(g.max(a.scale));
            prop_assert!(same(&result.unwrap(), &truncate(exact_num, pow10(exact_scale), r)));
        } else if a.coeff.is_zero() {
            prop_assert_eq!(result, Err(RuntimeError::NegativePowerOfZero));
        } else {
            prop_assert!(same(&result.unwrap(), &truncate(pow10(exact_scale), exact_num, g)));
        }
    }

    #[test]
    fn prop_scale_limits_are_enforced(a in arb_bcnum(), b in arb_nonzero_bcnum()) {
        // The `%` result scale is max(scale + scale(b), scale(a)); it may not exceed BC_SCALE_MAX.
        let b_fraction = BCNum::new(b.coeff.clone() * 10, b.scale + 1);
        prop_assert_eq!(
            a.try_mod_op(&b_fraction, BC_SCALE_MAX),
            Err(RuntimeError::ScaleTooLarge)
        );
        let huge_exp = BCNum::new(BigInt::from(BC_SCALE_MAX) + 1, 0);
        let fractional = BCNum::new(a.coeff.clone() + 1, a.scale.max(1));
        prop_assert_eq!(
            fractional.try_pow(&huge_exp, 0),
            Err(RuntimeError::ScaleTooLarge)
        );
        let too_big_exp = BCNum::new(BigInt::from(i64::MAX) + 1, 0);
        prop_assert_eq!(a.try_pow(&too_big_exp, 0), Err(RuntimeError::ExponentTooLarge));
    }

    #[test]
    fn prop_obase_ibase_integer_roundtrip(
        val in -1_000_000_000_000_000_000_000_000_000i128..=1_000_000_000_000_000_000_000_000_000i128,
        base in 2usize..=16usize
    ) {
        let n = BCNum::new(BigInt::from(val), 0);
        let formatted = n.format_obase(base);
        let (negative, digits) = match formatted.strip_prefix('-') {
            Some(rest) => (true, rest),
            None => (false, formatted.as_str()),
        };
        let parsed = BCNum::from_string(digits, base);
        let parsed = if negative { BCNum::new(-parsed.coeff, parsed.scale) } else { parsed };
        prop_assert!(same(&parsed, &n));
    }

    #[test]
    fn prop_fraction_output_in_base_is_a_truncation(
        coeff in 0i64..=1_000_000i64,
        scale in 1usize..=6usize,
        base in 2usize..=16usize
    ) {
        // POSIX: the output has the smallest number k of base digits with base^k >= 10^scale,
        // and its value f = digits / base^k satisfies x - base^-k < f <= x (truncation).
        let x = BCNum::new(BigInt::from(coeff), scale);
        let printed = x.format_obase(base);
        let (int_digits, frac_digits) = printed.split_once('.').unwrap_or((&printed, ""));
        let k = frac_digits.len();
        let base_k = BigInt::from(base).pow(k as u32);
        prop_assert!(base_k >= pow10(scale));
        prop_assert!(k == 0 || BigInt::from(base).pow(k as u32 - 1) < pow10(scale));
        let digits = format!("0{int_digits}{frac_digits}");
        let num = BigInt::parse_bytes(digits.as_bytes(), base as u32).unwrap();
        let f_scaled = &num * pow10(scale);
        let x_scaled = &x.coeff * &base_k;
        prop_assert!(f_scaled <= x_scaled);
        prop_assert!(x_scaled - f_scaled < pow10(scale));
    }

    #[test]
    fn prop_parser_never_panics_on_arbitrary_ascii(s in "[\\x20-\\x7E\\n]{0,256}") {
        if let Ok(mut parser) = Parser::try_new(Lexer::new(&s)) {
            let _ = parser.try_parse_program();
        }
    }

    #[test]
    fn prop_evaluator_never_panics_on_bounded_programs(prog in arb_bounded_bc_program()) {
        let mut ev = Evaluator::new(false, Box::new(String::new()), Box::new(String::new()));
        let summary = ev.run_source(&prog, STDIN_SOURCE);
        // The last line always divides by zero; everything before it is valid.
        prop_assert!(summary.errors >= 1);
        prop_assert!(!summary.quit);
    }
}
