// SPDX-License-Identifier: MIT

//! Property-based tests (`proptest`) of `bc_core`'s public API: base-conversion round trips, and
//! that the parser and evaluator never panic. The arithmetic and the `-l` functions are tested
//! against exact references in the crate's unit tests (`src/math/proptests.rs`).

#![cfg(not(miri))]

use bc_core::{BCNum, Evaluator, Lexer, Parser, STDIN_SOURCE};
use num_bigint::BigInt;
use proptest::prelude::*;

fn pow10(n: usize) -> BigInt {
    BigInt::from(10).pow(n as u32)
}

/// Compares numeric value and scale (the coefficient representation must match exactly).
fn same(actual: &BCNum, expected: &BCNum) -> bool {
    actual.scale == expected.scale && actual.coeff == expected.coeff
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
        let parsed = BCNum::try_from_string(digits, base).expect("at most BC_SCALE_MAX fraction digits");
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
