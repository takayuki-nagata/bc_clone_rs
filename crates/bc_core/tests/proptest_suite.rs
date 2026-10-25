// SPDX-License-Identifier: MIT

//! Memory-bounded Property-Based Testing (`proptest`) suite for `bc_core`.
//!
//! Verifies algebraic identities of `BCNum`, base conversion roundtrips across bases 2..=16,
//! and total-function (panic-free) resilience of `Parser::try_parse_program` and
//! `Evaluator::try_execute`.

#![cfg(not(miri))]

use bc_core::{BCNum, Evaluator, Lexer, Parser};
use num_bigint::BigInt;
use proptest::prelude::*;

fn arb_bcnum() -> impl Strategy<Value = BCNum> {
    (
        -1_000_000_000_000_000_000i128..=1_000_000_000_000_000_000i128,
        0usize..=10usize,
    )
        .prop_map(|(c, scale)| BCNum::new(BigInt::from(c), scale))
}

fn arb_nonzero_bcnum() -> impl Strategy<Value = BCNum> {
    (
        prop_oneof![
            -1_000_000_000_000i128..=-1i128,
            1i128..=1_000_000_000_000i128
        ],
        0usize..=8usize,
    )
        .prop_map(|(c, scale)| BCNum::new(BigInt::from(c), scale))
}

fn arb_bounded_bc_program() -> impl Strategy<Value = String> {
    (
        0usize..=8usize,
        -10_000i64..=10_000i64,
        -10_000i64..=10_000i64,
        -100i64..=100i64,
        -4i32..=4i32,
        prop::sample::select(vec!["+", "-", "*", "/", "%"]),
        prop::sample::select(vec!["==", "!=", "<=", ">=", "<", ">"]),
    )
        .prop_map(|(scale, a, b, c, exp, arith_op, rel_op)| {
            format!(
                "scale = {scale}; x = ({a}) {arith_op} ({b}); ({a}) {rel_op} ({b}); y = ({c}) ^ ({exp}); z = sqrt({a}); x + y + z\n"
            )
        })
}

proptest! {
    #![proptest_config(ProptestConfig {
        cases: 64,
        fork: false,
        .. ProptestConfig::default()
    })]

    #[test]
    fn prop_add_commutative_and_sub_inverse(a in arb_bcnum(), b in arb_bcnum()) {
        let sum_ab = a.add(&b);
        let sum_ba = b.add(&a);
        prop_assert_eq!(&sum_ab, &sum_ba);
        prop_assert_eq!(sum_ab.scale, core::cmp::max(a.scale, b.scale));

        // (a + b) - b preserves value of a scaled to max(a.scale, b.scale)
        let recovered = sum_ab.sub(&b);
        let expected_a = a.add(&BCNum::new(BigInt::from(0), b.scale));
        prop_assert_eq!(recovered, expected_a);
    }

    #[test]
    fn prop_mul_commutative_and_posix_scale(
        a in arb_bcnum(),
        b in arb_bcnum(),
        global_scale in 0usize..=15usize
    ) {
        let prod_ab = a.mul(&b, global_scale);
        let prod_ba = b.mul(&b, global_scale);
        let prod_ba_comm = b.mul(&a, global_scale);
        prop_assert_eq!(&prod_ab, &prod_ba_comm);

        let expected_scale = core::cmp::min(
            a.scale + b.scale,
            core::cmp::max(global_scale, core::cmp::max(a.scale, b.scale)),
        );
        prop_assert_eq!(prod_ab.scale, expected_scale);
        prop_assert!(prod_ba.coeff >= BigInt::from(0));
    }

    #[test]
    fn prop_div_and_mod_posix_identity(
        a in arb_bcnum(),
        b in arb_nonzero_bcnum(),
        global_scale in 0usize..=10usize
    ) {
        let q = a.try_div(&b, global_scale).unwrap();
        let r = a.try_mod_op(&b, global_scale).unwrap();
        prop_assert_eq!(q.scale, global_scale);
        prop_assert_eq!(
            r.scale,
            core::cmp::max(a.scale, b.scale + global_scale)
        );

        // Exact POSIX remainder identity: a == q * b (untruncated) + r
        let exact_qb = BCNum::new(&q.coeff * &b.coeff, q.scale + b.scale);
        let reconstructed = exact_qb.add(&r);
        let expected_a = a.add(&BCNum::new(BigInt::from(0), reconstructed.scale));
        prop_assert_eq!(reconstructed, expected_a);
    }

    #[test]
    fn prop_ibase_obase_integer_roundtrip(
        val in 0u128..=1_000_000_000_000_000_000_000_000_000u128,
        base in 2usize..=16usize
    ) {
        let n = BCNum::new(BigInt::from(val), 0);
        let formatted = n.format_obase(base);
        let parsed = BCNum::from_string(&formatted, base);
        prop_assert_eq!(parsed, n);
    }

    #[test]
    fn prop_parser_never_panics_on_arbitrary_ascii(s in "[\\x20-\\x7E\\n]{0,64}") {
        if let Ok(mut parser) = Parser::try_new(Lexer::new(&s)) {
            let _ = parser.try_parse_program();
        }
    }

    #[test]
    fn prop_evaluator_never_panics_on_bounded_programs(prog in arb_bounded_bc_program()) {
        let mut parser = Parser::try_new(Lexer::new(&prog)).unwrap();
        let stmts = parser.try_parse_program().unwrap();
        let mut ev = Evaluator::new(
            false,
            Box::new(String::new()),
            Box::new(String::new()),
        );
        for stmt in &stmts {
            let _ = ev.try_execute(stmt);
        }
    }
}
