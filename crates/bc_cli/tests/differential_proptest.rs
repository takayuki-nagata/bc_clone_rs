// SPDX-License-Identifier: MIT

//! Randomized differential testing against GNU bc.
//!
//! Generates programs from the bc grammar (arithmetic at random scales, registers, arrays,
//! control flow, functions with `auto` and recursion, and runtime errors), runs them through
//! GNU bc and bc_clone, and requires identical stdout, diagnostics, and exit status
//! (`docs/COMPATIBILITY.md` §3).
//!
//! Inputs where GNU bc knowingly deviates from POSIX (§5) are not generated: `sqrt` of exactly 0
//! or 1, odd powers that can produce GNU's negative zero, syntax errors (GNU's yacc recovery),
//! `ibase` above 16, and the `-l` library (checked by an oracle test instead).
//! Set `PROPTEST_CASES` to run more cases, e.g. for a long fuzzing session.

#![cfg(not(miri))]

mod common;

use common::check_differential_unless_gnu_times_out;
use proptest::prelude::*;

fn number() -> impl Strategy<Value = String> {
    (0u32..2000, prop::option::of("[0-9]{1,4}")).prop_map(|(int, frac)| match frac {
        Some(f) if int == 0 => format!(".{f}"),
        Some(f) => format!("{int}.{f}"),
        None => int.to_string(),
    })
}

fn sqrt_argument() -> impl Strategy<Value = String> {
    number().prop_filter("GNU special-cases sqrt(0) and sqrt(1)", |n| {
        let v: f64 = n.parse().unwrap_or(0.0);
        v != 0.0 && v != 1.0
    })
}

fn variable() -> impl Strategy<Value = String> {
    prop::sample::select(vec!["a", "b", "c", "x", "y"]).prop_map(str::to_string)
}

fn expr() -> impl Strategy<Value = String> {
    let leaf = prop_oneof![
        4 => number(),
        3 => variable(),
        1 => (variable(), 0u8..4).prop_map(|(v, i)| format!("{v}[{i}]")),
        1 => Just("scale".to_string()),
        1 => sqrt_argument().prop_map(|n| format!("sqrt({n})")),
    ];
    leaf.prop_recursive(4, 24, 2, |inner| {
        prop_oneof![
            4 => (inner.clone(), prop::sample::select(vec!["+", "-", "*", "/", "%"]), inner.clone())
                .prop_map(|(l, op, r)| format!("({l} {op} {r})")),
            // Odd powers only of non-negative literals: GNU bc turns a negative result that
            // truncates to zero into a "-0" that compares below 0 (§5).
            1 => (inner.clone(), prop::sample::select(vec![-2, 0, 2, 4]))
                .prop_map(|(b, e)| format!("({b} ^ {e})")),
            1 => (number(), -3i32..6).prop_map(|(b, e)| format!("({b} ^ {e})")),
            // Parenthesized so that `-` never merges with a following `--` into a syntax error:
            // after a syntax error GNU bc's yacc recovery may also swallow the next line (§5).
            1 => inner.clone().prop_map(|e| format!("-({e})")),
            1 => inner.clone().prop_map(|e| format!("length({e})")),
            1 => inner.clone().prop_map(|e| format!("scale({e})")),
            1 => (variable(), inner.clone()).prop_map(|(v, e)| format!("({v} = {e})")),
            1 => (variable(), prop::sample::select(vec!["++", "--"]), any::<bool>())
                .prop_map(|(v, op, pre)| if pre { format!("{op}{v}") } else { format!("{v}{op}") }),
            1 => (inner.clone(), inner).prop_map(|(a, b)| format!("f({a}, {b})")),
        ]
    })
}

fn condition() -> impl Strategy<Value = String> {
    (
        expr(),
        prop::sample::select(vec!["==", "!=", "<", "<=", ">", ">="]),
        expr(),
    )
        .prop_map(|(l, op, r)| format!("{l} {op} {r}"))
}

fn statement() -> impl Strategy<Value = String> {
    let simple = prop_oneof![
        4 => expr(),
        3 => (variable(), prop::sample::select(vec!["=", "+=", "-=", "*=", "/=", "%="]), expr())
            .prop_map(|(v, op, e)| format!("{v} {op} {e}")),
        1 => (variable(), 0u8..4, expr()).prop_map(|(v, i, e)| format!("{v}[{i}] = {e}")),
        2 => (0u32..15).prop_map(|s| format!("scale = {s}")),
        1 => (2u32..40).prop_map(|b| format!("obase = {b}")),
        1 => Just("obase = 10".to_string()),
        1 => "[a-z ]{0,8}".prop_map(|s| format!("\"{s}\"")),
    ];
    simple.prop_recursive(2, 8, 3, |inner| {
        prop_oneof![
            (condition(), inner.clone()).prop_map(|(c, s)| format!("if ({c}) {s}")),
            // A random counter name keeps nested loops from resetting each other's counter.
            (0u32..4, any::<u16>(), inner.clone()).prop_map(|(n, id, s)| {
                format!("for (i{id} = 0; i{id} < {n}; i{id}++) {{ {s} }}")
            }),
            prop::collection::vec(inner, 1..3).prop_map(|v| format!("{{ {} }}", v.join("; "))),
        ]
    })
}

/// A function used by `expr()`: `auto` locals, a parameter shadowing a global, and bounded
/// recursion.
const PRELUDE: &str = "define f(a, n) {\n\
                       auto x\n\
                       x = a * 2\n\
                       if (n > 0) if (n < 4) return (x + f(a, n - 1))\n\
                       return (x - n)\n\
                       }\n";

fn program() -> impl Strategy<Value = String> {
    prop::collection::vec(prop::collection::vec(statement(), 1..4), 1..6).prop_map(|lines| {
        let body: Vec<String> = lines.into_iter().map(|l| l.join("; ")).collect();
        format!("{PRELUDE}{}\n", body.join("\n"))
    })
}

proptest! {
    #![proptest_config(ProptestConfig {
        cases: 300,
        fork: false,
        // The generator is tuned over time, so persisted seeds would not reproduce old failures.
        failure_persistence: None,
        .. ProptestConfig::default()
    })]

    #[test]
    fn prop_matches_gnu_bc(prog in program()) {
        if !check_differential_unless_gnu_times_out(&prog, &[]) {
            eprintln!("skipped (GNU bc timed out): {prog:?}");
        }
    }
}
