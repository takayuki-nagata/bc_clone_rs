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
//! A second generator produces deeply nested input (long operator chains, nested parentheses,
//! blocks and `if`s, deep recursion, functions that change `ibase`), within the CLI's nesting
//! limit (`docs/COMPATIBILITY.md` §2), which GNU bc also evaluates.
//! Set `PROPTEST_CASES` to run more cases, e.g. for a long fuzzing session.

#![cfg(not(miri))]

mod common;

use common::check_differential_unless_gnu_times_out;
use common::generators::program;
use proptest::prelude::*;

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

/// Deeply nested programs, at most a few thousand levels deep: well within the nesting limit of
/// debug builds (20 000), and evaluated by GNU bc as well.
fn deep_program() -> impl Strategy<Value = String> {
    let op = || prop::sample::select(vec!["+", "-", "*"]);
    prop_oneof![
        // A long left-associative chain, which the parser builds without recursion.
        prop::collection::vec((op(), 0u32..10), 1..3000).prop_map(|terms| {
            let chain: String = terms.iter().map(|(o, n)| format!("{o}{n}")).collect();
            format!("1{chain}\n")
        }),
        // Nested parentheses around alternating operators.
        (1usize..1500, op()).prop_map(|(depth, o)| {
            format!("{}1{}\n", format!("(2{o}").repeat(depth), ")".repeat(depth))
        }),
        // Nested blocks and `if`s.
        (1usize..800, any::<bool>()).prop_map(|(depth, blocks)| if blocks {
            format!("{}x = 7; x{}\n", "{".repeat(depth), "}".repeat(depth))
        } else {
            format!("{}7\n", "if (1 < 2) ".repeat(depth))
        }),
        // Deep recursion, with a different argument expression at each level.
        (1usize..3000, 1u32..5).prop_map(|(n, k)| format!(
            "define g(n) {{\nif (n == 0) return (0)\nreturn (n % {k} + g(n - 1))\n}}\ng({n})\n"
        )),
        // A function that changes `ibase` before reading its constants (POSIX: constants use
        // the `ibase` of the invocation).
        (2u32..17, 0u32..10).prop_map(|(base, n)| format!(
            "define f() {{\nibase = {base}\nreturn (10 + {n})\n}}\nf()\n10\n"
        )),
    ]
}

proptest! {
    #![proptest_config(ProptestConfig {
        cases: 40,
        fork: false,
        failure_persistence: None,
        .. ProptestConfig::default()
    })]

    #[test]
    fn prop_deep_programs_match_gnu_bc(prog in deep_program()) {
        if !check_differential_unless_gnu_times_out(&prog, &[]) {
            eprintln!("skipped (GNU bc timed out): {:?}", &prog[..prog.len().min(80)]);
        }
    }
}
