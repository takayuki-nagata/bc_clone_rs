// SPDX-License-Identifier: MIT

//! Randomized differential testing against the executable specification (`crates/bc_spec`).
//!
//! The oracle is `bc_spec_oracle`, built by `scripts/build_spec_oracle.sh` from Verus
//! specifications whose arithmetic is proved exact; set `BC_SPEC_ORACLE` to its path. Without
//! it the tests are skipped, unless `BC_SPEC_ORACLE_REQUIRED` is set (as in CI), when they fail.
//!
//! - `prop_matches_spec` generates what `differential_proptest.rs` cannot compare with GNU bc:
//!   `ibase` changes and hexadecimal digits, `sqrt(0)` and `sqrt(1)`, odd powers of negative
//!   numbers, syntax and lexical errors, `while`/`break`, `quit`, extensions under `-w` and
//!   `-s`, and strings long enough to wrap.
//! - `prop_byte_inputs_match_spec` feeds invalid UTF-8, NUL and control characters.
//! - `prop_spec_matches_gnu_bc` checks the specification itself against GNU bc on the inputs
//!   where GNU bc follows POSIX (the generator of `differential_proptest.rs`).
//!
//! Inputs are kept small and shallow: the compiled specification copies its state at every
//! step, so its time grows quadratically with the nesting depth. Cases where
//! either side exceeds the time limit, or that the specification does not model, are skipped.
//! Set `PROPTEST_CASES` for long runs.

#![cfg(not(miri))]

mod common;

use common::generators::{PRELUDE, expr, program, statement, variable};
use common::{TIMED_OUT, check_against_gnu, run_command_bytes};
use proptest::prelude::*;

/// Exit status of the oracle for inputs outside the specification.
const NOT_MODELED: i32 = 125;

/// `Evaluator::max_depth` of the `bc_clone` binary under test (`bc_cli::ENGINE_MAX_DEPTH`).
const MAX_DEPTH: &str = if cfg!(debug_assertions) {
    "20000"
} else {
    "100000"
};

/// The oracle's path, or `None` (with a note, once) when the tests should be skipped.
fn oracle() -> Option<String> {
    static ORACLE: std::sync::OnceLock<Option<String>> = std::sync::OnceLock::new();
    ORACLE
        .get_or_init(|| match std::env::var("BC_SPEC_ORACLE") {
            Ok(path) => Some(path),
            Err(_) => {
                assert!(
                    std::env::var_os("BC_SPEC_ORACLE_REQUIRED").is_none(),
                    "BC_SPEC_ORACLE is not set; build it with scripts/build_spec_oracle.sh"
                );
                eprintln!("skipped: BC_SPEC_ORACLE is not set (scripts/build_spec_oracle.sh)");
                None
            }
        })
        .clone()
}

/// Runs `input` through bc_clone and the specification and requires identical stdout,
/// stderr and exit status. Returns `false` when the case is skipped.
fn check_against_spec(input: &[u8], flags: &[&str]) -> bool {
    let Some(oracle) = oracle() else {
        return false;
    };
    let envs = [("BC_SPEC_MAX_DEPTH", MAX_DEPTH)];
    let (spec_code, spec_out, spec_err) = run_command_bytes(&oracle, flags, &envs, input);
    if spec_code == TIMED_OUT || spec_code == NOT_MODELED {
        return false;
    }
    let (code, out, err) = run_command_bytes(env!("CARGO_BIN_EXE_bc_clone"), flags, &[], input);
    if code == TIMED_OUT {
        return false;
    }
    let shown = String::from_utf8_lossy(input);
    assert_eq!(
        out, spec_out,
        "Stdout mismatch!\nProgram: {shown:?}\nFlags: {flags:?}"
    );
    assert_eq!(
        err, spec_err,
        "Stderr mismatch!\nProgram: {shown:?}\nFlags: {flags:?}"
    );
    assert_eq!(
        code, spec_code,
        "Exit status mismatch!\nProgram: {shown:?}\nFlags: {flags:?}"
    );
    true
}

/// Constants with hexadecimal digits (meaningful once `ibase` is above 10).
fn hex_number() -> impl Strategy<Value = String> {
    ("[0-9A-F]{1,3}", prop::option::of("[0-9A-F]{1,3}")).prop_map(|(i, f)| match f {
        Some(f) => format!("{i}.{f}"),
        None => i,
    })
}

/// Expressions, plus what GNU bc gets wrong or does differently.
fn spec_expr() -> impl Strategy<Value = String> {
    prop_oneof![
        6 => expr(),
        1 => hex_number(),
        1 => prop::sample::select(vec!["sqrt(0)", "sqrt(1)", "sqrt(1.000)", "sqrt(0.0)"])
            .prop_map(str::to_string),
        1 => (expr(), prop::sample::select(vec![1, 3, 5, -1, -3]))
            .prop_map(|(b, e)| format!("(-({b}) ^ {e})")),
        1 => prop::sample::select(vec!["ibase", "obase", "scale"]).prop_map(str::to_string),
        1 => (expr(), expr()).prop_map(|(a, b)| format!("{a} {b}")),
        1 => prop::sample::select(vec!["abc", "x_1", "long_name"]).prop_map(str::to_string),
    ]
}

/// A line that is lexically or syntactically wrong, or uses tokens GNU bc recovers from
/// differently.
fn bad_line() -> impl Strategy<Value = String> {
    prop_oneof![
        prop::collection::vec(
            prop::sample::select(vec![
                "1", "a", "+", "-", "*", "(", ")", "[", "]", "{", "}", "=", ";", ",", "if", "for",
                "while", "define", "auto", "return", "break", "++", "^", "<", "==", "\"s\"",
            ]),
            1..6,
        )
        .prop_map(|v| v.join(" ")),
        prop::sample::select(vec!["@", "#", "&", "!x", "G", "1.2.3", "a = = 1", "x[1"])
            .prop_map(str::to_string),
    ]
}

/// Statements, plus registers, loops, extensions, long strings and errors.
fn spec_statement() -> impl Strategy<Value = String> {
    prop_oneof![
        6 => statement(),
        2 => spec_expr(),
        1 => (2u32..17).prop_map(|b| format!("ibase = {b}")),
        1 => prop::sample::select(vec!["ibase = A", "obase = F", "ibase = 1", "obase = 99999999999"])
            .prop_map(str::to_string),
        1 => (0u32..4, spec_expr()).prop_map(|(n, e)| {
            format!("w = 0; while (w < {n}) {{ w = w + 1; if (w == 2) break; {e} }}")
        }),
        1 => "[a-z ]{60,90}".prop_map(|s| format!("\"{s}\"")),
        1 => (variable(), spec_expr()).prop_map(|(v, e)| format!("{v} < {e}")),
        1 => bad_line(),
    ]
}

/// A function definition that uses extensions (one-line body, `return` without parentheses).
const SPEC_PRELUDE: &str = "define g(n) { auto t; t = n * 3; return t }\n";

fn spec_program() -> impl Strategy<Value = String> {
    (
        prop::collection::vec(prop::collection::vec(spec_statement(), 1..4), 1..6),
        any::<bool>(),
        prop::option::of(0usize..6),
    )
        .prop_map(|(lines, use_g, quit_at)| {
            let mut body: Vec<String> = lines.into_iter().map(|l| l.join("; ")).collect();
            if let Some(i) = quit_at.filter(|&i| i < body.len()) {
                body.insert(i, "quit".to_string());
            }
            let prelude = if use_g { SPEC_PRELUDE } else { "" };
            format!("{PRELUDE}{prelude}{}\n", body.join("\n"))
        })
}

fn flags() -> impl Strategy<Value = Vec<&'static str>> {
    prop::sample::select(vec![vec![], vec!["-w"], vec!["-s"], vec!["-sw"]])
}

/// Nested programs within the specification's practical depth.
fn shallow_deep_program() -> impl Strategy<Value = String> {
    let op = || prop::sample::select(vec!["+", "-", "*"]);
    prop_oneof![
        prop::collection::vec((op(), 0u32..10), 1..300).prop_map(|terms| {
            let chain: String = terms.iter().map(|(o, n)| format!("{o}{n}")).collect();
            format!("1{chain}\n")
        }),
        (1usize..150, op()).prop_map(|(depth, o)| {
            format!("{}1{}\n", format!("(2{o}").repeat(depth), ")".repeat(depth))
        }),
        (1usize..100, 1u32..5).prop_map(|(n, k)| format!(
            "define g(n) {{\nif (n == 0) return (0)\nreturn (n % {k} + g(n - 1))\n}}\ng({n})\n"
        )),
    ]
}

/// Input bytes: text with invalid UTF-8, NUL, control characters and non-ASCII characters.
fn byte_input() -> impl Strategy<Value = Vec<u8>> {
    let chunk = prop_oneof![
        4 => prop::sample::select(vec![
            &b"1+2\n"[..], b"x=3;x\n", b"\"str\"\n", b"\"\xc3\xa9t\xc3\xa9\"\n", b"/* c */ 4\n",
        ])
        .prop_map(<[u8]>::to_vec),
        2 => prop::collection::vec(any::<u8>(), 1..4),
        1 => prop::sample::select(vec![
            &b"\x00"[..], b"\xff", b"\xe2\x82", b"\xed\xa0\x80", b"\xf4\x90\x80\x80", b"\x7f", b"\r\n",
        ])
        .prop_map(<[u8]>::to_vec),
    ];
    prop::collection::vec(chunk, 1..8).prop_map(|v| {
        let mut bytes = v.concat();
        bytes.push(b'\n');
        bytes
    })
}

proptest! {
    #![proptest_config(ProptestConfig {
        cases: 300,
        fork: false,
        failure_persistence: None,
        .. ProptestConfig::default()
    })]

    #[test]
    fn prop_matches_spec(prog in spec_program(), flags in flags()) {
        check_against_spec(prog.as_bytes(), &flags);
    }

    #[test]
    fn prop_byte_inputs_match_spec(input in byte_input()) {
        check_against_spec(&input, &[]);
    }
}

proptest! {
    #![proptest_config(ProptestConfig {
        cases: 40,
        fork: false,
        failure_persistence: None,
        .. ProptestConfig::default()
    })]

    #[test]
    fn prop_nested_programs_match_spec(prog in shallow_deep_program()) {
        check_against_spec(prog.as_bytes(), &[]);
    }

    #[test]
    fn prop_spec_matches_gnu_bc(prog in program()) {
        if let Some(oracle) = oracle() {
            check_against_gnu(&oracle, &[("BC_SPEC_MAX_DEPTH", MAX_DEPTH)], &prog, &[]);
        }
    }
}
