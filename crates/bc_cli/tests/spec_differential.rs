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
//! - `prop_parser_output_corresponds_to_*` check, in-process and without the oracle, the
//!   assumption of the refinement theorem of `Evaluator::run_parsed`: for every unit, the
//!   production parser's syntax tree (or error) and extension uses correspond to the compiled
//!   specification's `parse_unit` (`driver::r_parsed`).
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

// ---------------------------------------------------------------------------------------------
// The parser assumption of the refinement theorem
// ---------------------------------------------------------------------------------------------

/// Checks, on generated inputs, the assumption `driver::r_parsed` under which the verified
/// `Evaluator::run_parsed` refines the specification's `run_unit`: for each
/// unit of the specification, the production parser's statements (or error) and extension uses
/// correspond to the specification's `parse_unit`, as `refine::r_stmt` and `r_expr` relate
/// them. Runs the compiled specification in-process, so it needs no oracle binary.
mod parser_relation {
    use bc_core::error::BcError;
    use bc_core::parser::{
        AssignOp, BinOp, Expr, ExprOrArray, ExtensionPolicy, Lexer, Param, Parser, Register, RelOp,
        Stmt,
    };
    use bc_spec::lexer::{exec_split_units, exec_tokenize, exec_utf8_lossy};
    use bc_spec::parser::{ExecArg, ExecNode, ExecPCfg, ExecParam, exec_parse_unit};

    fn bin_code(op: BinOp) -> u8 {
        match op {
            BinOp::Add => 0,
            BinOp::Sub => 1,
            BinOp::Mul => 2,
            BinOp::Div => 3,
            BinOp::Mod => 4,
            BinOp::Pow => 5,
        }
    }

    fn rel_code(op: RelOp) -> u8 {
        match op {
            RelOp::Eq => 0,
            RelOp::Ne => 1,
            RelOp::Lt => 2,
            RelOp::Le => 3,
            RelOp::Gt => 4,
            RelOp::Ge => 5,
        }
    }

    fn assign_code(op: AssignOp) -> u8 {
        match op {
            AssignOp::Assign => 0,
            AssignOp::Compound(b) => bin_code(b) + 1,
        }
    }

    fn reg_code(r: Register) -> u8 {
        match r {
            Register::Scale => 0,
            Register::Ibase => 1,
            Register::Obase => 2,
        }
    }

    fn named(e: &Expr) -> bool {
        matches!(
            e,
            Expr::Variable(_) | Expr::ArrayAccess(..) | Expr::RegisterAccess(_)
        )
    }

    fn r_params(ps: &[Param], qs: &[ExecParam]) -> bool {
        ps.len() == qs.len()
            && ps
                .iter()
                .zip(qs)
                .all(|(p, q)| q.name == p.name.as_bytes() && q.is_array == p.is_array)
    }

    /// `refine::r_arg`.
    fn r_arg(a: &ExprOrArray, nodes: &[ExecNode], s: &ExecArg) -> bool {
        match a {
            ExprOrArray::Expr(e) => !s.is_array && r_expr(e, nodes, s.expr),
            ExprOrArray::ArrayArg(name) => s.is_array && s.name == name.as_bytes(),
        }
    }

    /// `refine::r_expr`.
    fn r_expr(e: &Expr, nodes: &[ExecNode], n: usize) -> bool {
        let Some(node) = nodes.get(n) else {
            return false;
        };
        match (e, node) {
            (Expr::Number(t), ExecNode::Number(u)) => u == t.as_bytes(),
            (Expr::Variable(x), ExecNode::Var(y)) => y == x.as_bytes(),
            (Expr::ArrayAccess(x, i), ExecNode::Array(y, j)) => {
                y == x.as_bytes() && r_expr(i, nodes, *j)
            }
            (Expr::RegisterAccess(r), ExecNode::Reg(c)) => *c == reg_code(*r),
            (Expr::Negate(a), ExecNode::Neg(j)) => r_expr(a, nodes, *j),
            (Expr::BinaryOp(op, l, r), ExecNode::Binary(c, a, b)) => {
                *c == bin_code(*op) && r_expr(l, nodes, *a) && r_expr(r, nodes, *b)
            }
            (Expr::RelationalOp(op, l, r), ExecNode::Rel(c, a, b)) => {
                *c == rel_code(*op) && r_expr(l, nodes, *a) && r_expr(r, nodes, *b)
            }
            (Expr::Update(inc, prefix, t), ExecNode::Update(i2, p2, j)) => {
                named(t) && i2 == inc && p2 == prefix && r_expr(t, nodes, *j)
            }
            (Expr::AssignOp(op, t, v), ExecNode::Assign(c, a, b)) => {
                named(t) && *c == assign_code(*op) && r_expr(t, nodes, *a) && r_expr(v, nodes, *b)
            }
            (Expr::Call(name, args), ExecNode::Call(m, sargs)) => {
                m == name.as_bytes()
                    && args.len() == sargs.len()
                    && args.iter().zip(sargs).all(|(a, s)| r_arg(a, nodes, s))
            }
            (Expr::LengthCall(a), ExecNode::Length(j))
            | (Expr::SqrtCall(a), ExecNode::Sqrt(j))
            | (Expr::ScaleCall(a), ExecNode::ScaleOf(j))
            | (Expr::Paren(a), ExecNode::Paren(j)) => r_expr(a, nodes, *j),
            _ => false,
        }
    }

    /// `refine::r_stmts`.
    fn r_stmts(list: &[Stmt], nodes: &[ExecNode], ns: &[usize]) -> bool {
        list.len() == ns.len() && list.iter().zip(ns).all(|(s, n)| r_stmt(s, nodes, *n))
    }

    /// `refine::r_stmt`.
    fn r_stmt(s: &Stmt, nodes: &[ExecNode], n: usize) -> bool {
        let Some(node) = nodes.get(n) else {
            return false;
        };
        match (s, node) {
            (Stmt::Block(list), ExecNode::Block(ns)) => r_stmts(list, nodes, ns),
            (Stmt::Expr(e), ExecNode::ExprStmt(j)) => r_expr(e, nodes, *j),
            (Stmt::StringLiteral(t), ExecNode::Str(u)) => u == t.as_bytes(),
            (Stmt::Break, ExecNode::Break) => true,
            (Stmt::Return(v), ExecNode::Return(hv, j)) => match v {
                Some(e) => *hv && r_expr(e, nodes, *j),
                None => !*hv,
            },
            (Stmt::If(c, b), ExecNode::If(i, j)) | (Stmt::While(c, b), ExecNode::While(i, j)) => {
                r_expr(c, nodes, *i) && r_stmt(b, nodes, *j)
            }
            (Stmt::For(i, c, p, b), ExecNode::For(a, d, e, f)) => {
                r_expr(i, nodes, *a)
                    && r_expr(c, nodes, *d)
                    && r_expr(p, nodes, *e)
                    && r_stmt(b, nodes, *f)
            }
            (Stmt::FunctionDef(fd), ExecNode::Define(name, ps, autos, body)) => {
                name == fd.name.as_bytes()
                    && r_params(&fd.params, ps)
                    && r_params(&fd.autos, autos)
                    && r_stmts(&fd.body, nodes, body)
            }
            _ => false,
        }
    }

    /// Parses every unit of `input` with both parsers and checks `r_parsed`, as
    /// `Evaluator::run_unit` and the specification's `run_unit` parse it under `policy`.
    pub fn check(input: &[u8], policy: ExtensionPolicy) {
        const MAX_DEPTH: usize = 1000;
        let units = exec_split_units(&exec_utf8_lossy(input));
        for unit in units {
            let text = String::from_utf8(unit.text.clone()).expect("utf8_lossy gives UTF-8");
            let cfg = ExecPCfg {
                record_extensions: policy != ExtensionPolicy::Allow,
                max_depth: MAX_DEPTH as u64,
            };
            let p = exec_parse_unit(&exec_tokenize(&unit.text), &cfg);
            if p.err.out_of_fuel {
                continue;
            }
            let mut ext = Vec::new();
            let parsed = Parser::try_new(Lexer::new(&text)).and_then(|mut parser| {
                parser.set_extension_policy(policy);
                parser.set_max_depth(MAX_DEPTH);
                let stmts = parser.try_parse_program();
                ext = parser.take_extension_uses();
                stmts
            });
            let ext_ok = ext.len() == p.st.ext.len()
                && ext
                    .iter()
                    .zip(&p.st.ext)
                    .all(|((line, desc), e)| e.line == *line as u64 && e.desc == desc.as_bytes());
            assert!(ext_ok, "extension uses differ for {text:?}: {ext:?}");
            match parsed {
                Ok(stmts) => assert!(
                    p.ok && r_stmts(&stmts, &p.st.nodes, &p.list),
                    "syntax trees differ for {text:?}"
                ),
                Err(BcError::Quit) => assert!(!p.ok && p.err.quit, "quit differs for {text:?}"),
                Err(BcError::Syntax { line, message, .. }) => assert!(
                    !p.ok
                        && !p.err.quit
                        && p.err.line == line as u64
                        && p.err.msg == message.as_bytes(),
                    "syntax errors differ for {text:?}: line {line}, {message:?}"
                ),
                Err(e) => panic!("the parser returned {e:?} for {text:?}"),
            }
        }
    }
}

/// Runs `parser_relation::check` on a thread with room for the compiled specification's
/// recursion.
fn check_parser_relation(input: Vec<u8>, policy: bc_core::parser::ExtensionPolicy) {
    std::thread::Builder::new()
        .stack_size(256 << 20)
        .spawn(move || parser_relation::check(&input, policy))
        .expect("spawn")
        .join()
        .expect("the parser relation holds");
}

proptest! {
    #![proptest_config(ProptestConfig {
        cases: 300,
        fork: false,
        failure_persistence: None,
        .. ProptestConfig::default()
    })]

    #[test]
    fn prop_parser_output_corresponds_to_spec(prog in spec_program(), policy in 0..3u8) {
        use bc_core::parser::ExtensionPolicy;
        let policy = [ExtensionPolicy::Allow, ExtensionPolicy::Warn, ExtensionPolicy::Reject][policy as usize];
        check_parser_relation(prog.into_bytes(), policy);
    }

    #[test]
    fn prop_parser_output_corresponds_to_spec_on_bytes(input in byte_input()) {
        check_parser_relation(input, bc_core::parser::ExtensionPolicy::Allow);
    }

    #[test]
    fn prop_parser_output_corresponds_to_spec_on_gnu_programs(prog in program()) {
        check_parser_relation(prog.into_bytes(), bc_core::parser::ExtensionPolicy::Allow);
    }
}
