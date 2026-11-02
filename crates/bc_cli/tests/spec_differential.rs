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
//! - `prop_parser_output_corresponds_to_*` check, in-process and without the oracle, what the
//!   parser's theorem states (`parse_unit_ref`, `driver::r_parsed`) through the public `Parser`
//!   API, which is not itself proved: for every unit, the syntax tree (or error) and extension
//!   uses correspond to the compiled specification's `parse_unit`.
//!
//! Inputs are kept small and shallow: the compiled specification copies its state at every
//! step, so its time grows quadratically with the nesting depth. Cases where
//! either side exceeds the time limit, or that the specification does not model, are skipped.
//! Set `PROPTEST_CASES` for long runs.

#![cfg(not(miri))]

mod common;

use common::generators::{PRELUDE, expr, program, statement, variable};
use common::{TIMED_OUT, check_against_gnu, run_command_raw};
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
    let (spec_code, spec_out, spec_err) = run_command_raw(&oracle, flags, &envs, input);
    if spec_code == TIMED_OUT || spec_code == NOT_MODELED {
        return false;
    }
    let (code, out, err) = run_command_raw(env!("CARGO_BIN_EXE_bc_clone"), flags, &[], input);
    if code == TIMED_OUT {
        return false;
    }
    // Compared as bytes: a string's bytes are printed unchanged, UTF-8 or not.
    let shown = String::from_utf8_lossy(input);
    let text = |b: &[u8]| String::from_utf8_lossy(b).into_owned();
    assert!(
        out == spec_out,
        "Stdout mismatch!\nProgram: {shown:?}\nFlags: {flags:?}\nbc_clone: {out:?} ({:?})\nspec: {spec_out:?} ({:?})",
        text(&out),
        text(&spec_out)
    );
    assert!(
        err == spec_err,
        "Stderr mismatch!\nProgram: {shown:?}\nFlags: {flags:?}\nbc_clone: {:?}\nspec: {:?}",
        text(&err),
        text(&spec_err)
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
        // Strings whose bytes are not UTF-8, which are printed unchanged.
        1 => prop::sample::select(vec![
            &b"\"a\xffb\"\n"[..], b"\"\xed\xa0\x80\"\n", b"\"\xe2\x82\"\n", b"\"\xc0\x80\x00\"\n",
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

/// Checks, on generated inputs, the relation `driver::r_parsed` under which the verified
/// `Evaluator::run_parsed` refines the specification's `run_unit`: for each
/// unit of the specification, the production parser's statements (or error) and extension uses
/// correspond to the specification's `parse_unit`, as `refine::r_code` relates them. Runs the compiled specification in-process, so it needs no oracle binary.
mod parser_relation {
    use bc_core::error::BcError;
    use bc_core::parser::{
        Arg, AssignOp, BinOp, ExtensionPolicy, Lexer, Node, Param, Parser, Register, RelOp,
    };
    use bc_spec::lexer::{exec_split_units, exec_tokenize};
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

    fn r_params(ps: &[Param], qs: &[ExecParam]) -> bool {
        ps.len() == qs.len()
            && ps
                .iter()
                .zip(qs)
                .all(|(p, q)| q.name == p.name.as_bytes() && q.is_array == p.is_array)
    }

    /// `refine::r_arg`.
    fn r_arg(a: &Arg, s: &ExecArg) -> bool {
        match a {
            Arg::Expr(e) => !s.is_array && s.expr == *e,
            Arg::Array(name) => s.is_array && s.name == name.as_bytes(),
        }
    }

    /// `refine::r_node`.
    fn r_node(p: &Node, s: &ExecNode) -> bool {
        match (p, s) {
            (Node::Number(t), ExecNode::Number(u)) => u == t.as_bytes(),
            (Node::Var(x), ExecNode::Var(y)) => y == x.as_bytes(),
            (Node::Array(x, i), ExecNode::Array(y, j)) => y == x.as_bytes() && i == j,
            (Node::Reg(r), ExecNode::Reg(c)) => *c == reg_code(*r),
            (Node::Neg(a), ExecNode::Neg(j))
            | (Node::Length(a), ExecNode::Length(j))
            | (Node::Sqrt(a), ExecNode::Sqrt(j))
            | (Node::ScaleOf(a), ExecNode::ScaleOf(j))
            | (Node::Paren(a), ExecNode::Paren(j))
            | (Node::ExprStmt(a), ExecNode::ExprStmt(j)) => a == j,
            (Node::Binary(op, l, r), ExecNode::Binary(c, a, b)) => {
                *c == bin_code(*op) && l == a && r == b
            }
            (Node::Rel(op, l, r), ExecNode::Rel(c, a, b)) => {
                *c == rel_code(*op) && l == a && r == b
            }
            (Node::Update(inc, prefix, t), ExecNode::Update(i2, p2, j)) => {
                inc == i2 && prefix == p2 && t == j
            }
            (Node::Assign(op, t, v), ExecNode::Assign(c, a, b)) => {
                *c == assign_code(*op) && t == a && v == b
            }
            (Node::Call(name, args), ExecNode::Call(m, sargs)) => {
                m == name.as_bytes()
                    && args.len() == sargs.len()
                    && args.iter().zip(sargs).all(|(a, s)| r_arg(a, s))
            }
            (Node::Block(l), ExecNode::Block(m)) => l == m,
            (Node::Str(t), ExecNode::Str(u)) => u == t,
            (Node::Break, ExecNode::Break) => true,
            (Node::Return(v), ExecNode::Return(hv, j)) => match v {
                Some(e) => *hv && e == j,
                None => !*hv,
            },
            (Node::If(a, b), ExecNode::If(c, d)) | (Node::While(a, b), ExecNode::While(c, d)) => {
                a == c && b == d
            }
            (Node::For(i, c, p, b), ExecNode::For(a, d, e, f)) => {
                i == a && c == d && p == e && b == f
            }
            (Node::Define(name, ps, autos, body), ExecNode::Define(m, qs, rs, ns)) => {
                m == name.as_bytes() && r_params(ps, qs) && r_params(autos, rs) && body == ns
            }
            _ => false,
        }
    }

    /// `refine::r_nodes`.
    fn r_nodes(ps: &[Node], ss: &[ExecNode]) -> bool {
        ps.len() == ss.len() && ps.iter().zip(ss).all(|(p, s)| r_node(p, s))
    }

    /// Parses every unit of `input` with both parsers and checks `r_parsed`, as
    /// `Evaluator::run_unit` and the specification's `run_unit` parse it under `policy`.
    pub fn check(input: &[u8], policy: ExtensionPolicy, max_depth: usize) {
        let units = exec_split_units(input);
        for unit in units {
            let text = String::from_utf8_lossy(&unit.text);
            let cfg = ExecPCfg {
                record_extensions: policy != ExtensionPolicy::Allow,
                max_depth: max_depth as u64,
            };
            let p = exec_parse_unit(&exec_tokenize(&unit.text), &cfg);
            if p.err.out_of_fuel {
                continue;
            }
            let mut ext = Vec::new();
            let mut nodes = Vec::new();
            let parsed = Parser::try_new(Lexer::new(&unit.text)).and_then(|mut parser| {
                parser.set_extension_policy(policy);
                parser.set_max_depth(max_depth);
                let stmts = parser.try_parse_program();
                ext = parser.take_extension_uses();
                nodes = parser.take_code().nodes;
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
                    p.ok && r_nodes(&nodes, &p.st.nodes) && stmts == p.list,
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
fn check_parser_relation(
    input: Vec<u8>,
    policy: bc_core::parser::ExtensionPolicy,
    max_depth: usize,
) {
    std::thread::Builder::new()
        .stack_size(256 << 20)
        .spawn(move || parser_relation::check(&input, policy, max_depth))
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
        check_parser_relation(prog.into_bytes(), policy, 1000);
    }

    #[test]
    fn prop_parser_output_corresponds_to_spec_on_bytes(input in byte_input()) {
        check_parser_relation(input, bc_core::parser::ExtensionPolicy::Allow, 1000);
    }

    #[test]
    fn prop_parser_output_corresponds_to_spec_on_gnu_programs(prog in program()) {
        check_parser_relation(prog.into_bytes(), bc_core::parser::ExtensionPolicy::Allow, 1000);
    }
}

/// Expressions and statements nested around a small `max_depth`, so that the nesting limit is
/// reached by every construct: the parser's heights (`Parser::check_height`) must match the
/// specification's exactly at the boundary.
fn nested_unit() -> impl Strategy<Value = String> {
    let atom = prop_oneof![
        Just("a".to_string()),
        Just("1".to_string()),
        Just("a[1]".to_string()),
        Just("scale".to_string()),
    ];
    let expr = atom.prop_recursive(14, 64, 2, |inner| {
        prop_oneof![
            inner.clone().prop_map(|e| format!("-{e}")),
            inner.clone().prop_map(|e| format!("({e})")),
            inner.clone().prop_map(|e| format!("a[{e}]")),
            inner.clone().prop_map(|e| format!("a = {e}")),
            inner.clone().prop_map(|e| format!("length({e})")),
            Just("++a".to_string()),
            Just("a--".to_string()),
            (inner.clone(), inner.clone()).prop_map(|(l, r)| format!("{l} + {r}")),
            (inner.clone(), inner.clone()).prop_map(|(l, r)| format!("{l} * {r}")),
            (inner.clone(), inner.clone()).prop_map(|(l, r)| format!("{l} ^ {r}")),
            (inner.clone(), inner).prop_map(|(l, r)| format!("{l} < {r}")),
        ]
    });
    let stmt = (expr.clone(), expr.clone(), expr.clone()).prop_flat_map(|(e, l, r)| {
        prop_oneof![
            Just(e.clone()),
            Just(format!("-{e}")),
            Just(format!("if ({l} < {r}) a")),
            Just(format!("while ({l} == -{r}) break")),
            Just(format!("for (a = 0; {l} > {r}; a++) a")),
        ]
    });
    let stmt = stmt.prop_recursive(4, 16, 2, |inner| {
        prop_oneof![
            inner.clone().prop_map(|s| format!("{{{s}}}")),
            inner.clone().prop_map(|s| format!("if (a) {s}")),
            inner.clone().prop_map(|s| format!("while (a < 1) {s}")),
            (inner.clone(), inner).prop_map(|(a, b)| format!("{{{a}; {b}}}")),
        ]
    });
    stmt.prop_map(|s| format!("{s}\n"))
}

proptest! {
    #![proptest_config(ProptestConfig {
        cases: 300,
        fork: false,
        failure_persistence: None,
        .. ProptestConfig::default()
    })]

    #[test]
    fn prop_parser_nesting_limit_corresponds_to_spec(unit in nested_unit(), max_depth in 2..14usize) {
        check_parser_relation(unit.into_bytes(), bc_core::parser::ExtensionPolicy::Allow, max_depth);
    }
}

/// Unary minus chains at every small `max_depth`, in the positions where their height decides
/// the limit (an enclosing operator, assignment, subscript or condition). Random nesting rarely
/// produces these exact boundaries.
#[test]
fn parser_nesting_limit_of_unary_minus_corresponds_to_spec() {
    let shapes = [
        "{}a + 1",
        "1 + {}a",
        "a = {}a",
        "{}(a + 1)",
        "if ({}a < 1) a",
        "if (1 < {}a) a",
        "a[{}a]",
        "{}a < 1",
        "({}a) * 2 + 3",
    ];
    for max_depth in 1..10 {
        for k in 0..12 {
            for shape in shapes {
                let unit = shape.replace("{}", &"-".repeat(k)) + "\n";
                check_parser_relation(
                    unit.into_bytes(),
                    bc_core::parser::ExtensionPolicy::Allow,
                    max_depth,
                );
            }
        }
    }
}
