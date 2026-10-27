// SPDX-License-Identifier: MIT

//! Executable formal specification of `bc_clone` (the reference interpreter).
//!
//! The specification is a Verus `spec fn` from the program inputs (options, then each file
//! operand and standard input as bytes) to the observable outcome (stdout bytes, stderr bytes,
//! exit status). `exec_spec_verified!` compiles each `spec fn` into an `exec_*` function and
//! proves that the two are equal; this binary runs the compiled function as the oracle of the
//! differential tests (`scripts/build_spec_oracle.sh`, `crates/bc_cli/tests/spec_differential.rs`).
//!
//! **Authority.** POSIX.1-2024 `bc` and the implementation-defined choices in
//! `docs/COMPATIBILITY.md` are what this specification encodes. Where it disagrees with
//! `bc_core`, decide which side follows those documents and fix that side.
//!
//! **Layers.** Numbers mean values of the L0 model in `spec_num.rs` (`SpecBCNum` over `int`).
//! The executable layer (L1) stores them as decimal digit sequences, because `exec_spec` cannot
//! compile `int`; each L1 operation carries a lemma that it computes the L0 operation.
//!
//! **Writing rules** (forced by `exec_spec_verified!`):
//! - recurse on `drop_first`, not on an index `i + 1`;
//! - no `*` on machine integers (the generated code cannot carry `nonlinear_arith` hints);
//!   multiply digit sequences by repeated addition;
//! - no recursive types: the syntax tree is an arena (`Seq<Node>` with `usize` children);
//! - no `Map` fields: environments are association lists;
//! - no typed `let`, no `&` expressions.
//!
//! Functions that are compiled with `exec_spec_unverified!` because their equivalence proof
//! does not go through are listed here: (none yet).
//!
//! **Not modeled** (the oracle exits with `NOT_MODELED`): `-l`, the interactive REPL and SIGINT,
//! unreadable files, memory exhaustion.

use vstd::prelude::*;

#[path = "../../bc_core/src/spec_num.rs"]
pub mod spec_num;
pub mod top;

use top::{ExecInput, ExecOptions, NOT_MODELED, exec_run};

/// Stack for the compiled specification, whose functions recurse once per digit, token and
/// syntax-tree level.
const ORACLE_STACK_BYTES: usize = 1 << 30;

fn not_modeled(what: &str) -> ! {
    eprintln!("bc_spec_oracle: not modeled: {what}");
    std::process::exit(i32::from(NOT_MODELED));
}

/// Parses the command line like `bc_clone` (XBD 12.2: grouped flags, `--`, `-` as an operand).
fn parse_args(args: &[String]) -> (ExecOptions, Vec<String>) {
    let mut opts = ExecOptions { reject_extensions: false, warn_extensions: false };
    let mut files = Vec::new();
    let mut operands_only = false;
    for arg in args {
        if operands_only || arg == "-" || !arg.starts_with('-') {
            files.push(arg.clone());
        } else if arg == "--" {
            operands_only = true;
        } else {
            for flag in arg[1..].chars() {
                match flag {
                    's' => opts.reject_extensions = true,
                    'w' => opts.warn_extensions = true,
                    'l' => not_modeled("-l"),
                    _ => not_modeled("invalid option"),
                }
            }
        }
    }
    (opts, files)
}

fn oracle_main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let (opts, files) = parse_args(&args);
    let mut inputs = Vec::new();
    for name in files {
        match std::fs::read(&name) {
            Ok(text) => inputs.push(ExecInput { name: name.into_bytes(), text }),
            Err(_) => not_modeled("unreadable file"),
        }
    }
    let mut stdin = Vec::new();
    if std::io::Read::read_to_end(&mut std::io::stdin(), &mut stdin).is_err() {
        not_modeled("unreadable standard input");
    }
    inputs.push(ExecInput { name: b"(standard_in)".to_vec(), text: stdin });

    let outcome = exec_run(&opts, &inputs);
    use std::io::Write;
    let _ = std::io::stdout().write_all(&outcome.stdout);
    let _ = std::io::stderr().write_all(&outcome.stderr);
    std::process::exit(i32::from(outcome.status));
}

fn main() {
    let worker = std::thread::Builder::new().stack_size(ORACLE_STACK_BYTES).spawn(oracle_main);
    match worker.map(std::thread::JoinHandle::join) {
        Ok(Ok(())) => {}
        _ => not_modeled("oracle thread failed"),
    }
}
