// SPDX-License-Identifier: MIT

//! `bc_spec_oracle`: the executable specification (`bc_spec`) as a command with the interface of
//! `bc_clone`, used as the oracle of the differential tests.

use bc_spec::top::{ExecInput, ExecOptions, NOT_MODELED, exec_run};

/// Stack for the compiled specification, whose functions recurse once per digit, token and
/// syntax-tree level.
const ORACLE_STACK_BYTES: usize = 1 << 30;

fn not_modeled(what: &str) -> ! {
    eprintln!("bc_spec_oracle: not modeled: {what}");
    std::process::exit(i32::from(NOT_MODELED));
}

/// Parses the command line like `bc_clone` (XBD 12.2: grouped flags, `--`, `-` as an operand).
fn parse_args(args: &[String]) -> (ExecOptions, Vec<String>) {
    let max_depth = std::env::var("BC_SPEC_MAX_DEPTH")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(100_000);
    let mut opts = ExecOptions {
        reject_extensions: false,
        warn_extensions: false,
        max_depth,
    };
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
            Ok(text) => inputs.push(ExecInput {
                name: name.into_bytes(),
                text,
            }),
            Err(_) => not_modeled("unreadable file"),
        }
    }
    let mut stdin = Vec::new();
    if std::io::Read::read_to_end(&mut std::io::stdin(), &mut stdin).is_err() {
        not_modeled("unreadable standard input");
    }
    inputs.push(ExecInput {
        name: b"(standard_in)".to_vec(),
        text: stdin,
    });

    let outcome = exec_run(&opts, &inputs);
    if outcome.not_modeled {
        not_modeled("out of fuel");
    }
    use std::io::Write;
    let _ = std::io::stdout().write_all(&outcome.stdout);
    let _ = std::io::stderr().write_all(&outcome.stderr);
    std::process::exit(i32::from(outcome.status));
}

fn main() {
    let worker = std::thread::Builder::new()
        .stack_size(ORACLE_STACK_BYTES)
        .spawn(oracle_main);
    match worker.map(std::thread::JoinHandle::join) {
        Ok(Ok(())) => {}
        _ => not_modeled("oracle thread failed"),
    }
}
