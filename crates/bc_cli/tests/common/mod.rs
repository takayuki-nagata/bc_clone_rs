// SPDX-License-Identifier: MIT

//! Helpers shared by the differential tests: run GNU bc and bc_clone on the same input and
//! compare stdout, diagnostics, and exit status (`docs/COMPATIBILITY.md` §3).

#![allow(dead_code)]

pub mod generators;

use std::io::Write;
use std::process::{Command, Stdio};

/// Exit status reported by coreutils `timeout` when the command was killed.
pub const TIMED_OUT: i32 = 124;

/// Seconds after which a command is killed (see [`TIMED_OUT`]).
const TIME_LIMIT_SECS: &str = "20";

/// Runs `cmd_name args...` with `input` on stdin under a time limit and returns
/// `(exit status, stdout, stderr)`.
pub fn run_command(cmd_name: &str, args: &[&str], input: &str) -> (i32, String, String) {
    run_command_bytes(cmd_name, args, &[], input.as_bytes())
}

/// Like [`run_command`], with raw input bytes and extra environment variables. Output that is
/// not UTF-8 is decoded lossily; [`run_command_raw`] returns the bytes.
pub fn run_command_bytes(
    cmd_name: &str,
    args: &[&str],
    envs: &[(&str, &str)],
    input: &[u8],
) -> (i32, String, String) {
    let (exit_code, stdout, stderr) = run_command_raw(cmd_name, args, envs, input);
    (
        exit_code,
        String::from_utf8_lossy(&stdout).into_owned(),
        String::from_utf8_lossy(&stderr).into_owned(),
    )
}

/// Like [`run_command_bytes`], returning stdout and stderr as bytes.
pub fn run_command_raw(
    cmd_name: &str,
    args: &[&str],
    envs: &[(&str, &str)],
    input: &[u8],
) -> (i32, Vec<u8>, Vec<u8>) {
    let mut child = Command::new("timeout")
        .arg(TIME_LIMIT_SECS)
        .arg(cmd_name)
        .args(args)
        .envs(envs.iter().copied())
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("failed to spawn command");

    {
        let stdin = child.stdin.as_mut().expect("failed to get stdin");
        stdin.write_all(input).expect("failed to write to stdin");
    }

    let output = child.wait_with_output().expect("failed to wait for output");
    let exit_code = output.status.code().unwrap_or(-1);
    (exit_code, output.stdout, output.stderr)
}

/// Rewrites GNU bc diagnostics into the format specified in `docs/COMPATIBILITY.md` §3.2:
/// the bytecode address (`, adr=N`) is removed, and only the first syntax diagnostic of each
/// input line is kept, because bc_clone discards the rest of the input unit after a syntax
/// error instead of emulating yacc error recovery.
pub fn normalize_gnu_stderr(stderr: &str) -> String {
    let mut out = String::new();
    let mut last_syntax_prefix: Option<String> = None;
    for line in stderr.lines() {
        if line.starts_with("(standard_in) ") {
            let prefix = line.split(':').next().unwrap_or(line).to_string();
            if last_syntax_prefix.as_deref() == Some(prefix.as_str()) {
                continue;
            }
            last_syntax_prefix = Some(prefix);
        }
        match (line.find(", adr="), line.find("):")) {
            (Some(start), Some(end)) if start < end => {
                out.push_str(&line[..start]);
                out.push_str(&line[end..]);
            }
            _ => out.push_str(line),
        }
        out.push('\n');
    }
    out
}

/// Exit status mandated by `docs/COMPATIBILITY.md` §3.1: 1 if any error was diagnosed,
/// otherwise GNU's status. Warnings do not count as errors.
pub fn expected_exit_code(gnu_code: i32, normalized_stderr: &str) -> i32 {
    let has_error = normalized_stderr
        .lines()
        .any(|line| !line.starts_with("Runtime warning") && !line.contains(": (Warning) "));
    if has_error { 1 } else { gnu_code }
}

/// Runs `program` through GNU bc and bc_clone and requires identical stdout, identical
/// diagnostics (modulo `adr=N`), and the exit status defined by the compatibility spec.
pub fn check_differential(program: &str, flags: &[&str]) {
    assert!(
        check_differential_unless_gnu_times_out(program, flags),
        "GNU bc timed out on {:?}",
        program
    );
}

/// Like [`check_differential`], but returns `false` without comparing when GNU bc exceeds the
/// time limit (GNU's algorithms are slower for some inputs, e.g. large powers of fractions).
pub fn check_differential_unless_gnu_times_out(program: &str, flags: &[&str]) -> bool {
    check_against_gnu(env!("CARGO_BIN_EXE_bc_clone"), &[], program, flags)
}

/// Runs `program` through GNU bc and the bc implementation `bin_path` (with the environment
/// `envs`), comparing as [`check_differential`] does. Returns `false` without comparing when
/// GNU bc exceeds the time limit.
pub fn check_against_gnu(
    bin_path: &str,
    envs: &[(&str, &str)],
    program: &str,
    flags: &[&str],
) -> bool {
    let input = if program.ends_with('\n') {
        program.to_string()
    } else {
        format!("{}\n", program)
    };

    let (bc_code, bc_out, bc_err) = run_command("bc", flags, &input);
    if bc_code == TIMED_OUT {
        return false;
    }
    let expected_err = normalize_gnu_stderr(&bc_err);
    let expected_code = expected_exit_code(bc_code, &expected_err);

    let (clone_code, clone_out, clone_err) =
        run_command_bytes(bin_path, flags, envs, input.as_bytes());

    assert_eq!(
        clone_out, bc_out,
        "Stdout mismatch!\nProgram: {:?}\nExpected:\n{:?}\nGot:\n{:?}",
        program, bc_out, clone_out
    );
    assert_eq!(
        clone_err, expected_err,
        "Stderr mismatch!\nProgram: {:?}\nExpected:\n{:?}\nGot:\n{:?}",
        program, expected_err, clone_err
    );
    assert_eq!(
        clone_code, expected_code,
        "Exit code mismatch!\nProgram: {:?}\nExpected: {}\nGot: {}",
        program, expected_code, clone_code
    );
    true
}
