// SPDX-License-Identifier: MIT

//! The parts of the M5Stamp C3 application that decide something: the self-tests' report and
//! verdict, the stack budget, and the serial REPL. They take the hardware as arguments (the
//! terminal, the evaluator's writers, the bytes read and the stack measurement), so the host's
//! unit tests run them under Miri; the binary (`src/bin/main.rs`) only connects them to the USB
//! serial port, the heap and the stack. The self-tests and the nesting workloads are the QEMU
//! runner's (`bc_qemu_riscv32`).

#![cfg_attr(not(test), no_std)]

extern crate alloc;

use alloc::boxed::Box;
use alloc::vec::Vec;
use bc_core::verified_kernels::{
    M5STAMP_MAX_STACK_PERCENT, REPL_ACTION_APPEND_CHAR, REPL_ACTION_BACKSPACE, REPL_ACTION_CTRL_C,
    REPL_ACTION_EVAL_LINE, verified_m5stamp_stack_within_budget, verified_zephyr_repl_action,
};
use bc_core::{BcWriter, Evaluator, STDIN_SOURCE, UnitAccumulator};
use bc_qemu_riscv32::SelfTest;
use bc_qemu_riscv32::stack_workloads::Workload;
use core::fmt::Write;

/// Longest input line the serial REPL accepts (see `bc_zephyr::REPL_MAX_LINE`).
pub const REPL_MAX_LINE: usize = 1024;

/// Nesting limit (`docs/COMPATIBILITY.md` §2). At 128 levels the workloads use about 32 KB of
/// the 185 KB stack on the board (the budget is [`M5STAMP_MAX_STACK_PERCENT`]). The heap is
/// measured on QEMU with the same optimization settings and a 128 KiB heap
/// (`scripts/measure_m5stamp_stack.sh`): 87 KB at 128, and none left at 160. Running out of heap
/// is not recoverable here, so the heap decides this limit (`AGENTS.md`, "Nesting limits").
pub const M5STAMP_MAX_DEPTH: usize = 128;

// coverage: miri(test_self_tests_pass, test_self_tests_report_failures); why: fmt, dyn
/// Runs `cases`, the nesting-limit tests and `workloads` at `depth`, then checks the stack
/// against the budget: `stack` is the stack region (bottom, top), and `high_water` returns the
/// bytes of it used. Writes the
/// report to `out` and returns whether every test passed. The last line before the closing rule
/// is what `scripts/flash_and_test_m5stamp_c3.sh` waits for.
pub fn run_self_tests<W: Write>(
    out: &mut W,
    cases: &[SelfTest],
    workloads: &[Workload],
    depth: usize,
    stack: (usize, usize),
    high_water: impl FnOnce() -> usize,
) -> bool {
    let _ = writeln!(out, "\n=================================================");
    let _ = writeln!(out, "  bc_clone (bc_core) on M5Stamp C3 (ESP32-C3)    ");
    let _ = writeln!(out, "  {}", bc_build_info::VERSION_LINE);
    let _ = writeln!(out, "=================================================");
    let _ = writeln!(out, "[ESP32-C3] Initialized successfully @ 160MHz.");
    let _ = writeln!(out, "[ESP32-C3] 128KB SRAM Heap allocated for bc_core.\n");

    let mut all_passed = bc_qemu_riscv32::run_cases(out, cases, workloads, depth);

    let used = high_water();
    let size = stack.1.saturating_sub(stack.0);
    let _ = writeln!(
        out,
        "[ESP32-C3] Stack high-water mark: {} of {} bytes.",
        used, size
    );
    if !verified_m5stamp_stack_within_budget(used, size) {
        let _ = writeln!(
            out,
            "  [FAIL] over {}% of the stack",
            M5STAMP_MAX_STACK_PERCENT
        );
        all_passed = false;
    }

    let _ = writeln!(out, "-------------------------------------------------");
    if all_passed {
        let _ = writeln!(out, "ALL M5STAMP-C3 BC_CORE TESTS PASSED (100%)!");
    } else {
        let _ = writeln!(out, "SOME M5STAMP-C3 BC_CORE TESTS FAILED!");
    }
    let _ = writeln!(out, "=================================================\n");
    all_passed
}

// coverage: miri(test_repl_banner); why: fmt
/// Writes the REPL's greeting and its first prompt.
pub fn repl_banner<W: Write>(out: &mut W) {
    let _ = writeln!(out, "Entering bc_core Interactive REPL mode...");
    let _ = writeln!(out, "{}", bc_build_info::VERSION_LINE);
    let _ = writeln!(
        out,
        "Type bc expressions (e.g. 2^64, scale=10; 4*a(1), define f(x)...)"
    );
    let _ = write!(out, "bc> ");
}

/// The serial REPL: an evaluator that keeps its variables and functions, the line being typed,
/// and the lines of an input unit not yet complete.
pub struct Repl {
    evaluator: Evaluator,
    line: Vec<u8>,
    acc: UnitAccumulator,
}

impl Repl {
    // coverage: miri(test_repl_ignores_failed_and_empty_reads); why: dyn
    /// A REPL with the math library, the nesting limit [`M5STAMP_MAX_DEPTH`], and `out` and
    /// `err` as the evaluator's output and diagnostics.
    pub fn new(out: Box<dyn BcWriter>, err: Box<dyn BcWriter>) -> Self {
        let mut evaluator = Evaluator::new(true, out, err);
        evaluator.max_depth = M5STAMP_MAX_DEPTH;
        evaluator.max_eval_depth = M5STAMP_MAX_DEPTH;
        Repl {
            evaluator,
            line: Vec::new(),
            acc: UnitAccumulator::new(),
        }
    }

    // coverage: miri(test_repl_ignores_failed_and_empty_reads); why: io
    /// Handles the result of one read of the serial port into `buf`: each byte read, none after
    /// an error. The echo and the prompts go to `term`.
    pub fn poll<E, W: Write>(&mut self, read: Result<usize, E>, buf: &[u8], term: &mut W) {
        let count = read.unwrap_or(0);
        for &byte in buf.iter().take(count) {
            self.feed(byte, term);
        }
    }

    // coverage: miri(via poll); why: fmt, dyn
    /// Handles one byte typed at the terminal.
    fn feed<W: Write>(&mut self, byte: u8, term: &mut W) {
        match verified_zephyr_repl_action(byte, self.line.len(), REPL_MAX_LINE) {
            REPL_ACTION_EVAL_LINE => {
                let _ = term.write_str("\r\n");
                self.line.push(b'\n');
                // Lines are grouped into input units exactly as in the CLI. There is no
                // process to exit on bare metal, so `quit` only ends the current unit.
                if let Some((unit, first_line)) = self.acc.push_line(&self.line) {
                    self.evaluator.run_unit(&unit, STDIN_SOURCE, first_line);
                    self.evaluator.clear_quit();
                }
                self.line.clear();
                let _ = term.write_str(if self.acc.is_pending() {
                    "... "
                } else {
                    "bc> "
                });
            }
            REPL_ACTION_BACKSPACE => {
                self.line.pop();
                let _ = term.write_str("\x08 \x08");
            }
            REPL_ACTION_CTRL_C => {
                // Cancels the current line and any pending multi-line unit.
                self.line.clear();
                self.acc.clear();
                let _ = term.write_str("^C\r\nbc> ");
            }
            // Characters beyond REPL_MAX_LINE are ignored so typing cannot exhaust the heap.
            REPL_ACTION_APPEND_CHAR => {
                self.line.push(byte);
                let _ = term.write_char(byte as char);
            }
            // Other control characters, and backspace on an empty line.
            _ => {}
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use bc_qemu_riscv32::stack_workloads::{Expect, WORKLOADS};
    use bc_qemu_riscv32::{SELF_TESTS, SharedBuffer};
    use std::string::String;

    #[test]
    fn test_self_tests_pass() {
        let mut out = String::new();
        let passed = run_self_tests(
            &mut out,
            &SELF_TESTS,
            &WORKLOADS[..2],
            100,
            (1000, 1100),
            || 60,
        );
        assert!(passed, "{out}");
        assert!(out.starts_with("\n=================================================\n"));
        assert!(out.contains(bc_build_info::VERSION_LINE));
        assert!(out.contains("Running: Scale Limit on 32-bit usize"));
        assert!(out.contains("Running: Nesting Limit: Recursion Too Deep"));
        assert!(out.contains("Running: limit, unary minus"));
        assert!(!out.contains("FAIL"));
        assert!(out.ends_with(
            "[ESP32-C3] Stack high-water mark: 60 of 100 bytes.\n\
             -------------------------------------------------\n\
             ALL M5STAMP-C3 BC_CORE TESTS PASSED (100%)!\n\
             =================================================\n\n"
        ));
    }

    #[test]
    fn test_self_tests_report_failures() {
        // Over the stack budget, with every test passing.
        let mut out = String::new();
        assert!(!run_self_tests(
            &mut out,
            &SELF_TESTS[..1],
            &[],
            20,
            (1000, 1100),
            || 61
        ));
        assert!(out.contains("  [FAIL] over 60% of the stack\n"));
        assert!(out.contains("SOME M5STAMP-C3 BC_CORE TESTS FAILED!"));
        assert!(!out.contains("ALL M5STAMP-C3"));

        // A failing case, within the budget.
        let wrong = [SelfTest {
            name: "wrong",
            code: "1 + 1\n",
            math: false,
            scale: 0,
            expected: "3",
        }];
        let mut out = String::new();
        assert!(!run_self_tests(
            &mut out,
            &wrong,
            &[],
            20,
            (1000, 1100),
            || 0
        ));
        assert!(out.contains("[FAIL]\n    Expected: \"3\"\n    Actual  : \"2\"\n"));
        assert!(!out.contains("of the stack\n"));
        assert!(out.contains("SOME M5STAMP-C3 BC_CORE TESTS FAILED!"));

        // A failing workload.
        let mut workload = WORKLOADS[0];
        workload.expect = Expect::Fixed("2");
        let mut out = String::new();
        assert!(!run_self_tests(
            &mut out,
            &[],
            &[workload],
            20,
            (1000, 1100),
            || 0
        ));
        assert!(out.contains("limit, parentheses"));
        assert!(out.contains("SOME M5STAMP-C3 BC_CORE TESTS FAILED!"));
    }

    /// Types `input` one byte per read, as the USB serial port delivers it, and returns what the
    /// terminal and the evaluator wrote.
    fn session(input: &[u8]) -> (String, String) {
        let shown = SharedBuffer::default();
        let mut term = String::new();
        let mut repl = Repl::new(Box::new(shown.clone()), Box::new(shown.clone()));
        for &b in input {
            repl.poll::<(), _>(Ok(1), &[b], &mut term);
        }
        let out = shown.0.borrow().clone();
        (term, out)
    }

    #[test]
    fn test_repl_session() {
        let (term, out) = session(
            b"2^10\r\
              define f(x) {\n  return (x * 2)\n}\nf(21)\n\
              1+\x7f2\n\
              x = 5\n{\nx = 6\x03x\n\
              quit\n7\n\x01\n",
        );
        // DEL erases the `+`, so the line is `12`; Ctrl-C drops the pending block, so `x` is 5.
        assert_eq!(out, "1024\n42\n12\n5\n7\n");
        assert!(term.starts_with("2^10\r\nbc> "));
        // A multi-line definition prompts for its continuation lines.
        assert!(term.contains("define f(x) {\r\n...   return (x * 2)\r\n... }\r\nbc> f(21)"));
        assert!(term.contains("1+\x08 \x082\r\n"));
        assert!(term.contains("{\r\n... x = 6^C\r\nbc> x\r\n"));
        // `quit` ends only its unit.
        assert!(term.contains("quit\r\nbc> 7\r\nbc> "));
        // A control character is neither echoed nor kept.
        assert!(term.ends_with("7\r\nbc> \r\nbc> "));
    }

    #[test]
    fn test_repl_banner() {
        let mut term = String::new();
        repl_banner(&mut term);
        assert_eq!(
            term,
            format!(
                "Entering bc_core Interactive REPL mode...\n{}\n\
                 Type bc expressions (e.g. 2^64, scale=10; 4*a(1), define f(x)...)\nbc> ",
                bc_build_info::VERSION_LINE
            )
        );
    }

    #[test]
    fn test_repl_line_limit() {
        let mut input = vec![b'1'; REPL_MAX_LINE + 5];
        input.push(b'\n');
        let (term, out) = session(&input);
        let ones = "1".repeat(REPL_MAX_LINE);
        assert_eq!(term, format!("{ones}\r\nbc> "));
        // The line is longer than the 70 columns of a number, so the output wraps.
        assert_eq!(out.replace("\\\n", ""), format!("{ones}\n"));
    }

    #[test]
    fn test_repl_ignores_failed_and_empty_reads() {
        let shown = SharedBuffer::default();
        let mut term = String::new();
        let mut repl = Repl::new(Box::new(shown.clone()), Box::new(shown.clone()));
        repl.poll(Err("broken"), b"9", &mut term);
        repl.poll::<(), _>(Ok(0), b"9", &mut term);
        assert_eq!(term, "");
        repl.poll::<(), _>(Ok(2), b"8\n", &mut term);
        assert_eq!(term, "8\r\nbc> ");
        assert_eq!(*shown.0.borrow(), "8\n");
    }
}
