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
use alloc::string::String;
use alloc::vec::Vec;
use bc_core::verified_kernels::{
    M5STAMP_MAX_STACK_PERCENT, REPL_ACTION_APPEND_CHAR, REPL_ACTION_BACKSPACE, REPL_ACTION_CTRL_C,
    REPL_ACTION_EVAL_LINE, verified_cli_initial_scale, verified_m5stamp_stack_within_budget,
    verified_zephyr_repl_action,
};
use bc_core::{BcWriter, Evaluator, STDIN_SOURCE, UnitAccumulator};
use bc_qemu_riscv32::SelfTest;
use bc_qemu_riscv32::stack_workloads::Workload;
use core::fmt::Write;

/// Longest input line the serial REPL accepts (see `bc_zephyr::REPL_MAX_LINE`).
pub const REPL_MAX_LINE: usize = 1024;

/// Nesting limit (`docs/COMPATIBILITY.md` §2). At 128 levels the self-tests use about 34 KB of
/// the 185 KB stack and 89 KB of the 128 KiB heap on the board (the stack budget is
/// [`M5STAMP_MAX_STACK_PERCENT`]); on QEMU, with the same optimization settings
/// (`scripts/measure_m5stamp_stack.sh`), no heap is left at 160. Running out of heap is not
/// recoverable here, so the heap decides this limit (`AGENTS.md`, "Nesting limits").
pub const M5STAMP_MAX_DEPTH: usize = 128;

// coverage: miri(test_heap_high_water); why: string
/// The largest heap use and the heap size in the statistics of esp-alloc (its `HeapStats`,
/// printed with the feature `internal-heap-stats`): its lines `Max usage: N` and `Size: N`.
pub fn heap_high_water(stats: &str) -> Option<(usize, usize)> {
    let field = |name: &str| {
        stats
            .lines()
            .find_map(|line| line.trim().strip_prefix(name))
            .and_then(|value| value.trim().parse::<usize>().ok())
    };
    Some((field("Max usage:")?, field("Size:")?))
}

// coverage: miri(test_self_tests_pass, test_self_tests_report_failures); why: fmt, dyn
/// Runs `cases`, the nesting-limit tests and `workloads` at `depth`, then checks the stack
/// against the budget: `stack` is the stack region (bottom, top), and `high_water` returns the
/// bytes of it used. Then reports the largest heap use from the allocator's statistics, which
/// `heap_stats` returns as text (no budget: running out of heap ends in the panic handler).
/// Writes the report to `out` and returns whether every test passed. The last line before the
/// closing rule is what `scripts/flash_and_test_m5stamp_c3.sh` waits for.
pub fn run_self_tests<W: Write>(
    out: &mut W,
    cases: &[SelfTest],
    workloads: &[Workload],
    depth: usize,
    stack: (usize, usize),
    high_water: impl FnOnce() -> usize,
    heap_stats: impl FnOnce() -> String,
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
    match heap_high_water(&heap_stats()) {
        Some((used, size)) => {
            let _ = writeln!(
                out,
                "[ESP32-C3] Heap high-water mark: {} of {} bytes.",
                used, size
            );
        }
        None => {
            let _ = writeln!(out, "[ESP32-C3] Heap high-water mark: not reported.");
        }
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

/// At most this many bytes are discarded before the REPL starts, so the discarding ends even if
/// input keeps arriving.
pub const DISCARD_MAX: usize = 4096;

/// The discarding ends once no byte has arrived for this many microseconds. The port takes the
/// host's next packet only after the previous one has been read, a millisecond or more later.
pub const DISCARD_QUIET_US: u64 = 100_000;

// coverage: miri(test_discard_pending_input); why: hw
/// Discards the input that arrived before the REPL starts, until none has arrived for
/// [`DISCARD_QUIET_US`] by the clock `now_us`, and returns how many bytes it read. `read_byte`
/// returns a byte received, or `None` when none is waiting. The board's USB port is enumerated
/// again at every reset, and the host's terminal echoes what the board prints until a program
/// puts it in raw mode; the first prompt would otherwise take that echo as input.
pub fn discard_pending_input(
    mut read_byte: impl FnMut() -> Option<u8>,
    mut now_us: impl FnMut() -> u64,
) -> usize {
    let mut count = 0;
    let mut last = now_us();
    while count < DISCARD_MAX {
        if read_byte().is_some() {
            count += 1;
            last = now_us();
        } else if now_us().saturating_sub(last) >= DISCARD_QUIET_US {
            break;
        }
    }
    count
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
    /// A REPL with the math library and its initial `scale` of 20 (as with `bc -l`), the nesting
    /// limit [`M5STAMP_MAX_DEPTH`], and `out` and `err` as the evaluator's output and
    /// diagnostics.
    pub fn new(out: Box<dyn BcWriter>, err: Box<dyn BcWriter>) -> Self {
        let mut evaluator = Evaluator::new(true, out, err);
        evaluator.set_scale(verified_cli_initial_scale(true));
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

    /// The statistics of esp-alloc 0.8 with `internal-heap-stats`, as its `Display` prints them.
    const STATS: &str = "HEAP INFO\nSize: 131072\nCurrent usage: 1024\nMax usage: 88000\n\
                         Total freed: 5\nTotal allocated: 6\nMemory Layout: \n\
                         Internal | Size: 131072 | Used: 1024\n";

    #[test]
    fn test_heap_high_water() {
        assert_eq!(heap_high_water(STATS), Some((88000, 131072)));
        // Without `internal-heap-stats` there is no peak.
        assert_eq!(
            heap_high_water("HEAP INFO\nSize: 131072\nCurrent usage: 1024\n"),
            None
        );
        assert_eq!(heap_high_water("Max usage: x\nSize: 1\n"), None);
        assert_eq!(heap_high_water(""), None);
    }

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
            || String::from(STATS),
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
             [ESP32-C3] Heap high-water mark: 88000 of 131072 bytes.\n\
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
            || 61,
            || String::from(STATS),
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
            || 0,
            String::new,
        ));
        assert!(out.contains("[FAIL]\n    Expected: \"3\"\n    Actual  : \"2\"\n"));
        assert!(!out.contains("of the stack\n"));
        assert!(out.contains("[ESP32-C3] Heap high-water mark: not reported.\n"));
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
            || 0,
            || String::from(STATS),
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
    fn test_repl_starts_at_the_scale_of_the_math_library() {
        let (_, out) = session(b"scale\n4*a(1)\n");
        assert_eq!(out, "20\n3.14159265358979323844\n");
    }

    /// A clock that advances `step` microseconds at each reading.
    fn clock(step: u64) -> impl FnMut() -> u64 {
        let mut t = 0;
        move || {
            t += step;
            t
        }
    }

    #[test]
    fn test_discard_pending_input() {
        // One byte at once, then a packet of 7 that arrives later, within the quiet period.
        let mut calls = 0;
        let mut late = b"PASS]\r\n".to_vec();
        let read = || {
            calls += 1;
            if calls == 1 {
                Some(b'[')
            } else if calls > 30 && !late.is_empty() {
                Some(late.remove(0))
            } else {
                None
            }
        };
        assert_eq!(discard_pending_input(read, clock(1_000)), 8);
        assert!(late.is_empty());

        // Nothing waiting: it reads until the quiet period has passed, then ends.
        let mut reads = 0;
        let n = discard_pending_input(
            || {
                reads += 1;
                None
            },
            clock(1_000),
        );
        assert_eq!(n, 0);
        assert_eq!(reads as u64, DISCARD_QUIET_US / 1_000);

        // Input that never stops is cut off.
        assert_eq!(discard_pending_input(|| Some(b'x'), clock(1)), DISCARD_MAX);
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
