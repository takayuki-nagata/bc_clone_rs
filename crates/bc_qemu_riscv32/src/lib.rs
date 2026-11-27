// SPDX-License-Identifier: MIT

//! The parts of the bare-metal RISC-V 32 runner that decide something: the self-tests and their
//! verdict, the measurement loop for the M5Stamp C3, the serial writer's line endings and the
//! peak-counting allocator. They take the hardware as arguments, so the host's unit tests run them
//! under Miri; the binary (`main.rs`) only connects them to the UART, the heap and QEMU's test
//! device. The M5Stamp C3 application (`examples/m5stamp_c3`) runs the same self-tests and
//! workloads through this library, built without the feature `bin` (the binary's dependencies).

#![cfg_attr(not(test), no_std)]

extern crate alloc;

pub mod stack_workloads;

use alloc::boxed::Box;
use alloc::rc::Rc;
use alloc::string::String;
use bc_core::{BcWriter, Evaluator, STDIN_SOURCE};
use core::alloc::{GlobalAlloc, Layout};
use core::cell::RefCell;
use core::fmt::Write;
use core::sync::atomic::{AtomicUsize, Ordering::Relaxed};
use stack_workloads::{Workload, blocks, parens, recursion};

/// Nesting limit (`docs/COMPATIBILITY.md` §2). One level takes at most about 800 bytes of stack
/// on RV32 (measured), and the stack is the rest of the 16 MiB RAM after the 2 MiB heap.
pub const QEMU_MAX_DEPTH: usize = 1000;

/// A reference-counted, interior-mutable String buffer implementing BcWriter.
#[derive(Clone, Default)]
pub struct SharedBuffer(pub Rc<RefCell<String>>);

// SAFETY: the runner has one thread.
unsafe impl Send for SharedBuffer {}

impl Write for SharedBuffer {
    // coverage: miri(test_shared_buffer); why: trait
    fn write_str(&mut self, s: &str) -> core::fmt::Result {
        self.0.borrow_mut().push_str(s);
        Ok(())
    }
}

impl BcWriter for SharedBuffer {
    // coverage: miri(test_shared_buffer); why: trait
    fn flush(&mut self) -> core::fmt::Result {
        Ok(())
    }
}

// coverage: miri(test_eval_bc_at_depth); why: dyn
/// Evaluates a bc program under the nesting limit `depth` and returns its output and diagnostics.
pub fn eval_bc_at_depth(
    code: &str,
    math_enabled: bool,
    default_scale: usize,
    depth: usize,
) -> String {
    let out_buf = SharedBuffer::default();

    let mut evaluator = Evaluator::new(
        math_enabled,
        Box::new(out_buf.clone()),
        Box::new(out_buf.clone()),
    );
    evaluator.set_scale(default_scale);
    evaluator.max_depth = depth;
    evaluator.max_eval_depth = depth;

    evaluator.run_source(code.as_bytes(), STDIN_SOURCE);

    out_buf.0.borrow().clone()
}

/// A self-test: the output of `code` must be `expected`, both trimmed.
pub struct SelfTest {
    pub name: &'static str,
    pub code: &'static str,
    pub math: bool,
    pub scale: usize,
    pub expected: &'static str,
}

// coverage: miri(test_self_tests_report_failures); why: string
const fn case(
    name: &'static str,
    code: &'static str,
    math: bool,
    scale: usize,
    expected: &'static str,
) -> SelfTest {
    SelfTest {
        name,
        code,
        math,
        scale,
        expected,
    }
}

/// The self-tests that do not depend on the nesting limit.
pub const SELF_TESTS: [SelfTest; 13] = [
    case(
        "Basic Arithmetic & Precedence",
        "1 + 2 * 3 - 4 / 2\n",
        false,
        0,
        "5",
    ),
    case("Scale Division", "scale = 4; 5 / 3\n", false, 0, "1.6666"),
    case(
        "BigInt Power (2^100)",
        "2^100\n",
        false,
        0,
        "1267650600228229401496703205376",
    ),
    // The exact scale of a power is computed in u64: on 32-bit targets an exponent beyond
    // usize::MAX must not make a scale-0 power "scale too large".
    case(
        "Power with an exponent beyond u32",
        "1^5000000000; (-1)^5000000001; 0^5000000000\n",
        false,
        0,
        "1\n-1\n0",
    ),
    case(
        "Recursive Factorial f(20)",
        "define f(n) { if (n <= 1) return (1); return (n * f(n - 1)); }; f(20)\n",
        false,
        0,
        "2432902008176640000",
    ),
    case(
        "Transcendental Pi: 4 * a(1)",
        "4 * a(1)\n",
        true,
        20,
        "3.14159265358979323844",
    ),
    case(
        "Transcendental Exp: e(1)",
        "e(1)\n",
        true,
        15,
        "2.718281828459045",
    ),
    case(
        "Transcendental Log: l(2.718281828459045)",
        "l(2.718281828459045)\n",
        true,
        15,
        ".999999999999999",
    ),
    case(
        "Transcendental Sine & Cosine",
        "s(0) + c(0)\n",
        true,
        15,
        "1.000000000000000",
    ),
    case(
        "Base Conversion (Hex to Binary)",
        "ibase = 16; obase = 2; FF\n",
        false,
        0,
        "11111111",
    ),
    case(
        "Arrays and Dynamic Auto Scoping",
        "a[0] = 10; a[1] = 20\ndefine sum(x[]) {\n  auto s\n  s = x[0] + x[1]\n  return (s)\n}\nsum(a[])\n",
        false,
        0,
        "30",
    ),
    case(
        "Error Recovery (Div by Zero)",
        "1 / 0\n",
        false,
        0,
        "Runtime error (func=(main)): Divide by zero",
    ),
    // 2^32 + 1 does not fit a 32-bit usize; it must clamp, not wrap to 1.
    case(
        "Scale Limit on 32-bit usize",
        "scale = 4294967297; scale\n",
        false,
        0,
        "Runtime warning (func=(main)): scale too large, set to 1000000000\n1000000000",
    ),
];

// coverage: miri(via run_cases); why: fmt, string
/// Runs one test, writes its line, and returns whether it passed.
fn check<W: Write>(
    out: &mut W,
    name: &str,
    code: &str,
    math: bool,
    scale: usize,
    expected: &str,
    depth: usize,
) -> bool {
    let _ = write!(out, "  Running: {:<35} ... ", name);
    let actual = eval_bc_at_depth(code, math, scale, depth);
    if actual.trim() == expected.trim() {
        let _ = writeln!(out, "[PASS]");
        true
    } else {
        let _ = writeln!(out, "[FAIL]");
        let _ = writeln!(out, "    Expected: {:?}", expected.trim());
        let _ = writeln!(out, "    Actual  : {:?}", actual.trim());
        false
    }
}

// coverage: miri(test_self_tests_pass, test_self_tests_report_failures); why: fmt, dyn
/// Runs `cases`, the nesting-limit tests for `depth`, and every workload at `depth`, writing a
/// report to `out` between the QEMU runner's banner and verdict; returns whether every test
/// passed.
pub fn run_self_tests<W: Write>(
    out: &mut W,
    cases: &[SelfTest],
    workloads: &[Workload],
    depth: usize,
) -> bool {
    let _ = writeln!(out, "=================================================");
    let _ = writeln!(out, " bc_clone RISC-V 32 Baremetal Test Suite on QEMU ");
    let _ = writeln!(out, " {}", bc_build_info::VERSION_LINE);
    let _ = writeln!(out, "=================================================");

    let all_passed = run_cases(out, cases, workloads, depth);

    let _ = writeln!(out, "-------------------------------------------------");
    if all_passed {
        let _ = writeln!(out, "ALL RISC-V 32 BAREMETAL TESTS PASSED (100%)!");
    } else {
        let _ = writeln!(out, "SOME RISC-V 32 BAREMETAL TESTS FAILED!");
    }
    let _ = writeln!(out, "=================================================");
    all_passed
}

// coverage: miri(test_run_cases); why: fmt, dyn
/// Runs `cases`, the nesting-limit tests for `depth`, and every workload at `depth`, writing one
/// line for each to `out`; returns whether every test passed. The QEMU runner and the M5Stamp C3
/// application both run their self-tests with it.
pub fn run_cases<W: Write>(
    out: &mut W,
    cases: &[SelfTest],
    workloads: &[Workload],
    depth: usize,
) -> bool {
    let mut all_passed = true;
    for c in cases {
        all_passed &= check(out, c.name, c.code, c.math, c.scale, c.expected, depth);
    }

    // `depth` levels of nesting must run without overflowing the stack; one more is an error. A
    // call nests 2 levels, a parenthesis or block 1 (plus 3 for the statement).
    let max_calls = depth.saturating_sub(6) / 2;
    let max_parens = depth.saturating_sub(3);
    let deep_cases = [
        ("Nesting Limit: Recursion", recursion(max_calls), "0"),
        (
            "Nesting Limit: Recursion Too Deep",
            recursion(max_calls + 1),
            "Runtime error (func=f): nesting too deep",
        ),
        ("Nesting Limit: Parentheses", parens(max_parens), "1"),
        (
            "Nesting Limit: Parentheses Too Deep",
            parens(max_parens + 1),
            "(standard_in) 1: nesting too deep",
        ),
        ("Nesting Limit: Blocks", blocks(max_parens), "1"),
    ];
    for (name, code, expected) in &deep_cases {
        all_passed &= check(out, name, code, false, 0, expected, depth);
    }

    // Every workload at the limit; `deepest` also checks that one level more is an error.
    for workload in workloads {
        let _ = write!(out, "  Running: limit, {:<28} ... ", workload.name);
        let mut run =
            |code: &str, math: bool, scale: usize| eval_bc_at_depth(code, math, scale, depth);
        match stack_workloads::deepest(workload, &mut run, depth) {
            Ok(_) => {
                let _ = writeln!(out, "[PASS]");
            }
            Err(message) => {
                let _ = writeln!(out, "[FAIL]\n    {message}");
                all_passed = false;
            }
        }
    }
    all_passed
}

/// What the measurement of one workload found.
pub struct Measured {
    /// The deepest input the limit accepts, or why the workload failed.
    pub result: Result<usize, String>,
    /// Bytes of stack used.
    pub stack: usize,
    /// Largest number of bytes of heap in use.
    pub heap: usize,
}

// coverage: miri(test_probe_workloads); why: fmt, dyn
/// Measures `workloads` from index `first` on with `measure` and writes one line for each.
pub fn probe_workloads<W: Write>(
    out: &mut W,
    workloads: &[Workload],
    first: usize,
    mut measure: impl FnMut(&Workload) -> Measured,
) {
    for (index, workload) in workloads.iter().enumerate().skip(first) {
        // Printed first: running out of heap ends the run in the panic handler.
        let _ = write!(out, "{index} {}: ", workload.name);
        let measured = measure(workload);
        match measured.result {
            Ok(n) => {
                let _ = writeln!(out, "n={n} stack={} heap={}", measured.stack, measured.heap);
            }
            Err(message) => {
                let _ = writeln!(out, "FAILED {message}");
            }
        }
    }
    let _ = writeln!(out, "PROBE DONE");
}

/// Allocator that passes every call on to `inner` and records the largest number of bytes in use.
/// Its counters are the state of the global allocator of the measurement build (hence `why: hw`).
pub struct PeakAllocator<A> {
    pub inner: A,
    used: AtomicUsize,
    peak: AtomicUsize,
}

impl<A> PeakAllocator<A> {
    // coverage: miri(test_peak_allocator); why: hw
    pub const fn new(inner: A) -> Self {
        Self {
            inner,
            used: AtomicUsize::new(0),
            peak: AtomicUsize::new(0),
        }
    }

    // coverage: miri(test_peak_allocator); why: hw
    /// Starts a new measurement from the bytes in use now.
    pub fn reset_peak(&self) {
        self.peak.store(self.used.load(Relaxed), Relaxed);
    }

    // coverage: miri(test_peak_allocator); why: hw
    /// The largest number of bytes in use since the last [`Self::reset_peak`].
    pub fn peak(&self) -> usize {
        self.peak.load(Relaxed)
    }
}

// SAFETY: every call is passed on to `inner`.
unsafe impl<A: GlobalAlloc> GlobalAlloc for PeakAllocator<A> {
    // coverage: miri(test_peak_allocator); why: trait
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        let used = self.used.load(Relaxed) + layout.size();
        self.used.store(used, Relaxed);
        self.peak.store(self.peak.load(Relaxed).max(used), Relaxed);
        // SAFETY: the caller's contract.
        unsafe { self.inner.alloc(layout) }
    }

    // coverage: miri(test_peak_allocator); why: trait
    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        self.used
            .store(self.used.load(Relaxed) - layout.size(), Relaxed);
        // SAFETY: the caller's contract.
        unsafe { self.inner.dealloc(ptr, layout) }
    }
}

/// A serial writer that sends each byte to `put`, with `\r` before every `\n`.
pub struct CrlfWriter<P>(pub P);

impl<P: FnMut(u8) + Send> Write for CrlfWriter<P> {
    // coverage: miri(test_crlf_writer); why: trait
    fn write_str(&mut self, s: &str) -> core::fmt::Result {
        self.write_bytes(s.as_bytes())
    }
}

impl<P: FnMut(u8) + Send> BcWriter for CrlfWriter<P> {
    // coverage: miri(test_crlf_writer); why: trait
    fn write_bytes(&mut self, b: &[u8]) -> core::fmt::Result {
        for &byte in b {
            if byte == b'\n' {
                (self.0)(b'\r');
            }
            (self.0)(byte);
        }
        Ok(())
    }

    // coverage: miri(test_crlf_writer); why: trait
    fn flush(&mut self) -> core::fmt::Result {
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use stack_workloads::{Expect, WORKLOADS};
    use std::alloc::System;
    use std::vec::Vec;

    #[test]
    fn test_shared_buffer() {
        let buf = SharedBuffer::default();
        let mut writer = buf.clone();
        writer.write_str("ab").unwrap();
        BcWriter::write_bytes(&mut writer, b"c").unwrap();
        BcWriter::flush(&mut writer).unwrap();
        assert_eq!(*buf.0.borrow(), "abc");
    }

    #[test]
    fn test_eval_bc_at_depth() {
        assert_eq!(
            eval_bc_at_depth("scale\n1/3\n", false, 5, 20),
            "5\n.33333\n"
        );
        assert_eq!(eval_bc_at_depth("s(0)\n", true, 3, 20), "0\n");
        assert_eq!(
            eval_bc_at_depth("((((1))))\n", false, 0, 4),
            "(standard_in) 1: nesting too deep\n"
        );
    }

    #[test]
    fn test_self_tests_pass() {
        let mut out = String::new();
        let passed = run_self_tests(&mut out, &SELF_TESTS, &WORKLOADS[..2], 100);
        assert!(passed, "{out}");
        assert!(out.contains(bc_build_info::VERSION_LINE));
        assert!(out.contains("Running: Nesting Limit: Recursion Too Deep"));
        assert!(out.contains("Running: limit, unary minus"));
        assert!(!out.contains("[FAIL]"));
        assert!(out.ends_with(
            "ALL RISC-V 32 BAREMETAL TESTS PASSED (100%)!\n=================================================\n"
        ));
    }

    #[test]
    fn test_self_tests_report_failures() {
        let wrong = [case("wrong", "1 + 1\n", false, 0, "3")];
        let mut out = String::new();
        assert!(!run_self_tests(&mut out, &wrong, &[], 20));
        assert!(out.contains("[FAIL]\n    Expected: \"3\"\n    Actual  : \"2\"\n"));
        assert!(out.contains("SOME RISC-V 32 BAREMETAL TESTS FAILED!"));

        let mut workload = WORKLOADS[0];
        workload.expect = Expect::Fixed("2");
        let mut out = String::new();
        assert!(!run_self_tests(&mut out, &[], &[workload], 20));
        assert!(out.contains("limit, parentheses"));
        assert!(out.contains("[FAIL]\n    at depth 17: expected \"2\", got \"1\"\n"));
    }

    #[test]
    fn test_run_cases() {
        let mut out = String::new();
        assert!(run_cases(&mut out, &SELF_TESTS[..1], &WORKLOADS[..1], 20));
        assert_eq!(
            out.lines().filter(|l| l.ends_with("[PASS]")).count(),
            1 + 5 + 1,
            "{out}"
        );
        assert!(!out.contains("====="));

        let wrong = [case("wrong", "1 + 1\n", false, 0, "3")];
        let mut out = String::new();
        assert!(!run_cases(&mut out, &wrong, &[], 20));
        assert!(out.starts_with("  Running: wrong"));
    }

    #[test]
    fn test_probe_workloads() {
        let mut out = String::new();
        let mut seen = Vec::new();
        probe_workloads(&mut out, &WORKLOADS[..3], 1, |w| {
            seen.push(w.name);
            Measured {
                result: if seen.len() == 1 {
                    Ok(5)
                } else {
                    Err(String::from("broken"))
                },
                stack: 100,
                heap: 200,
            }
        });
        assert_eq!(seen, ["unary minus", "power chain"]);
        assert_eq!(
            out,
            "1 unary minus: n=5 stack=100 heap=200\n2 power chain: FAILED broken\nPROBE DONE\n"
        );
    }

    #[test]
    fn test_peak_allocator() {
        let a = PeakAllocator::new(System);
        let small = Layout::from_size_align(16, 8).unwrap();
        let large = Layout::from_size_align(64, 8).unwrap();
        // SAFETY: each pointer is freed once with its own layout.
        unsafe {
            let p = a.alloc(small);
            let q = a.alloc(large);
            assert!(!p.is_null() && !q.is_null());
            assert_eq!(a.peak(), 80);
            a.dealloc(q, large);
            assert_eq!(a.peak(), 80);
            a.reset_peak();
            assert_eq!(a.peak(), 16);
            let r = a.alloc(small);
            assert_eq!(a.peak(), 32);
            a.dealloc(r, small);
            a.dealloc(p, small);
        }
        a.reset_peak();
        assert_eq!(a.peak(), 0);
    }

    #[test]
    fn test_crlf_writer() {
        let mut sent = Vec::new();
        {
            let mut w = CrlfWriter(|b| sent.push(b));
            w.write_str("a\nb").unwrap();
            BcWriter::write_bytes(&mut w, b"\n\xff").unwrap();
            BcWriter::flush(&mut w).unwrap();
        }
        assert_eq!(sent, b"a\r\nb\r\n\xff");
    }
}
