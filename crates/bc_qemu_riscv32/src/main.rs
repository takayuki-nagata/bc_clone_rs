// SPDX-License-Identifier: MIT

//! Baremetal RISC-V 32 QEMU runner and automated validation suite for bc_clone.

#![no_std]
#![no_main]

extern crate alloc;

mod qemu_exit;
#[allow(
    dead_code,
    reason = "the stack measurement is used by the m5stamp-probe feature and the M5Stamp C3"
)]
mod stack_workloads;
mod uart;

use alloc::boxed::Box;
use alloc::rc::Rc;
use alloc::string::String;
use bc_core::{BcWriter, Evaluator, STDIN_SOURCE};
use core::cell::RefCell;
use core::fmt::Write;
use core::panic::PanicInfo;
use embedded_alloc::LlffHeap as Heap;
use riscv_rt::entry;
use uart::Uart;

#[cfg(not(feature = "m5stamp-probe"))]
#[global_allocator]
static HEAP: Heap = Heap::empty();

#[cfg(feature = "m5stamp-probe")]
static HEAP: Heap = Heap::empty();

/// Allocator that records the largest number of bytes in use.
#[cfg(feature = "m5stamp-probe")]
struct PeakAllocator {
    used: core::sync::atomic::AtomicUsize,
    peak: core::sync::atomic::AtomicUsize,
}

#[cfg(feature = "m5stamp-probe")]
impl PeakAllocator {
    fn reset_peak(&self) {
        use core::sync::atomic::Ordering::Relaxed;
        self.peak.store(self.used.load(Relaxed), Relaxed);
    }

    fn peak(&self) -> usize {
        self.peak.load(core::sync::atomic::Ordering::Relaxed)
    }
}

// SAFETY: every call is passed on to `HEAP`.
#[cfg(feature = "m5stamp-probe")]
unsafe impl core::alloc::GlobalAlloc for PeakAllocator {
    unsafe fn alloc(&self, layout: core::alloc::Layout) -> *mut u8 {
        use core::sync::atomic::Ordering::Relaxed;
        let used = self.used.load(Relaxed) + layout.size();
        self.used.store(used, Relaxed);
        self.peak.store(self.peak.load(Relaxed).max(used), Relaxed);
        // SAFETY: the caller's contract.
        unsafe { HEAP.alloc(layout) }
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: core::alloc::Layout) {
        use core::sync::atomic::Ordering::Relaxed;
        self.used
            .store(self.used.load(Relaxed) - layout.size(), Relaxed);
        // SAFETY: the caller's contract.
        unsafe { HEAP.dealloc(ptr, layout) }
    }
}

#[cfg(feature = "m5stamp-probe")]
#[global_allocator]
static ALLOCATOR: PeakAllocator = PeakAllocator {
    used: core::sync::atomic::AtomicUsize::new(0),
    peak: core::sync::atomic::AtomicUsize::new(0),
};

struct SingleHartCs;
unsafe impl critical_section::Impl for SingleHartCs {
    unsafe fn acquire() -> critical_section::RawRestoreState {}
    unsafe fn release(_token: critical_section::RawRestoreState) {}
}
critical_section::set_impl!(SingleHartCs);

// 2MB static heap buffer for baremetal calculations, or the M5Stamp C3's 128 KiB when measuring
// for it
#[cfg(not(feature = "m5stamp-probe"))]
const HEAP_SIZE: usize = 2 * 1024 * 1024;
#[cfg(feature = "m5stamp-probe")]
const HEAP_SIZE: usize = 128 * 1024;
static mut HEAP_MEM: [u8; HEAP_SIZE] = [0; HEAP_SIZE];

/// A reference-counted, interior-mutable String buffer implementing BcWriter.
#[derive(Clone, Default)]
struct SharedBuffer(Rc<RefCell<String>>);

unsafe impl Send for SharedBuffer {}

impl Write for SharedBuffer {
    fn write_str(&mut self, s: &str) -> core::fmt::Result {
        self.0.borrow_mut().push_str(s);
        Ok(())
    }
}

impl BcWriter for SharedBuffer {
    fn flush(&mut self) -> core::fmt::Result {
        Ok(())
    }
}

/// Nesting limit (`docs/COMPATIBILITY.md` §2). One level takes at most about 800 bytes of stack
/// on RV32 (measured), and the stack is the rest of the 16 MiB RAM after the 2 MiB heap.
const QEMU_MAX_DEPTH: usize = 1000;

/// Evaluates a bc program string on baremetal RISC-V and returns the captured output string.
fn eval_bc_string(code: &str, math_enabled: bool, default_scale: usize) -> String {
    eval_bc_at_depth(code, math_enabled, default_scale, QEMU_MAX_DEPTH)
}

/// [`eval_bc_string`] with the given nesting limit.
fn eval_bc_at_depth(code: &str, math_enabled: bool, default_scale: usize, depth: usize) -> String {
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

#[entry]
#[cfg_attr(
    feature = "m5stamp-probe",
    allow(unreachable_code, reason = "run_probe does not return")
)]
fn main() -> ! {
    // 1. Initialize global heap
    unsafe {
        #[allow(static_mut_refs)]
        HEAP.init(HEAP_MEM.as_ptr() as usize, HEAP_SIZE);
    }

    let mut uart = Uart::new();
    #[cfg(feature = "m5stamp-probe")]
    run_probe(&mut uart);
    let _ = writeln!(uart, "=================================================");
    let _ = writeln!(uart, " bc_clone RISC-V 32 Baremetal Test Suite on QEMU ");
    let _ = writeln!(uart, " {}", bc_build_info::VERSION_LINE);
    let _ = writeln!(uart, "=================================================");

    let mut all_passed = true;

    // Test cases: (Name, Code, MathEnabled, Scale, ExpectedSubstring)
    let test_cases = [
        (
            "Basic Arithmetic & Precedence",
            "1 + 2 * 3 - 4 / 2\n",
            false,
            0,
            "5",
        ),
        ("Scale Division", "scale = 4; 5 / 3\n", false, 0, "1.6666"),
        (
            "BigInt Power (2^100)",
            "2^100\n",
            false,
            0,
            "1267650600228229401496703205376",
        ),
        (
            // The exact scale of a power is computed in u64: on 32-bit targets an exponent
            // beyond usize::MAX must not make a scale-0 power "scale too large".
            "Power with an exponent beyond u32",
            "1^5000000000; (-1)^5000000001; 0^5000000000\n",
            false,
            0,
            "1\n-1\n0",
        ),
        (
            "Recursive Factorial f(20)",
            "define f(n) { if (n <= 1) return (1); return (n * f(n - 1)); }; f(20)\n",
            false,
            0,
            "2432902008176640000",
        ),
        (
            "Transcendental Pi: 4 * a(1)",
            "4 * a(1)\n",
            true,
            20,
            "3.14159265358979323844",
        ),
        (
            "Transcendental Exp: e(1)",
            "e(1)\n",
            true,
            15,
            "2.718281828459045",
        ),
        (
            "Transcendental Log: l(2.718281828459045)",
            "l(2.718281828459045)\n",
            true,
            15,
            ".999999999999999",
        ),
        (
            "Transcendental Sine & Cosine",
            "s(0) + c(0)\n",
            true,
            15,
            "1.000000000000000",
        ),
        (
            "Base Conversion (Hex to Binary)",
            "ibase = 16; obase = 2; FF\n",
            false,
            0,
            "11111111",
        ),
        (
            "Arrays and Dynamic Auto Scoping",
            "a[0] = 10; a[1] = 20\ndefine sum(x[]) {\n  auto s\n  s = x[0] + x[1]\n  return (s)\n}\nsum(a[])\n",
            false,
            0,
            "30",
        ),
        (
            "Error Recovery (Div by Zero)",
            "1 / 0\n",
            false,
            0,
            "Runtime error (func=(main)): Divide by zero",
        ),
        (
            // 2^32 + 1 does not fit a 32-bit usize; it must clamp, not wrap to 1.
            "Scale Limit on 32-bit usize",
            "scale = 4294967297; scale\n",
            false,
            0,
            "Runtime warning (func=(main)): scale too large, set to 1000000000\n1000000000",
        ),
    ];

    // QEMU_MAX_DEPTH levels of nesting must run without overflowing the stack; one more is an
    // error. A call nests 2 levels, a parenthesis or block 1 (plus 3 for the statement).
    use stack_workloads::{blocks, parens, recursion};
    let max_calls = QEMU_MAX_DEPTH / 2 - 3;
    let max_parens = QEMU_MAX_DEPTH - 3;
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
    let deep_cases = deep_cases
        .iter()
        .map(|(name, code, expected)| (*name, code.as_str(), false, 0, *expected));

    for (name, code, math_enabled, scale, expected) in test_cases.into_iter().chain(deep_cases) {
        let _ = write!(uart, "  Running: {:<35} ... ", name);

        let actual = eval_bc_string(code, math_enabled, scale);

        if actual.trim() == expected.trim() {
            let _ = writeln!(uart, "[PASS]");
        } else {
            let _ = writeln!(uart, "[FAIL]");
            let _ = writeln!(uart, "    Expected: {:?}", expected.trim());
            let _ = writeln!(uart, "    Actual  : {:?}", actual.trim());
            all_passed = false;
        }
    }

    // Every workload at the limit; `deepest` also checks that one level more is an error.
    for workload in &stack_workloads::WORKLOADS {
        let _ = write!(uart, "  Running: limit, {:<28} ... ", workload.name);
        let mut run = |code: &str, math: bool, scale: usize| eval_bc_string(code, math, scale);
        match stack_workloads::deepest(workload, &mut run, QEMU_MAX_DEPTH) {
            Ok(_) => {
                let _ = writeln!(uart, "[PASS]");
            }
            Err(message) => {
                let _ = writeln!(uart, "[FAIL]\n    {message}");
                all_passed = false;
            }
        }
    }

    let _ = writeln!(uart, "-------------------------------------------------");
    if all_passed {
        let _ = writeln!(uart, "ALL RISC-V 32 BAREMETAL TESTS PASSED (100%)!");
        let _ = writeln!(uart, "=================================================");
        qemu_exit::exit_success();
    } else {
        let _ = writeln!(uart, "SOME RISC-V 32 BAREMETAL TESTS FAILED!");
        let _ = writeln!(uart, "=================================================");
        qemu_exit::exit_failure();
    }
}

/// Measures every workload for the M5Stamp C3: the nesting limit and the workload to start from
/// come from the words at [`PROBE_ARGS`], put there by QEMU's `-device loader`.
#[cfg(feature = "m5stamp-probe")]
fn run_probe(uart: &mut Uart) -> ! {
    unsafe extern "C" {
        static _stack_start: u8;
    }
    /// Above the image and below the stack (`memory.x`).
    const PROBE_ARGS: usize = 0x80ff_fff0;
    /// Far more than the 181 KiB stack of the M5Stamp C3.
    const PROBED_STACK: usize = 1024 * 1024;

    // SAFETY: the loader wrote the two words, in RAM that nothing else uses.
    let (limit, first) = unsafe {
        (
            core::ptr::read_volatile(PROBE_ARGS as *const u32) as usize,
            core::ptr::read_volatile((PROBE_ARGS + 4) as *const u32) as usize,
        )
    };
    let top = core::ptr::addr_of!(_stack_start) as usize;
    let bottom = top - PROBED_STACK;
    let mut run = |code: &str, math: bool, scale: usize| eval_bc_at_depth(code, math, scale, limit);
    for (index, workload) in stack_workloads::WORKLOADS.iter().enumerate().skip(first) {
        // Printed first: running out of heap ends the run in the panic handler.
        let _ = write!(uart, "{index} {}: ", workload.name);
        // SAFETY: the stack in use is far smaller than PROBED_STACK, and nothing else is there.
        unsafe { stack_workloads::paint_stack(bottom) };
        ALLOCATOR.reset_peak();
        let result = stack_workloads::deepest(workload, &mut run, limit);
        // SAFETY: as for `paint_stack` above.
        let stack = unsafe { stack_workloads::stack_high_water(bottom, top) };
        let heap = ALLOCATOR.peak();
        match result {
            Ok(n) => {
                let _ = writeln!(uart, "n={n} stack={stack} heap={heap}");
            }
            Err(message) => {
                let _ = writeln!(uart, "FAILED {message}");
            }
        }
    }
    let _ = writeln!(uart, "PROBE DONE");
    qemu_exit::exit_success();
}

#[cfg(not(test))]
#[panic_handler]
fn panic(info: &PanicInfo) -> ! {
    let mut uart = Uart::new();
    let _ = writeln!(uart, "\n!!! RISC-V BAREMETAL PANIC !!!");
    let _ = writeln!(uart, "{}", info);
    qemu_exit::exit_failure();
}
