// SPDX-License-Identifier: MIT

//! Baremetal RISC-V 32 QEMU runner and automated validation suite for bc_clone.

#![no_std]
#![no_main]

extern crate alloc;

mod qemu_exit;
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

#[global_allocator]
static HEAP: Heap = Heap::empty();

struct SingleHartCs;
unsafe impl critical_section::Impl for SingleHartCs {
    unsafe fn acquire() -> critical_section::RawRestoreState {}
    unsafe fn release(_token: critical_section::RawRestoreState) {}
}
critical_section::set_impl!(SingleHartCs);

// 2MB static heap buffer for baremetal calculations
const HEAP_SIZE: usize = 2 * 1024 * 1024;
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
    let out_buf = SharedBuffer::default();

    let mut evaluator = Evaluator::new(
        math_enabled,
        Box::new(out_buf.clone()),
        Box::new(out_buf.clone()),
    );
    evaluator.set_scale(default_scale);
    evaluator.max_depth = QEMU_MAX_DEPTH;

    evaluator.run_source(code, STDIN_SOURCE);

    out_buf.0.borrow().clone()
}

#[entry]
fn main() -> ! {
    // 1. Initialize global heap
    unsafe {
        #[allow(static_mut_refs)]
        HEAP.init(HEAP_MEM.as_ptr() as usize, HEAP_SIZE);
    }

    let mut uart = Uart::new();
    let _ = writeln!(uart, "=================================================");
    let _ = writeln!(uart, " bc_clone RISC-V 32 Baremetal Test Suite on QEMU ");
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
    let recursion = |n: usize| {
        alloc::format!(
            "define f(n) {{\n  if (n == 0) return (0)\n  return (f(n - 1))\n}}\nf({n})\n"
        )
    };
    let parens = |n: usize| alloc::format!("{}1{}\n", "(".repeat(n), ")".repeat(n));
    let blocks = |n: usize| alloc::format!("{}1{}\n", "{".repeat(n), "}".repeat(n));
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

#[cfg(not(test))]
#[panic_handler]
fn panic(info: &PanicInfo) -> ! {
    let mut uart = Uart::new();
    let _ = writeln!(uart, "\n!!! RISC-V BAREMETAL PANIC !!!");
    let _ = writeln!(uart, "{}", info);
    qemu_exit::exit_failure();
}
