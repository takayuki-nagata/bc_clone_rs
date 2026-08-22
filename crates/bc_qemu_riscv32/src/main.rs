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
use bc_core::{BcWriter, Evaluator, Lexer, Parser};
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

/// Evaluates a bc program string on baremetal RISC-V and returns the captured output string.
fn eval_bc_string(code: &str, math_enabled: bool, default_scale: usize) -> String {
    let out_buf = SharedBuffer::default();
    let err_buf = SharedBuffer::default();

    let mut evaluator = Evaluator::new(math_enabled, Box::new(out_buf.clone()), Box::new(err_buf));
    evaluator.scale = default_scale;

    let lexer = Lexer::new(code);
    let mut parser = Parser::new(lexer);
    let stmts = parser.parse_program();

    for stmt in &stmts {
        evaluator.execute(stmt);
    }
    let _ = evaluator.stdout_writer.flush();

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
    ];

    for (name, code, math_enabled, scale, expected) in test_cases {
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
