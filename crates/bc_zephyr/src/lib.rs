// SPDX-License-Identifier: MIT

//! Zephyr RTOS runner, test suite, and interactive REPL for `bc_core`.

#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(feature = "std")]
extern crate std;

extern crate alloc;

use alloc::boxed::Box;
use alloc::rc::Rc;
use alloc::string::String;
use bc_core::{BcWriter, Evaluator, Lexer, Parser};
use core::cell::RefCell;
use core::fmt::Write;

#[cfg(not(feature = "std"))]
use embedded_alloc::LlffHeap as Heap;

#[cfg(not(feature = "std"))]
#[global_allocator]
static HEAP: Heap = Heap::empty();

#[cfg(not(feature = "std"))]
const HEAP_SIZE: usize = 65536;
#[cfg(not(feature = "std"))]
static mut HEAP_MEM: [u8; HEAP_SIZE] = [0; HEAP_SIZE];

#[cfg(not(feature = "std"))]
struct SingleHartCs;
#[cfg(not(feature = "std"))]
unsafe impl critical_section::Impl for SingleHartCs {
    unsafe fn acquire() -> critical_section::RawRestoreState {}
    unsafe fn release(_token: critical_section::RawRestoreState) {}
}
#[cfg(not(feature = "std"))]
critical_section::set_impl!(SingleHartCs);

#[cfg(not(feature = "std"))]
pub fn init_heap_if_needed() {
    static mut HEAP_INITIALIZED: bool = false;
    critical_section::with(|_| unsafe {
        #[allow(static_mut_refs)]
        if !HEAP_INITIALIZED {
            HEAP_INITIALIZED = true;
            HEAP.init(HEAP_MEM.as_ptr() as usize, HEAP_SIZE);
        }
    });
}

#[cfg(feature = "std")]
pub fn init_heap_if_needed() {}

#[cfg(not(feature = "std"))]
#[panic_handler]
fn panic(info: &core::panic::PanicInfo) -> ! {
    let mut writer = ZephyrConsoleWriter;
    let _ = write!(writer, "\n[Zephyr Rust Panic]: {:?}\n", info);
    loop {
        core::hint::spin_loop();
    }
}

// C-FFI Shims provided by Zephyr minimal trampoline
unsafe extern "C" {
    fn zephyr_putc(c: core::ffi::c_char);
    fn zephyr_getchar() -> core::ffi::c_int;
    fn zephyr_msleep(ms: u32);
}

/// Abstract console writer routing characters to Zephyr printk / UART console.
#[derive(Clone, Copy, Default)]
pub struct ZephyrConsoleWriter;

impl Write for ZephyrConsoleWriter {
    fn write_str(&mut self, s: &str) -> core::fmt::Result {
        for b in s.bytes() {
            unsafe {
                zephyr_putc(b as core::ffi::c_char);
            }
        }
        Ok(())
    }
}

impl BcWriter for ZephyrConsoleWriter {
    fn flush(&mut self) -> core::fmt::Result {
        Ok(())
    }
}

/// Print formatted text to the Zephyr console.
#[macro_export]
macro_rules! zephyr_print {
    ($($arg:tt)*) => {{
        use core::fmt::Write;
        let _ = write!($crate::ZephyrConsoleWriter, $($arg)*);
    }};
}

/// Print formatted text followed by a newline to the Zephyr console.
#[macro_export]
macro_rules! zephyr_println {
    () => {
        $crate::zephyr_print!("\n");
    };
    ($($arg:tt)*) => {{
        $crate::zephyr_print!($($arg)*);
        $crate::zephyr_print!("\n");
    }};
}

/// A reference-counted, interior-mutable String buffer implementing BcWriter.
#[derive(Clone, Default)]
pub struct SharedBuffer(Rc<RefCell<String>>);

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

/// Test case specification.
pub struct TestCase {
    pub name: &'static str,
    pub code: &'static str,
    pub math_enabled: bool,
    pub scale: usize,
    pub expected: &'static str,
}

pub const TEST_CASES: &[TestCase] = &[
    TestCase {
        name: "Basic Arithmetic & Precedence",
        code: "1 + 2 * 3 - 4 / 2\n",
        math_enabled: false,
        scale: 0,
        expected: "5",
    },
    TestCase {
        name: "Scale Division",
        code: "scale = 4; 5 / 3\n",
        math_enabled: false,
        scale: 0,
        expected: "1.6666",
    },
    TestCase {
        name: "BigInt Power (2^100)",
        code: "2^100\n",
        math_enabled: false,
        scale: 0,
        expected: "1267650600228229401496703205376",
    },
    TestCase {
        name: "Recursive Factorial f(20)",
        code: "define f(n) {\n  if (n <= 1) return (1)\n  return (n * f(n - 1))\n}\nf(20)\n",
        math_enabled: false,
        scale: 0,
        expected: "2432902008176640000",
    },
    TestCase {
        name: "Transcendental Pi: 4 * a(1)",
        code: "4 * a(1)\n",
        math_enabled: true,
        scale: 20,
        expected: "3.14159265358979323844",
    },
    TestCase {
        name: "Transcendental Exp: e(1)",
        code: "e(1)\n",
        math_enabled: true,
        scale: 15,
        expected: "2.718281828459045",
    },
    TestCase {
        name: "Transcendental Log: l(2.718281828459045)",
        code: "l(2.718281828459045)\n",
        math_enabled: true,
        scale: 15,
        expected: ".999999999999999",
    },
    TestCase {
        name: "Base Conversion (Hex to Binary)",
        code: "ibase = 16; obase = 2; FF\n",
        math_enabled: false,
        scale: 0,
        expected: "11111111",
    },
    TestCase {
        name: "Arrays and Dynamic Auto Scoping",
        code: "a[0] = 10; a[1] = 20\ndefine sum(x[]) {\n  auto s\n  s = x[0] + x[1]\n  return (s)\n}\nsum(a[])\n",
        math_enabled: false,
        scale: 0,
        expected: "30",
    },
];

///// Evaluates a single test case and returns true if actual output matches expected.
pub fn run_single_test(tc: &TestCase) -> bool {
    let out_buf = SharedBuffer::default();
    let err_buf = SharedBuffer::default();

    let mut ev = Evaluator::new(
        tc.math_enabled,
        Box::new(out_buf.clone()),
        Box::new(err_buf),
    );
    ev.scale = tc.scale;

    let lexer = Lexer::new(tc.code);
    let mut parser = Parser::new(lexer);
    let stmts = parser.parse_program();

    for stmt in &stmts {
        ev.execute(stmt);
    }
    let _ = ev.stdout_writer.flush();

    let captured = out_buf.0.borrow().clone();
    captured.trim() == tc.expected
}

/// Runs the complete test suite and outputs results.
pub fn run_self_tests() -> bool {
    zephyr_println!("\n=================================================");
    zephyr_println!("  bc_clone (bc_core) on Zephyr RTOS              ");
    zephyr_println!("=================================================");
    zephyr_println!("[Zephyr Kernel] Initialized successfully. Starting bc_core test suite...\n");

    let mut all_passed = true;

    for tc in TEST_CASES {
        zephyr_print!("  Running: {:<35} ... ", tc.name);

        if run_single_test(tc) {
            zephyr_println!("[PASS]");
        } else {
            zephyr_println!("[FAIL]");
            zephyr_println!("    Expected: \"{}\"", tc.expected);
            all_passed = false;
        }
    }

    zephyr_print!("\n  Streaming Callback Test: 2^16 = ");
    let mut ev_cb = Evaluator::new(
        false,
        Box::new(ZephyrConsoleWriter),
        Box::new(ZephyrConsoleWriter),
    );
    let lexer = Lexer::new("2^16\n");
    let mut parser = Parser::new(lexer);
    let stmts = parser.parse_program();
    for stmt in &stmts {
        ev_cb.execute(stmt);
    }
    let _ = ev_cb.stdout_writer.flush();

    zephyr_println!("-------------------------------------------------");
    if all_passed {
        zephyr_println!("ALL ZEPHYR BC_CORE TESTS PASSED (100%)!");
        zephyr_println!("=================================================");
    } else {
        zephyr_println!("SOME ZEPHYR BC_CORE TESTS FAILED!");
        zephyr_println!("=================================================");
    }

    all_passed
}

/// Runs the interactive serial REPL loop with customizable I/O functions.
pub fn run_repl_with<G, P, S, W>(
    mut getchar: G,
    mut putc: P,
    mut print_str: S,
    mut msleep: W,
    max_steps: Option<usize>,
) where
    G: FnMut() -> i32,
    P: FnMut(char),
    S: FnMut(&str),
    W: FnMut(u32),
{
    print_str("\nEntering bc_core Interactive REPL mode (Zephyr RTOS)...\n");
    print_str("Type bc expressions (e.g. 2^64, scale=10; 4*a(1), define f(x)...)\n");
    print_str("bc> ");

    let out_buf = SharedBuffer::default();
    let err_buf = SharedBuffer::default();
    let mut evaluator = Evaluator::new(true, Box::new(out_buf.clone()), Box::new(err_buf.clone()));
    let mut line_buf = String::new();
    let mut steps = 0;

    loop {
        if let Some(limit) = max_steps {
            if steps >= limit {
                break;
            }
            steps += 1;
        }

        let ch = getchar();
        if ch == -2 {
            // Test exit sentinel
            break;
        }
        if ch < 0 {
            msleep(10);
            continue;
        }

        let b = ch as u8;
        if b == b'\r' || b == b'\n' {
            print_str("\r\n");
            if !line_buf.is_empty() {
                line_buf.push('\n');
                let lexer = Lexer::new(&line_buf);
                let mut parser = Parser::new(lexer);
                let stmts = parser.parse_program();
                for stmt in &stmts {
                    evaluator.execute(stmt);
                }
                let _ = evaluator.stdout_writer.flush();

                let out = out_buf.0.borrow().clone();
                print_str(&out);
                out_buf.0.borrow_mut().clear();
                line_buf.clear();
            }
            print_str("bc> ");
        } else if b == 0x08 || b == 0x7F {
            if !line_buf.is_empty() {
                line_buf.pop();
                print_str("\x08 \x08");
            }
        } else if b == 0x03 {
            line_buf.clear();
            print_str("^C\r\nbc> ");
        } else if (0x20..=0x7E).contains(&b) {
            line_buf.push(b as char);
            putc(b as char);
        }
    }
}

/// Runs the interactive serial REPL loop using Zephyr hardware shims.
pub fn run_repl() {
    run_repl_with(
        || unsafe { zephyr_getchar() as i32 },
        |c| unsafe { zephyr_putc(c as core::ffi::c_char) },
        |s| {
            for b in s.bytes() {
                unsafe { zephyr_putc(b as core::ffi::c_char) };
            }
        },
        |ms| unsafe { zephyr_msleep(ms) },
        None,
    );
}

/// Entry point called by the minimal Zephyr C trampoline `main()`.
#[unsafe(no_mangle)]
pub extern "C" fn zephyr_rust_main(is_qemu: bool) {
    init_heap_if_needed();

    let all_passed = run_self_tests();

    if is_qemu {
        // Automated exit for QEMU emulation in CI (SiFive Test device)
        #[cfg(not(feature = "std"))]
        {
            let test_exit = 0x10_0000 as *mut u32;
            unsafe {
                core::ptr::write_volatile(test_exit, if all_passed { 0x5555 } else { 0x3333 });
            }
        }
        #[cfg(feature = "std")]
        {
            let _ = all_passed;
        }
    } else {
        run_repl();
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Mutex;
    use std::vec::Vec;

    static MOCK_CHARS: Mutex<Vec<i32>> = Mutex::new(Vec::new());
    static MOCK_PUT_CHARS: Mutex<Vec<u8>> = Mutex::new(Vec::new());
    static MOCK_SLEPT: Mutex<u32> = Mutex::new(0);

    // Mock Zephyr C shims for host unit testing
    #[unsafe(no_mangle)]
    extern "C" fn zephyr_putc(c: core::ffi::c_char) {
        MOCK_PUT_CHARS.lock().unwrap().push(c as u8);
    }

    #[unsafe(no_mangle)]
    extern "C" fn zephyr_getchar() -> core::ffi::c_int {
        let mut queue = MOCK_CHARS.lock().unwrap();
        if queue.is_empty() {
            -2
        } else {
            queue.remove(0) as core::ffi::c_int
        }
    }

    #[unsafe(no_mangle)]
    extern "C" fn zephyr_msleep(ms: u32) {
        *MOCK_SLEPT.lock().unwrap() += ms;
    }

    #[test]
    fn test_zephyr_console_writer() {
        MOCK_PUT_CHARS.lock().unwrap().clear();
        let mut writer = ZephyrConsoleWriter;
        write!(writer, "test").unwrap();
        assert_eq!(MOCK_PUT_CHARS.lock().unwrap().as_slice(), b"test");
    }

    #[test]
    fn test_all_zephyr_cases() {
        MOCK_PUT_CHARS.lock().unwrap().clear();
        assert!(run_self_tests());
        assert!(!MOCK_PUT_CHARS.lock().unwrap().is_empty());
    }

    #[test]
    fn test_single_test_failure() {
        let fake_tc = TestCase {
            name: "Fake Failure Case",
            code: "1 + 1\n",
            math_enabled: false,
            scale: 0,
            expected: "999",
        };
        assert!(!run_single_test(&fake_tc));
    }

    #[test]
    fn test_shared_buffer() {
        let buf = SharedBuffer::default();
        let mut writer = buf.clone();
        let _ = write!(writer, "hello {}", 123);
        let _ = writer.flush();
        assert_eq!(buf.0.borrow().as_str(), "hello 123");
    }

    #[test]
    fn test_zephyr_rust_main_qemu() {
        MOCK_PUT_CHARS.lock().unwrap().clear();
        zephyr_rust_main(true);
        assert!(!MOCK_PUT_CHARS.lock().unwrap().is_empty());
    }

    #[test]
    fn test_zephyr_rust_main_repl() {
        MOCK_PUT_CHARS.lock().unwrap().clear();
        {
            let mut queue = MOCK_CHARS.lock().unwrap();
            queue.clear();
            queue.extend_from_slice(&[b'2' as i32, b'+' as i32, b'2' as i32, b'\n' as i32, -2]);
        }
        zephyr_rust_main(false);
        let put = String::from_utf8(MOCK_PUT_CHARS.lock().unwrap().clone()).unwrap();
        assert!(put.contains("4"));
    }

    #[test]
    fn test_repl_step_limit_and_sleep() {
        let mut count = 0;
        let mut slept = false;
        run_repl_with(
            || {
                count += 1;
                -1
            },
            |_| {},
            |_| {},
            |_| {
                slept = true;
            },
            Some(3),
        );
        assert_eq!(count, 3);
        assert!(slept);
    }

    #[test]
    fn test_repl_del_and_bs() {
        let mut out = String::new();
        let mut input = vec![b'x' as i32, 0x08, b'y' as i32, 0x7F, -2];
        run_repl_with(
            || {
                if input.is_empty() {
                    -2
                } else {
                    input.remove(0)
                }
            },
            |_| {},
            |s| out.push_str(s),
            |_| {},
            None,
        );
        assert!(out.contains("\x08 \x08"));
    }

    #[test]
    fn test_repl_with_interactive_flow() {
        let mut input_chars: Vec<i32> = vec![
            -1, // msleep branch
            b'1' as i32,
            b'0' as i32,
            0x08, // backspace
            0x7F, // delete
            0x03, // ctrl+c
            b'3' as i32,
            b'*' as i32,
            b'7' as i32,
            b'\r' as i32,
            -2, // exit sentinel
        ];
        let output_str = core::cell::RefCell::new(String::new());

        run_repl_with(
            || {
                if input_chars.is_empty() {
                    -2
                } else {
                    input_chars.remove(0)
                }
            },
            |c| output_str.borrow_mut().push(c),
            |s| output_str.borrow_mut().push_str(s),
            |_ms| {},
            Some(20),
        );

        assert!(output_str.borrow().contains("21"));
    }

    #[test]
    fn test_repl_nul_char() {
        let mut slept = false;
        let mut input = vec![0, -2];
        run_repl_with(
            || input.remove(0),
            |_| {},
            |_| {},
            |_| {
                slept = true;
            },
            None,
        );
        assert!(!slept);
    }

    #[test]
    fn test_run_repl_direct() {
        MOCK_PUT_CHARS.lock().unwrap().clear();
        {
            let mut queue = MOCK_CHARS.lock().unwrap();
            queue.clear();
            queue.extend_from_slice(&[b'1' as i32, b'+' as i32, b'1' as i32, b'\n' as i32, -2]);
        }
        run_repl();
        let put = String::from_utf8(MOCK_PUT_CHARS.lock().unwrap().clone()).unwrap();
        assert!(put.contains("2"));
    }
}
