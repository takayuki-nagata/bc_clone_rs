// SPDX-License-Identifier: MIT

#![no_std]
#![no_main]

extern crate alloc;

use alloc::boxed::Box;
use alloc::rc::Rc;
use alloc::string::String;
use alloc::vec::Vec;
use bc_core::{BcWriter, Evaluator, Lexer, Parser};
use core::cell::RefCell;
use core::fmt::Write;
use embedded_io::Read;
use esp_hal::clock::CpuClock;
use esp_hal::main;
use esp_hal::usb_serial_jtag::UsbSerialJtag;
use esp_println::{print, println};

#[panic_handler]
fn panic(info: &core::panic::PanicInfo) -> ! {
    println!("\n[M5Stamp C3 PANIC]: {:?}", info);
    loop {}
}

esp_bootloader_esp_idf::esp_app_desc!();

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

/// Direct terminal writer that streams output directly to esp-println (USB-Serial).
struct SerialWriter;

impl Write for SerialWriter {
    fn write_str(&mut self, s: &str) -> core::fmt::Result {
        for c in s.chars() {
            if c == '\n' {
                print!("\r\n");
            } else {
                print!("{}", c);
            }
        }
        Ok(())
    }
}

impl BcWriter for SerialWriter {
    fn flush(&mut self) -> core::fmt::Result {
        Ok(())
    }
}

fn eval_bc_string(code: &str, math_enabled: bool, default_scale: usize) -> String {
    let out_buf = SharedBuffer::default();
    let err_buf = SharedBuffer::default();

    let mut ev = Evaluator::new(
        math_enabled,
        Box::new(out_buf.clone()),
        Box::new(err_buf.clone()),
    );
    ev.scale = default_scale;

    let lexer = Lexer::new(code);
    let mut parser = Parser::new(lexer);
    let stmts = parser.parse_program();

    for stmt in &stmts {
        ev.execute(stmt);
    }
    let _ = ev.stdout_writer.flush();

    out_buf.0.borrow().clone()
}

fn run_self_tests() -> bool {
    println!("\n=================================================");
    println!("  bc_clone (bc_core) on M5Stamp C3 (ESP32-C3)    ");
    println!("=================================================");
    println!("[ESP32-C3] Initialized successfully @ 160MHz.");
    println!("[ESP32-C3] 128KB SRAM Heap allocated for bc_core.\n");

    let test_cases: [(&str, &str, bool, usize, &str); 10] = [
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
            "define f(n) {\n  if (n <= 1) return (1)\n  return (n * f(n - 1))\n}\nf(20)\n",
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

    let mut all_passed = true;
    for (name, code, math_enabled, scale, expected) in test_cases {
        print!("  Running: {:<35} ... ", name);

        let actual = eval_bc_string(code, math_enabled, scale);

        if actual.trim() == expected.trim() {
            println!("[PASS]");
        } else {
            println!("[FAIL]");
            println!("    Expected: \"{}\"", expected);
            println!("    Actual  : \"{}\"", actual.trim());
            all_passed = false;
        }
    }

    println!("-------------------------------------------------");
    if all_passed {
        println!("ALL M5STAMP-C3 BC_CORE TESTS PASSED (100%)!");
        println!("=================================================\n");
    } else {
        println!("SOME M5STAMP-C3 BC_CORE TESTS FAILED!");
        println!("=================================================\n");
    }
    all_passed
}

#[main]
fn main() -> ! {
    // Initialize 128KB heap for arbitrary-precision arithmetic
    esp_alloc::heap_allocator!(size: 128 * 1024);

    let config = esp_hal::Config::default().with_cpu_clock(CpuClock::max());
    let peripherals = esp_hal::init(config);
    let mut usb_serial = UsbSerialJtag::new(peripherals.USB_DEVICE);

    // 1. Run automated self-tests first
    run_self_tests();

    // 2. Start Interactive REPL CLI
    println!("Entering bc_core Interactive REPL mode...");
    println!("Type bc expressions (e.g. 2^64, scale=10; 4*a(1), define f(x)...)");
    print!("bc> ");

    // Persistent Evaluator holding variables, user functions, scale, ibase, obase
    let mut evaluator = Evaluator::new(
        true, // Enable math library functions (s, c, e, l, a, j)
        Box::new(SerialWriter),
        Box::new(SerialWriter),
    );

    let mut line_buf = Vec::new();
    let mut rx_byte = [0u8; 1];

    loop {
        let count: usize = usb_serial.read(&mut rx_byte).unwrap_or_default();
        if count == 0 {
            continue;
        }
        let byte = rx_byte[0];

            match byte {
                b'\r' | b'\n' => {
                    print!("\r\n");
                    if !line_buf.is_empty() {
                        if let Ok(input_str) = core::str::from_utf8(&line_buf) {
                            let mut code_to_eval = String::from(input_str);
                            code_to_eval.push('\n');

                            let lexer = Lexer::new(&code_to_eval);
                            let mut parser = Parser::new(lexer);
                            let stmts = parser.parse_program();

                            for stmt in &stmts {
                                evaluator.execute(stmt);
                            }
                            let _ = evaluator.stdout_writer.flush();
                        }
                        line_buf.clear();
                    }
                    print!("bc> ");
                }
                0x08 | 0x7F if !line_buf.is_empty() => {
                    // Backspace / Delete
                    line_buf.pop();
                    print!("\x08 \x08");
                }
                0x08 | 0x7F => {
                    // Backspace with empty buffer: do nothing
                }
                0x03 => {
                    // Ctrl+C: Cancel current line
                    line_buf.clear();
                    print!("^C\r\nbc> ");
                }
                0x20..=0x7E => {
                    // Printable ASCII characters
                    line_buf.push(byte);
                    print!("{}", byte as char);
                }
                _ => {
                    // Ignore other control characters
                }
            }
    }
}
