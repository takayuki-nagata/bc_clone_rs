// SPDX-License-Identifier: MIT

//! The M5Stamp C3 (ESP32-C3) application: the self-tests, then the serial REPL.
//!
//! Only the hardware is here: the heap, the USB serial port, the stack region and the panic
//! handler. What the application decides is in the library (`src/lib.rs`) and the QEMU runner's
//! library, which the host's unit tests run.

#![no_std]
#![no_main]

extern crate alloc;

use alloc::boxed::Box;
use bc_qemu_riscv32::CrlfWriter;
use bc_qemu_riscv32::SELF_TESTS;
use bc_qemu_riscv32::stack_workloads::{WORKLOADS, paint_stack, stack_high_water};
use embedded_io::Read;
use esp_hal::clock::CpuClock;
use esp_hal::main;
use esp_hal::usb_serial_jtag::UsbSerialJtag;
use esp_println::{Printer, println};
use m5stamp_c3_bc::{M5STAMP_MAX_DEPTH, Repl, repl_banner, run_self_tests};

// coverage: shim(scripts/flash_and_test_m5stamp_c3.sh); why: hw, fmt
#[panic_handler]
fn panic(info: &core::panic::PanicInfo) -> ! {
    println!("\n[M5Stamp C3 PANIC]: {:?}", info);
    loop {}
}

esp_bootloader_esp_idf::esp_app_desc!();

// coverage: shim(scripts/flash_and_test_m5stamp_c3.sh); why: hw
/// Writes one byte to the USB serial port.
fn put(byte: u8) {
    Printer::write_bytes(&[byte]);
}

// coverage: shim(scripts/flash_and_test_m5stamp_c3.sh); why: hw
/// The stack region: above esp-hal's guard word, which must not be written, up to its top.
fn stack_region() -> (usize, usize) {
    unsafe extern "C" {
        static __stack_chk_guard: u32;
        static _stack_start: u8;
    }
    (
        core::ptr::addr_of!(__stack_chk_guard) as usize + 4,
        core::ptr::addr_of!(_stack_start) as usize,
    )
}

// coverage: shim(scripts/flash_and_test_m5stamp_c3.sh); why: hw
#[main]
fn main() -> ! {
    // Initialize 128KB heap for arbitrary-precision arithmetic
    esp_alloc::heap_allocator!(size: 128 * 1024);

    let config = esp_hal::Config::default().with_cpu_clock(CpuClock::max());
    let peripherals = esp_hal::init(config);
    let mut usb_serial = UsbSerialJtag::new(peripherals.USB_DEVICE);

    // 1. Run automated self-tests first
    let (stack_bottom, stack_top) = stack_region();
    // SAFETY: the region is the stack, and everything below the current frame is unused.
    unsafe { paint_stack(stack_bottom) };
    run_self_tests(
        &mut Printer,
        &SELF_TESTS,
        &WORKLOADS,
        M5STAMP_MAX_DEPTH,
        (stack_bottom, stack_top),
        // SAFETY: the region painted above.
        || unsafe { stack_high_water(stack_bottom, stack_top) },
    );

    // 2. Start Interactive REPL CLI: one evaluator keeps variables, functions, scale, ibase and
    // obase across lines, with the math library.
    repl_banner(&mut Printer);
    let mut repl = Repl::new(
        Box::new(CrlfWriter(put as fn(u8))),
        Box::new(CrlfWriter(put as fn(u8))),
    );
    let mut rx_byte = [0u8; 1];
    loop {
        let read = usb_serial.read(&mut rx_byte);
        repl.poll(read, &rx_byte, &mut Printer);
    }
}
