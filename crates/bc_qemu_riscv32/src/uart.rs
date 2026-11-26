// SPDX-License-Identifier: MIT

//! NS16550A UART of the QEMU virt machine.

use bc_qemu_riscv32::CrlfWriter;

const UART_BASE: *mut u8 = 0x1000_0000 as *mut u8;

/// The serial console, with `\r\n` line endings.
pub type Uart = CrlfWriter<fn(u8)>;

// coverage: shim(scripts/run_qemu_riscv32_tests.sh); why: hw
/// Writes one byte to the UART transmitter.
fn put(byte: u8) {
    unsafe {
        core::ptr::write_volatile(UART_BASE, byte);
    }
}

// coverage: shim(scripts/run_qemu_riscv32_tests.sh); why: hw
/// The serial console.
pub fn new() -> Uart {
    CrlfWriter(put)
}
