// SPDX-License-Identifier: MIT

//! NS16550A UART driver for QEMU virt machine.

use bc_core::BcWriter;
use core::fmt::{self, Write};

const UART_BASE: *mut u8 = 0x1000_0000 as *mut u8;

/// QEMU Virt UART output writer.
#[derive(Default)]
pub struct Uart;

impl Uart {
    /// Creates a new Uart writer.
    pub fn new() -> Self {
        Self
    }

    /// Writes a single byte to the UART transmitter.
    pub fn write_byte(&mut self, byte: u8) {
        unsafe {
            core::ptr::write_volatile(UART_BASE, byte);
        }
    }
}

impl Write for Uart {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        for byte in s.bytes() {
            if byte == b'\n' {
                self.write_byte(b'\r');
            }
            self.write_byte(byte);
        }
        Ok(())
    }
}

impl BcWriter for Uart {
    fn flush(&mut self) -> fmt::Result {
        Ok(())
    }
}
