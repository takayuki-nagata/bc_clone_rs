// SPDX-License-Identifier: MIT

//! SiFive Test Finisher exit device for QEMU virt machine.

const TEST_FINISHER_ADDR: *mut u32 = 0x10_0000 as *mut u32;
const FINISHER_FAIL: u32 = 0x3333;
const FINISHER_PASS: u32 = 0x5555;

/// Exits QEMU emulator with success status code (0).
pub fn exit_success() -> ! {
    unsafe {
        core::ptr::write_volatile(TEST_FINISHER_ADDR, FINISHER_PASS);
    }
    loop {
        core::hint::spin_loop();
    }
}

/// Exits QEMU emulator with failure status code (1).
pub fn exit_failure() -> ! {
    unsafe {
        core::ptr::write_volatile(TEST_FINISHER_ADDR, FINISHER_FAIL);
    }
    loop {
        core::hint::spin_loop();
    }
}
