// SPDX-License-Identifier: MIT

//! SiFive Test Finisher exit device for QEMU virt machine.

use bc_core::verified_kernels::verified_qemu_test_exit_code;

const TEST_FINISHER_ADDR: *mut u32 = 0x10_0000 as *mut u32;

// coverage: shim(scripts/run_qemu_riscv32_tests.sh); why: hw
/// Exits QEMU, with status 0 exactly when `passed`.
pub fn exit(passed: bool) -> ! {
    unsafe {
        core::ptr::write_volatile(TEST_FINISHER_ADDR, verified_qemu_test_exit_code(passed));
    }
    loop {
        core::hint::spin_loop();
    }
}
