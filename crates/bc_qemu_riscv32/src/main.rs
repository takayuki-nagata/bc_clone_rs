// SPDX-License-Identifier: MIT

//! Baremetal RISC-V 32 QEMU runner and automated validation suite for bc_clone.
//!
//! Only the hardware is here: the heap, the UART, QEMU's test device, the panic handler and the
//! arguments of the measurement. What the runner decides is in the library, which the host's unit
//! tests run.

#![no_std]
#![no_main]

extern crate alloc;

mod qemu_exit;
mod uart;

use bc_qemu_riscv32::stack_workloads::WORKLOADS;
use bc_qemu_riscv32::{QEMU_MAX_DEPTH, SELF_TESTS, run_self_tests};
use core::fmt::Write;
use core::panic::PanicInfo;
use embedded_alloc::LlffHeap as Heap;
use riscv_rt::entry;

#[cfg(not(feature = "m5stamp-probe"))]
#[global_allocator]
static HEAP: Heap = Heap::empty();

#[cfg(feature = "m5stamp-probe")]
#[global_allocator]
static ALLOCATOR: bc_qemu_riscv32::PeakAllocator<Heap> =
    bc_qemu_riscv32::PeakAllocator::new(Heap::empty());

// coverage: shim(scripts/run_qemu_riscv32_tests.sh); why: hw
/// The heap behind the global allocator.
#[cfg(not(feature = "m5stamp-probe"))]
fn heap() -> &'static Heap {
    &HEAP
}

// coverage: shim(scripts/run_qemu_riscv32_tests.sh); why: hw
/// The heap behind the global allocator, which counts its use.
#[cfg(feature = "m5stamp-probe")]
fn heap() -> &'static Heap {
    &ALLOCATOR.inner
}

// The runner has one hart and no interrupts, so a critical section has nothing to save or
// restore. `critical_section::set_impl!` generates two `#[no_mangle]` functions that forward to
// these methods, and nothing else.
struct SingleHartCs;
unsafe impl critical_section::Impl for SingleHartCs {
    // coverage: shim(scripts/run_qemu_riscv32_tests.sh); why: hw, trait
    unsafe fn acquire() -> critical_section::RawRestoreState {}
    // coverage: shim(scripts/run_qemu_riscv32_tests.sh); why: hw, trait
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

// coverage: shim(scripts/run_qemu_riscv32_tests.sh); why: hw
#[entry]
#[cfg_attr(
    feature = "m5stamp-probe",
    allow(unreachable_code, reason = "run_probe does not return")
)]
fn main() -> ! {
    // SAFETY: runs once, before anything allocates; nothing else uses HEAP_MEM.
    unsafe {
        heap().init(core::ptr::addr_of!(HEAP_MEM) as usize, HEAP_SIZE);
    }

    let mut uart = uart::new();
    #[cfg(feature = "m5stamp-probe")]
    run_probe(&mut uart);
    let passed = run_self_tests(&mut uart, &SELF_TESTS, &WORKLOADS, QEMU_MAX_DEPTH);
    qemu_exit::exit(passed);
}

// coverage: shim(scripts/run_qemu_riscv32_tests.sh); why: hw
/// Measures every workload for the M5Stamp C3: the nesting limit and the workload to start from
/// come from the words at [`PROBE_ARGS`], put there by QEMU's `-device loader`.
#[cfg(feature = "m5stamp-probe")]
fn run_probe(uart: &mut uart::Uart) -> ! {
    use bc_qemu_riscv32::stack_workloads::{deepest, paint_stack, stack_high_water};
    use bc_qemu_riscv32::{Measured, eval_bc_at_depth, probe_workloads};

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
    probe_workloads(uart, &WORKLOADS, first, |workload| {
        // SAFETY: the stack in use is far smaller than PROBED_STACK, and nothing else is there.
        unsafe { paint_stack(bottom) };
        ALLOCATOR.reset_peak();
        let result = deepest(workload, &mut run, limit);
        Measured {
            result,
            // SAFETY: as for `paint_stack` above.
            stack: unsafe { stack_high_water(bottom, top) },
            heap: ALLOCATOR.peak(),
        }
    });
    qemu_exit::exit(true);
}

// coverage: shim(scripts/run_qemu_riscv32_tests.sh); why: hw, fmt
/// Prints the panic and exits QEMU with status 1 (bc_core does not panic on any input; exhausting
/// the heap does).
#[panic_handler]
fn panic(info: &PanicInfo) -> ! {
    let mut uart = uart::new();
    let _ = writeln!(uart, "\n!!! RISC-V BAREMETAL PANIC !!!");
    let _ = writeln!(uart, "{}", info);
    qemu_exit::exit(false);
}
