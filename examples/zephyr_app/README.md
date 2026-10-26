# bc_clone_rs Zephyr RTOS Application Example

This example demonstrates executing the arbitrary-precision mathematical engine `bc_core` inside **Zephyr RTOS** kernel threads with a **Rust-first architecture (`crates/bc_zephyr`)** and a minimal C trampoline (`src/main.c`).

All application logic, self-test verification, formatted output, and interactive serial REPL are implemented in pure `#![no_std]` Rust, while C is minimized to a thin ~40-line bridge layer interfacing with Zephyr Devicetree and kernel macros.

## Supported Targets

| Target | Board Identifier | Architecture | Description |
| :--- | :--- | :--- | :--- |
| **QEMU Virt** | `qemu_riscv32` | `riscv32imac-unknown-none-elf` | Automated CI test runner with zero-exit signaling |
| **M5Stamp C3** | `stamp_c3` | `riscv32imc-unknown-none-elf` | ESP32-C3 hardware with USB-Serial interactive REPL |

## Prerequisites

1. A Zephyr v3.7.2 workspace with the Zephyr SDK and `west`. The pinned setup that CI and the
   release workflow use creates one, including Zephyr SDK 0.16.8 with the riscv64 toolchain:
   ```bash
   bash scripts/setup_zephyr_workspace.sh ~/zephyrproject-bc
   # then export the WEST, ZEPHYR_BASE, ZEPHYR_SDK_INSTALL_DIR and ZEPHYR_TOOLCHAIN_VARIANT
   # values the script prints
   ```
   Any existing workspace also works; see the
   [Zephyr Getting Started Guide](https://docs.zephyrproject.org/latest/develop/getting_started/index.html).
2. Rust RISC-V 32 baremetal targets:
   ```bash
   rustup target add riscv32imac-unknown-none-elf riscv32imc-unknown-none-elf
   ```

## Running on QEMU RISC-V 32

To build and run the test suite on QEMU:

```bash
bash scripts/run_zephyr_tests.sh
```

On QEMU the application normally runs the self-tests and exits through the SiFive test device.
To get the interactive REPL on QEMU instead, build with `CONFIG_BC_QEMU_REPL=y`:

```bash
west build -b qemu_riscv32 -s examples/zephyr_app -d build_repl -- -DCONFIG_BC_QEMU_REPL=y
qemu-system-riscv32 -M virt -cpu rv32 -bios none -m 256 -nographic -kernel build_repl/zephyr/zephyr.elf
```

Prebuilt QEMU and M5Stamp C3 images with run and flash scripts are attached to each GitHub release
(`bc_clone-<version>-zephyr.tar.gz`).

## Building for M5Stamp C3 (`stamp_c3`)

To compile the Zephyr application binary for M5Stamp C3:

```bash
bash scripts/build_zephyr_m5stamp_c3.sh
```

## Flashing and Testing on M5Stamp C3 Hardware

To flash the connected M5Stamp C3 (`/dev/ttyACM0`) and run automated self-tests + self-verification:

```bash
bash scripts/flash_and_test_zephyr_m5stamp_c3.sh
```

## Launching Interactive REPL Terminal

To flash and directly open an interactive terminal session where you can type commands:

```bash
bash scripts/repl_zephyr_m5stamp_c3.sh
```

## Interactive REPL on Hardware

When booted on physical hardware (or opened in a serial monitor at 115200 baud):

```text
*** Booting Zephyr OS build v3.7.2 ***

=================================================
  bc_clone (bc_core) on Zephyr RTOS              
=================================================
[Zephyr Kernel] Initialized successfully. Starting bc_core test suite...

  Running: Basic Arithmetic & Precedence       ... [PASS]
  Running: Scale Division                      ... [PASS]
  Running: BigInt Power (2^100)                ... [PASS]
  Running: Recursive Factorial f(20)           ... [PASS]
  Running: Transcendental Pi: 4 * a(1)         ... [PASS]
  Running: Transcendental Exp: e(1)            ... [PASS]
  Running: Transcendental Log: l(2.718281828459045) ... [PASS]
  Running: Base Conversion (Hex to Binary)     ... [PASS]
  Running: Arrays and Dynamic Auto Scoping     ... [PASS]

  Streaming Callback Test: 2^16 = 65536
-------------------------------------------------
ALL ZEPHYR BC_CORE TESTS PASSED (100%)!
=================================================

Entering bc_core Interactive REPL mode (Zephyr RTOS)...
Type bc expressions (e.g. 2^64, scale=10; 4*a(1), define f(x)...)
bc> 2^64
18446744073709551616
bc> define sq(x) { return (x * x); }
bc> sq(25)
625
bc> 
```
