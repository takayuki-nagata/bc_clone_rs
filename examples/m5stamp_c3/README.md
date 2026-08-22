# bc_clone_rs on M5Stamp C3 (ESP32-C3 Baremetal)

This example demonstrates running the arbitrary-precision mathematical engine `bc_core` (`#![no_std]` + `alloc`) directly on the **M5Stamp C3** micro-controller board (powered by the Espressif ESP32-C3 RISC-V 32-bit RV32IMC @ 160MHz).

## Prerequisites

1. Rust target for RISC-V 32 IMC:
   ```bash
   rustup target add riscv32imc-unknown-none-elf
   rustup component add rust-src
   ```
2. `espflash` tool for flashing and monitoring over USB-Serial:
   ```bash
   cargo install espflash
   ```

## Building the Application (Cross-Compile & Lint Only)

To build the release ELF binary without physical hardware:

```bash
# Using the automated build script
bash scripts/build_m5stamp_c3.sh

# Or directly using Cargo inside examples/m5stamp_c3
cd examples/m5stamp_c3
cargo build --release --target riscv32imc-unknown-none-elf
```

## Flashing & Automated Hardware Testing

To flash the binary to a connected M5Stamp C3 and automatically verify test results over the serial monitor (115200 bps):

```bash
# Automated flash and test runner
bash scripts/flash_and_test_m5stamp_c3.sh

# Or manual flash & monitor using Cargo
cd examples/m5stamp_c3
cargo run --release
```

## Expected Serial Output

```text
=================================================
  bc_clone (bc_core) on M5Stamp C3 (ESP32-C3)    
=================================================
[ESP32-C3] Initialized successfully @ 160MHz.
[ESP32-C3] 128KB SRAM Heap allocated for bc_core.

  Running: Basic Arithmetic & Precedence       ... [PASS]
  Running: Scale Division                      ... [PASS]
  Running: BigInt Power (2^100)                ... [PASS]
  Running: Recursive Factorial f(20)           ... [PASS]
  Running: Transcendental Pi: 4 * a(1)         ... [PASS]
  Running: Transcendental Exp: e(1)            ... [PASS]
  Running: Transcendental Log: l(2.718281828459045) ... [PASS]
  Running: Transcendental Sine & Cosine        ... [PASS]
  Running: Base Conversion (Hex to Binary)     ... [PASS]
  Running: Arrays and Dynamic Auto Scoping     ... [PASS]
-------------------------------------------------
ALL M5STAMP-C3 BC_CORE TESTS PASSED (100%)!
=================================================

[M5Stamp C3 Heartbeat] Uptime tick #1, bc_core active.
```
