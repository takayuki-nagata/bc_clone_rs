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

## Host Unit Tests

The application's decisions (the self-test report, the stack budget and the serial REPL) are in
its library, which runs on the host. Run the tests from the repository root, where this
directory's `.cargo/config.toml` (which selects the ESP32-C3) does not apply:

```bash
cargo test --manifest-path examples/m5stamp_c3/Cargo.toml --lib
bash scripts/run_miri_tests.sh m5stamp
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
  bc_clone 0.5.0 (a916de2)
=================================================
[ESP32-C3] Initialized successfully @ 160MHz.
[ESP32-C3] 128KB SRAM Heap allocated for bc_core.

  Running: Basic Arithmetic & Precedence       ... [PASS]
  Running: Scale Division                      ... [PASS]
  Running: BigInt Power (2^100)                ... [PASS]
  Running: Power with an exponent beyond u32   ... [PASS]
  Running: Recursive Factorial f(20)           ... [PASS]
  Running: Transcendental Pi: 4 * a(1)         ... [PASS]
  Running: Transcendental Exp: e(1)            ... [PASS]
  Running: Transcendental Log: l(2.718281828459045) ... [PASS]
  Running: Transcendental Sine & Cosine        ... [PASS]
  Running: Base Conversion (Hex to Binary)     ... [PASS]
  Running: Arrays and Dynamic Auto Scoping     ... [PASS]
  Running: Error Recovery (Div by Zero)        ... [PASS]
  Running: Scale Limit on 32-bit usize         ... [PASS]
  Running: Nesting Limit: Recursion            ... [PASS]
  Running: Nesting Limit: Recursion Too Deep   ... [PASS]
  Running: Nesting Limit: Parentheses          ... [PASS]
  Running: Nesting Limit: Parentheses Too Deep ... [PASS]
  Running: Nesting Limit: Blocks               ... [PASS]
  Running: limit, parentheses                  ... [PASS]
  ...
  Running: limit, long output at the bottom    ... [PASS]
[ESP32-C3] Stack high-water mark: 34360 of 185152 bytes.
[ESP32-C3] Heap high-water mark: 88640 of 131072 bytes.
-------------------------------------------------
ALL M5STAMP-C3 BC_CORE TESTS PASSED (100%)!
=================================================

Entering bc_core Interactive REPL mode...
bc_clone 0.5.0 (a916de2)
Type bc expressions (e.g. 2^64, scale=10; 4*a(1), define f(x)...)
bc> 2^64
18446744073709551616
bc> scale = 10; 4 * a(1)
3.1415926532
bc> define sq(x) { return (x * x) }; sq(12)
144
bc> 
```
