#!/usr/bin/env bash
# SPDX-License-Identifier: MIT
set -e

# Script to build and run baremetal RISC-V 32 automated tests on QEMU virt machine.

echo "=== Building bc_qemu_riscv32 for riscv32imac-unknown-none-elf (RV32IMAC QEMU Virt) ==="
cargo build --package bc_qemu_riscv32 --target riscv32imac-unknown-none-elf --release --quiet

echo "=== Running Baremetal Tests on QEMU (RV32IMAC) ==="
qemu-system-riscv32 \
    -M virt \
    -cpu rv32 \
    -bios none \
    -kernel target/riscv32imac-unknown-none-elf/release/bc_qemu_riscv32 \
    -nographic

echo ""
echo "=== Building bc_qemu_riscv32 for riscv32imc-unknown-none-elf (RV32IMC / ESP32-C3 compatible) ==="
cargo build --package bc_qemu_riscv32 --target riscv32imc-unknown-none-elf --release --quiet

echo "=== Running Baremetal Tests on QEMU (RV32IMC) ==="
qemu-system-riscv32 \
    -M virt \
    -cpu rv32 \
    -bios none \
    -kernel target/riscv32imc-unknown-none-elf/release/bc_qemu_riscv32 \
    -nographic

echo ""
echo "=== All QEMU RISC-V 32 Baremetal Tests PASSED 100%! ==="
