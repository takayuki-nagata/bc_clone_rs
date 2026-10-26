#!/usr/bin/env bash
# SPDX-License-Identifier: MIT
# Runs the Zephyr build of bc_clone on QEMU RISC-V 32: self-tests, then the interactive REPL.
# Exit QEMU with Ctrl+A then X. Requires qemu-system-riscv32.
set -euo pipefail
DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
echo "Starting Zephyr on QEMU (exit with Ctrl+A then X)..."
exec qemu-system-riscv32 -M virt -cpu rv32 -bios none -m 256 -nographic \
    -kernel "${DIR}/qemu_riscv32/zephyr-repl.elf"
