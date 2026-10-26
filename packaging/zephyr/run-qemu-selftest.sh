#!/usr/bin/env bash
# SPDX-License-Identifier: MIT
# Runs the bc_clone self-tests on Zephyr in QEMU RISC-V 32. The exit status is 0 if they pass.
# Requires qemu-system-riscv32.
set -euo pipefail
DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
exec qemu-system-riscv32 -M virt -cpu rv32 -bios none -m 256 -nographic \
    -kernel "${DIR}/qemu_riscv32/zephyr-selftest.elf"
