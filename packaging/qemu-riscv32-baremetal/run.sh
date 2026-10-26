#!/usr/bin/env bash
# SPDX-License-Identifier: MIT
# Boots the bare-metal bc_clone self-test on QEMU's RISC-V 32 "virt" machine.
# The exit status is 0 if every self-test passed. Requires qemu-system-riscv32.
#   ./run.sh          # riscv32imac build
#   ./run.sh imc      # riscv32imc build (ESP32-C3 compatible ISA)
set -euo pipefail
DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
VARIANT="${1:-imac}"
case "${VARIANT}" in
    imac | imc) ;;
    *) echo "usage: $0 [imac|imc]" >&2; exit 2 ;;
esac
exec qemu-system-riscv32 -M virt -cpu rv32 -bios none -nographic \
    -kernel "${DIR}/bc_qemu_riscv32-riscv32${VARIANT}.elf"
