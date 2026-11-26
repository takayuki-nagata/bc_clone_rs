#!/usr/bin/env bash
# SPDX-License-Identifier: MIT
set -eo pipefail

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
echo "=== Running the M5Stamp C3 measurement build (RV32IMC) ==="
# The measurement loop, the peak-counting allocator, the stack painting and the panic handler run
# only in this build. At 128 levels every workload must finish; at 160 the 128 KiB heap runs out,
# which must end in the panic handler and exit QEMU with status 1.
probe_log="$(mktemp)"
trap 'rm -f "${probe_log}"' EXIT
bash "$(dirname "${BASH_SOURCE[0]}")/measure_m5stamp_stack.sh" 128 160 | tee "${probe_log}"
at_128="$(sed -n '/^=== Nesting limit 128 ===/,/^exit status/p' "${probe_log}")"
at_160="$(sed -n '/^=== Nesting limit 160 ===/,/^exit status/p' "${probe_log}")"
if ! grep -q '^PROBE DONE' <<<"${at_128}" || grep -q 'FAILED' <<<"${at_128}" \
    || ! grep -q '^exit status 0$' <<<"${at_128}"; then
    echo "FAIL: the measurement at 128 levels did not finish every workload with status 0" >&2
    exit 1
fi
if ! grep -q '^!!! RISC-V BAREMETAL PANIC !!!' <<<"${at_160}" \
    || ! grep -q 'memory allocation of [0-9]* bytes failed' <<<"${at_160}" \
    || grep -q '^PROBE DONE' <<<"${at_160}" || ! grep -q '^exit status 1$' <<<"${at_160}"; then
    echo "FAIL: running out of heap at 160 levels did not panic and exit with status 1" >&2
    exit 1
fi

echo ""
echo "=== All QEMU RISC-V 32 Baremetal Tests PASSED 100%! ==="
