#!/usr/bin/env bash
# SPDX-License-Identifier: MIT
set -e

# Measures the stack and heap use of the nesting workloads for the M5Stamp C3 on QEMU, at the
# nesting limits given as arguments. The build has the optimization settings of
# examples/m5stamp_c3 and its 128 KiB heap, but it is not the application's ELF.

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "${REPO_ROOT}"

export CARGO_TARGET_DIR="${REPO_ROOT}/target/m5probe"
export RUSTFLAGS="-C force-frame-pointers"
export CARGO_PROFILE_RELEASE_OPT_LEVEL=s
export CARGO_PROFILE_RELEASE_LTO=fat
export CARGO_PROFILE_RELEASE_CODEGEN_UNITS=1
cargo build --package bc_qemu_riscv32 --features m5stamp-probe \
    --target riscv32imc-unknown-none-elf --release --quiet

for limit in "${@:-128}"; do
    echo "=== Nesting limit ${limit} ==="
    # The limit and the first workload are read from these addresses (`run_probe`).
    qemu-system-riscv32 -M virt -cpu rv32 -bios none -nographic \
        -kernel "${CARGO_TARGET_DIR}/riscv32imc-unknown-none-elf/release/bc_qemu_riscv32" \
        -device "loader,addr=0x80fffff0,data=${limit},data-len=4" \
        -device "loader,addr=0x80fffff4,data=0,data-len=4" </dev/null || true
done
