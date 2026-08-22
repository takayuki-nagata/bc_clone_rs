#!/usr/bin/env bash
# SPDX-License-Identifier: MIT
set -e

# Script to cross-compile and lint the M5Stamp C3 (ESP32-C3) baremetal application.
# Safe for CI and developer machines without physical hardware connected.

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
APP_DIR="${REPO_ROOT}/examples/m5stamp_c3"

echo "=== Building M5Stamp C3 (ESP32-C3) baremetal application ==="

cargo clippy \
    --manifest-path "${APP_DIR}/Cargo.toml" \
    --target riscv32imc-unknown-none-elf \
    -- -D warnings

cargo build \
    --manifest-path "${APP_DIR}/Cargo.toml" \
    --release \
    --target riscv32imc-unknown-none-elf

echo ""
echo "=== M5Stamp C3 build and lint PASSED successfully! ==="
