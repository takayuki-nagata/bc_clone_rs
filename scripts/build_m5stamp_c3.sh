#!/usr/bin/env bash
# SPDX-License-Identifier: MIT
set -e

# Script to cross-compile and lint the M5Stamp C3 (ESP32-C3) baremetal application.
# Safe for CI and developer machines without physical hardware connected.

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
APP_DIR="${REPO_ROOT}/examples/m5stamp_c3"

echo "=== Building M5Stamp C3 (ESP32-C3) baremetal application ==="

# Cargo reads `.cargo/config.toml` from the working directory, not from the manifest's: build
# inside the application so that its settings (`force-frame-pointers`, with which the stack use
# is measured) apply wherever the script is run from.
cd "${APP_DIR}"

cargo clippy \
    --target riscv32imc-unknown-none-elf \
    -- -D warnings

cargo build \
    --release \
    --target riscv32imc-unknown-none-elf

echo ""
echo "=== M5Stamp C3 build and lint PASSED successfully! ==="
