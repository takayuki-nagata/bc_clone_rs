#!/usr/bin/env bash
# SPDX-License-Identifier: MIT
set -e

# Script to flash M5Stamp C3 and monitor serial output to run automated verification.
# Requires connected M5Stamp C3 hardware via USB / Serial.

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
APP_DIR="${REPO_ROOT}/examples/m5stamp_c3"
ELF_PATH="${APP_DIR}/target/riscv32imc-unknown-none-elf/release/m5stamp_c3_bc"

echo "=== M5Stamp C3 Flash & Automated Hardware Test ==="

# 1. Build release binary first
"${REPO_ROOT}/scripts/build_m5stamp_c3.sh"

echo ""
echo "=== Flashing to M5Stamp C3 and monitoring serial output ==="

# 2. Flash and monitor output with timeout
TIMEOUT_SEC=20
OUTPUT=$(timeout "${TIMEOUT_SEC}" espflash flash --monitor "${ELF_PATH}" 2>&1 || true)

echo "${OUTPUT}"

if echo "${OUTPUT}" | grep -q "ALL M5STAMP-C3 BC_CORE TESTS PASSED (100%)!"; then
    echo ""
    echo "=== M5Stamp C3 Hardware Tests PASSED 100%! ==="
    exit 0
else
    echo ""
    echo "Error: M5Stamp C3 hardware test suite did not complete with 100% success!"
    exit 1
fi
