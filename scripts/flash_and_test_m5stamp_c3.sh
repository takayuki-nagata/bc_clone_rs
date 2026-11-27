#!/usr/bin/env bash
# SPDX-License-Identifier: MIT
set -e

# Script to flash M5Stamp C3 and monitor serial output to run automated verification.
# Requires connected M5Stamp C3 hardware via USB / Serial.

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
APP_DIR="${REPO_ROOT}/examples/m5stamp_c3"
ELF_PATH="${APP_DIR}/target/riscv32imc-unknown-none-elf/release/m5stamp_c3_bc"

PORT="${ESPFLASH_PORT:-/dev/ttyACM0}"

echo "=== M5Stamp C3 Flash & Automated Hardware Test ==="

# 1. Build release binary first
"${REPO_ROOT}/scripts/build_m5stamp_c3.sh"

if [ ! -e "${PORT}" ]; then
    echo ""
    echo "Notice: Target port ${PORT} not connected. Skipping physical flash test."
    exit 0
fi

echo ""
echo "=== Flashing to M5Stamp C3 on ${PORT} ==="
# The board's USB-Serial/JTAG port is reset through USB: espflash's default reset (DTR/RTS) does
# not reach it, and the DTR/RTS sequence boots the chip into download mode.
espflash flash --port "${PORT}" --before usb-reset --non-interactive "${ELF_PATH}"

echo ""
echo "=== Monitoring M5Stamp C3 Serial Output ==="
# The monitor resets the board and attaches a moment after it boots, so the first lines of the
# report may be missing; the verdict line is printed only if every test passed.
log="$(mktemp)"
trap 'rm -f "${log}"' EXIT
timeout 90 espflash monitor --port "${PORT}" --before usb-reset --non-interactive >"${log}" 2>&1 &
monitor=$!
for _ in $(seq 90); do
    sleep 1
    if grep -q 'ALL M5STAMP-C3 BC_CORE TESTS PASSED (100%)!' "${log}"; then
        kill "${monitor}" 2>/dev/null || true
        cat "${log}"
        echo ""
        echo "=== M5Stamp C3 Hardware Tests PASSED 100%! ==="
        exit 0
    fi
    if grep -q -e 'SOME M5STAMP-C3 BC_CORE TESTS FAILED!' -e 'M5Stamp C3 PANIC' "${log}"; then
        break
    fi
done
kill "${monitor}" 2>/dev/null || true
cat "${log}"
echo ""
echo "Error: Test success message not detected within timeout!"
exit 1
