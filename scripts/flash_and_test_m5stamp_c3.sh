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
espflash flash --port "${PORT}" --non-interactive "${ELF_PATH}"

echo ""
echo "=== Monitoring M5Stamp C3 Serial Output ==="
python3 -c "
import serial, time, sys

try:
    ser = serial.Serial('${PORT}', 115200, timeout=1)
except Exception as e:
    print(f'Error opening serial port: {e}')
    sys.exit(1)

# Reset ESP32-C3 via DTR/RTS
ser.dtr = False
ser.rts = True
time.sleep(0.1)
ser.dtr = True
ser.rts = False
time.sleep(0.1)
ser.dtr = False
ser.rts = False

start = time.time()
while time.time() - start < 8:
    line = ser.readline().decode('utf-8', errors='replace')
    if line:
        print(line, end='')
        if 'ALL M5STAMP-C3 BC_CORE TESTS PASSED (100%)!' in line:
            print('\n=== M5Stamp C3 Hardware Tests PASSED 100%! ===')
            ser.close()
            sys.exit(0)

ser.close()
print('\nError: Test success message not detected within timeout!')
sys.exit(1)
"
