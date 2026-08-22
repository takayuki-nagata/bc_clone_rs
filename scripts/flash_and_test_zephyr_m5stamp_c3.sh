#!/usr/bin/env bash
# SPDX-License-Identifier: MIT
set -e

# Script to flash M5Stamp C3 with Zephyr RTOS and monitor serial output to verify tests and interactive REPL.
# Requires connected M5Stamp C3 hardware via USB / Serial.

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
APP_DIR="${REPO_ROOT}/examples/zephyr_app"
BUILD_DIR="${APP_DIR}/build_stamp_c3"
BIN_PATH="${BUILD_DIR}/zephyr/zephyr.bin"

PORT="${ESPFLASH_PORT:-/dev/ttyACM0}"

echo "=== Zephyr RTOS M5Stamp C3 Flash & Automated Hardware Test ==="

# 1. Build Zephyr application for stamp_c3 first
"${REPO_ROOT}/scripts/build_zephyr_m5stamp_c3.sh"

if [ ! -e "${PORT}" ]; then
    echo ""
    echo "Notice: Target port ${PORT} not connected. Skipping physical flash test."
    exit 0
fi

# 2. Discover Python with esptool support
PYTHON_EXE="python3"
if [ -x "${HOME}/VUX9K/.venv/bin/python3" ]; then
    PYTHON_EXE="${HOME}/VUX9K/.venv/bin/python3"
elif [ -x "${HOME}/zephyrproject/.venv/bin/python3" ]; then
    PYTHON_EXE="${HOME}/zephyrproject/.venv/bin/python3"
fi

# Discover esptool.py
ESPTOOL_PY=""
if command -v esptool.py &>/dev/null; then
    ESPTOOL_PY="esptool.py"
elif [ -n "${ZEPHYR_BASE}" ] && [ -f "${ZEPHYR_BASE}/../modules/hal/espressif/tools/esptool_py/esptool.py" ]; then
    ESPTOOL_PY="${ZEPHYR_BASE}/../modules/hal/espressif/tools/esptool_py/esptool.py"
elif [ -f "${HOME}/zephyrproject/modules/hal/espressif/tools/esptool_py/esptool.py" ]; then
    ESPTOOL_PY="${HOME}/zephyrproject/modules/hal/espressif/tools/esptool_py/esptool.py"
else
    echo "Error: esptool.py could not be found."
    exit 1
fi

echo ""
echo "=== Flashing Zephyr RTOS to M5Stamp C3 on ${PORT} ==="
"${PYTHON_EXE}" "${ESPTOOL_PY}" --chip esp32c3 --port "${PORT}" --baud 921600 write_flash 0x0 "${BIN_PATH}"

echo ""
echo "=== Monitoring M5Stamp C3 Zephyr Serial Output & Interactive REPL ==="
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
found_tests_passed = False
found_repl_prompt = False

while time.time() - start < 30:
    line = ser.readline().decode('utf-8', errors='replace')
    if line:
        print(line, end='')
        if 'ALL ZEPHYR BC_CORE TESTS PASSED (100%)!' in line:
            found_tests_passed = True
        if 'bc>' in line or 'Entering bc_core Interactive REPL' in line:
            found_repl_prompt = True

    if found_tests_passed and found_repl_prompt:
        break

if not (found_tests_passed and found_repl_prompt):
    print('\nError: Test success message or REPL prompt not detected within timeout!')
    ser.close()
    sys.exit(1)

print('\n--- Verifying Interactive REPL input/output over serial ---')

def send_and_expect(cmd, expected):
    print(f'  Sending: {cmd.strip()}')
    ser.write(cmd.encode('utf-8'))
    ser.flush()
    time.sleep(0.2)
    resp = ''
    t0 = time.time()
    while time.time() - t0 < 3:
        if ser.in_waiting:
            resp += ser.read(ser.in_waiting).decode('utf-8', errors='replace')
            if expected in resp:
                print(f'  [PASS] Got response containing: \"{expected}\"')
                return True
        time.sleep(0.05)
    print(f'  [FAIL] Expected: \"{expected}\", received:\n{resp}')
    return False

if not send_and_expect('2^32\r\n', '4294967296'):
    ser.close()
    sys.exit(1)

if not send_and_expect('define cube(x) { return (x^3); }\r\n', 'bc>'):
    ser.close()
    sys.exit(1)

if not send_and_expect('cube(5)\r\n', '125'):
    ser.close()
    sys.exit(1)

if not send_and_expect('scale = 6; 22 / 7\r\n', '3.142857'):
    ser.close()
    sys.exit(1)

print('\n=== Zephyr M5Stamp C3 Hardware & REPL Tests PASSED 100%! ===')
ser.close()
"
