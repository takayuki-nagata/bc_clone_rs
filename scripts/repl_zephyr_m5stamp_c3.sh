#!/usr/bin/env bash
# SPDX-License-Identifier: MIT
set -e

# Script to flash M5Stamp C3 with Zephyr RTOS and start an interactive serial REPL terminal.
# Requires connected M5Stamp C3 hardware via USB / Serial.

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
APP_DIR="${REPO_ROOT}/examples/zephyr_app"
BUILD_DIR="${APP_DIR}/build_stamp_c3"
BIN_PATH="${BUILD_DIR}/zephyr/zephyr.bin"

PORT="${ESPFLASH_PORT:-/dev/ttyACM0}"

echo "=== Zephyr RTOS M5Stamp C3 Interactive REPL ==="

# 1. Build Zephyr application for stamp_c3
"${REPO_ROOT}/scripts/build_zephyr_m5stamp_c3.sh"

if [ ! -e "${PORT}" ]; then
    echo ""
    echo "Error: Target port ${PORT} not connected."
    exit 1
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
echo "=================================================================="
echo "  Connected to M5Stamp C3 Zephyr REPL Console (${PORT} @ 115200bps)"
echo "  Press CTRL+] or CTRL+C twice to exit."
echo "=================================================================="
echo ""

# Launch interactive serial terminal via pyserial miniterm
python3 -m serial.tools.miniterm --raw "${PORT}" 115200
