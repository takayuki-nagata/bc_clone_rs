#!/usr/bin/env bash
# SPDX-License-Identifier: MIT
set -e

# Script to flash M5Stamp C3 (baremetal) and start an interactive serial REPL terminal.
# Requires connected M5Stamp C3 hardware via USB / Serial.

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
APP_DIR="${REPO_ROOT}/examples/m5stamp_c3"
ELF_PATH="${APP_DIR}/target/riscv32imc-unknown-none-elf/release/m5stamp_c3_bc"

PORT="${ESPFLASH_PORT:-/dev/ttyACM0}"

echo "=== M5Stamp C3 (Baremetal) Interactive REPL ==="

# 1. Build release binary
"${REPO_ROOT}/scripts/build_m5stamp_c3.sh"

if [ ! -e "${PORT}" ]; then
    echo ""
    echo "Error: Target port ${PORT} not connected."
    exit 1
fi

echo ""
echo "=== Flashing to M5Stamp C3 on ${PORT} ==="
espflash flash --port "${PORT}" --non-interactive "${ELF_PATH}"

echo ""
echo "=================================================================="
echo "  Connected to M5Stamp C3 Baremetal REPL Console (${PORT} @ 115200bps)"
echo "  Press CTRL+] or CTRL+C twice to exit."
echo "=================================================================="
echo ""

python3 -m serial.tools.miniterm --raw "${PORT}" 115200
