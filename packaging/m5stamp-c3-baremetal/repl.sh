#!/usr/bin/env bash
# SPDX-License-Identifier: MIT
# Opens the serial REPL of an M5Stamp C3 that already runs the bc_clone firmware.
# Requires python3 with pyserial (pip install pyserial). Exit with Ctrl+].
set -euo pipefail
PORT="${PORT:-/dev/ttyACM0}"
echo "bc_clone REPL on ${PORT} @ 115200 bps (press Enter for a prompt, Ctrl+] to exit)"
exec python3 -m serial.tools.miniterm --raw "${PORT}" 115200
