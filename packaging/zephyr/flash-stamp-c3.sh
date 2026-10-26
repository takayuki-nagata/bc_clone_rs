#!/usr/bin/env bash
# SPDX-License-Identifier: MIT
# Flashes the Zephyr build of bc_clone to an M5Stamp C3 (ESP32-C3) and opens the REPL.
# Requires esptool (pip install esptool) and pyserial.
#   ./flash-stamp-c3.sh                 # port /dev/ttyACM0
#   PORT=/dev/ttyUSB0 ./flash-stamp-c3.sh
set -euo pipefail
DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PORT="${PORT:-/dev/ttyACM0}"
python3 -m esptool --chip esp32c3 --port "${PORT}" --baud 921600 \
    write_flash 0x0 "${DIR}/stamp_c3/zephyr.bin"
exec "${DIR}/repl-stamp-c3.sh"
