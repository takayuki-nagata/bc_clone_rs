#!/usr/bin/env bash
# SPDX-License-Identifier: MIT
# Flashes the bare-metal bc_clone firmware to an M5Stamp C3 (ESP32-C3) and opens the REPL.
# Requires espflash (cargo install espflash) and, for the console, python3 with pyserial.
#   ./flash.sh                 # port /dev/ttyACM0
#   PORT=/dev/ttyUSB0 ./flash.sh
set -euo pipefail
DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PORT="${PORT:-/dev/ttyACM0}"
espflash flash --chip esp32c3 --port "${PORT}" --non-interactive "${DIR}/m5stamp_c3_bc.elf"
exec "${DIR}/repl.sh"
