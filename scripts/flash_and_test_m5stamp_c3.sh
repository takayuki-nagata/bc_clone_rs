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
passed=0
for _ in $(seq 90); do
    sleep 1
    if grep -q 'ALL M5STAMP-C3 BC_CORE TESTS PASSED (100%)!' "${log}" && grep -q '^bc> ' "${log}"; then
        passed=1
        # Anything the REPL received before its first prompt is discarded; a diagnostic here
        # would mean that input reached it (such as the host's terminal echoing the report).
        sleep 2
        break
    fi
    if grep -q -e 'SOME M5STAMP-C3 BC_CORE TESTS FAILED!' -e 'M5Stamp C3 PANIC' "${log}"; then
        break
    fi
done
kill "${monitor}" 2>/dev/null || true
wait "${monitor}" 2>/dev/null || true
cat "${log}"
if [ "${passed}" != 1 ]; then
    echo ""
    echo "Error: Test success message not detected within timeout!"
    exit 1
fi
if sed -n '/^Entering bc_core Interactive REPL/,$p' "${log}" | grep -q 'standard_in'; then
    echo ""
    echo "Error: the REPL received input before anything was typed"
    exit 1
fi

echo ""
echo "=== Checking the REPL and the panic handler ==="
# Types into the REPL without resetting the board (DTR and RTS stay low): the initial scale,
# evaluator output, then a number larger than the 128 KiB heap, which must end in the panic
# handler with nothing printed after it.
python3 - "${PORT}" <<'PY'
import serial, sys, time

port = serial.Serial()
port.port, port.baudrate, port.timeout = sys.argv[1], 115200, 0.2
port.dtr = port.rts = False
port.open()
seen = b""

def read_until(marker, seconds):
    global seen
    end = time.time() + seconds
    while time.time() < end:
        seen += port.read(4096)
        if marker in seen:
            return True
    return False

def fail(message):
    sys.stdout.write(seen.decode("utf-8", "replace"))
    print(f"\nError: {message}")
    sys.exit(1)

# The board may restart when the port is opened; wait for a prompt either way.
port.write(b"\n")
if not read_until(b"bc> ", 60):
    fail("no REPL prompt")
for line, expected in [(b"scale", b"\r\n20\r\n"), (b"2^10", b"\r\n1024\r\n")]:
    seen = b""
    port.write(line + b"\n")
    if not (read_until(b"bc> ", 10) and expected in seen):
        fail(f"{line.decode()}: expected {expected!r}")
    print(f"  {line.decode()} -> {expected.strip().decode()} [PASS]")
seen = b""
port.write(b"2^(2^20)\n")
if not read_until(b"[M5Stamp C3 PANIC]", 60) or not read_until(b"memory allocation", 5):
    fail("running out of heap did not reach the panic handler")
read_until(b"\0", 2)
after = len(seen)
read_until(b"\0", 3)
if len(seen) != after:
    fail("output after the panic")
print("  2^(2^20) -> [M5Stamp C3 PANIC] memory allocation ... [PASS]")
port.close()
PY

echo ""
echo "=== M5Stamp C3 Hardware Tests PASSED 100%! ==="
