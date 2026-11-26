#!/usr/bin/env bash
# SPDX-License-Identifier: MIT
set -e

# Script to build and run the Zephyr RTOS bc_core integration app on QEMU RISC-V 32.
# Designed to be portable and clean for open-source CI and local environments.

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
APP_DIR="${REPO_ROOT}/examples/zephyr_app"
BUILD_DIR="${APP_DIR}/build"

echo "=== Zephyr RTOS bc_core Integration Runner ==="

# 1. Discover west tool dynamically
if [ -z "${WEST}" ]; then
    if command -v west &> /dev/null; then
        WEST="west"
    elif [ -n "${VIRTUAL_ENV}" ] && [ -x "${VIRTUAL_ENV}/bin/west" ]; then
        WEST="${VIRTUAL_ENV}/bin/west"
    elif [ -x "${HOME}/.venv/bin/west" ]; then
        WEST="${HOME}/.venv/bin/west"
    elif [ -x "${HOME}/zephyrproject/.venv/bin/west" ]; then
        WEST="${HOME}/zephyrproject/.venv/bin/west"
    else
        # Dynamic discovery under user home directory
        WEST_CANDIDATE=$(find "${HOME}" -maxdepth 4 -path "*/.venv/bin/west" 2>/dev/null | head -n 1 || true)
        if [ -n "${WEST_CANDIDATE}" ] && [ -x "${WEST_CANDIDATE}" ]; then
            WEST="${WEST_CANDIDATE}"
        else
            echo "Error: 'west' tool not found in PATH or standard virtual environments."
            echo "Please install west or set the WEST environment variable (e.g. export WEST=/path/to/west)."
            exit 1
        fi
    fi
fi

# Add west's binary directory to PATH if it contains tools like cmake / ninja
WEST_BIN_DIR="$(dirname "${WEST}")"
if [ -d "${WEST_BIN_DIR}" ]; then
    export PATH="${WEST_BIN_DIR}:${PATH}"
fi

echo "Using west: ${WEST}"

# 2. Discover ZEPHYR_BASE if not explicitly set
if [ -z "${ZEPHYR_BASE}" ]; then
    if [ -d "${HOME}/zephyrproject/zephyr" ]; then
        export ZEPHYR_BASE="${HOME}/zephyrproject/zephyr"
    else
        ZEPHYR_CANDIDATE=$(find "${HOME}" -maxdepth 4 -type d -path "*/zephyr/subsys" 2>/dev/null | head -n 1 || true)
        if [ -n "${ZEPHYR_CANDIDATE}" ]; then
            export ZEPHYR_BASE="$(dirname "${ZEPHYR_CANDIDATE}")"
        else
            echo "Error: ZEPHYR_BASE environment variable is not set and could not be auto-detected."
            echo "Please set ZEPHYR_BASE (e.g. export ZEPHYR_BASE=/path/to/zephyr)."
            exit 1
        fi
    fi
fi

echo "Using ZEPHYR_BASE: ${ZEPHYR_BASE}"

# 3. Configure Zephyr Toolchain
if [ -z "${ZEPHYR_TOOLCHAIN_VARIANT}" ]; then
    export ZEPHYR_TOOLCHAIN_VARIANT="zephyr"
fi

if [ -z "${ZEPHYR_SDK_INSTALL_DIR}" ]; then
    SDK_CANDIDATE=$(find "${HOME}/.local" /opt -maxdepth 2 -name "zephyr-sdk-*" -type d 2>/dev/null | head -n 1 || true)
    if [ -n "${SDK_CANDIDATE}" ]; then
        export ZEPHYR_SDK_INSTALL_DIR="${SDK_CANDIDATE}"
    fi
fi

if [ -n "${ZEPHYR_SDK_INSTALL_DIR}" ]; then
    echo "Using ZEPHYR_SDK_INSTALL_DIR: ${ZEPHYR_SDK_INSTALL_DIR}"
fi

# 4. Self-tests: build and run the self-test image. It exits QEMU through the SiFive test
# device, with status 0 only if every self-test passed (the no_std heap, its critical section
# and the report to the test device run here and nowhere else).
echo "=== Building Zephyr Application for qemu_riscv32 ==="
"${WEST}" -z "${ZEPHYR_BASE}" build -b qemu_riscv32 -p always -s "${APP_DIR}" -d "${BUILD_DIR}"

QEMU=(qemu-system-riscv32 -M virt -cpu rv32 -bios none -m 256)

echo ""
echo "=== Running Zephyr Application on QEMU RISC-V 32 ==="
# The timeout only guards against a firmware that hangs.
set +e
OUTPUT=$(timeout 600 "${QEMU[@]}" -kernel "${BUILD_DIR}/zephyr/zephyr.elf" -nographic 2>&1)
STATUS=$?
set -e

echo "${OUTPUT}"

if ! echo "${OUTPUT}" | grep -q "ALL ZEPHYR BC_CORE TESTS PASSED (100%)!"; then
    echo ""
    echo "Error: Zephyr test suite did not complete with 100% success!"
    exit 1
fi
if [ "${STATUS}" -ne 0 ]; then
    echo ""
    echo "Error: QEMU exited with status ${STATUS}, not through the test device's pass value"
    exit 1
fi
echo "=== Zephyr RTOS bc_core self-tests PASSED (QEMU exit status 0) ==="

# 5. REPL: build the image with CONFIG_BC_QEMU_REPL=y and type into its serial console through
# a pair of FIFOs. This runs the REPL on Zephyr's UART, and exhausting the 64 KiB heap reaches
# the panic handler, which prints the panic and must then halt: QEMU keeps running until killed.
REPL_BUILD_DIR="${APP_DIR}/build_repl"
echo ""
echo "=== Building the REPL image for qemu_riscv32 ==="
"${WEST}" -z "${ZEPHYR_BASE}" build -b qemu_riscv32 -p always -s "${APP_DIR}" -d "${REPL_BUILD_DIR}" \
    -- -DCONFIG_BC_QEMU_REPL=y

FIFO_DIR="$(mktemp -d)"
QEMU_PID=""
CAT_PID=""
cleanup() {
    [ -n "${QEMU_PID}" ] && kill "${QEMU_PID}" 2>/dev/null || true
    [ -n "${CAT_PID}" ] && kill "${CAT_PID}" 2>/dev/null || true
    rm -rf "${FIFO_DIR}"
}
trap cleanup EXIT
mkfifo "${FIFO_DIR}/serial.in" "${FIFO_DIR}/serial.out"
LOG="${FIFO_DIR}/serial.log"
: > "${LOG}"

echo "=== Running the REPL on QEMU RISC-V 32 ==="
"${QEMU[@]}" -kernel "${REPL_BUILD_DIR}/zephyr/zephyr.elf" -display none -monitor none \
    -serial "pipe:${FIFO_DIR}/serial" &
QEMU_PID=$!
cat "${FIFO_DIR}/serial.out" > "${LOG}" &
CAT_PID=$!
# Read-write, so that opening the FIFO does not block if QEMU failed to start.
exec 3<> "${FIFO_DIR}/serial.in"

# wait_for TEXT SECONDS [-x]: waits until the console has printed TEXT (with -x, as a whole line).
wait_for() {
    local i
    for ((i = 0; i < $2 * 10; i++)); do
        # The console ends lines with \r\n.
        if tr -d '\r' < "${LOG}" | grep -qF ${3:-} -- "$1"; then
            return 0
        fi
        if ! kill -0 "${QEMU_PID}" 2>/dev/null; then
            break
        fi
        sleep 0.1
    done
    echo "${LOG}:"
    cat "${LOG}"
    echo ""
    echo "Error: the REPL did not print '$1'"
    exit 1
}

wait_for "bc> " 600
printf '2^10\r' >&3
# A whole line, so that the commit hash in the banner cannot match.
wait_for "1024" 60 -x
# 2^(2^20) needs more than the 64 KiB heap: the allocation error handler panics.
printf '2^(2^20)\r' >&3
wait_for "[Zephyr Rust Panic]" 300
wait_for "memory allocation" 10
# Halted: QEMU is still running and prints nothing more (no reboot, no new prompt).
sleep 1
size=$(wc -c < "${LOG}")
sleep 3
if ! kill -0 "${QEMU_PID}" 2>/dev/null || [ "$(wc -c < "${LOG}")" -ne "${size}" ]; then
    cat "${LOG}"
    echo "Error: the application did not halt in the panic handler"
    exit 1
fi
exec 3>&-
cat "${LOG}"
echo ""
echo "=== Zephyr RTOS bc_core Tests PASSED 100%! ==="
