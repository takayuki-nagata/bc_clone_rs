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

# 4. Clean and build Zephyr application
echo "=== Building Zephyr Application for qemu_riscv32 ==="
"${WEST}" -z "${ZEPHYR_BASE}" build -b qemu_riscv32 -p always -s "${APP_DIR}" -d "${BUILD_DIR}"

echo ""
echo "=== Running Zephyr Application on QEMU RISC-V 32 ==="
OUTPUT=$(qemu-system-riscv32 \
    -M virt \
    -cpu rv32 \
    -bios none \
    -m 256 \
    -kernel "${BUILD_DIR}/zephyr/zephyr.elf" \
    -nographic 2>&1 || true)

echo "${OUTPUT}"

if echo "${OUTPUT}" | grep -q "ALL ZEPHYR BC_CORE TESTS PASSED (100%)!"; then
    echo ""
    echo "=== Zephyr RTOS bc_core Tests PASSED 100%! ==="
    exit 0
else
    echo ""
    echo "Error: Zephyr test suite did not complete with 100% success!"
    exit 1
fi
