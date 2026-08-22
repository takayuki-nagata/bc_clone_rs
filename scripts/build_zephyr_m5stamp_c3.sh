#!/usr/bin/env bash
# SPDX-License-Identifier: MIT
set -e

# Script to build the Zephyr RTOS bc_core integration app for M5Stamp C3 (stamp_c3).
# Designed to be portable and clean for open-source CI and local environments.

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
APP_DIR="${REPO_ROOT}/examples/zephyr_app"
BUILD_DIR="${APP_DIR}/build_stamp_c3"
BOARD="stamp_c3"

echo "=== Zephyr RTOS bc_core M5Stamp C3 (${BOARD}) Builder ==="

# 1. Discover west tool
if [ -z "${WEST}" ]; then
    if command -v west &> /dev/null; then
        WEST="west"
    elif [ -x "${HOME}/.venv/bin/west" ]; then
        WEST="${HOME}/.venv/bin/west"
    elif [ -x "${HOME}/zephyrproject/.venv/bin/west" ]; then
        WEST="${HOME}/zephyrproject/.venv/bin/west"
    elif [ -x "${HOME}/VUX9K/.venv/bin/west" ]; then
        WEST="${HOME}/VUX9K/.venv/bin/west"
    else
        echo "Error: 'west' tool not found in PATH or standard virtual environments."
        echo "Please install west or set the WEST environment variable (e.g. export WEST=/path/to/west)."
        exit 1
    fi
fi

# Add west's binary directory to PATH
WEST_BIN_DIR="$(dirname "${WEST}")"
if [ -d "${WEST_BIN_DIR}" ]; then
    export PATH="${WEST_BIN_DIR}:${PATH}"
fi

echo "Using west: ${WEST}"

# 2. Discover ZEPHYR_BASE if not explicitly set
if [ -z "${ZEPHYR_BASE}" ]; then
    if [ -d "${HOME}/zephyrproject/zephyr" ]; then
        export ZEPHYR_BASE="${HOME}/zephyrproject/zephyr"
    elif [ -d "${HOME}/VUX9K/zephyr_workspace/zephyr" ]; then
        export ZEPHYR_BASE="${HOME}/VUX9K/zephyr_workspace/zephyr"
    else
        echo "Error: ZEPHYR_BASE environment variable is not set and could not be auto-detected."
        echo "Please set ZEPHYR_BASE (e.g. export ZEPHYR_BASE=/path/to/zephyr)."
        exit 1
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

# 4. Clean and build Zephyr application for stamp_c3
echo ""
echo "=== Building Zephyr Application for ${BOARD} ==="
"${WEST}" -z "${ZEPHYR_BASE}" build -b "${BOARD}" -p always -s "${APP_DIR}" -d "${BUILD_DIR}"

if [ -f "${BUILD_DIR}/zephyr/zephyr.bin" ]; then
    echo ""
    echo "=== Zephyr M5Stamp C3 (${BOARD}) build PASSED successfully! ==="
    echo "Output Binary: ${BUILD_DIR}/zephyr/zephyr.bin"
    exit 0
else
    echo ""
    echo "Error: Build output zephyr.bin not found!"
    exit 1
fi
