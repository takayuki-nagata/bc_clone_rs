#!/usr/bin/env bash
# SPDX-License-Identifier: MIT
set -euo pipefail

# Creates a pinned Zephyr workspace for building examples/zephyr_app. CI and the release workflow
# use it, and developers can too.
#
#   scripts/setup_zephyr_workspace.sh [WORKSPACE_DIR]     (default: ~/zephyrproject-bc)
#
# Installs, inside WORKSPACE_DIR:
#   - a Python venv with west and Zephyr's base requirements;
#   - Zephyr ${ZEPHYR_VERSION} plus only the modules the app needs (hal_espressif for stamp_c3);
#   - Zephyr SDK ${SDK_VERSION} with the riscv64 toolchain, unless ZEPHYR_SDK_INSTALL_DIR already
#     points to an SDK.
# Then prints the environment variables the build scripts read (WEST, ZEPHYR_BASE,
# ZEPHYR_SDK_INSTALL_DIR). Under GitHub Actions it also appends them to $GITHUB_ENV.

ZEPHYR_VERSION="v3.7.2"
SDK_VERSION="0.16.8"
WS="$(mkdir -p "${1:-${HOME}/zephyrproject-bc}" && cd "${1:-${HOME}/zephyrproject-bc}" && pwd)"

echo "=== Zephyr ${ZEPHYR_VERSION} workspace in ${WS} ==="

if [ ! -x "${WS}/.venv/bin/west" ]; then
    python3 -m venv "${WS}/.venv"
    "${WS}/.venv/bin/pip" install --quiet --upgrade pip west
fi
WEST="${WS}/.venv/bin/west"

if [ ! -d "${WS}/.west" ]; then
    "${WEST}" init -m https://github.com/zephyrproject-rtos/zephyr --mr "${ZEPHYR_VERSION}" "${WS}"
fi
(
    cd "${WS}"
    "${WEST}" config manifest.project-filter -- '-.*,+hal_espressif'
    "${WEST}" update --narrow -o=--depth=1
)
"${WS}/.venv/bin/pip" install --quiet -r "${WS}/zephyr/scripts/requirements-base.txt"

if [ -z "${ZEPHYR_SDK_INSTALL_DIR:-}" ]; then
    ZEPHYR_SDK_INSTALL_DIR="${WS}/zephyr-sdk-${SDK_VERSION}"
    if [ ! -d "${ZEPHYR_SDK_INSTALL_DIR}/riscv64-zephyr-elf" ]; then
        echo "=== Installing Zephyr SDK ${SDK_VERSION} (riscv64 toolchain) ==="
        SDK_URL="https://github.com/zephyrproject-rtos/sdk-ng/releases/download/v${SDK_VERSION}/zephyr-sdk-${SDK_VERSION}_linux-x86_64_minimal.tar.xz"
        curl -fsSL "${SDK_URL}" | tar -xJ -C "${WS}"
        "${ZEPHYR_SDK_INSTALL_DIR}/setup.sh" -t riscv64-zephyr-elf -h -c
    fi
fi

ENV_LINES="WEST=${WEST}
ZEPHYR_BASE=${WS}/zephyr
ZEPHYR_SDK_INSTALL_DIR=${ZEPHYR_SDK_INSTALL_DIR}
ZEPHYR_TOOLCHAIN_VARIANT=zephyr"

if [ -n "${GITHUB_ENV:-}" ]; then
    echo "${ENV_LINES}" >> "${GITHUB_ENV}"
fi
echo ""
echo "=== Export these before running the Zephyr build scripts ==="
echo "${ENV_LINES}" | sed 's/^/export /'
