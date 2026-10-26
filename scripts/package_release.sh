#!/usr/bin/env bash
# SPDX-License-Identifier: MIT
set -euo pipefail

# Builds the example targets and packages them with the scripts and READMEs in packaging/.
#
#   scripts/package_release.sh VERSION OUT_DIR COMPONENT...
#
# COMPONENT is one of:
#   wasm     bc_clone-VERSION-wasm-web-app.zip              (needs wasm-bindgen-cli)
#   m5stamp  bc_clone-VERSION-m5stamp-c3-baremetal.tar.gz
#   qemu     bc_clone-VERSION-qemu-riscv32-baremetal.tar.gz
#   zephyr   bc_clone-VERSION-zephyr.tar.gz                 (needs the environment printed by
#                                                            scripts/setup_zephyr_workspace.sh)

if [ "$#" -lt 3 ]; then
    sed -n '4,16p' "$0" >&2
    exit 2
fi

VERSION="$1"
OUT_DIR="$(mkdir -p "$2" && cd "$2" && pwd)"
shift 2

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
STAGE_ROOT="$(mktemp -d)"
trap 'rm -rf "${STAGE_ROOT}"' EXIT

# stage NAME: creates the staging directory for package NAME with its packaging/ templates.
stage() {
    local dir="${STAGE_ROOT}/bc_clone-${VERSION}-$1"
    mkdir -p "${dir}"
    cp -p "${REPO_ROOT}/packaging/$1/"* "${dir}/"
    cp -p "${REPO_ROOT}/LICENSE" "${dir}/"
    echo "${dir}"
}

archive_tgz() {
    tar -C "${STAGE_ROOT}" -czf "${OUT_DIR}/bc_clone-${VERSION}-$1.tar.gz" "bc_clone-${VERSION}-$1"
    echo "Created ${OUT_DIR}/bc_clone-${VERSION}-$1.tar.gz"
}

package_wasm() {
    bash "${REPO_ROOT}/scripts/build_wasm.sh"
    local dir
    dir="$(stage wasm-web-app)"
    cp -rp "${REPO_ROOT}/examples/wasm_web_app/www" "${REPO_ROOT}/examples/wasm_web_app/pkg" "${dir}/"
    (cd "${STAGE_ROOT}" && zip -qr "${OUT_DIR}/bc_clone-${VERSION}-wasm-web-app.zip" \
        "bc_clone-${VERSION}-wasm-web-app")
    echo "Created ${OUT_DIR}/bc_clone-${VERSION}-wasm-web-app.zip"
}

package_m5stamp() {
    bash "${REPO_ROOT}/scripts/build_m5stamp_c3.sh"
    local dir
    dir="$(stage m5stamp-c3-baremetal)"
    cp "${REPO_ROOT}/examples/m5stamp_c3/target/riscv32imc-unknown-none-elf/release/m5stamp_c3_bc" \
        "${dir}/m5stamp_c3_bc.elf"
    archive_tgz m5stamp-c3-baremetal
}

package_qemu() {
    local dir variant
    dir="$(stage qemu-riscv32-baremetal)"
    for variant in imac imc; do
        cargo build --manifest-path "${REPO_ROOT}/Cargo.toml" --package bc_qemu_riscv32 \
            --release --target "riscv32${variant}-unknown-none-elf"
        cp "${REPO_ROOT}/target/riscv32${variant}-unknown-none-elf/release/bc_qemu_riscv32" \
            "${dir}/bc_qemu_riscv32-riscv32${variant}.elf"
    done
    archive_tgz qemu-riscv32-baremetal
}

package_zephyr() {
    : "${WEST:?run scripts/setup_zephyr_workspace.sh and export its variables}"
    : "${ZEPHYR_BASE:?run scripts/setup_zephyr_workspace.sh and export its variables}"
    local app="${REPO_ROOT}/examples/zephyr_app"
    local build="${REPO_ROOT}/target/zephyr-build"
    "${WEST}" -z "${ZEPHYR_BASE}" build -b qemu_riscv32 -p always -s "${app}" -d "${build}/qemu_selftest"
    "${WEST}" -z "${ZEPHYR_BASE}" build -b qemu_riscv32 -p always -s "${app}" -d "${build}/qemu_repl" \
        -- -DCONFIG_BC_QEMU_REPL=y
    "${WEST}" -z "${ZEPHYR_BASE}" build -b stamp_c3 -p always -s "${app}" -d "${build}/stamp_c3"

    local dir
    dir="$(stage zephyr)"
    mkdir -p "${dir}/qemu_riscv32" "${dir}/stamp_c3"
    cp "${build}/qemu_selftest/zephyr/zephyr.elf" "${dir}/qemu_riscv32/zephyr-selftest.elf"
    cp "${build}/qemu_repl/zephyr/zephyr.elf" "${dir}/qemu_riscv32/zephyr-repl.elf"
    cp "${build}/stamp_c3/zephyr/zephyr.bin" "${build}/stamp_c3/zephyr/zephyr.elf" "${dir}/stamp_c3/"
    archive_tgz zephyr
}

for component in "$@"; do
    case "${component}" in
        wasm) package_wasm ;;
        m5stamp) package_m5stamp ;;
        qemu) package_qemu ;;
        zephyr) package_zephyr ;;
        *) echo "unknown component: ${component}" >&2; exit 2 ;;
    esac
done
