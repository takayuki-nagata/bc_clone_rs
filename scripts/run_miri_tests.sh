#!/usr/bin/env bash
# SPDX-License-Identifier: MIT
set -euo pipefail

# Script to run Miri Undefined Behavior (UB) and memory-safety verification
# across bc_core, bc_c_api, bc_zephyr, bc_qemu_riscv32, bc_clone (bc_cli), bc_build_info, the
# M5Stamp C3 application's library (examples/m5stamp_c3) and the Wasm binding
# (examples/wasm_web_app/crate), the last two outside the workspace.
#
# usage: run_miri_tests.sh                       runs every stage
#        run_miri_tests.sh STAGE [-- ARGS...]    runs one stage, passing ARGS to the test binary
#                                                (a test-name filter, `--skip NAME`, ...)
# STAGE is one of: c_api, core, zephyr, qemu, cli, build_info, m5stamp, wasm, c_api_tree. CI runs the stages as separate jobs and
# splits `core`, the slowest, by test name.

MIRI_TOOLCHAIN="${MIRI_TOOLCHAIN:-nightly}"
STAGES=(c_api core zephyr qemu cli build_info m5stamp wasm c_api_tree)

stage="${1:-all}"
[ $# -gt 0 ] && shift
if [ $# -gt 0 ]; then
    if [ "$1" != "--" ] || [ "$stage" = "all" ]; then
        echo "usage: $0 [STAGE [-- ARGS...]]  (STAGE: ${STAGES[*]})" >&2
        exit 2
    fi
    shift
fi
if [ "$stage" != "all" ] && [[ ! " ${STAGES[*]} " =~ " ${stage} " ]]; then
    echo "unknown stage '${stage}' (expected one of: ${STAGES[*]})" >&2
    exit 2
fi

if ! rustup toolchain list | grep -q "^${MIRI_TOOLCHAIN}"; then
    echo "Installing Rust ${MIRI_TOOLCHAIN} toolchain with miri and rust-src components..."
    rustup toolchain install "${MIRI_TOOLCHAIN}" --profile minimal --component miri --component rust-src --no-self-update
else
    if ! cargo "+${MIRI_TOOLCHAIN}" miri --version >/dev/null 2>&1; then
        echo "Installing miri component for ${MIRI_TOOLCHAIN}..."
        rustup component add miri --toolchain "${MIRI_TOOLCHAIN}"
    fi
    if ! rustup component list --toolchain "${MIRI_TOOLCHAIN}" --installed | grep -q "^rust-src"; then
        echo "Installing rust-src component for ${MIRI_TOOLCHAIN}..."
        rustup component add rust-src --toolchain "${MIRI_TOOLCHAIN}"
    fi
fi

echo "=== Preparing Miri sysroot ==="
cargo "+${MIRI_TOOLCHAIN}" miri setup

echo "=== Running Miri Undefined Behavior & Memory-Safety Suite ==="
cargo "+${MIRI_TOOLCHAIN}" miri --version

export MIRIFLAGS="-Zmiri-strict-provenance -Zmiri-symbolic-alignment-check -Zmiri-disable-isolation"

# run_stage STAGE ARGS... — runs one stage; ARGS go to the test binary.
run_stage() {
    local name=$1
    shift
    case "$name" in
        c_api)
            echo "--- [1/9] Verifying bc_c_api (Unsafe C-FFI, raw pointers, sessions, callbacks) ---"
            cargo "+${MIRI_TOOLCHAIN}" miri test --package bc_c_api --lib -- "$@"
            ;;
        core)
            echo "--- [2/9] Verifying bc_core (BigInt math, Parser, Evaluator, call-frame restore on errors) ---"
            cargo "+${MIRI_TOOLCHAIN}" miri test --package bc_core --lib -- "$@"
            ;;
        zephyr)
            echo "--- [3/9] Verifying bc_zephyr (RTOS C-FFI shims, SharedBuffer, interactive REPL) ---"
            cargo "+${MIRI_TOOLCHAIN}" miri test --package bc_zephyr --lib -- "$@"
            ;;
        qemu)
            echo "--- [4/9] Verifying bc_qemu_riscv32 (self-tests, measurement loop, serial writer, peak allocator) ---"
            cargo "+${MIRI_TOOLCHAIN}" miri test --package bc_qemu_riscv32 --lib -- "$@"
            ;;
        cli)
            echo "--- [5/9] Verifying bc_clone CLI (catch_unwind, AtomicBool signal state, REPL loop) ---"
            cargo "+${MIRI_TOOLCHAIN}" miri test --package bc_clone --bin bc_clone -- "$@"
            ;;
        build_info)
            echo "--- [6/9] Verifying bc_build_info (the build script's decisions on a fake git) ---"
            cargo "+${MIRI_TOOLCHAIN}" miri test --package bc_build_info --lib -- "$@"
            ;;
        m5stamp)
            echo "--- [7/9] Verifying the M5Stamp C3 application (self-test report, stack budget, serial REPL) ---"
            # Its own .cargo/config.toml (riscv32imc, build-std) applies only inside its directory;
            # the host target is given explicitly as well.
            (
                cd "$(dirname "${BASH_SOURCE[0]}")/.."
                cargo "+${MIRI_TOOLCHAIN}" miri test --manifest-path examples/m5stamp_c3/Cargo.toml \
                    --package m5stamp_c3_bc --lib --target "$(rustc -vV | sed -n 's/^host: //p')" -- "$@"
            )
            ;;
        wasm)
            echo "--- [8/9] Verifying the Wasm binding (the exported functions and the session, on the host) ---"
            # The exports are plain Rust functions on the host; stack-probe adds set_max_depth.
            (
                cd "$(dirname "${BASH_SOURCE[0]}")/.."
                cargo "+${MIRI_TOOLCHAIN}" miri test --manifest-path examples/wasm_web_app/crate/Cargo.toml \
                    --package bc_wasm --lib --all-features -- "$@"
            )
            ;;
        c_api_tree)
            echo "--- [9/9] Re-checking bc_c_api (the crate with unsafe code) under Tree Borrows ---"
            MIRIFLAGS="${MIRIFLAGS} -Zmiri-tree-borrows" cargo "+${MIRI_TOOLCHAIN}" miri test --package bc_c_api --lib -- "$@"
            ;;
    esac
}

if [ "$stage" = "all" ]; then
    for s in "${STAGES[@]}"; do
        run_stage "$s"
    done
    echo ""
    echo "=== All Miri Undefined Behavior & Memory Leak Checks Passed (0 errors)! ==="
else
    run_stage "$stage" "$@"
    echo ""
    echo "=== Miri stage '${stage}' passed (0 errors) ==="
fi
