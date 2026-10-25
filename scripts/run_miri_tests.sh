#!/usr/bin/env bash
# SPDX-License-Identifier: MIT
set -euo pipefail

# Script to run Miri Undefined Behavior (UB) and memory-safety verification
# across bc_core, bc_c_api, bc_zephyr, and bc_clone (bc_cli).

MIRI_TOOLCHAIN="${MIRI_TOOLCHAIN:-nightly}"

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

echo "--- [1/4] Verifying bc_c_api (Unsafe C-FFI, raw pointers, sessions, callbacks) ---"
cargo "+${MIRI_TOOLCHAIN}" miri test --package bc_c_api --lib

echo "--- [2/4] Verifying bc_core (BigInt math, Parser, Evaluator, ScopeGuard unwinding) ---"
cargo "+${MIRI_TOOLCHAIN}" miri test --package bc_core --lib

echo "--- [3/4] Verifying bc_zephyr (RTOS C-FFI shims, SharedBuffer, interactive REPL) ---"
cargo "+${MIRI_TOOLCHAIN}" miri test --package bc_zephyr --lib

echo "--- [4/4] Verifying bc_clone CLI (catch_unwind, AtomicBool signal state, REPL loop) ---"
cargo "+${MIRI_TOOLCHAIN}" miri test --package bc_clone --bin bc_clone

echo ""
echo "=== All Miri Undefined Behavior & Memory Leak Checks Passed (0 errors)! ==="
