#!/usr/bin/env bash
# SPDX-License-Identifier: MIT
set -e

# Script to build and package WebAssembly (wasm32) module for bc_clone.

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
CRATE_DIR="${REPO_ROOT}/examples/wasm_web_app/crate"
PKG_DIR="${REPO_ROOT}/examples/wasm_web_app/pkg"

echo "=== Building bc_clone WebAssembly (wasm32) module ==="

# 1. Clippy Linter Check
cargo clippy \
    --manifest-path "${CRATE_DIR}/Cargo.toml" \
    --target wasm32-unknown-unknown \
    -- -D warnings

# 2. Release Build
cargo build \
    --manifest-path "${CRATE_DIR}/Cargo.toml" \
    --target wasm32-unknown-unknown \
    --release

# 3. Generate wasm-bindgen bindings
WASM_BIN="${REPO_ROOT}/target/wasm32-unknown-unknown/release/bc_wasm.wasm"
if [ ! -f "${WASM_BIN}" ]; then
    # Fallback to local crate target if target directory differs
    WASM_BIN="${CRATE_DIR}/target/wasm32-unknown-unknown/release/bc_wasm.wasm"
fi

echo "Generating wasm-bindgen JS bindings into ${PKG_DIR}..."
mkdir -p "${PKG_DIR}"
wasm-bindgen \
    --target web \
    --out-dir "${PKG_DIR}" \
    --out-name bc_wasm \
    "${WASM_BIN}"

echo ""
echo "=== bc_clone WebAssembly build and packaging PASSED successfully! ==="
