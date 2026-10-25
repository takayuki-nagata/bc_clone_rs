#!/usr/bin/env bash
# SPDX-License-Identifier: MIT
set -euo pipefail

# Script to run Kani bounded model checking across bc_core, bc_c_api, and bc_clone (bc_cli).
# Enforces a 4GB virtual memory limit (ulimit -v) so CBMC can never cause host OOM.

ulimit -v 4194304 || true

if ! command -v cargo-kani >/dev/null 2>&1; then
    echo "Installing Kani verifier..."
    cargo install --locked kani-verifier
    cargo kani setup
fi

echo "=== Running Kani Bounded Model Checking Suite ==="
cargo kani --version

echo "--- [1/3] Verifying bc_core (31 verified_kernels & multi-step state machines) ---"
cargo kani --package bc_core

echo "--- [2/3] Verifying bc_c_api (C-FFI pointer bounds, NUL termination & NULL guards) ---"
cargo kani --package bc_c_api

echo "--- [3/3] Verifying bc_clone CLI (REPL block scanner & CLI option slice safety) ---"
cargo kani --package bc_clone

echo ""
echo "=== All Kani Bounded Model Checking Proofs Verified Successfully! ==="
