#!/usr/bin/env bash
# SPDX-License-Identifier: MIT
set -euo pipefail

# Script to run Verus formal verification on bc_core.

VERUS_BIN="${VERUS_BIN:-}"
if [ -z "$VERUS_BIN" ]; then
    if command -v verus >/dev/null 2>&1; then
        VERUS_BIN="$(command -v verus)"
    elif [ -x "$HOME/.local/verus/verus" ]; then
        VERUS_BIN="$HOME/.local/verus/verus"
    else
        echo "Error: 'verus' binary not found in PATH or ~/.local/verus/verus" >&2
        exit 1
    fi
fi

echo "=== Running Verus Formal Verification on bc_core (verus_proofs) ==="
echo "Using Verus binary: $VERUS_BIN"
"$VERUS_BIN" --version

"$VERUS_BIN" \
    --crate-type=lib \
    crates/bc_core/src/lib.rs

echo ""
echo "=== All Verus Formal Proofs Verified Successfully! ==="
