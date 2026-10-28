#!/usr/bin/env bash
# SPDX-License-Identifier: MIT
set -euo pipefail

# Runs Verus formal verification on bc_core and on the executable specification (bc_spec).

# shellcheck source=scripts/verus_env.sh
source "$(dirname "$0")/verus_env.sh"

echo "=== Running Verus Formal Verification on bc_core (verus_proofs) ==="
echo "Using Verus binary: $VERUS_BIN"
"$VERUS_BIN" --version

cargo verus verify -p bc_core --features verify

echo ""
echo "=== Running Verus Formal Verification on the executable specification (bc_spec) ==="
cargo verus verify -p bc_spec

echo ""
echo "=== All Verus Formal Proofs Verified Successfully! ==="
