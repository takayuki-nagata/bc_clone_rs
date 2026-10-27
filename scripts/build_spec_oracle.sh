#!/usr/bin/env bash
# SPDX-License-Identifier: MIT
set -euo pipefail

# Verifies the executable specification (crates/bc_spec) with Verus and compiles it into the
# reference interpreter used as the differential-testing oracle.
# Usage: scripts/build_spec_oracle.sh [--no-verify] [OUTPUT]   (default: target/bc_spec_oracle)
# --no-verify skips the proofs, e.g. after scripts/run_verus_verification.sh has checked them.

# shellcheck source=scripts/verus_env.sh
source "$(dirname "$0")/verus_env.sh"

VERIFY_FLAGS=()
if [ "${1:-}" == "--no-verify" ]; then
    VERIFY_FLAGS=(--no-verify)
    shift
fi
OUT="${1:-target/bc_spec_oracle}"
mkdir -p "$(dirname "$OUT")"

"$VERUS_BIN" crates/bc_spec/src/main.rs "${VERIFY_FLAGS[@]}" --compile -C opt-level=3 -o "$OUT"
echo "Built $OUT"
