#!/usr/bin/env bash
# SPDX-License-Identifier: MIT
set -euo pipefail

# Verifies the executable specification (crates/bc_spec) with Verus and compiles it into the
# reference interpreter used as the differential-testing oracle.
# Usage: scripts/build_spec_oracle.sh [--no-verify] [OUTPUT]   (default: target/bc_spec_oracle)
# --no-verify skips the proofs, e.g. after scripts/run_verus_verification.sh has checked them.

# shellcheck source=scripts/verus_env.sh
source "$(dirname "$0")/verus_env.sh"

VERIFY=1
if [ "${1:-}" == "--no-verify" ]; then
    VERIFY=0
    shift
fi
OUT="${1:-target/bc_spec_oracle}"
mkdir -p "$(dirname "$OUT")"

if [ "$VERIFY" == 1 ]; then
    cargo verus verify -p bc_spec
fi
# `verus!` erases the specifications and proofs, so a normal build compiles the verified
# executable functions that `exec_spec_verified!` generated.
cargo build --release -p bc_spec --bin bc_spec_oracle
cp target/release/bc_spec_oracle "$OUT"
echo "Built $OUT"
