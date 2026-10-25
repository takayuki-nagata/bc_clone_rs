#!/usr/bin/env bash
# SPDX-License-Identifier: MIT
set -euo pipefail

# Script to run Verus formal verification on bc_core.

VERUS_VERSION="0.2026.10.18.7d82994"
VERUS_URL="https://github.com/verus-lang/verus/releases/download/release%2F${VERUS_VERSION}/verus-${VERUS_VERSION}-x86-linux.zip"

VERUS_BIN="${VERUS_BIN:-}"
if [ -z "$VERUS_BIN" ]; then
    if command -v verus >/dev/null 2>&1; then
        VERUS_BIN="$(command -v verus)"
    elif [ -x "$HOME/.local/verus/verus" ]; then
        VERUS_BIN="$HOME/.local/verus/verus"
    else
        echo "Installing Verus ${VERUS_VERSION} from ${VERUS_URL}..."
        TMP_DIR="$(mktemp -d)"
        curl -fL "$VERUS_URL" -o "$TMP_DIR/verus.zip"
        unzip -q "$TMP_DIR/verus.zip" -d "$TMP_DIR/extracted"
        mkdir -p "$HOME/.local/verus"
        if [ -d "$TMP_DIR/extracted/verus-x86-linux" ]; then
            cp -a "$TMP_DIR/extracted/verus-x86-linux/." "$HOME/.local/verus/"
        else
            cp -a "$TMP_DIR/extracted/." "$HOME/.local/verus/"
        fi
        chmod +x "$HOME/.local/verus/verus" "$HOME/.local/verus/rust_verify" "$HOME/.local/verus/z3" "$HOME/.local/verus/cargo-verus" 2>/dev/null || true
        rm -rf "$TMP_DIR"
        VERUS_BIN="$HOME/.local/verus/verus"
    fi
fi

VERUS_DIR="$(dirname "$VERUS_BIN")"
if [ -f "$VERUS_DIR/version.json" ] && command -v rustup >/dev/null 2>&1; then
    REQUIRED_TOOLCHAIN="$(sed -n 's/.*"toolchain": "\([^" ]*\).*/\1/p' "$VERUS_DIR/version.json" | head -n 1)"
    if [ -n "$REQUIRED_TOOLCHAIN" ] && ! rustup toolchain list | grep -q "^${REQUIRED_TOOLCHAIN}"; then
        echo "Installing Rust toolchain required by Verus: ${REQUIRED_TOOLCHAIN}..."
        rustup toolchain install "$REQUIRED_TOOLCHAIN" --profile minimal --no-self-update
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
