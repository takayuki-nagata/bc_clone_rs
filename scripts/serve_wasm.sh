#!/usr/bin/env bash
# SPDX-License-Identifier: MIT
set -e

# Script to build Wasm and start a local web server to test the web frontend.

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
APP_DIR="${REPO_ROOT}/examples/wasm_web_app"

echo "=== Building WebAssembly Module ==="
"${REPO_ROOT}/scripts/build_wasm.sh"

PORT="${PORT:-8080}"
echo ""
echo "=== Starting Local HTTP Server on http://localhost:${PORT}/www/ ==="
echo "Press CTRL+C to stop the server."
echo ""

python3 -m http.server "${PORT}" -d "${APP_DIR}"
