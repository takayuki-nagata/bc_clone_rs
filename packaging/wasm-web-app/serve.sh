#!/usr/bin/env bash
# SPDX-License-Identifier: MIT
# Serves the bc_clone WebAssembly calculator on http://localhost:${PORT:-8080}/www/
# Requires python3. Browsers only load WebAssembly modules over http(s), not file://.
set -euo pipefail
DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PORT="${PORT:-8080}"
echo "Open http://localhost:${PORT}/www/ in your browser (Ctrl+C to stop)."
exec python3 -m http.server "${PORT}" --bind 127.0.0.1 -d "${DIR}"
