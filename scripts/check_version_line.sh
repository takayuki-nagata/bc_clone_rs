#!/usr/bin/env bash
# SPDX-License-Identifier: MIT
# Checks that the output of a release build names the release: that FILE has the line
# "bc_clone VERSION (COMMIT)" (after optional leading blanks) with a 7-digit commit, neither
# "unknown" nor "-dirty". VERSION may carry the tag's "v" prefix.
#   scripts/check_version_line.sh v0.5.0 output.txt
set -euo pipefail
if [[ $# -ne 2 ]]; then
    echo "usage: $0 VERSION FILE" >&2
    exit 2
fi
version="${1#v}"
file="$2"
pattern="^[[:space:]]*bc_clone ${version//./\\.} \\([0-9a-f]{7}\\)\$"
# The bare-metal UARTs end lines with "\r\n".
if tr -d '\r' <"${file}" | grep -Eq "${pattern}"; then
    echo "version line found: bc_clone ${version}"
else
    echo "error: no line \"bc_clone ${version} (COMMIT)\" with a clean commit in ${file}:" >&2
    tr -d '\r' <"${file}" | grep -E "bc_clone [0-9]" >&2 || true
    exit 1
fi
