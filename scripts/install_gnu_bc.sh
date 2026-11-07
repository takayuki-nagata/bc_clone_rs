#!/usr/bin/env bash
# SPDX-License-Identifier: MIT
set -euo pipefail

# Builds GNU bc from its release tarball into PREFIX/bin/bc. The differential tests compare
# bc_clone with the `bc` on PATH and expect GNU bc 1.08; distributions often ship 1.07.
#
# usage: install_gnu_bc.sh PREFIX

VERSION="1.08.2"
PREFIX="${1:?usage: $0 PREFIX}"

if [ -x "${PREFIX}/bin/bc" ] && "${PREFIX}/bin/bc" --version | head -n 1 | grep -q "^bc ${VERSION}\$"; then
    echo "GNU bc ${VERSION} is already installed in ${PREFIX}"
    exit 0
fi

WORK_DIR="$(mktemp -d)"
trap 'rm -rf "${WORK_DIR}"' EXIT

echo "=== Fetching GNU bc ${VERSION} ==="
curl -fsSL "https://ftp.gnu.org/gnu/bc/bc-${VERSION}.tar.gz" -o "${WORK_DIR}/bc.tar.gz" ||
    curl -fsSL "https://alpha.gnu.org/gnu/bc/bc-${VERSION}.tar.gz" -o "${WORK_DIR}/bc.tar.gz"
tar -xzf "${WORK_DIR}/bc.tar.gz" -C "${WORK_DIR}"

echo "=== Building GNU bc ${VERSION} ==="
cd "${WORK_DIR}/bc-${VERSION}"
./configure --prefix="${PREFIX}" >/dev/null
# Only the library and bc itself: the documentation would need makeinfo, and dc is not used.
make -C lib >/dev/null
make -C bc >/dev/null
mkdir -p "${PREFIX}/bin"
cp bc/bc "${PREFIX}/bin/bc"

"${PREFIX}/bin/bc" --version | head -n 1
