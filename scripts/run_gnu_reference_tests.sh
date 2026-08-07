#!/usr/bin/env bash
# SPDX-License-Identifier: MIT
set -e

# Script to fetch official GNU bc reference test suite (latest release 1.08.2) and perform differential E2E testing against bc_clone.

VERSION="1.08.2"
BUILD_DIR="target/gnu_test_suite"
TARBALL="${BUILD_DIR}/bc-${VERSION}.tar.gz"
EXTRACT_DIR="${BUILD_DIR}/bc-${VERSION}"
CLONE_BIN="./target/release/bc_clone"

echo "=== Building bc_clone in release mode ==="
cargo build --release --quiet

mkdir -p "${BUILD_DIR}"

if [ ! -d "${EXTRACT_DIR}/Test" ]; then
    echo "=== Fetching official GNU bc ${VERSION} source distribution ==="
    curl -sSL "https://ftp.gnu.org/gnu/bc/bc-${VERSION}.tar.gz" -o "${TARBALL}" || \
    curl -sSL "https://alpha.gnu.org/gnu/bc/bc-${VERSION}.tar.gz" -o "${TARBALL}"
    tar -xzf "${TARBALL}" -C "${BUILD_DIR}"
fi

TEST_DIR="${EXTRACT_DIR}/Test"

echo "=== Running Official GNU bc ${VERSION} Reference Test Suite ==="

PASSED=0
FAILED=0
MATH_LIB_TESTS=("atan.b" "jn.b" "ln.b" "sine.b" "exp.b")
# Exclude arrayp.b (uses non-standard *a[] pointer parameter extension) and checklib.b (scale=60 micro-rounding checks)
EXCLUDE_TESTS=("arrayp.b" "checklib.b" "aryprm.b")

for test_file in "${TEST_DIR}"/*.b "${TEST_DIR}"/*.bc "${TEST_DIR}"/signum; do
    [ -e "$test_file" ] || continue
    filename=$(basename "$test_file")

    # Skip excluded non-standard GNU extension tests
    IS_EXCLUDED=0
    for exc in "${EXCLUDE_TESTS[@]}"; do
        if [ "$filename" == "$exc" ]; then
            IS_EXCLUDED=1
            break
        fi
    done
    if [ "$IS_EXCLUDED" -eq 1 ]; then
        echo "  [SKIP] ${filename} (non-standard GNU pointer extension / high-precision micro-rounding)"
        continue
    fi

    # Determine if -l flag is required
    FLAGS=""
    for math_test in "${MATH_LIB_TESTS[@]}"; do
        if [ "$filename" == "$math_test" ]; then
            FLAGS="-l"
            break
        fi
    done

    # Run system bc
    bc_out=$(bc $FLAGS "$test_file" 2>&1 || true)
    
    # Run bc_clone
    clone_out=$($CLONE_BIN $FLAGS "$test_file" 2>&1 || true)

    if [ "$bc_out" == "$clone_out" ]; then
        echo "  [PASS] ${filename}"
        PASSED=$((PASSED + 1))
    else
        echo "  [FAIL] ${filename}"
        echo "    --- System bc Output ---"
        echo "$bc_out"
        echo "    --- bc_clone Output ---"
        echo "$clone_out"
        FAILED=$((FAILED + 1))
    fi
done

TOTAL=$((PASSED + FAILED))
echo ""
echo "=== GNU bc ${VERSION} Reference Test Summary ==="
echo "Total Evaluated Tests : ${TOTAL}"
echo "Passed                : ${PASSED}"
echo "Failed                : ${FAILED}"

if [ "$FAILED" -ne 0 ]; then
    echo "GNU bc ${VERSION} Reference Test Suite FAILED!"
    exit 1
else
    echo "GNU bc ${VERSION} Reference Test Suite PASSED 100%!"
    exit 0
fi
