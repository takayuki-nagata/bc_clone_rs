#!/usr/bin/env bash
# SPDX-License-Identifier: MIT
set -euo pipefail

# Links a C program against the bc_c_api static library through include/bc_core.h and runs it on
# the host, for both builds of the library:
#
# - std (the default features);
# - no_std (`--no-default-features`, panic = "abort"): its own 64 KiB heap, its critical-section
#   implementation and its panic handler, which the Rust unit tests never run. The panic handler
#   is reached by exhausting the heap (the allocation error handler panics) and must halt: the
#   program is killed by `timeout` instead of returning.
#
# Needs a C compiler (`cc`, or `CC`) and coreutils `timeout`.

cd "$(dirname "$0")/.."
CC="${CC:-cc}"
command -v "$CC" >/dev/null || { echo "error: C compiler '$CC' not found" >&2; exit 1; }
command -v timeout >/dev/null || { echo "error: coreutils timeout not found" >&2; exit 1; }

SRC=crates/bc_c_api/tests/c/smoke.c
INC=crates/bc_c_api/include
OUT=target/c_api_link
mkdir -p "$OUT"
CFLAGS=(-std=c11 -Wall -Wextra -Werror -O1 -I"$INC")

echo "=== std library ==="
CARGO_TARGET_DIR=target/c_api_std cargo build --quiet --release --package bc_c_api
"$CC" "${CFLAGS[@]}" "$SRC" target/c_api_std/release/libbc_c_api.a -lpthread -ldl -lm \
    -o "$OUT/smoke_std"
"$OUT/smoke_std"
# The std library has an unbounded heap: the large computation finishes.
std_oom="$(timeout 60 "$OUT/smoke_std" oom)" || true
if [ "$std_oom" != "oom done" ]; then
    echo "error: the std library did not finish the large computation (output '$std_oom')" >&2
    exit 1
fi
echo "std: large computation finished"

echo "=== no_std library ==="
CARGO_TARGET_DIR=target/c_api_nostd CARGO_PROFILE_RELEASE_PANIC=abort \
    cargo build --quiet --release --package bc_c_api --no-default-features
# The stub defines the unwinding personality that the host's prebuilt `core` refers to.
"$CC" "${CFLAGS[@]}" "$SRC" crates/bc_c_api/tests/c/eh_personality_stub.c \
    target/c_api_nostd/release/libbc_c_api.a -o "$OUT/smoke_nostd"
"$OUT/smoke_nostd"
# Exhausting the 64 KiB heap reaches the panic handler, which spins: `timeout` ends the program
# (status 124) before it can print "oom done".
set +e
oom_out="$(timeout 10 "$OUT/smoke_nostd" oom)"
oom_status=$?
set -e
if [ "$oom_status" -ne 124 ] || [ -n "$oom_out" ]; then
    echo "error: no_std heap exhaustion did not halt in the panic handler" \
        "(status $oom_status, output '$oom_out')" >&2
    exit 1
fi
echo "no_std: heap exhaustion halted in the panic handler"

echo "=== C API link tests passed ==="
