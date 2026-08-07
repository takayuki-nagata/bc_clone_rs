#!/usr/bin/env bash
set -e

# Script to perform differential POSIX IEEE Std 1003.1 compliance testing against bc_clone.
# All messages, comments, and outputs are written in English.

CLONE_BIN="./target/release/bc_clone"

echo "=== Building bc_clone in release mode ==="
cargo build --release --quiet

echo "=== Running POSIX IEEE Std 1003.1 Compliance Test Suite ==="

# Define test cases as (Name | Flags | Input Code)
declare -a POSIX_TESTS=(
    "POSIX Arithmetic Precedence||1 + 2 * 3 - 4 / 2\n"
    "POSIX Scale Propagation||scale = 4; 5 / 3\n"
    "POSIX Scale Modulo Preserving Scale||scale = 2; 7.5 % 2.1\n"
    "POSIX ibase 16 Input Parsing||ibase = 16; FF + 1\n"
    "POSIX obase 16 Output Conversion||obase = 16; 255\n"
    "POSIX ibase 16 obase 10 Mixed Conversion||ibase = 16; obase = 10; FF\n"
    "POSIX obase 16 ibase 10 Mixed Conversion||obase = 16; ibase = 10; 255\n"
    "POSIX Transcendental Sine|-l|s(1.5707963267948966)\n"
    "POSIX Transcendental Cosine|-l|c(0)\n"
    "POSIX Transcendental Exponential|-l|e(1)\n"
    "POSIX Transcendental Natural Logarithm|-l|l(2.718281828459045)\n"
    "POSIX Transcendental Arctangent|-l|a(1)\n"
    "POSIX Transcendental Bessel Function|-l|j(0, 1)\n"
    "POSIX For Loop Accumulator||scale = 2; s = 0; for(i=1; i<=50; i++) s += i/10; s\n"
    "POSIX While Loop Decrement||scale = 0; n = 10; s = 0; while(n > 0) { s += n; n-- }; s\n"
    "POSIX Function Auto Variable Scoping||define f(x) {\n  auto a;\n  a = x*2;\n  return a;\n}\nf(5)\n"
    "POSIX Function Array Parameter Passing||define f(a[]) {\n  return a[0] + a[1];\n}\nv[0]=10;\nv[1]=20;\nf(v[])\n"

    "POSIX Array Indexing and Mutation||a[0]=10; a[1]=20; a[0] + a[1]\n"
    "POSIX Multi-Line Comment Stripping||/* comment line 1\n line 2 */ 42\n"
    "POSIX Output Line Wrapping at 70 Chars||2^200\n"
)

PASSED=0
FAILED=0

for test_spec in "${POSIX_TESTS[@]}"; do
    IFS="|" read -r name flags code <<< "$test_spec"
    
    # Run system bc
    bc_out=$(echo -e "$code" | bc $flags 2>&1 || true)
    
    # Run bc_clone
    clone_out=$(echo -e "$code" | $CLONE_BIN $flags 2>&1 || true)
    
    # Trim trailing whitespace
    bc_out_trimmed=$(echo "$bc_out" | sed -e 's/[[:space:]]*$//')
    clone_out_trimmed=$(echo "$clone_out" | sed -e 's/[[:space:]]*$//')
    
    if [ "$bc_out_trimmed" == "$clone_out_trimmed" ]; then
        echo "  [PASS] ${name}"
        PASSED=$((PASSED + 1))
    else
        echo "  [FAIL] ${name}"
        echo "    --- System bc Output ---"
        echo "$bc_out"
        echo "    --- bc_clone Output ---"
        echo "$clone_out"
        FAILED=$((FAILED + 1))
    fi
done

TOTAL=$((PASSED + FAILED))
echo ""
echo "=== POSIX IEEE Std 1003.1 Compliance Test Summary ==="
echo "Total Evaluated Tests : ${TOTAL}"
echo "Passed                : ${PASSED}"
echo "Failed                : ${FAILED}"

if [ "$FAILED" -ne 0 ]; then
    echo "POSIX Compliance Test Suite FAILED!"
    exit 1
else
    echo "POSIX Compliance Test Suite PASSED 100%!"
    exit 0
fi
