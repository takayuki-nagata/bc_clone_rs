#!/usr/bin/env bash
# SPDX-License-Identifier: MIT
set -u

# POSIX.1-2024 (Issue 8) bc conformance tests.
#
# Expected outputs are derived from the POSIX text (sections noted per case), not from another
# bc implementation. Every case uses only POSIX syntax, so it runs twice: in the default mode and
# with -s (extensions rejected). Usage:
#
#   scripts/run_posix_compliance_tests.sh            # tests ./target/release/bc_clone
#   BC_BIN=bc scripts/run_posix_compliance_tests.sh  # sanity-checks the expectations against GNU bc

if [ -z "${BC_BIN:-}" ]; then
    echo "=== Building bc_clone in release mode ==="
    cargo build --release --quiet -p bc_clone || exit 1
    BC_BIN="./target/release/bc_clone"
fi

WORK_DIR="$(mktemp -d)"
trap 'rm -rf "$WORK_DIR"' EXIT

PASSED=0
FAILED=0

# check <name> <flags> <stdin> <expected stdout> [expected status] [stderr: empty|nonempty]
check() {
    local name="$1" flags="$2" input="$3" expected="$4" status="${5:-0}" stderr_kind="${6:-empty}"
    local mode out err code ok
    for mode in "" "-s"; do
        # shellcheck disable=SC2086
        printf '%s' "$input" | "$BC_BIN" $mode $flags >"$WORK_DIR/out" 2>"$WORK_DIR/err"
        code=$?
        out="$(cat "$WORK_DIR/out"; printf x)"
        out="${out%x}"
        err="$(cat "$WORK_DIR/err")"
        ok=1
        [ "$out" == "$expected" ] || ok=0
        if [ "$status" == "nonzero" ]; then [ "$code" -ne 0 ] || ok=0; else [ "$code" -eq "$status" ] || ok=0; fi
        if [ "$stderr_kind" == "empty" ]; then [ -z "$err" ] || ok=0; else [ -n "$err" ] || ok=0; fi
        if [ "$ok" -eq 1 ]; then
            PASSED=$((PASSED + 1))
        else
            FAILED=$((FAILED + 1))
            echo "  [FAIL] ${name} (flags: ${mode} ${flags})"
            echo "    expected stdout: $(printf '%q' "$expected"), status ${status}, stderr ${stderr_kind}"
            echo "    actual stdout:   $(printf '%q' "$out"), status ${code}, stderr $(printf '%q' "$err")"
        fi
    done
}

echo "=== Running POSIX.1-2024 bc Conformance Tests against ${BC_BIN} ==="

# --- OPTIONS / OPERANDS / INPUT FILES -----------------------------------------------------------
check "-l sets scale to 20" "-l" $'scale\n' $'20\n'
check "scale defaults to 0" "" $'scale\n' $'0\n'
check "ibase and obase default to 10" "" $'ibase\nobase\n' $'10\n10\n'
printf 'a = 2\n' > "$WORK_DIR/first.bc"
printf 'b = 3\n' > "$WORK_DIR/second.bc"
check "files are read in order, then standard input" "$WORK_DIR/first.bc $WORK_DIR/second.bc" \
    $'a * b\n' $'6\n'
check "an inaccessible file operand is a diagnosed error" "$WORK_DIR/missing.bc" \
    $'1\n' "" nonzero nonempty

# --- Lexical conventions ---------------------------------------------------------------------------
check "NUMBER forms integer . integer" "" $'1.5\n.5\n5.\n0.50\n' $'1.5\n.5\n5\n.50\n'
check "backslash-newline inside a NUMBER is ignored" "" $'12\\\n34\n' $'1234\n'
check "single digits A-F are digits" "" $'A\nF\n' $'10\n15\n'
check "STRING is written without a newline" "" $'"abc"\n' 'abc'
check "backslash-newline inside a STRING is kept" "" $'"a\\\nb"\n' $'a\\\nb'
check "comments may span lines" "" $'/* x */ 1 /* y\n z */ + 2\n' $'3\n'
check "a NUMBER is not a named expression" "" $'A = 1\n' "" nonzero nonempty

# --- Registers ------------------------------------------------------------------------------------
check "assigned register values are truncated" "" $'scale = 2.9\nscale\n' $'2\n'
check "a single digit assigned to ibase is hexadecimal" "" $'ibase = 16\nibase = A\n10\n' $'10\n'
check "a single digit assigned to obase is hexadecimal" "" $'obase = A\n10\n' $'10\n'
check "ibase 2" "" $'ibase = 2\n1010\n' $'10\n'
check "ibase 16 with a fraction" "" $'ibase = 16\n0.8\n' $'.5\n'

# --- Expressions: scale of results -------------------------------------------------------------------
check "results are truncated, not rounded" "" $'scale = 0\n3.2 / 1\n' $'3\n'
check "+ and - use the larger scale" "" $'1.25 + 2.5\n1 - 0.25\n-1.5 - 1\n' $'3.75\n.75\n-2.5\n'
check "* scale is min(a+b, max(scale,a,b)), limited by operands" "" $'scale = 1\n1.25 * 1.5\n' $'1.87\n'
check "* scale is min(a+b, max(scale,a,b)), exact" "" $'scale = 5\n1.25 * 1.5\n' $'1.875\n'
check "/ scale is scale" "" $'scale = 3\n1 / 3\n-1 / 3\n' $'.333\n-.333\n'
check "% is the remainder with scale max(scale+b, a)" "" $'7 % 3\n-7 % 3\nscale = 1\n7.5 % 2\n' $'1\n-1\n.1\n'
check "^ with a positive exponent" "" $'2 ^ 10\nscale = 2\n1.5 ^ 3\n(-2) ^ 3\n' $'1024\n3.37\n-8\n'
check "^ with a negative exponent has scale scale" "" $'scale = 4\n2 ^ -2\n' $'.2500\n'
check "unary minus keeps the scale" "" $'-1.50\n' $'-1.50\n'
check "++ and -- keep the scale" "" $'a = 1.50\n++a\na--\na\n' $'2.50\n2.50\n1.50\n'
check "assignment keeps the scale of the value" "" $'a = 1.500\na\n' $'1.500\n'
check "sqrt scale is max(scale, a)" "" $'sqrt(2)\nscale = 4\nsqrt(2)\nsqrt(1.000)\n' $'1\n1.4142\n1.0000\n'
check "length and scale" "" $'length(123.45)\nscale(123.45)\nlength(.0012)\n' $'5\n2\n4\n'
check "compound assignment operators" "" \
    $'a = 5\na += 2\na -= 1\na *= 3\na /= 2\na %= 4\na ^= 2\na\n' $'1\n'

# --- Output ----------------------------------------------------------------------------------------
check "obase 16 uses digits 0-F" "" $'obase = 16\n255\n' $'FF\n'
check "obase > 16 writes space-separated decimal digits" "" $'obase = 25\n1024\n' $' 01 15 24\n'
check "obase 2 fractions" "" $'obase = 2\nscale = 1\n1 / 2\n' $'.1000\n'
check "leading zero is omitted for |x| < 1" "" $'.5\n-0.5\n' $'.5\n-.5\n'
check "long numbers are split at 70 characters" "" $'2 ^ 300\n' \
    $'20370359763344860862684456884093781610514683936659362506361404493543\\\n81299763336706183397376\n'

# --- Statements and functions ----------------------------------------------------------------------
check "quit stops at the point where it occurs" "" $'1\nquit\n2\n' $'1\n'
check "quit inside a function definition" "" $'define f() {\nquit\n}\n2\n' ""
check "return forms" "" \
    $'define f() {\nreturn\n}\ndefine g() {\nreturn ()\n}\ndefine h() {\nreturn (3)\n}\nf()\ng()\nh()\n' \
    $'0\n0\n3\n'
check "dynamic scoping of parameters" "" \
    $'a = 1\ndefine g() {\nreturn (a)\n}\ndefine f(a) {\nreturn (g())\n}\nf(5)\na\n' $'5\n1\n'
check "auto arrays are local" "" \
    $'define f() {\nauto b[]\nb[0] = 2\nreturn (b[0])\n}\nb[0] = 9\nf()\nb[0]\n' $'2\n9\n'
check "an array may be the last parameter (Defect 1230)" "" \
    $'define f(x, y[]) {\nreturn (x + y[1])\n}\nz[1] = 4\nf(1, z[])\n' $'5\n'
check "arrays are passed by value" "" \
    $'define f(y[]) {\ny[0] = 7\nreturn (y[0])\n}\nz[0] = 1\nf(z[])\nz[0]\n' $'7\n1\n'
check "while" "" $'i = 0\nwhile (i < 3) i = i + 1\ni\n' $'3\n'
check "for and break" "" $'for (i = 0; i < 10; i++) if (i == 2) break\ni\n' $'2\n'
check "if with a relational condition" "" $'if (2 > 1) 5\nif (2 < 1) 6\n' $'5\n'
check "assignments are not printed, expressions are" "" $'a = 5\na\n(a = 6)\n' $'5\n6\n'
check "compound statements" "" $'{ 1; 2 }\n' $'1\n2\n'

# --- Math library (-l) -----------------------------------------------------------------------------
check "-l functions use the caller's scale and restore it" "-l" $'scale = 5\nx = s(1)\nscale\nx\n' $'5\n.84147\n'
check "-l s c a" "-l" $'scale = 10\ns(1)\nc(1)\na(1)\n' $'.8414709848\n.5403023058\n.7853981633\n'
check "-l l e" "-l" $'l(2)\ne(1)\n' $'.69314718055994530941\n2.71828182845904523536\n'
check "-l j" "-l" $'scale = 10\nj(0, 1)\nj(1, 1)\n' $'.7651976865\n.4400505857\n'

TOTAL=$((PASSED + FAILED))
echo ""
echo "=== POSIX.1-2024 bc Conformance Test Summary (each case in default and -s mode) ==="
echo "Total Evaluated Runs : ${TOTAL}"
echo "Passed               : ${PASSED}"
echo "Failed               : ${FAILED}"

if [ "$FAILED" -ne 0 ]; then
    echo "POSIX Compliance Test Suite FAILED!"
    exit 1
fi
echo "POSIX Compliance Test Suite PASSED 100%!"
