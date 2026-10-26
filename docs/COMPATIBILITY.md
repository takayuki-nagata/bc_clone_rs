# bc_clone Compatibility Specification

This document defines the behavior that `bc_clone` v0.4.0 implements. It is the oracle for the
test suites: if the implementation and this document disagree, that is a bug in one of them.

- **Normative base**: POSIX.1-2024 (IEEE Std 1003.1-2024, Issue 8), *bc — arbitrary-precision
  arithmetic language*: <https://pubs.opengroup.org/onlinepubs/9799919799/utilities/bc.html>.
- **Implementation-defined behavior**: where POSIX says *undefined* or *unspecified*, or leaves a
  value to the implementation, `bc_clone` follows GNU `bc` 1.08 closely and records the choice in
  §2 and §3.
- **Extensions**: §4 lists the non-POSIX syntax that `bc_clone` accepts. `-s` rejects these
  extensions and `-w` warns about them.
- **Known differences from GNU bc**: §5.

> **Status.** Every item in this document is implemented and covered by tests in
> `crates/bc_cli/tests/integration_tests.rs`, `scripts/run_posix_compliance_tests.sh`, or the unit
> tests of `bc_core`. A change in behavior must update this document in the same commit.

---

## 1. POSIX requirements

Each item below is a normative requirement. `scripts/run_posix_compliance_tests.sh` checks each one
against an expected output written by hand (not against GNU `bc`).

### 1.1 Invocation
| Requirement | Notes |
|---|---|
| `bc [-l] [file ...]` | Files are read in order, then standard input. `bc_clone` also accepts `-s` and `-w` (§4); each option must be a separate argument (`-ls` is invalid) |
| `-l` defines `s c a l e j` and sets `scale` to 20 | |
| An unreadable file operand produces a diagnostic (`bc: cannot open file <f>`) and terminates bc with status 1 without processing anything further | Operands before it have already been processed, as in GNU |
| Standard error is used only for diagnostics | |

### 1.2 Lexical conventions
| Requirement | Notes |
|---|---|
| `NUMBER`: digits `0-9` and `A-F`, at most one radix point; `integer`, `.integer`, `integer.`, `integer.integer` | A lone `.` is not a number (§5) |
| Backslash-newline inside a `NUMBER` is ignored | |
| `STRING`: any characters except `"`; a backslash-newline inside a string is kept as-is | Issue 8 wording |
| Comments are `/* ... */` | |
| Keywords: `auto break define ibase if for length obase quit return scale sqrt while` | |
| A `NUMBER` is not a named expression: `A = 1` is a syntax error | |

### 1.3 Registers
| Requirement | Notes |
|---|---|
| `ibase` must be in 2..16 and `obase` in 2..`BC_BASE_MAX`; both default to 10 | Out-of-range handling: §3 |
| `scale` must be in 0..`BC_SCALE_MAX` and defaults to 0 | |
| Values assigned to `ibase`, `obase`, and `scale` are truncated to integers | |
| A single-digit value assigned to `ibase` or `obase` is read as hexadecimal (`ibase=A` always means 10) | |

### 1.4 Arithmetic and scale rules
Let *a* and *b* be the scales of the operands and *scale* the register value. Results that are not
exact are **truncated** (toward zero).

| Operation | Result scale |
|---|---|
| `-e` (unary minus), `++` / `--` | scale of the operand |
| `e1 + e2`, `e1 - e2` | max(*a*, *b*) |
| `e1 * e2` | min(*a*+*b*, max(*scale*, *a*, *b*)) |
| `e1 / e2` | *scale* |
| `e1 % e2` | max(*scale*+*b*, *a*). The value is `e1 - (e1/e2)*e2`, with `e1/e2` computed at *scale* |
| `e1 ^ e2`, `e2 >= 0` | min(*a*·\|e2\|, max(*scale*, *a*)) |
| `e1 ^ e2`, `e2 < 0` | *scale* |
| `sqrt(e)` | max(*scale*, *a*) |
| `length(e)`, `scale(e)` | 0 |
| assignment | the scale of the assigned value |

### 1.5 Output
| Requirement | Notes |
|---|---|
| Bases 2..16 use the digits `0-9A-F` | |
| For `obase > 16`, each digit is written as a decimal number zero-padded to the width of `obase-1` and preceded by a space (1024 in base 25 is ` 01 15 24`) | |
| Long numbers are split at 70 characters per line; each continued line ends with `\` | |
| Values with \|x\| < 1 print without a leading `0` (`.5`) | |

### 1.6 Statements and functions
| Requirement | Notes |
|---|---|
| `quit` stops execution at the point where it appears in the input, even inside a function definition or a compound statement | |
| `return`, `return ()`, `return (e)`; `return ()` returns 0 | GNU bc rejects `return ()` (§5) |
| Function parameters and `auto` variables are dynamically scoped | |
| Arrays may be passed as parameters (`f(a[])`), including as the last parameter (Issue 8, Austin Group Defect 1230) | |
| A relational expression is valid as the condition of `if`, of `while`, and as the middle clause of `for` | Other positions: §4 |
| An expression statement is printed unless it is an assignment | As in GNU's grammar, an assignment binds to the named expression right before it: `a + b = 3` is `a + (b = 3)` and is printed; `-a = 5` is `-(a = 5)` and is not printed; `(a = 5)` is printed |

### 1.7 Math library (`-l`)
POSIX defines `s(x)`, `c(x)`, `a(x)`, `l(x)`, `e(x)`, and `j(n,x)`. Each result is computed to the
`scale` in effect at the call, and `scale` is restored afterwards. POSIX states no accuracy
requirement; §3.4 defines the one `bc_clone` meets.

---

## 2. Implementation-defined limits

| Limit | Value | Rationale |
|---|---|---|
| `BC_SCALE_MAX` | 1 000 000 000 | Equals `MAX_VERIFIED_SCALE`, so every verified kernel's precondition holds and `2·scale` cannot overflow a 32-bit `usize`. |
| `BC_BASE_MAX` | 2 147 483 647 | Same value as GNU `bc`. |
| `BC_DIM_MAX` | 16 777 216 | Valid subscripts are 0..16 777 215 (POSIX: 0..`BC_DIM_MAX`−1), the same range GNU `bc` accepts. |
| `BC_STRING_MAX` | 2 147 483 647 | Same value as GNU `bc`. |
| Exponent of `^` | The integer part must fit in a signed 64-bit integer | Same as GNU's "MAX Exponent". |
| Exact scale of `a ^ b` | `scale(a) · \|b\|` must not exceed `BC_SCALE_MAX` | `bc_clone` computes the exact power and then truncates it. GNU truncates intermediate results, so it can evaluate `0.5 ^ 2000000000` (slowly). |

Every `BCNum` scale stays at most `BC_SCALE_MAX`. This invariant establishes the
`scale <= MAX_VERIFIED_SCALE` preconditions of the Verus-verified scale kernels, and keeps every
decimal shift below `u32::MAX`, including on 32-bit targets.

Running out of memory (for example `scale=1000000000; 1/3`) is outside the language semantics: the
process may abort, as GNU `bc` does.

---

## 3. Behavior for undefined or unspecified cases

### 3.1 Errors and recovery
- **Runtime errors**: `bc_clone` prints a diagnostic to stderr, discards the remainder of the
  current *input unit*, and continues with the next one. An input unit is one line, or one complete
  multi-line construct (a braced block or a `define`). Example: `printf '1/0; 5\n7\n'` prints the
  diagnostic and then `7`.
- **Syntax errors**: a diagnostic, then processing continues with the next input unit.
- Dynamic scopes (parameters and `auto`) are restored when an error unwinds out of a function.
- **Exit status**: 0 when all input was processed without any error. 1 when any syntax or runtime
  error occurred (processing still continues to the end), when an option is invalid, or when a file
  cannot be opened. Warnings do not change the exit status.

### 3.2 Diagnostic formats
| Kind | Format |
|---|---|
| Syntax error | `<source> <line>: syntax error`, or `<source> <line>: illegal character: <c>` for a character that cannot start a token (`<source>` is the file name, or `(standard_in)` for stdin) |
| Runtime error | `Runtime error (func=<name>): <message>` (`<name>` is `(main)` at top level) |
| Runtime warning | `Runtime warning (func=<name>): <message>` |

The message texts follow GNU `bc`: `Divide by zero`, `Modulo by zero`,
`Square root of a negative number`, `Parameter type mismatch parameter <p>.`,
`Function <f> not defined.`, `Parameter number mismatch`, `Array <a> subscript out of bounds.`,
`exponent too large in raise`, `scale too large`. Unlike GNU, `bc_clone` does not print a bytecode
address (`adr=N`).

### 3.3 Out-of-range and undefined operations
| Situation (POSIX: undefined) | Behavior |
|---|---|
| Division by zero / modulus by zero | Runtime error `Divide by zero` / `Modulo by zero` |
| `sqrt` of a negative number | Runtime error `Square root of a negative number` |
| Non-integer exponent | Warning `non-zero scale in exponent`; the integer part is used |
| `ibase` < 0, < 2, or > 16 | Warning `negative ibase, set to 2` / `ibase too small, set to 2` / `ibase too large, set to 16`; value clamped |
| `obase` < 0, < 2, or > `BC_BASE_MAX` | Warning `negative obase, set to 2` / `obase too small, set to 2` / `obase too large, set to 2147483647`; value clamped |
| `scale` < 0 or > `BC_SCALE_MAX` | Warning `negative scale, set to 0` / `scale too large, set to 1000000000`; value clamped. The sign is that of the assigned value (`scale=-0.5` warns). Also applies to `++`/`--` |
| Value of an assignment to a register | The value assigned, before clamping (`x = (scale = 2.7)` sets `x` to 2.7), as in GNU |
| A result or literal whose scale would exceed `BC_SCALE_MAX` (`%` with `scale + scale(b)` too large, `a^b` with a too-large exact scale) | Runtime error `scale too large` |
| Exponent outside the signed 64-bit range | Runtime error `exponent too large in raise` |
| Array subscript < 0 (including fractions like `-0.5`) or ≥ `BC_DIM_MAX` | Runtime error `Array <a> subscript out of bounds.` |
| Input digit ≥ `ibase` | As in GNU: a single-digit number keeps its face value (`ibase=2; 3` → 3); in a multi-digit number, such a digit counts as `ibase`−1 (`ibase=2; 12` → 3) |
| `break` outside a loop, `return` outside a function | Syntax error `Break outside a for/while` / `Return outside of a function.` (GNU wording) |
| Calling an undefined function, or calling with the wrong number of arguments | Runtime error |
| `l(x)` with `x <= 0` | Returns −(10^scale − 1) for the caller's `scale`, like GNU's library (`scale=3; l(0)` → `-999.000`) |

### 3.4 Accuracy of the math library
For `s`, `c`, `a`, `l`, `e`, `j`, the result is the exact mathematical value **truncated toward
zero** to the current `scale`. This must hold for any argument magnitude whose result fits in
memory: argument reduction must carry enough guard digits for the size of the argument.
`s` and `c` compute π with as many extra digits as the argument has integer digits. The
integration test `test_math_library_against_high_precision_oracle` checks every function against
GNU `bc` evaluated at `scale + 100` and truncated.

---

## 4. Extensions

These are accepted by default. Each use is reported with GNU bc's wording, as
`<source> <line>: (Warning) <description>` under `-w` (the unit still runs), or as
`<source> <line>: Error: <description>` under `-s` (the unit is not executed and counts as an
error). If both are given, `-s` wins. Embedders select the same behavior with
`Evaluator::extension_policy`, `bc_session_set_extension_policy` (C), or
`BcSession.set_extension_policy` (Wasm).

| Extension | Example |
|---|---|
| Identifiers longer than one letter (letters, digits, `_`) for variables, arrays, functions, parameters, and `auto` names — `multiple letter name - <name>` | `total = 5`, `define fib(n)` |
| A relational expression as a statement (its value, 0 or 1, is printed) — `comparison in expression` | `1 < 2` |
| `return` with an expression that is not in parentheses — `return expression requires parenthesis` | `return x + 1` |
| A function body that does not begin with a newline after `{` — `End of line required` | `define f(x) { return (x) }` |

### Not supported in v0.4.0
These GNU `bc` extensions are a syntax error in every mode: `else`, `print`, `continue`, `halt`,
`limits`, `warranty`, `read()`, `&&`, `||`, `!`, `#` comments, relational operators inside larger
expressions (`x = (1 < 2)`), empty `for` clauses (`for (;;)`), `last` and `.` as "last printed
value", `define void`, and array references (`*a[]`). The names `last`, `halt`, etc. are ordinary
multi-letter identifiers.

---

## 5. Known differences from GNU bc 1.08

| Area | GNU bc | bc_clone |
|---|---|---|
| Math library accuracy | Can be wrong at low `scale` for large arguments (`scale=5; s(1000000)` → `-.27332`) | Exact truncation (`-.34999`) |
| Maximum `ibase`, digits | 36; digits `G`–`Z` are accepted | 16 (POSIX); only `0-9A-F` are digits, so `1G` is a syntax error |
| `BC_SCALE_MAX` | 2 147 483 647 | 1 000 000 000 |
| Exit status after errors | 0 | 1 (§3.1) |
| `sqrt` of an exact value | `sqrt(1.000)` prints `1` | `1.0000` at `scale=4`, as POSIX's scale rule requires |
| `return ()` | Syntax error | Returns 0, as POSIX's grammar allows |
| Diagnostics | Include `adr=N` | No address |
| Unsupported extensions | — | §4 "Not supported" |
| Command-line options | `-h -i -l -q -s -v -w` and long forms; options can be grouped | Only `-l`, `-s`, `-w`, one per argument; any other option is an error (status 1) |
