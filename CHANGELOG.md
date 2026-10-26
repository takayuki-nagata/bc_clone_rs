# Changelog

## v0.4.0 — unreleased

This release makes POSIX.1-2024 the authoritative specification and fixes the defects found by
reviewing the verification suite and testing against GNU `bc`. All behavior is specified in
[docs/COMPATIBILITY.md](docs/COMPATIBILITY.md).

### Behavior changes
- **Runtime errors no longer print Rust panic messages.** Errors use GNU `bc`'s wording without the
  bytecode address, e.g. `Runtime error (func=f): Divide by zero` and
  `(standard_in) 3: syntax error`. Processing continues with the next input unit. A unit is one
  line, or one multi-line construct.
- **Exit status**: 1 if any syntax or runtime error occurred, otherwise 0. Earlier files no
  longer stop later files and stdin from being processed.
- **Limits** (`docs/COMPATIBILITY.md` §2):
  - `scale` is clamped to 0..1 000 000 000, `obase` to 2..2 147 483 647, and `ibase` to 2..16,
    with GNU-style warnings (`negative scale, set to 0`, …);
  - array subscripts outside 0..16 777 215 are runtime errors;
  - exponents outside the 64-bit range are errors;
  - a non-integer exponent warns.
- Syntax errors are reported with line numbers that count across the whole input.
- `break` outside a loop and `return` outside a function are syntax errors.
- `return ()` returns 0, as POSIX allows.
- New options `-s` (reject GNU extensions) and `-w` (warn about them).
- In a multi-digit number, a digit ≥ `ibase` counts as `ibase`−1, as in GNU `bc`.
- `l(x)` for x ≤ 0 returns 1 − 10^scale at the caller's scale.

### Fixed
- `scale=4294967297; x = 1/3; x == 0.3` printed 1. Scales were silently truncated to 32 bits.
- `s(x)` and `c(x)` lost accuracy for large arguments (`scale=20; s(10^40)`).
- `A = 1` (a number on the left of `=`) was accepted. `a + b = 3` silently did nothing; it is now
  `a + (b = 3)`, as in GNU `bc`.
- `(a = 5)` was not printed.
- A name first used as a function parameter or `auto` local caused an internal panic when it was
  assigned at top level after the call.
- An array subscript in `a[i++] += 1` or `a[i++]++` was evaluated twice. The target of `op=` is now
  read before the right-hand side, so `c = 5; c += c++` gives 10, as in GNU `bc`.
- An unterminated block at the end of input was silently ignored.
- `%` by zero reports `Modulo by zero`; zero to a negative power reports `divide by zero`.
- C API: a `default_scale` above the limit could break the evaluator's scale invariant. An
  output that does not fit the caller's buffer now leaves an empty string instead of an
  untouched buffer.
- Zephyr and ESP32-C3 REPLs: multi-line input (including POSIX function definitions) now works,
  and input lines are capped at 1024 bytes so typing cannot exhaust the heap.

### API changes (`bc_core`)
- Errors are typed: `BcError` / `RuntimeError` replace `String` and `&'static str`.
- New `driver` module: `UnitAccumulator`, `Evaluator::run_unit`, and `Evaluator::run_source`.
- The `scale`, `ibase`, and `obase` fields are private. Use `scale()` / `set_scale()` (clamping),
  `ibase()`, and `obase()`.
- New `Evaluator::extension_policy` (`ExtensionPolicy`) and `Expr::Paren`. Registers are
  `Expr::RegisterAccess(Register)`.
- C API: `bc_session_set_extension_policy()`. Wasm: `BcSession.set_extension_policy()`.

### Verification
- `docs/COMPATIBILITY.md`: a POSIX.1-2024 based specification used as the test oracle.
- The differential tests compare stdout, diagnostics, and exit status (they previously compared
  stdout only).
- The POSIX conformance suite has expected outputs derived from the standard, and each case runs
  in the default mode and with `-s`.
- Property tests check the arithmetic against an exact reference. Random programs are compared
  with GNU `bc`. The math library is checked against GNU `bc` at `scale + 100`.
- Kani verifies the production C-FFI output helper. Miri also runs the C API under Tree Borrows.
- Documentation states what the Verus, Kani, Miri, property, differential, and mutation layers
  do and do not cover.
