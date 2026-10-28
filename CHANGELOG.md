# Changelog

## Unreleased

### Verification
- New executable formal specification `crates/bc_spec`: Verus specifications from input bytes to
  stdout, stderr and exit status (decoding, input units, tokens, parsing, evaluation, output and
  diagnostics; `-l` is not modeled). `exec_spec_verified!` compiles it into the reference
  interpreter `bc_spec_oracle` (`scripts/build_spec_oracle.sh`) and proves the compiled code equal
  to the specification; lemmas prove its arithmetic exact against integer definitions.
- `crates/bc_cli/tests/spec_differential.rs` compares `bc_clone` with the specification on random
  programs, including inputs that cannot be compared with GNU `bc` (syntax errors, `ibase`
  changes, `-s`/`-w`, `quit`, invalid UTF-8), and checks the specification against GNU `bc`. The
  POSIX conformance script also runs against the specification (`BC_BIN=target/bc_spec_oracle`).
- `crates/bc_spec` is a Cargo package (library and the `bc_spec_oracle` binary) in the workspace,
  outside `default-members`. It is verified with `cargo verus verify -p bc_spec`, and the oracle
  is compiled with a normal `cargo build`.
- `bc_core` is verified with `cargo verus verify -p bc_core --features verify`. The `verify`
  feature links `vstd` and the executable specification (for the refinement proofs); production
  builds link neither. The L0 number model `spec_num.rs` moved into `crates/bc_spec`.
- Lemmas for the refinement proofs, in `crates/bc_spec`: an evaluation that did not run out of
  fuel gives the same result with more fuel (`fuel.rs`), and array subscripts and register
  stores depend only on the value of a number, not on its digit sequence (`values.rs`).
- The output of a number has an integer-level definition in the specification (`l0_format` in
  `crates/bc_spec/src/format.rs`: digits by repeated division and multiplication, and the
  smallest `k` with `obase^k >= 10^scale` fraction digits), and Verus proves that the executable
  `format_num` computes it for every `obase` from 2 to `BC_BASE_MAX`. The specification now also
  prints the integer part of numbers with 2^28 or more digits, which it used to omit.
- The output of numbers in `bc_core` (`BCNum::format_bytes`, behind `format_obase`) is verified
  with Verus to write that definition for every `obase`, with the same output and speed as before.
- `BCNum::add`, `sub`, `mul`, `try_div`, `try_mod_op`, `try_pow`, `try_sqrt`, `length`,
  `scale_func`, the comparison used by `==`, `<`, … (`cmp_val`) and the value of a constant
  (`from_digit_values`) are verified with Verus: they compute the integer (L0) definitions of
  the POSIX operations exactly, assuming only the `num-bigint` operations listed in
  `crates/bc_core/src/trusted_bigint.rs`.

### Math library
- `s`, `c`, `a`, `l`, `e`, `j` now compute with rigorous error bounds (midpoint-radius interval
  arithmetic) and return a result only when every value within the bounds truncates to it,
  recomputing with twice the guard digits otherwise. The result is the exact value truncated
  toward zero for every argument, not only for arguments where fixed guard digits happened to
  suffice. Verus proves the truncation decision; `docs/MATH_ERROR_BOUNDS.md` derives the bounds.
- `j(n,x)` with an argument whose integer part exceeds 2 000 000 000 is `argument too large`
  instead of a computation that cannot finish.

### Fixes
- On 32-bit targets (RISC-V, Wasm), a power of a number without fractional digits whose exponent
  does not fit in 32 bits, such as `1^5000000000`, is no longer `scale too large`: the exact scale
  of a power is computed in 64 bits. Found by the refinement proof of `^`.
- A NUL character in the input no longer ends the input unit silently. It is reported as
  `illegal character: ^@` and processing continues with the next unit. Other control characters
  are shown as `^X`, and DEL and non-ASCII characters as octal escapes (`\177`), as in GNU `bc`.
- An unterminated string is reported at the line where it starts.
- Input that is not valid UTF-8 is no longer discarded without a diagnostic. Invalid bytes are
  reported as illegal characters and the rest of the input is processed, on standard input
  (also interactively) and in files. A file that is not UTF-8 is no longer reported as
  `cannot open file`.
- `e(x)` with a very large argument no longer crashes or returns 0: `e(-(10^20))` used to abort
  with an internal error and `e(10^20)` printed `0`. A result that truncates to 0 is now
  returned without computing it, and an argument whose integer part exceeds 2 000 000 000 is the
  new runtime error `argument too large`.
- `j(n,x)` with an order outside the 64-bit range no longer computes `J_0`
  (`j(10^20,1)` printed `.765…`), and `j(-9223372036854775808,1)` no longer aborts. Large orders
  whose result truncates to 0 return 0; other orders outside the range are `argument too large`.
- `bc_core` no longer panics when an embedder empties a scope stack through the public
  `Evaluator::variables` / `Evaluator::arrays` fields.
- Deep nesting no longer crashes with a stack overflow. Programs such as a 20 000-term sum, 10 000
  nested parentheses, or recursion 10 000 calls deep aborted the process (and could corrupt
  memory on embedded targets). Statements, expressions, and pending calls now have a nesting
  limit (`docs/COMPATIBILITY.md` §2), reported as `nesting too deep`. The CLI evaluates on a
  512 MiB-stack thread with a limit of 100 000 levels; embedders set `Evaluator::max_depth` or
  call the new `bc_session_set_max_depth`. The Zephyr main stack grows to 96 KiB.
- Numeric constants in a function body are interpreted in the `ibase` in effect when the
  function was invoked, as POSIX requires, even if the body changes `ibase`:
  `define f() { ibase = 16; return (10) }; f()` printed 16 and now prints 10, as GNU `bc` does.
- Documented behavior: a name repeated in a function's parameter and `auto` lists is accepted.
- Command-line options follow the XBD 12.2 Utility Syntax Guidelines, as POSIX requires: options
  may be grouped (`-lw`), `--` ends the options, and `-` is a file operand. Long options are
  reported as `bc: unrecognized option '--name'`.

### API changes (`bc_core`)
- The panicking convenience wrappers (`BCNum::div`, `mod_op`, `pow`, `sqrt`,
  `Lexer::get_next_token`, `Lexer::peek_token`, `Parser::new`, `Parser::parse_program`,
  `Evaluator::evaluate`, `Evaluator::execute`) are removed from the public API. Use the `try_*`
  forms, which return every error as an `Err`.
- `math::bc_sin`, `bc_cos`, `bc_atan`, `bc_ln`, `bc_exp` and `bc_bessel` return
  `Result<BCNum, RuntimeError>`; the new `RuntimeError::MathArgumentTooLarge` is reported as
  `argument too large`.
- `bc_core` denies `unwrap`, `expect`, `panic!`, and lossy integer casts outside tests.
- `BCNum::from_string` is replaced by `BCNum::try_from_string`, which returns `ScaleTooLarge`
  for a constant with more than `BC_SCALE_MAX` fraction digits before converting it; the
  panicking `from_string` remains for tests only.

## v0.4.0 — 2026-10-26

This release makes POSIX.1-2024 the authoritative specification and fixes the defects found by
reviewing the verification suite and testing against GNU `bc`. All behavior is specified in
[docs/COMPATIBILITY.md](docs/COMPATIBILITY.md).

### Release assets
- Releases now also include the example targets, each with run/flash scripts and a README:
  the WebAssembly web app, the bare-metal M5Stamp C3 firmware, the bare-metal QEMU RISC-V 32
  self-test images, and the Zephyr RTOS images (QEMU RISC-V 32 with self-test and REPL variants,
  and M5Stamp C3). `scripts/package_release.sh` builds them.
- `scripts/setup_zephyr_workspace.sh` creates a pinned Zephyr v3.7.2 / SDK 0.16.8 workspace.
  CI now builds and tests the Zephyr application on QEMU on every push.
- The Zephyr application has a `CONFIG_BC_QEMU_REPL` option to start the REPL on QEMU.

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
