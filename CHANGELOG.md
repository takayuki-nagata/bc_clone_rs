# Changelog

## Unreleased

Without `-l`, the execution of every input unit after parsing is now proved with Verus to refine
an executable formal specification of `bc`, and each `-l` function is proved to return the exact
value truncated toward zero at `scale`. The parser is not proved; differential tests check it
against the specification. AGENTS.md lists what the proofs assume.

### Verification
- **Executable specification.** `crates/bc_spec` defines `bc_clone`'s stdout, stderr and exit
  status for any input without `-l`: input units, tokens, parsing, evaluation, output
  and diagnostics. `exec_spec_verified!` compiles it into the reference interpreter
  `bc_spec_oracle` (`scripts/build_spec_oracle.sh`) and proves the compiled code equal to the
  specification, and lemmas prove its arithmetic and output exact against integer definitions
  (`spec_num.rs`, `l0_format`). It is a Cargo package outside `default-members`, verified with
  `cargo verus verify -p bc_spec`.
- **Arithmetic and output.** `BCNum`'s operations (`add`, `sub`, `mul`, `try_div`, `try_mod_op`,
  `try_pow`, `try_sqrt`, `length`, `scale_func`, the comparison `cmp_val`) and the value of a
  constant compute the integer definitions of the POSIX operations exactly. The output of a
  number (`format_bytes`) writes the specification's `l0_format` for every `obase`, and the
  70-column wrapping matches the specification's `write_wrapped`.
- **Evaluator.** Expression evaluation, statement execution, function calls and the execution of
  an input unit (`Evaluator::run_parsed`: `-w`/`-s` diagnostics, syntax and runtime diagnostics,
  `quit`, whether the unit failed) refine the specification for every program the parser builds,
  without `-l` (partial correctness). The theorem assumes that the parser's output corresponds
  to the specification's (`driver::r_parsed`), which the differential tests check.
  `Evaluator::new` and the public setters are proved to establish and keep the invariant that
  these theorems assume.
- **Math library.** Verus proves, over the reals, that the ball operations contain their exact
  results, that the retry loop returns the truncation of the true value, that the balls of π and
  ln 2 and of each series with its tail bound contain their values, and so that an `Ok` result of
  `s`, `c`, `a`, `l`, `e` or `j` is the exact value truncated toward zero (partial correctness:
  that a series loop ends is not proved). The facts of real analysis the proofs assume are stated
  as axioms with their sources in `crates/bc_core/src/trusted_math.rs`.
- **Tests.** `crates/bc_cli/tests/spec_differential.rs` compares `bc_clone` with the specification
  on random programs, including inputs that cannot be compared with GNU `bc` (syntax errors,
  `ibase` changes, `-s`/`-w`, `quit`, invalid UTF-8), checks the parser's output against the
  specification's, and checks the specification against GNU `bc`. The POSIX conformance script
  also runs against the specification (`BC_BIN=target/bc_spec_oracle`). A second differential
  fuzzer generates deeply nested programs.
- **Build.** `bc_core` is verified with `cargo verus verify -p bc_core --features verify`; the
  `verify` feature links `vstd` and the specification, which production builds never link.

### Math library
- `s`, `c`, `a`, `l`, `e`, `j` compute with rigorous error bounds (midpoint-radius interval
  arithmetic) and return a result only when every value within the bounds truncates to it,
  recomputing with twice the guard digits otherwise. The result is the exact value truncated
  toward zero for every argument, not only where fixed guard digits happened to suffice.
  `docs/MATH_ERROR_BOUNDS.md` derives the bounds.
- `e(x)` with a very large argument no longer crashes or returns 0 (`e(-(10^20))` aborted with an
  internal error and `e(10^20)` printed `0`), and `j(n,x)` with an order outside the 64-bit range
  no longer computes `J_0` (`j(10^20,1)` printed `.765…`) or aborts
  (`j(-9223372036854775808,1)`). Results that truncate to 0 are returned without computing them;
  an argument of `e` or `j` whose integer part exceeds 2 000 000 000, and an order of `j` outside
  the range whose result is not provably 0, are the new runtime error `argument too large`.

### Behavior changes and fixes
- An input unit longer than 1 000 000 000 bytes is now the syntax error `input unit too long`
  (`docs/COMPATIBILITY.md` §2), instead of leaving the range the lexer's bounds were checked for.
- **Input.** A NUL character no longer ends the input unit silently: it is reported as
  `illegal character: ^@` and processing continues. Other control characters are shown as `^X`,
  and DEL and non-ASCII characters as octal escapes (`\177`), as in GNU `bc`. Input that is not
  valid UTF-8 is no longer discarded without a diagnostic: invalid bytes are reported as illegal
  characters and the rest is processed, on standard input (also interactively) and in files, and
  such a file is no longer `cannot open file`. Input is read as bytes and not decoded: the
  bytes of a string are printed unchanged (as in GNU; before, invalid UTF-8 became U+FFFD), and
  outside a string an invalid byte is shown as itself (`\377`), while a well-formed multi-byte
  character is shown as one (`\303\251`). The C API no longer rejects code that is not UTF-8
  with `BC_STATUS_ERR_EXECUTION`. An unterminated string is reported at the line where it
  starts.
- **Nesting limit.** Deep nesting no longer crashes with a stack overflow (a 20 000-term sum,
  10 000 nested parentheses or recursion 10 000 calls deep aborted the process, and could corrupt
  memory on embedded targets). Statements, expressions and pending calls have a nesting limit
  (`docs/COMPATIBILITY.md` §2), reported as `nesting too deep`. The CLI evaluates on a 512 MiB
  stack with a limit of 100 000 levels; embedders set `Evaluator::max_depth` or call the new
  `bc_session_set_max_depth`. The Zephyr main stack grows to 96 KiB.
- **`ibase` in functions.** Numeric constants in a function body are interpreted in the `ibase` in
  effect when the function was invoked, as POSIX requires, even if the body changes `ibase`:
  `define f() { ibase = 16; return (10) }; f()` printed 16 and now prints 10.
- **Powers on 32-bit targets.** On RISC-V and Wasm, a power of a number without fractional digits
  whose exponent does not fit in 32 bits, such as `1^5000000000`, is no longer
  `scale too large`.
- **Diagnostics.** A syntax error no longer clears the `break` and `return` flags (only a runtime
  error does; no unit leaves them set). A diagnostic's line number above 2³² − 1 is replaced by
  the unit's first line (`docs/COMPATIBILITY.md` §3.2).
- A name repeated in a function's parameter and `auto` lists is accepted (now documented).

### Command line
- Options follow the XBD 12.2 Utility Syntax Guidelines, as POSIX requires: options may be grouped
  (`-lw`), `--` ends the options, and `-` is a file operand. Long options are reported as
  `bc: unrecognized option '--name'`.

### API changes (`bc_core`)
- The `Evaluator`'s state is no longer public: `variables`, `arrays`, `functions`,
  `math_enabled`, the output streams, the `break`/`return`/`quit` flags and `return_value` are
  crate-private, so that code outside `bc_core` cannot store a number that breaks the invariant
  the proofs rely on (every scale at most `BC_SCALE_MAX`). Front ends use the new methods
  `stderr_writer()` (an `ErrWriter` with `write_fmt` and `flush`, so `writeln!` works),
  `request_quit()`, `clear_quit()` and `reset_control_flags()`; `max_depth` and
  `extension_policy` stay public.
- The panicking convenience wrappers (`BCNum::from_string`, `div`, `mod_op`, `pow`, `sqrt`,
  `Lexer::get_next_token`, `Lexer::peek_token`, `Parser::new`, `Parser::parse_program`,
  `Evaluator::evaluate`, `Evaluator::execute`) are removed from the public API. Use the `try_*`
  forms, which return every error as an `Err`.
- `BCNum`'s arithmetic (`add`, `sub`, `mul`, `try_div`, `try_mod_op`, `try_pow`, `try_sqrt`,
  `length`, `cmp_val`, `from_digit_values`), `format_bytes`, the math library functions
  (`math::bc_sin`, …, `bc_bessel`) and the kernels in `verified_kernels` that no front end
  calls are no longer public. They require bounds that nothing checks at run time (every scale
  at most `BC_SCALE_MAX`), so a caller outside `bc_core` could break the proofs' preconditions
  with a `BCNum` built by `BCNum::new`. Evaluate through `Evaluator` instead.
- `BCNum::format_obase` is replaced by `try_format_obase`. It returns the new
  `RuntimeError::BaseOutOfRange` for an `obase` outside 2 to `BC_BASE_MAX`, and `ScaleTooLarge`
  for a scale above `BC_SCALE_MAX`.
- `BCNum::try_from_string` returns `BaseOutOfRange` for an `ibase` outside 2 to 16, and
  `ScaleTooLarge` for a constant with more than `BC_SCALE_MAX` fraction digits before converting it, and reads a constant with the evaluator's verified digit
  conversion. Lowercase letters read as uppercase; the result for characters that cannot appear
  in a constant is unspecified (they used to read as 0).
- The new `RuntimeError::MathArgumentTooLarge` is reported as `argument too large` (see
  Math library).
- Operators in the syntax tree are enums instead of strings: `Expr::BinaryOp(BinOp, …)`,
  `RelationalOp(RelOp, …)`, `AssignOp(AssignOp, …)` (`Assign` or `Compound(BinOp)`),
  `Negate(…)` instead of `UnaryOp(char, …)`, and `Update(increment, prefix, target)` instead of
  `UpdateOp(String, prefix, target)`, in the order of the specification's operator codes.
- Array frames are `BTreeMap<usize, BCNum>` instead of `BTreeMap<BigInt, BCNum>` (subscripts are
  below `BC_DIM_MAX`). `BcError::in_function` takes the function name as `&String`.
  `Register::name` is removed.
- Input is bytes: `Lexer::new`, `Evaluator::run_source`, `Evaluator::run_unit` and
  `UnitAccumulator::push_line` take `&[u8]`, `UnitAccumulator` returns units as `Vec<u8>`,
  `Token::value` is a `Vec<u8>`, and a string in the syntax tree is
  `Stmt::StringLiteral(Vec<u8>)`. Pass `text.as_bytes()` where a `&str` was passed.
  `bc_cli`'s `count_open_braces`, `is_block_incomplete` and `run_non_interactive_block` take
  `&[u8]` too.
- `BcWriter` has a new method `write_bytes`, through which the evaluator writes all output.
  Its default implementation passes the bytes to `write_str`, replacing invalid UTF-8 with
  U+FFFD; a writer to a byte stream overrides it to write them unchanged (`bc_cli`'s
  `IoWriter` does). The output streams used to drop a chunk that was not UTF-8.
- `bc_core` denies `unwrap`, `expect`, `panic!`, and lossy integer casts outside tests.

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
