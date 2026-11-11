# bc_clone_rs: Design, Verification Architecture & Agent Guide

This document describes the architecture, numerical algorithms, and verification strategy of
`bc_clone_rs`, a Rust implementation of the POSIX `bc` calculator (binary: `bc_clone`). It is the
reference for both human contributors and AI coding agents.

> Development history: v0.1.0–v0.3.0 were written by the Antigravity agent. From v0.4.0 the project
> is developed with Claude Code. Statements in this file are kept in sync with the code; when you
> change behavior or verification coverage, update this file in the same commit.

## Specification

- **Authoritative specification**: POSIX.1-2024 (Issue 8), `bc` utility —
  <https://pubs.opengroup.org/onlinepubs/9799919799/utilities/bc.html>.
- Where POSIX leaves behavior undefined or unspecified, `bc_clone` chooses behavior close to
  GNU `bc` 1.08 and documents it as implementation-defined in `docs/COMPATIBILITY.md`.
- The GNU extensions listed in `docs/COMPATIBILITY.md` §4 (multi-letter names, relational
  expressions as statements, `return` without parentheses, one-line function bodies) are accepted
  by default; `-s` rejects and `-w` warns about them. `else`, `print`, `continue`, `&&` and the
  other GNU additions are not supported.
- The executable specification in `crates/bc_spec` encodes POSIX and these implementation-defined
  choices as a function from input bytes to stdout, stderr and exit status. It is the primary
  oracle of the differential tests; GNU `bc` remains a secondary check of the specification.
- Results of the `-l` math library are defined as the mathematically exact value truncated toward
  zero at the current `scale`; GNU `bc` output is *not* the oracle for these functions.

## Workspace Layout

```mermaid
graph TD
    CLI[crates/bc_cli: CLI & REPL] --> Core[crates/bc_core: no_std + alloc engine]
    CAPI[crates/bc_c_api: C ABI staticlib] --> Core
    Zephyr[crates/bc_zephyr: Zephyr RTOS app logic] --> Core
    QEMU[crates/bc_qemu_riscv32: bare-metal self-test] --> Core
    Wasm[examples/wasm_web_app/crate: wasm-bindgen] --> Core
    Core --> Parser[parser/: Lexer + Pratt parser]
    Core --> Eval[eval/: Evaluator]
    Core --> Math[math.rs: BCNum]
    Core --> MathLib[mathlib/: certified -l library]
    Core --> Kernels[verified_kernels.rs: dual-mode kernels]
```

| Path | Role |
|---|---|
| `crates/bc_core` | `#![no_std]` + `alloc` engine: lexer, parser, evaluator, arithmetic, math library (`mathlib/`) |
| `crates/bc_cli` | `bc_clone` binary: option parsing, file/stdin processing, interactive REPL, SIGINT |
| `crates/bc_c_api` | C ABI (`include/bc_core.h`): `bc_eval`, `bc_eval_callback`, `bc_session_*` |
| `crates/bc_zephyr` | Zephyr RTOS application logic (self-tests, serial REPL); C trampoline in `examples/zephyr_app` |
| `crates/bc_qemu_riscv32` | Bare-metal RISC-V 32 self-test runner for QEMU `virt` |
| `crates/bc_spec` | Executable formal specification: Verus `spec fn`s from input bytes to stdout, stderr and exit status, compiled by `exec_spec_verified!` into the reference interpreter `bc_spec_oracle` (`scripts/build_spec_oracle.sh`). A workspace member outside `default-members`: `cargo verus verify -p bc_spec` checks it, and a normal `cargo build` compiles the oracle, because `verus!` erases the specifications |
| `examples/m5stamp_c3` | ESP32-C3 bare-metal app (`esp-hal`) |
| `examples/wasm_web_app` | Browser frontend backed by `bc_core` compiled to `wasm32-unknown-unknown` |

## Core Engine (`crates/bc_core`)

### Lexer and parser (`src/parser/`)
- The lexer is proved against the specification's `lex`: `Lexer::rest` is the tokens not yet
  returned, and `try_get_next_token` and `try_peek_token` take a token off it or look into it. It
  assumes the one-line wrappers `ascii_string` and `copy_bytes`.
- The lexer works on bytes, which need not be UTF-8. It tracks line numbers and handles
  `/* */` comments, strings, and backslash-newline continuation. A string keeps its bytes
  (`Node::Str(Vec<u8>)`). An illegal character is the well-formed UTF-8 sequence
  that starts at that byte, or the byte alone (`verified_utf8_char_len`).
- The parser is recursive descent, with Pratt precedence climbing for expressions. Assignment and
  `^` are right-associative. Precedence and associativity come from `verified_pratt_infix_info`.
- The syntax trees of a unit are a flat arena, `Code { nodes: Vec<Node> }`, with `usize` children.
  It has the variants and the indices of the specification's arena: the parser adds a node
  exactly when the specification's `add_node` does. Dropping or copying it does not recurse.
  A defined function, `FunctionDef { code: Rc<Code>, def }`, shares the arena of its unit, so a
  call does not copy the body, and a running body survives its redefinition; the arena stays
  in memory while a function defined in it does.
- Fallible API: `Lexer::try_get_next_token`, `Lexer::try_peek_token`, `Parser::try_new`,
  `Parser::try_parse_program`.
  `quit` makes `try_parse_program` return `Err(BcError::Quit)` so execution stops at that point, as
  POSIX requires.

### Numbers (`src/math.rs`)
- `BCNum { coeff: BigInt, scale: usize }` represents `coeff × 10^-scale`. Arithmetic follows the
  POSIX scale rules. The scale and shift computations are delegated to kernels in
  `verified_kernels.rs`.
- `add`, `sub`, `mul`, `try_div`, `try_mod_op`, `try_pow`, `try_sqrt`, `length`, `scale_func`,
  `cmp_val` (comparison) and `from_digit_values` (the value of a constant) are written inside
  `verus!` and proved to compute the L0 operations of `spec_num` and `bc_spec` (`spec_add`, …,
  `spec_pow`, `is_isqrt`, `is_digit_count`, `spec_horner`, through `BCNum::val`), given scales of
  at most `BC_SCALE_MAX`. They use `BigInt` only through `bigint.rs`, which derives every
  operation in verified code from nine primitives in `trusted_bigint.rs` (`+`, `-`, `*`, the
  truncating quotient and remainder, comparison, clone, the conversions from `u64` and to `i64`,
  and the bit length). Verus assumes those one-line wrappers correct; each is checked by a test,
  the arithmetic ones on multi-limb values against the specification's decimal arithmetic and,
  for long products, against schoolbook multiplication. The output `format_bytes` (`src/format.rs`) is
  proved to write the specification's `l0_format` of the value for every `obase` from 2 to
  `BC_BASE_MAX`. Constants are read with the verified `math::literal_digit_values`, by the
  evaluator and by the public `BCNum::try_from_string` alike.
- Public API: nothing checks the scale bound of these operations at run time, so they are
  `pub(crate)`, as are `format_bytes` and the `-l` functions; the evaluator is their only
  caller. Outside the crate a `BCNum` is built with `new`, `zero` or `try_from_string` and
  printed with `try_format_obase`. These two conversions check their preconditions in verified
  code (`from_digit_values_checked`, `checked_format_bytes`) and return `BaseOutOfRange` or
  `ScaleTooLarge`. Do not make a function with a `requires` clause public.
- Fallible API: `try_from_string`, `try_format_obase` (public), and inside the crate `try_div`,
  `try_mod_op`, `try_pow`, `try_sqrt`. The panicking wrappers (`from_string`, `format_obase`,
  `div`, `pow`, …) are compiled only under `cfg(test)`, as are `Lexer::get_next_token`,
  `Parser::new`, `Parser::parse_program`, `Evaluator::evaluate`, and
  `Evaluator::execute`.
- Output for `obase != 10` uses exact `BigInt` arithmetic. The number of fractional digits is the
  smallest `k` with `obase^k >= 10^scale`, so no floating point or `libm` is needed.

### Math library (`-l`, `src/mathlib/`)
Every function computes a **ball** (midpoint and radius in ulps of a working precision) that
provably contains the exact value. Each ball operation carries its own error bound, and series
add a bound on their omitted tail. `certified_trunc` returns the truncation to `scale` only if
every value in the ball truncates to it; otherwise `certify` doubles the guard digits and
recomputes (Ziv's strategy). Exact results (`s(0)`, `c(0)`, `a(0)`, `e(0)`, `l(1)`, `j(n,0)`) are
returned directly; every other result is transcendental, so the loop ends.
`docs/MATH_ERROR_BOUNDS.md` derives every bound.

| Function | Algorithm (as implemented) |
|---|---|
| π, ln 2 (internal) | Machin's formula `π = 16·atan(1/5) − 4·atan(1/239)` and `ln 2 = 2·artanh(1/3)`, summed with exact integer terms (`arc_inv`) |
| `s(x)`, `c(x)` | Reduce `x` by the integer multiple of 2π nearest to it, with π carrying one extra digit per integer digit of `x` (`reduce_angle`), then the Taylor series |
| `a(x)` | For `|x| > 1` use `π/2 − atan(1/|x|)`. Then four argument halvings `y/(1+√(1+y²))`, the Taylor series, and multiply by 16 |
| `l(x)` | Write `x = m·2^k` with `m` in `[0.7, 1.43)`, then `ln m = 2·artanh((m−1)/(m+1))`, plus `k·ln 2` |
| `e(x)` | Write `x = n·ln2 + r`, the Taylor series for `e^r`, then multiply by `2^n`. Results that truncate to 0 are returned without computation; `|x|` above `EXP_ARG_MAX` is an error |
| `j(n,x)` | Power series of `J_n`; for negative orders, `J_{-n} = (-1)^n J_n`. Orders large enough that the result truncates to 0 return 0 without computation |

Accuracy contract: every result is the exact value truncated toward zero
(`docs/COMPATIBILITY.md` §3.4). Verus proves this in place for all six functions (`bc_sin`,
`bc_cos`, `bc_atan`, `bc_ln`, `bc_exp`, `bc_bessel`): an `Ok` result has the caller's scale and is
the exact value truncated toward zero at that scale. The proof covers the ball operations, the
truncation decision and the retry loop (`certify`), the constants, every series with its tail
bound, and every argument reduction (lemmas in `real_arith.rs` and `mathlib/`). It assumes the
facts of real analysis stated as axioms in `trusted_math.rs`, and it is partial correctness (that
a series loop ends is argued in `docs/MATH_ERROR_BOUNDS.md`, not proved). The tests remain
(`mathlib::tests`, and `test_math_library_against_high_precision_oracle`, which compares with GNU
bc at `scale + 100`).
GNU's own results are *not* exact at the requested scale. When you change a function, keep its
section of `docs/MATH_ERROR_BOUNDS.md` in sync.

### Evaluator (`src/eval/`)
- Expressions and statements run on an explicit stack of frames (`eval/machine.rs` and its submodules), so their
  nesting does not use the native stack. A frame is what remains of one syntactic form once a sub-computation has
  a result; the proof relates it to the specification's `bc_spec::den::K` and keeps the meaning
  of the stack (`den`) equal to the result of the whole evaluation, so `eval_ref` has the same
  theorem as when it recursed; `exec_ref` likewise. Function calls are frames too (the
  arguments, the running body and the caller's saved state), and so are the arguments of the
  `-l` functions, so recursion depth is bounded by `max_eval_depth` and the heap, not by the
  native stack. The parser still recurses, within `max_depth`.
- The fast path (`eval/machine/quick.rs`) runs a call-free expression, or a statement made of
  them, by native recursion when it is at most `QUICK_BUDGET` (8) levels deep: it saves the
  frames of the common shallow cases, and its recursion is bounded by the budget, not by the
  input. Verus checks the bound: every function of the fast path decreases `(b, stage)`, where
  `b` is the budget left and `stage` orders the functions that pass the same `b` on, and only
  the loop of `while` and `for` in `quick_loop` is exempt (it need not end). The check of
  whether a statement may take the fast path looks at no more than `QUICK_STMTS` (64)
  statement nodes, the enclosing ones included, and leaves a larger statement to the machine,
  which checks each statement inside again; so the check made at each step looks at a bounded
  number of nodes however wide a block is (a block skipped by `if (0)` is not scanned on every
  pass of a loop). Its functions have the theorems of the machine's steps (`bs_ev`, `bs_exec`,
  …), and it counts the levels of `max_eval_depth` as the machine does. A shortcut whose recursion
  grows with the input (such as one argument after another, which `push_sub` therefore leaves
  to the machine) must not be added.
- Dynamic scoping: each variable or array name maps to a stack. Function parameters and `auto`
  locals push a new entry on entry. `BTreeMap` keeps the storage `no_std`-friendly and deterministic.
- `Evaluator::leave_call` pops the parameter and `auto` frames and restores the caller's
  control-flow flags and invocation `ibase` on every return path of a call, including `Err`
  returns (`ret_call` in `eval/machine/func.rs`). It is called explicitly (there is no RAII guard, which Verus cannot
  reason about), so a panic inside a call would leave the frames pushed; `bc_core` must not
  panic.
- Output goes through the `BcWriter` trait. `WrappedStdout` wraps long numbers at 70 columns with
  `\` + newline, as POSIX requires. The wrapping itself is `format::wrap_output`, verified against
  the specification's `write_wrapped`; `write_str` passes its result to the writer in one call.
- Fallible API: `Evaluator::try_evaluate`, `Evaluator::try_execute`.
- The evaluator's state (variables, arrays, functions, registers, flags, output streams) is
  `pub(crate)`, so `Evaluator::inv` is established by `new` (the verified `with_streams`) and
  kept by the verified functions alone, the public setters included; the documentation of
  `inv` gives the argument. Front ends configure it (`set_scale`, `max_depth`, `max_eval_depth`, `extension_policy`) and use
  `stderr_writer`, `request_quit`, `clear_quit` and `reset_control_flags`; do not add a method
  that stores a number without going through the verified storage layer.

### Error handling contract
- `bc_core` itself never needs to panic on user input. Every syntax or runtime error must be
  reachable as an `Err` from the `try_*` APIs.
- `lib.rs` denies `clippy::unwrap_used`, `expect_used`, `panic`, and the lossy-cast lints outside
  tests. Every remaining exception is an `#[allow(..., reason = "...")]` that names the invariant
  justifying it (the Verus-proved casts in `verified_kernels.rs`, `math.rs` and `mathlib/`). Do not replace an `unwrap` with a silent default (`unwrap_or(0)`):
  return an error or derive the value so that no default is needed.
- Clippy lints the code inside `verus!` as well (a normal build erases only the specifications
  and proofs). Allow a style lint on the function that needs it, with its reason (Ghost
  arguments, a binding used only by the proof, no `let` chains in Verus), not on a module.
- Front ends must not rely on unwinding: `catch_unwind` does not work under `panic = "abort"` or on
  `wasm32-unknown-unknown`.
- Errors are typed: `BcError` (`Quit`, `Syntax`, `Runtime { kind: RuntimeError, func }`) in
  `src/error.rs`. Do not match on message strings.
- `src/driver.rs` is the only place that turns input into executed units. `UnitAccumulator`
  groups lines into units, `SourceUnits` splits a whole text into units one at a time,
  `Evaluator::run_unit` / `run_next_unit` / `run_source` parse and execute them, and
  diagnostics are written in the format of `docs/COMPATIBILITY.md` §3.2. `run_unit` parses with
  the verified `parse_unit_ref`, and `run_parsed` executes the statements and writes every
  diagnostic. Every front end (CLI,
  C API, Zephyr, QEMU, ESP32-C3, Wasm) uses this driver, so error recovery is identical on all
  targets. The driver takes bytes; the CLI and the C API pass their input without decoding it.
- Recursion is bounded: `Evaluator::max_depth` limits the depth of the syntax tree (checked while
  parsing, the only part whose native recursion grows with the input), and `Evaluator::max_eval_depth` the number of
  levels evaluated at once, function calls included, on the heap (`eval/machine.rs` and its
  submodules). Each front end sets the first for the stack it runs on (`bc_cli` runs the engine on a 512 MiB-stack
  thread) and the second for the heap (`bc_cli`: 2 000 000, about 320 bytes a level; the other
  targets use one limit for both). Do not add a recursive walk over the arena: the trees in it
  can be as deep as `max_depth`, and evaluation must not use more native stack than the fast
  path's constant budget.
- `bc_cli` additionally wraps each unit in `catch_unwind` (each call of `run_next_unit` for a
  file or piped standard input, of `run_unit` in the REPL). A panic there is a bug in `bc_core`; it
  is reported as `bc_clone: internal error: …` and counted as a failed unit. After such a panic
  the evaluator's state may be inconsistent (frames of an interrupted call are not popped), and
  so may the `SourceUnits` of a step that panicked; its position has already moved past the line
  being read, so the loop still ends.

## Verified Kernels (`src/verified_kernels.rs`)

Small pure functions are defined once with `dual_verified!` / `dual_verified_repl_scanner!`:

- under Verus (`cfg(verus_keep_ghost)`), they expand inside `verus! {}` with their
  `requires`/`ensures` contracts;
- under normal builds, the same bodies compile as `#[inline]` functions that are called from
  production code.

Examples are the POSIX scale and shift computations for `+ - * / sqrt ^`, digit parsing,
`ibase`/`obase` clamping, the `WrappedStdout` column step, lexer cursor and lookahead bounds, the
UTF-8 sequence length of an illegal character, Pratt
precedence, the C-FFI buffer-capacity check, the Zephyr REPL character class, the CLI argument
class, and the REPL block-completeness scanner.

**Preconditions are not checked at runtime; callers establish them.** Several kernels require
`scale <= MAX_VERIFIED_SCALE` (10^9). The evaluator maintains the invariant "every `BCNum` scale is
at most `BC_SCALE_MAX` (= `MAX_VERIFIED_SCALE`)":

- the `scale` register is clamped by `verified_clamp_register`;
- `%` and `^` return `scale too large` instead of producing a larger scale;
- numeric literals with more fractional digits are rejected.

Decimal shifts go through `math::pow10_within`, whose precondition `n <= u32::MAX` Verus checks
at every call in verified code (all of `math.rs`, `format.rs`, `eval/` and `mathlib/`). The
`-l` functions require scales of at most `MAX_VERIFIED_SCALE`, which their verified callers
`Evaluator::finish_math1` and `finish_bessel` establish from `Evaluator::inv`. Review any new code that creates a `BCNum` scale against
this invariant.

A kernel is `pub` only if a front end calls it; of those, only `verified_repl_block_completeness`
has a precondition. Every call of a function with a `requires` clause is in verified code,
except the following, whose preconditions are argued here but not proved:

- The CLI's `count_open_braces` and `is_block_incomplete`, compiled only for tests and Kani, call
  `verified_repl_block_completeness`, which requires at most 10^9 bytes.
- The trusted glue. `WrappedStdout::write_str` passes its column to `format::wrap_output`; the
  column is 0 or a column that `wrap_output` returned, so at most `POSIX_WRAP_COL_LIMIT`.
  The public `run_unit`, `run_next_unit`, `run_source` and `UnitAccumulator::push_line` are
  `external_body` wrappers of `run_unit_ref`, `run_next_source_unit_ref`, `run_source_ref` and
  `push_line_ref`, and the front ends call them and `try_evaluate` and `try_execute`, which
  require `Evaluator::inv` (or `UnitAccumulator::inv`, `SourceUnits::inv`); the invariants hold
  for every value outside the crate, because their fields are private to the crate.
  `SourceUnits::new` wraps `new_ref`, which requires a text shorter than `usize::MAX - 2`
  bytes, as `run_source_ref` does; a `Vec<u8>` holds at most `isize::MAX` bytes. The public `Parser::try_new`, `set_max_depth` and
  `try_parse_program`, used by tests only, are not related to the theorem (`run_unit_ref` calls
  `parse_unit_ref`), and nothing establishes the preconditions of `parse_program_ref` for them.

## Verification Stack — What Is and Is Not Covered

| Layer | Tool / script | What it actually establishes |
|---|---|---|
| Deductive proofs | Verus — `scripts/run_verus_verification.sh` (`verified_kernels.rs`, `math.rs`, `format.rs`, `parser/`, `eval/`, `driver.rs`, `refine.rs`, `mathlib/`, `real_arith.rs`, `bigint.rs`, the trusted `trusted_bigint.rs`, `trusted_std.rs` and `trusted_math.rs`, `verus_proofs.rs`, `crates/bc_spec` including `spec_num.rs`) | The kernels meet their contracts for all inputs that satisfy their preconditions, and production code establishes those preconditions (e.g. `BC_SCALE_MAX`). The production `BCNum::add`, `sub`, `mul`, `try_div`, `try_mod_op`, `try_pow`, `try_sqrt`, `length`, `scale_func`, `cmp_val` and `from_digit_values` compute the L0 operations exactly, and `format_bytes` writes `l0_format` of the value, assuming the `num-bigint` wrappers in `trusted_bigint.rs`. Without `-l`, `try_evaluate` and `try_execute` refine the specification's `ev` and `exec` (every finishing fuel gives a corresponding result and state, including output, diagnostics and runtime errors), assuming in addition the axioms of `trusted_std.rs` and the output-stream wrappers (`WrappedStdout::write_bytes` and `flush_out`, `ErrWriter::write_bytes` and `flush_err`); this is partial correctness. The lexer (`parser/lexer.rs`) produces the specification's `tokenize`, and the parser (`parser/parse.rs` and `parser/parse/`) the specification's `parse_unit` (for every fuel with which the specification finishes), assuming in addition the one-line wrappers `ascii_string`, `copy_bytes`, `append_bytes` and `subslice`. `Evaluator::run_unit_ref` refines the specification's `run_unit` (diagnostics, `quit`, the failure count), and `run_source_ref` refines `run_units` on `split_units` of the text: state, output, diagnostics, `quit`, and whether a unit failed. `run_source_ref` is a loop over `run_next_unit_ref`, whose theorem (`r_step`) is one step of `run_units` on the units of the text not yet run (`UnitCursor::rest`): `None` when none is left, and otherwise the outcome of the first. `with_streams` gives the specification's `initial` state, and `lemma_outcome` proves that evaluators going through `run_source_ref` on the inputs in order have the specification's `run`. Not proved: the front ends' loops (reading lines or files, the order of the inputs, the exit status, `catch_unwind`), and that parsing ends (partial correctness); stack and memory exhaustion are outside the model. The embedded targets, the C API and Wasm call `run_source`. For a file or piped standard input, `bc_clone` calls the public `run_next_unit` (`run_next_source_unit_ref`, with the same theorem) on `SourceUnits` until `None` or `quit`, each call under `catch_unwind` (`run_non_interactive_block`); that loop, which repeats `run_source_ref`'s, is not proved. Its interactive loop over `UnitAccumulator::push_line` and `run_unit` is not proved either. The six functions of the math library (`mathlib/`) return the exact value truncated toward zero at `scale` digits (partial correctness over the reals, assuming the facts of real analysis stated as axioms in `trusted_math.rs`); the evaluator calls them from the verified `finish_math1` and `finish_bessel`, which ensure that an `Ok` result is the function's exact value at some argument values (`mathlib::math_ok`); which argument values is not stated, because the refinement theorem excludes `-l`. `verus_proofs.rs` keeps **design models that production code does not call** (the C-FFI copy, the Zephyr line editor, CLI option parsing); its module documentation maps each model to its production counterpart. |
| Bounded model checking | Kani — `scripts/run_kani_verification.sh` (`kani_proofs.rs`, `bc_c_api`, `bc_cli`) | Kernels are free of overflow and panics over symbolic inputs (64-bit host only; the 32-bit targets are exercised by the QEMU and Zephyr self-tests). The production C-FFI output helper `write_c_string` never writes at or beyond `buf_size` and always NUL-terminates. C-API NULL and zero-size guards hold. The CLI brace scanner is consistent. |
| UB / memory safety | Miri — `scripts/run_miri_tests.sh` | No UB or leaks in the `--lib` unit tests of `bc_core`, `bc_c_api`, `bc_zephyr`, and `bc_cli` (strict provenance, symbolic alignment, Stacked Borrows), and `bc_c_api` again under Tree Borrows. CI runs each stage as its own job and splits `bc_core` by test name (`run_miri_tests.sh STAGE -- FILTER`). |
| Executable specification | Verus — `crates/bc_spec`, `scripts/build_spec_oracle.sh`; `crates/bc_cli/tests/spec_differential.rs` | `bc_spec` defines the observable behavior of `bc_clone` without `-l` (units, tokens, parsing, evaluation, output, diagnostics, exit status), mirroring the production structure. `exec_spec_verified!` proves that the compiled oracle equals the `spec fn`s, except for `vstd`'s unverified `Seq` translations; lemmas prove that its arithmetic (`+ - * / % ^ sqrt`, comparison, `length`, constants under `ibase`) computes the integer definitions of `spec_num.rs` exactly. The differential tests then show that `bc_clone` matches the specification **on the generated inputs only**. Deductively, a whole input given to `run_source` refines the specification, and so does each step of `bc_clone`'s own loop (the Verus row above). `prop_parser_output_corresponds_to_*` still compares the parser's output with the specification's on generated inputs, which also checks the unproved public wrappers around the parser. The specification itself is checked against POSIX only by review, the POSIX suite, and GNU bc. `exec_spec_verified!` copies the fields of every struct it builds, so the parts of the state that grow with the run (scope and call stacks, arenas, output streams, the token and unit lists) are types of `persist.rs`, which the compiled code shares through `Rc`; their `exec_*` operations are written and verified there by hand, and `lex_toks` and `split_units_into` are compiled twins of `lex` and `split_units_from`, proved equal to them. The oracle's time therefore grows about linearly with nesting depth and with the number of units and of output lines, and the tests nest a thousand levels deep. Other sequences are still copied at every step, so it stays quadratic in the number of statements or extension uses in one unit, the length of a number or string, and the number of set array elements, and it is slow for large powers (its digit arithmetic copies a sequence at every step); the tests skip a case where the oracle exceeds the time limit. |
| Property tests | proptest — `crates/bc_core/tests/proptest_suite.rs` | `+ - * / % ^ sqrt` against an exact `BigInt` reference truncated to the POSIX result scale (scales up to 40, negative values). Also checks the scale and exponent limits, integer and fractional base conversion, and that the parser and evaluator never panic. |
| Differential fuzzing | proptest — `crates/bc_cli/tests/differential_proptest.rs` | Random programs (expressions, registers, arrays, control flow, recursion, runtime errors) produce the same stdout, diagnostics, and exit status as GNU bc. A second generator produces deeply nested programs (operator chains, parentheses, blocks, recursion thousands of levels deep, functions that change `ibase`). 300 + 40 cases per `cargo test`; set `PROPTEST_CASES` for long runs. Inputs where GNU knowingly deviates from POSIX are not generated. |
| Differential tests | `crates/bc_cli/tests/integration_tests.rs` (helpers in `tests/common`), `scripts/run_gnu_reference_tests.sh` | stdout, diagnostics (GNU's text without `adr=N`), and exit status match GNU bc 1.08 (CI builds 1.08.2 with `scripts/install_gnu_bc.sh`), except for the documented differences. The math library is checked against GNU bc at `scale + 100`, truncated. |
| POSIX conformance | `scripts/run_posix_compliance_tests.sh` | Expected outputs derived from POSIX.1-2024 (not from GNU bc). Each case runs in the default mode and with `-s`. `BC_BIN=bc` runs the same cases against GNU bc to sanity-check the expectations, and `BC_BIN=target/bc_spec_oracle` against the executable specification (its `-l` cases are skipped). |
| Mutation testing | `cargo mutants` (`.cargo/mutants.toml`) | Diff-based in CI, split into shards (`--shard`). Some exclusions are broader than the equivalent mutants they target. |
| Coverage | `cargo llvm-cov` | Line coverage gate of 97% in CI. Most uncovered lines are branches that the proofs or the design make unreachable (an arena index out of range or a node of the wrong kind on the machine, cases the fast path always takes, a parser error the driver never sees from execution), overflow guards of the `-l` functions, and test code; tests cannot reach them, and removing them would mean rewriting proved code. |

The gaps listed above are known and remain open. Do not describe any layer as proving
"bug-freedom" or "100% compliance" of the whole program.

## Embedded and Wasm Targets

- **QEMU bare metal** (`scripts/run_qemu_riscv32_tests.sh`): builds for `riscv32imac` and
  `riscv32imc` and boots under `qemu-system-riscv32 -M virt -bios none`. It uses a 2 MiB
  `embedded-alloc` heap, an NS16550A UART at `0x1000_0000`, and the SiFive test device at
  `0x10_0000` to report the exit status.
- **Zephyr** (`scripts/run_zephyr_tests.sh`): `examples/zephyr_app` builds the `bc_zephyr`
  staticlib through CMake. It is tested on `qemu_riscv32`; `stamp_c3` is the hardware target.
  `scripts/setup_zephyr_workspace.sh` pins Zephyr v3.7.2 and SDK 0.16.8 for CI and releases.
  `CONFIG_BC_QEMU_REPL=y` starts the REPL on QEMU instead of exiting after the self-tests.
  The 96 KiB main stack (`prj.conf`) is sized for `bc_zephyr::ZEPHYR_MAX_DEPTH`; the self-tests
  run at the nesting limit, so a larger per-level stack use shows up as a test failure there:
  on QEMU, `CONFIG_HW_STACK_PROTECTION` turns an overflow into a fatal error, and `main.c`'s
  fatal-error handler exits QEMU with a failure status.
- **Nesting limits of Wasm and the M5Stamp C3** come from the workloads in
  `crates/bc_qemu_riscv32/src/stack_workloads.rs`, mirrored in
  `examples/wasm_web_app/tests/nesting_limit.mjs`. `deepest` finds the largest input the limit
  accepts, so each workload reaches the limit. The QEMU runner and the M5Stamp self-tests run them.
  - M5Stamp C3 (`M5STAMP_MAX_DEPTH` = 128): the criteria are at most 60% of the 185 KB stack and
    completing in the 128 KiB heap. Since evaluation runs on an explicit stack, the heap decides:
    `scripts/measure_m5stamp_stack.sh` gives 34 KB of stack and 87 KB of heap at 128 (nested
    `for`), and no heap left at 160. It measures a QEMU build with the same optimization settings
    and another allocator. The application's self-tests, which fail above 60% of the stack, passed
    on a board: 32 376 of 185 204 bytes of stack (17%; 82 104 bytes, 44%, with the recursive
    evaluator). The REPL has the same limit, and the self-tests take the board about 5 seconds to
    reach the prompt. The heap use is not measured on the board. An overflow runs into `.bss`; esp-hal's watchpoint only sees a write to its one guard
    word, so it may miss one.
  - Wasm (`WASM_MAX_DEPTH` = 1000): the criteria are at most 50% of the 1 MiB stack in linear
    memory, and at least twice the limit before an engine failure. `nesting_limit.mjs`, which
    `scripts/build_wasm.sh` runs when `node` is available, checks the first on the built module
    (12.3%; 46% with the recursive evaluator). With the recursive evaluator and the `stack-probe` feature, 2000 levels ran and 3000 did not, and 1000 levels ran
    with `--stack-size=492`, half of V8's default, but not with 250. The workloads also ran once by
    hand in headless Firefox 159 on aarch64, with the same stack use: 1000 and 2000 levels ran, 3000
    did not; the margin of Firefox's own stack was not measured separately. No automated test runs
    in a browser, and **Safari is not measured**.
  - A change to the per-level stack or heap use (the size of `Node` or `Frame`, the frames a
    construct pushes, the fast path's budget) requires measuring again.
- **C API**: `bc_c_api` embeds a 64 KiB LLFF heap on `no_std` targets. Status codes are defined in
  `include/bc_core.h`.
- **ESP32-C3** (`examples/m5stamp_c3`): built in CI by `scripts/build_m5stamp_c3.sh`. Flashing
  scripts exist for manual hardware testing.
- **Wasm** (`scripts/build_wasm.sh`): runs the `bc_wasm` tests, Clippy for host and wasm32, and
  produces the bundle.

## Release Packaging

`scripts/package_release.sh VERSION OUT_DIR wasm|m5stamp|qemu|zephyr...` builds the example
targets and archives each one with the scripts and `README.txt` from `packaging/<name>/`. The
release workflow (`.github/workflows/release.yml`) runs it for every tag and smoke-tests the QEMU
packages before uploading. When you change how an example is built or run, update its
`packaging/` directory too.

## Agent Workflow Rules

### Pre-commit verification (mandatory)
Run before every commit; do not commit unless everything passes:

```bash
cargo fmt --check && cargo clippy --package bc_core --package bc_clone --package bc_c_api --package bc_zephyr --all-targets -- -D warnings && cargo clippy --package bc_qemu_riscv32 --target riscv32imac-unknown-none-elf -- -D warnings && cargo clippy --package bc_c_api --target riscv32imac-unknown-none-elf --no-default-features -- -D warnings && cargo clippy --package bc_zephyr --target riscv32imac-unknown-none-elf --no-default-features -- -D warnings && cargo test
```

### Dividing work among subagents
- Implementing, proving and fixing stay in one agent: a proof is a tight loop of writing, verifying
  and reading errors, and a new agent would have to rebuild the invariants and the design.
- Use a separate agent for what gains from fresh eyes or a small report:
  - independent review of a finished change, in particular whether a theorem states what is
    claimed and whether the specification matches POSIX;
  - running a heavy check and reporting the verdict with its decisive log lines;
  - broad searches, and classifying the survivors of a mutants run.
- A reviewer or verifier does not take the author's word: it reads the code and the logs itself,
  and confirms that a result belongs to the commit or tree under discussion.
- Give each agent the commit, the files and the question, since it starts without this context.

### Process-global state in tests
Signal handlers and panic hooks are process-global. `bc_cli` registers the SIGINT handler only
under `#[cfg(not(test))]`, and tests that touch global state serialize on `TEST_MUTEX`.

### Mutation-testing exclusions
Only exclude mutants that are semantically equivalent (e.g. changes to over-precision guard digits
that cannot change a truncated result). Keep each `exclude_re` in `.cargo/mutants.toml` as narrow
as possible and state the reason next to it.

### Formal-verification hygiene
- `bc_core` is verified with `cargo verus verify -p bc_core --features verify`
  (`scripts/run_verus_verification.sh`). The `verify` feature links `vstd` and `crates/bc_spec`,
  and `bc_core::spec_num` re-exports the L0 model of `bc_spec`. Production builds never link
  either: `vstd` needs atomic compare-and-swap, which riscv32imc (ESP32-C3) lacks, and `bc_spec`
  needs `std`. In a normal build, `verus!` comes from `verus_builtin_macros` (a normal
  dependency, `no_std` and free of atomics) and erases specifications and proofs; import it with
  `#[cfg(not(verus_keep_ghost))] use verus_builtin_macros::verus;` and `vstd::prelude` only under
  `cfg(verus_keep_ghost)`. A `Ghost<T>` parameter stays in the signature after erasure, so its
  type must exist without `vstd` and `bc_spec`.
- The refinement relations between `bc_core` and `bc_spec` are in `src/refine.rs` (the arena,
  numbers, variables, arrays, functions) and `Evaluator::r_state` in `src/eval/` (the whole
  state; it reads `pub(crate)` fields, so it must stay `pub(crate)`). The arena's types are
  declared outside `verus!` and made visible to Verus with `external_type_specification`; the output streams `WrappedStdout` and `ErrWriter`
  are opaque (`external_body`) and modeled by `out_log`, `out_col` and `err_log`;
  `ErrWriter::write_bytes` is the trusted statement that a diagnostic write appends exactly its
  bytes to `err_log`.
- Variables and arrays are read and written only through the verified storage functions
  (`var_get`, `var_set`, `var_push`, `var_pop`, `arr_get`, `arr_set`, `arr_push`, `arr_pop` in
  `src/eval/`), which maintain `Evaluator::inv` (registers in range, every stored scale at most
  `BC_SCALE_MAX`). Reading a name does not create its binding. Other trusted facts about the
  standard library (`String` keys, the derived `Clone` of `FunctionDef`) are the axioms in
  `trusted_std.rs`.
- The refinement theorem of expression evaluation is the postcondition of `Evaluator::eval_ref`
  (behind `try_evaluate`): if the state corresponds to the specification's (`r_state`) and the
  arena to the specification's (`r_rc`), then for every fuel with which the specification's
  `ev` finishes, the result and the new state correspond to it (`r_result`). Statement execution
  has the same theorem in `Evaluator::exec_ref` (behind `try_execute`) against the
  specification's `exec`, with `r_unit`. Both cover every node of a related arena, including
  function calls (`step_call`, `enter_call`, `ret_call`). The functions of `-l` go through
  `finish_math1` and `finish_bessel`, which are verified (they keep `Evaluator::inv`, and their
  results satisfy `mathlib::math_ok`)
  but is outside the refinement theorem: `r_state` excludes `-l`.
- The trusted base of the refinement theorems (`run_source_ref`, `run_unit_ref`, `try_evaluate`, `try_execute`) is:
  Verus, Z3, rustc and `vstd` (including its specifications of `Vec`, `BTreeMap`, `String` and
  `str`); the `num-bigint` wrappers and `axiom_bigint_size` in `trusted_bigint.rs`; the axioms of
  `trusted_std.rs`; the output-stream wrappers in `eval/` (`WrappedStdout::write_bytes`,
  `flush_out`, `ErrWriter::write_bytes`, `flush_err`: a failing writer is outside the model, and a writer is taken to store exactly the bytes it receives, which the default `BcWriter::write_bytes` does not do for invalid UTF-8, nor the bare-metal UART, which turns `\n` into `\r\n`); and
  the one-line wrappers `ascii_string`, `share_code` and `copy_bytes` (`parser/`), `append_bytes` and `subslice`
  (`driver.rs`). `WrappedStdout::new` and `ErrWriter::new` are taken to start with an empty log.
  The theorems assume a text shorter than `usize::MAX - 2` bytes and a nesting limit below
  `usize::MAX - 2`. `-l` is excluded by `r_state`. Not covered: the front ends' loops over lines
  and inputs (reading files, the exit status, `catch_unwind`), which `lemma_run_inputs_step`
  and `lemma_outcome` describe but do not prove of those loops.
- The trusted base of the math-library theorems (`bc_sin`, …, `bc_bessel` in `mathlib/`) is:
  Verus, Z3, rustc and `vstd`; the `num-bigint` wrappers in `trusted_bigint.rs`; and the facts of
  real analysis in `trusted_math.rs`. Facts about the real functions go only in
  `trusted_math.rs`, as one-statement `axiom fn`s that name their DLMF section; derive anything
  else (ln 2 = 2·artanh(1/3), sin 0 = 0, e^2.3026 > 10, n! >= (n/3)^n, …) instead of assuming
  it. After adding an axiom, check that calling it does not make `assert(false)` provable.
- Trusted assumptions about `BigInt` go only in `trusted_bigint.rs`, as `#[verifier::external_body]`
  one-line wrappers with a test each (in `oracle_tests` against the specification's arithmetic
  as well). Derive any other operation in verified code in `bigint.rs` instead of adding a
  wrapper. Call a function of `bigint.rs` rather than using an operator on `BigInt` in verified
  code.
- A change to observable behavior must change `crates/bc_spec` in the same commit, so that the
  specification and the implementation stay equal; the differential tests against the
  specification catch the commits that forget one side. Follow the writing rules in the crate
  documentation of `bc_spec` (forced by `exec_spec_verified!`), and list any function that has to
  fall back to `exec_spec_unverified!` there.
- New kernels go in `verified_kernels.rs` via `dual_verified!` and must be called from production
  code. A proof about a re-implementation does not count as coverage of the production code.
- Every caller must establish the kernel's `requires` clause.
- Add or extend a Kani harness for each new kernel.
