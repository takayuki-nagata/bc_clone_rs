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
    Core --> Parser[parser.rs: Lexer + Pratt parser]
    Core --> Eval[eval.rs: Evaluator]
    Core --> Math[math.rs: BCNum]
    Core --> MathLib[mathlib.rs: certified -l library]
    Core --> Kernels[verified_kernels.rs: dual-mode kernels]
```

| Path | Role |
|---|---|
| `crates/bc_core` | `#![no_std]` + `alloc` engine: lexer, parser, evaluator, arithmetic, math library (`mathlib.rs`) |
| `crates/bc_cli` | `bc_clone` binary: option parsing, file/stdin processing, interactive REPL, SIGINT |
| `crates/bc_c_api` | C ABI (`include/bc_core.h`): `bc_eval`, `bc_eval_callback`, `bc_session_*` |
| `crates/bc_zephyr` | Zephyr RTOS application logic (self-tests, serial REPL); C trampoline in `examples/zephyr_app` |
| `crates/bc_qemu_riscv32` | Bare-metal RISC-V 32 self-test runner for QEMU `virt` |
| `crates/bc_spec` | Executable formal specification: Verus `spec fn`s from input bytes to stdout, stderr and exit status, compiled by `exec_spec_verified!` into the reference interpreter `bc_spec_oracle` (`scripts/build_spec_oracle.sh`). A workspace member outside `default-members`: `cargo verus verify -p bc_spec` checks it, and a normal `cargo build` compiles the oracle, because `verus!` erases the specifications |
| `examples/m5stamp_c3` | ESP32-C3 bare-metal app (`esp-hal`) |
| `examples/wasm_web_app` | Browser frontend backed by `bc_core` compiled to `wasm32-unknown-unknown` |

## Core Engine (`crates/bc_core`)

### Lexer and parser (`src/parser.rs`)
- The lexer tracks line numbers and handles `/* */` comments, strings, and backslash-newline
  continuation.
- The parser is recursive descent, with Pratt precedence climbing for expressions. Assignment and
  `^` are right-associative. Precedence and associativity come from `verified_pratt_infix_info`.
- Fallible API: `Lexer::try_get_next_token`, `Parser::try_new`, `Parser::try_parse_program`.
  `quit` makes `try_parse_program` return `Err("quit")` so execution stops at that point, as
  POSIX requires.

### Numbers (`src/math.rs`)
- `BCNum { coeff: BigInt, scale: usize }` represents `coeff × 10^-scale`. Arithmetic follows the
  POSIX scale rules. The scale and shift computations are delegated to kernels in
  `verified_kernels.rs`.
- `add`, `sub`, `mul`, `try_div`, `try_mod_op`, `try_pow`, `try_sqrt`, `length`, `scale_func`,
  `cmp_val` (comparison) and `from_digit_values` (the value of a constant) are written inside
  `verus!` and proved to compute the L0 operations of `spec_num` and `bc_spec` (`spec_add`, …,
  `spec_pow`, `is_isqrt`, `is_digit_count`, `spec_horner`, through `BCNum::val`), given scales of
  at most `BC_SCALE_MAX`. They use `BigInt` only through `trusted_bigint.rs`, whose one-line
  wrappers Verus assumes correct (each is checked by a test). The output `format_bytes` (`src/format.rs`) is
  proved to write the specification's `l0_format` of the value for every `obase` from 2 to
  `BC_BASE_MAX`; `format_obase` only turns those ASCII bytes into a `String`. Still outside
  `verus!`: `digit_values` (constant text to digit values).
- Fallible API: `try_from_string`, `try_div`, `try_mod_op`, `try_pow`, `try_sqrt`. The panicking
  wrappers (`from_string`, `div`, `pow`, …) are compiled only under `cfg(test)`, as are `Lexer::get_next_token`,
  `Lexer::peek_token`, `Parser::new`, `Parser::parse_program`, `Evaluator::evaluate`, and
  `Evaluator::execute`.
- Output for `obase != 10` uses exact `BigInt` arithmetic. The number of fractional digits is the
  smallest `k` with `obase^k >= 10^scale`, so no floating point or `libm` is needed.

### Math library (`-l`, `src/mathlib.rs`)
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
(`docs/COMPATIBILITY.md` §3.4). Verus proves the truncation decision
(`lemma_certified_truncation`); the ball and series bounds are argued in
`docs/MATH_ERROR_BOUNDS.md` and tested (`mathlib::tests`, and
`test_math_library_against_high_precision_oracle`, which compares with GNU bc at `scale + 100`).
GNU's own results are *not* exact at the requested scale. When you change a function, keep its
section of `docs/MATH_ERROR_BOUNDS.md` in sync.

### Evaluator (`src/eval.rs`)
- Dynamic scoping: each variable or array name maps to a stack. Function parameters and `auto`
  locals push a new entry on entry. `BTreeMap` keeps the storage `no_std`-friendly and deterministic.
- `ScopeGuard` (RAII) pops the parameter and `auto` frames and restores the caller's control-flow
  flags on every exit path, including `Err` returns and panics.
- Output goes through the `BcWriter` trait. `WrappedStdout` wraps long numbers at 70 columns with
  `\` + newline, as POSIX requires. The wrapping itself is `format::wrap_output`, verified against
  the specification's `write_wrapped`; `write_str` passes its result to the writer in one call.
- Fallible API: `Evaluator::try_evaluate`, `Evaluator::try_execute`.

### Error handling contract
- `bc_core` itself never needs to panic on user input. Every syntax or runtime error must be
  reachable as an `Err` from the `try_*` APIs.
- `lib.rs` denies `clippy::unwrap_used`, `expect_used`, `panic`, and the lossy-cast lints outside
  tests. Every remaining exception is an `#[allow(..., reason = "...")]` that names the invariant
  justifying it (`pow10`, the bit-length estimate in `decimal_ln`, and the Verus-proved casts in
  `verified_kernels.rs` and `math.rs`). Do not replace an `unwrap` with a silent default (`unwrap_or(0)`):
  return an error or derive the value so that no default is needed.
- Front ends must not rely on unwinding: `catch_unwind` does not work under `panic = "abort"` or on
  `wasm32-unknown-unknown`.
- Errors are typed: `BcError` (`Quit`, `Syntax`, `Runtime { kind: RuntimeError, func }`) in
  `src/error.rs`. Do not match on message strings.
- `src/driver.rs` is the only place that turns input into executed units. `UnitAccumulator`
  groups lines into units, `Evaluator::run_unit` / `run_source` parse and execute them, and
  diagnostics are written in the format of `docs/COMPATIBILITY.md` §3.2. Every front end (CLI,
  C API, Zephyr, QEMU, ESP32-C3, Wasm) uses this driver, so error recovery is identical on all
  targets.
- Recursion is bounded: `Evaluator::max_depth` limits the depth of the syntax tree (checked while
  parsing, so evaluation, `Clone`, and `Drop` of the tree stay within it) and the number of
  nested `try_evaluate`/`try_execute` calls, including across function calls. Each front end
  sets it for the stack it runs on; `bc_cli` runs the engine on a 512 MiB-stack thread. When
  you add a recursive walk over the AST, it must stay within the same bound.
- `bc_cli` additionally wraps each unit in `catch_unwind`. A panic there is a bug in `bc_core`; it
  is reported as `bc_clone: internal error: …` and counted as a failed unit.

## Verified Kernels (`src/verified_kernels.rs`)

Small pure functions are defined once with `dual_verified!` / `dual_verified_repl_scanner!`:

- under Verus (`cfg(verus_keep_ghost)`), they expand inside `verus! {}` with their
  `requires`/`ensures` contracts;
- under normal builds, the same bodies compile as `#[inline]` functions that are called from
  production code.

Examples are the POSIX scale and shift computations for `+ - * / sqrt ^`, digit parsing,
`ibase`/`obase` clamping, the `WrappedStdout` column step, lexer cursor and lookahead bounds, Pratt
precedence, the C-FFI buffer-capacity check, the Zephyr REPL character class, the CLI argument
class, and the REPL block-completeness scanner.

**Preconditions are not checked at runtime; callers establish them.** Several kernels require
`scale <= MAX_VERIFIED_SCALE` (10^9). The evaluator maintains the invariant "every `BCNum` scale is
at most `BC_SCALE_MAX` (= `MAX_VERIFIED_SCALE`)":

- the `scale` register is clamped by `verified_clamp_register`;
- `%` and `^` return `scale too large` instead of producing a larger scale;
- numeric literals with more fractional digits are rejected.

Decimal shifts go through `math::pow10`, which treats a shift above `u32::MAX` as a broken
invariant (an internal error) instead of truncating it. Review any new code that creates a
`BCNum` scale against this invariant.

## Verification Stack — What Is and Is Not Covered

| Layer | Tool / script | What it actually establishes |
|---|---|---|
| Deductive proofs | Verus — `scripts/run_verus_verification.sh` (`verified_kernels.rs`, `math.rs`, `format.rs`, `verus_proofs.rs`, `crates/bc_spec` including `spec_num.rs`) | The kernels meet their contracts for all inputs that satisfy their preconditions, and production code establishes those preconditions (e.g. `BC_SCALE_MAX`). The production `BCNum::add`, `sub`, `mul`, `try_div`, `try_mod_op`, `try_pow`, `try_sqrt`, `length`, `scale_func`, `cmp_val` and `from_digit_values` compute the L0 operations exactly, and `format_bytes` writes `l0_format` of the value, assuming the `num-bigint` wrappers in `trusted_bigint.rs`. The math library's certified-truncation decision is proved over the integers (`lemma_certified_truncation`). `verus_proofs.rs` also proves lemmas about ghost models (`SpecBCNum`, …) and **design models that production code does not call**; its module documentation maps each model to its production counterpart and to the tests that cover that counterpart. |
| Bounded model checking | Kani — `scripts/run_kani_verification.sh` (`kani_proofs.rs`, `bc_c_api`, `bc_cli`) | Kernels are free of overflow and panics over symbolic inputs (64-bit host only; the 32-bit targets are exercised by the QEMU and Zephyr self-tests). The production C-FFI output helper `write_c_string` never writes at or beyond `buf_size` and always NUL-terminates. C-API NULL and zero-size guards hold. The CLI brace scanner is consistent. |
| UB / memory safety | Miri — `scripts/run_miri_tests.sh` | No UB or leaks in the `--lib` unit tests of `bc_core`, `bc_c_api`, `bc_zephyr`, and `bc_cli` (strict provenance, symbolic alignment, Stacked Borrows), and `bc_c_api` again under Tree Borrows. |
| Executable specification | Verus — `crates/bc_spec`, `scripts/build_spec_oracle.sh`; `crates/bc_cli/tests/spec_differential.rs` | `bc_spec` defines the observable behavior of `bc_clone` without `-l` (decoding, units, tokens, parsing, evaluation, output, diagnostics, exit status), mirroring the production structure. `exec_spec_verified!` proves that the compiled oracle equals the `spec fn`s, except for `vstd`'s unverified `Seq` translations; lemmas prove that its arithmetic (`+ - * / % ^ sqrt`, comparison, `length`, constants under `ibase`) computes the integer definitions of `spec_num.rs` exactly. The differential tests then show that `bc_clone` matches the specification **on the generated inputs only**: there is no proof that `bc_clone` refines the specification, and the specification itself is checked against POSIX only by review, the POSIX suite, and GNU bc. The oracle is slow for deep nesting (its state is copied at every step), so the tests stay a few hundred levels deep. |
| Property tests | proptest — `crates/bc_core/tests/proptest_suite.rs` | `+ - * / % ^ sqrt` against an exact `BigInt` reference truncated to the POSIX result scale (scales up to 40, negative values). Also checks the scale and exponent limits, integer and fractional base conversion, and that the parser and evaluator never panic. |
| Differential fuzzing | proptest — `crates/bc_cli/tests/differential_proptest.rs` | Random programs (expressions, registers, arrays, control flow, recursion, runtime errors) produce the same stdout, diagnostics, and exit status as GNU bc. A second generator produces deeply nested programs (operator chains, parentheses, blocks, recursion thousands of levels deep, functions that change `ibase`). 300 + 40 cases per `cargo test`; set `PROPTEST_CASES` for long runs. Inputs where GNU knowingly deviates from POSIX are not generated. |
| Differential tests | `crates/bc_cli/tests/integration_tests.rs` (helpers in `tests/common`), `scripts/run_gnu_reference_tests.sh` | stdout, diagnostics (GNU's text without `adr=N`), and exit status match GNU bc, except for the documented differences. The math library is checked against GNU bc at `scale + 100`, truncated. |
| POSIX conformance | `scripts/run_posix_compliance_tests.sh` | Expected outputs derived from POSIX.1-2024 (not from GNU bc). Each case runs in the default mode and with `-s`. `BC_BIN=bc` runs the same cases against GNU bc to sanity-check the expectations, and `BC_BIN=target/bc_spec_oracle` against the executable specification (its `-l` cases are skipped). |
| Mutation testing | `cargo mutants` (`.cargo/mutants.toml`) | Diff-based in CI. Some exclusions are broader than the equivalent mutants they target. |
| Coverage | `cargo llvm-cov` | Line coverage gate of 98% in CI. |

The gaps listed above are tracked work for v0.4.0. Do not describe any layer as proving
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
- Trusted assumptions about `BigInt` go only in `trusted_bigint.rs`, as `#[verifier::external_body]`
  one-line wrappers with a test each. Name a function there rather than using an operator on
  `BigInt` in verified code.
- A change to observable behavior must change `crates/bc_spec` in the same commit, so that the
  specification and the implementation stay equal; the differential tests against the
  specification catch the commits that forget one side. Follow the writing rules in the crate
  documentation of `bc_spec` (forced by `exec_spec_verified!`), and list any function that has to
  fall back to `exec_spec_unverified!` there.
- New kernels go in `verified_kernels.rs` via `dual_verified!` and must be called from production
  code. A proof about a re-implementation does not count as coverage of the production code.
- Every caller must establish the kernel's `requires` clause.
- Add or extend a Kani harness for each new kernel.
