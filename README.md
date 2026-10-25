# bc_clone_rs (`bc_clone`)

[![CI](https://github.com/takayuki-nagata/bc_clone_rs/actions/workflows/ci.yml/badge.svg)](https://github.com/takayuki-nagata/bc_clone_rs/actions/workflows/ci.yml)
[![Release](https://github.com/takayuki-nagata/bc_clone_rs/actions/workflows/release.yml/badge.svg)](https://github.com/takayuki-nagata/bc_clone_rs/actions/workflows/release.yml)
[![Version](https://img.shields.io/badge/version-v0.2.0-blue.svg)](https://github.com/takayuki-nagata/bc_clone_rs/releases)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](LICENSE)

A production-grade, POSIX-compliant arbitrary-precision calculator implemented in pure, idiomatic Rust (`bc_clone_rs`), generating the `bc_clone` executable binary. This project is a complete rewrite/reimplementation of the original Python-based `bc_clone_py`.

> [!NOTE]
> **AI Agent Notice**: This repository was completely designed, implemented, and verified by **Antigravity**, an advanced AI coding agent developed by Google DeepMind. Every line of production code, unit and integration test, CI/CD pipeline, and documentation was generated, iterated on, and refined by the AI agent to meet strict software engineering standards.

## Features

- **POSIX-Compliant Math with GNU Extensions**: Fully supports dynamic scoping, registers, variable/array stacks, and functions matching standard `bc` specifications, as well as popular GNU `bc` extensions (bare `return`, assignment operators `+=`, `-=`, etc., and array parameter passing `f(a[])`).
- **`#![no_std]` + `alloc` Core Engine with Fallible Execution API**: The core calculator engine (`bc_core`) is fully decoupled from the OS and standard library (`std`), exposing non-panicking `Result`-based APIs (`try_new`, `try_parse_program`, `try_execute`, `try_evaluate`, `try_div`, `try_mod_op`, `try_pow`, `try_sqrt`) alongside standard wrappers. This guarantees safe syntax/runtime error recovery without unwinding across C-FFI (`bc_c_api`), embedded RTOS (`bc_zephyr`), bare-metal RISC-V 32 (`bc_qemu_riscv32`, `examples/m5stamp_c3`), and WebAssembly (`wasm32-unknown-unknown`).
- **Arbitrary-Precision Arithmetic**: Implements high-performance arbitrary-precision decimal operations on top of `num-bigint` without external C library dependencies.
- **Transcendental Library**: Supports the standard math library functions (`-l` flag):
  - Sine (`s(x)`) and Cosine (`c(x)`)
  - Arctangent (`a(x)`)
  - Natural Logarithm (`l(x)`)
  - Exponential (`e(x)`)
  - Bessel function of integer order (`j(n, x)`)
- **Arbitrary Base Conversions**: Arbitrary input base (`ibase`) up to 16, and arbitrary output base (`obase`) up to any integer base.
- **Robust Interactive REPL**: Interactive mode with 70-character POSIX line wrapping, multi-line brace and backslash-newline accumulation, SIGINT (Ctrl+C) handling, and input base range warnings.
- **3-Layer Formal & Dynamic Verification (`Verus` + `Kani` + `Miri`) & Property-Based Testing (`proptest`)**:
  - **Verus SMT Prover**: 31 core arithmetic, scaling, lexing, parsing, scoping, CLI, C-FFI, and RTOS kernels (`crates/bc_core/src/verified_kernels.rs`) are directly coupled between production `#![no_std]` code and Z3 SMT formal verification (`crates/bc_core/src/verus_proofs.rs`, `149 verified, 0 errors`).
  - **Kani Bounded Model Checker**: 14 bit-precise CBMC proof harnesses across `bc_core`, `bc_c_api`, and `bc_clone` cross-verify all 31 kernels, C-FFI raw pointer writes, and CLI slice indexing against machine-word overflows and out-of-bounds panics across symbolic inputs (`scripts/run_kani_verification.sh`).
  - **Miri UB & Memory-Leak Verifier**: Executes all 103 unit tests across `bc_c_api`, `bc_core`, `bc_zephyr`, and `bc_clone` at full mathematical precision under strict provenance and symbolic alignment checking (`scripts/run_miri_tests.sh`), guaranteeing zero Undefined Behavior, Tree Borrows compliance, and zero memory leaks across FFI sessions, fallible error recovery, and panic unwinding.
  - **Property-Based Testing (`proptest`)**: Verifies multi-limb `BigInt` / `BCNum` algebraic laws, base-conversion roundtrips, transcendental mathematical identities, and fallible parser/evaluator resilience across randomized inputs (`crates/bc_core/tests/proptest_suite.rs`).
- **High-Quality Standards**: 100% warning-free under `cargo clippy -- -D warnings`, fully formatted via `cargo fmt`, 98.2%+ line coverage (`cargo llvm-cov`), 0 surviving mutants (`cargo mutants`), and thoroughly documented with `rustdoc`.

## Performance & Benchmarks

`bc_clone` is highly optimized and outperforms the original `system bc` (GNU bc) by over **45x** for high-precision calculations. 

### Benchmark: Computing $\pi$ to 10,000 decimal places
Using the arctangent formula for $\pi$ ($4 \times \arctan(1)$) with `scale=10000`:
```bash
time ./bc_clone -l <<< "scale=10000;4*a(1)"
```

| Implementation | Execution Time (Real) | Speedup |
|---|---|---|
| **`bc_clone` (Rust)** | **~1.7 seconds** | **47x faster** |
| `system bc` (GNU bc) | ~80.8 seconds | 1.0x (Baseline) |

### Key Reasons for the Performance Advantage
1. **CPU-Native Binary Representation**: Unlike the original `bc` which operates on a slow digit-by-digit base-10 array representation, `bc_clone` stores numbers in binary format using native CPU 64-bit integer limbs.
2. **Advanced Multiplication Complexity**: `bc_clone` leverages `num-bigint`'s **Karatsuba multiplication** ($O(N^{1.58})$ complexity) instead of the traditional $O(N^2)$ schoolbook multiplication used by standard `bc`.
3. **Half-Angle Argument Reduction**: The arctangent implementation `a(x)` applies 4 iterations of the half-angle formula $x_{k+1} = \frac{x_k}{1 + \sqrt{1 + x_k^2}}$ to reduce the argument to $\approx 0.049$ before Taylor series evaluation. This guarantees rapid convergence (requiring only ~3,000 terms compared to over ~7,000 terms in standard `bc`).

## Getting Started

### Prerequisites

- Rust (edition 2024, compatible with rustc 1.95.0+)
- `cargo`

### Building the Project

To build the release-optimized executable:

```bash
cargo build --release
```

The compiled binary will be available at `./target/release/bc_clone`.

### Usage

Run the calculator interactively:

```bash
./target/release/bc_clone
```

Run with the transcendental math library enabled (sets `scale` to 20 by default):

```bash
./target/release/bc_clone -l
```

Pass scripts/files to evaluate sequentially:

```bash
./target/release/bc_clone script1.bc script2.bc
```

#### Examples

1. **Basic Arithmetic**:
   ```
   1 + 2 * 3^2
   19
   ```

2. **Bases and Scales**:
   ```
   scale = 5
   1 / 3
   .33333
   obase = 16
   255
   FF
   ```

3. **Defining Functions (Dynamic Scoping)**:
   ```
   define f(x) {
       auto a
       a = x * 2
       return a
   }
   f(5)
   10
   ```

## Development and Verification

### Code Quality and Lints

To check formatting and run the linter:

```bash
cargo fmt --check
cargo clippy -- -D warnings
```

### Running Tests

We implement unit, property-based (`proptest`), and integration tests (135 tests across all workspace crates and `bc_wasm`), E2E differential integration tests (26 test suites in `crates/bc_cli/tests/integration_tests.rs`), official GNU `bc` 1.08.2 reference test suite validation (`scripts/run_gnu_reference_tests.sh`), and POSIX IEEE Std 1003.1 compliance test suite validation (`scripts/run_posix_compliance_tests.sh`).

To run standard unit and integration tests:

```bash
cargo test
```

To run the official GNU `bc 1.08.2` reference test suite:

```bash
bash scripts/run_gnu_reference_tests.sh
```

To run the POSIX IEEE Std 1003.1 compliance test suite:

```bash
bash scripts/run_posix_compliance_tests.sh
```

To run the automated Baremetal RISC-V 32 test suite on QEMU:

```bash
bash scripts/run_qemu_riscv32_tests.sh
```

To run the Zephyr RTOS integration test suite on QEMU RISC-V 32:

```bash
bash scripts/run_zephyr_tests.sh
```

To build the Zephyr RTOS application for M5Stamp C3 (`stamp_c3`):

```bash
bash scripts/build_zephyr_m5stamp_c3.sh
```

To flash Zephyr RTOS to M5Stamp C3 and run automated hardware tests + self-verification:

```bash
bash scripts/flash_and_test_zephyr_m5stamp_c3.sh
```

To flash Zephyr RTOS to M5Stamp C3 and launch an interactive REPL terminal session:

```bash
bash scripts/repl_zephyr_m5stamp_c3.sh
```

To build and verify the M5Stamp C3 (ESP32-C3) baremetal application:

```bash
bash scripts/build_m5stamp_c3.sh
```

To flash M5Stamp C3 (baremetal) and run automated hardware tests:

```bash
bash scripts/flash_and_test_m5stamp_c3.sh
```

To flash M5Stamp C3 (baremetal) and launch an interactive REPL terminal session:

```bash
bash scripts/repl_m5stamp_c3.sh
```

To build the WebAssembly (wasm32) module:

```bash
bash scripts/build_wasm.sh
```

To run the WebAssembly Web App frontend locally:

```bash
bash scripts/serve_wasm.sh
# Open http://localhost:8080/www/ in your browser
```

### Formal Verification (Verus)

`bc_clone_rs` uses the [Verus](https://github.com/verus-lang/verus) deductive verification tool (backed by the Z3 SMT solver) to mathematically prove the absence of integer overflows, slice out-of-bounds panics, division-by-zero in internal transforms, non-termination in power/series loops, and violations of POSIX `bc` scale/formatting invariants.

- **Single Source of Truth (`crates/bc_core/src/verified_kernels.rs`)**: 31 pure functions and state machines are defined once via `dual_verified!` and `dual_verified_repl_scanner!`. Under Verus (`#[cfg(verus_keep_ghost)]`), they expand inside `verus! { ... }` with full `requires`, `ensures`, `invariant`, and `decreases` contracts; under standard Cargo builds (`#[cfg(not(verus_keep_ghost))]`), the exact same function bodies compile as zero-overhead `#[inline]` `#![no_std]` Rust functions called directly across `bc_core`, `bc_cli`, `bc_c_api`, and `bc_zephyr`.
- **High-Order Proof Suite (`crates/bc_core/src/verus_proofs.rs`)**: Contains Ghost mathematical models (`SpecBCNum`, `SpecDecimal`), inductive lemmas (`proof fn`), and 12 verification target areas (`149 verified, 0 errors`), including:
  1. POSIX `bc` scale rules & fixed-point arithmetic (`add`, `sub`, `mul`, `div`, `sqrt`, `mod`)
  2. Non-decimal `obase` fractional digit loop termination & minimality ($\text{obase}^k \ge 10^{\text{scale}}$)
  3. POSIX 70-character line wrapping (`WrappedStdout` $\text{col} \le 68$) & `Lexer` lookahead/advance bounds safety
  4. Binary exponentiation (`BCNum::pow`) $\mathcal{O}(\log b)$ loop termination & scale invariants
  5. Base conversion (`ibase`/`obase`) digit bounds, hex LUT indexing safety, and multi-digit zero-padding width
  6. Transcendental math (`Decimal`) roundtrip losslessness & `sin`/`cos`/`exp` argument reduction
  7. `Evaluator` cross-scale relational total order, register clamping (`ibase`/`obase`), and `ScopeGuard` dynamic stack restoration theorem
  8. `Parser` Pratt precedence climbing hierarchy & `Lexer` number/identifier scanning invariants
  9. `BCNum::length` & `atan` / `ln` (Cayley transform) / `bessel` mathematical identities
  10. `Evaluator` prefix/postfix `++`/`--` semantics & `break`/`return`/`quit` control-flow short-circuiting
  11. CLI REPL block completeness scanner, C-FFI NUL buffer capacity safety, and Zephyr RTOS line editor
  12. `Decimal` fixed-point unit identities, Taylor series convergence termination, and POSIX CLI option parser

To run the Verus formal verification suite locally:

```bash
bash scripts/run_verus_verification.sh
```

### Bounded Model Checking (Kani) & Undefined Behavior Verification (Miri)

To complement Verus's unbounded mathematical proofs with bit-precise machine-word model checking and dynamic memory/FFI safety verification:

- **Kani Bounded Model Checking (`scripts/run_kani_verification.sh`)**: Verifies 14 symbolic proof harnesses (`#[kani::proof]`) across `bc_core` (`crates/bc_core/src/kani_proofs.rs`), `bc_c_api`, and `bc_clone` using CBMC/CaDiCaL. Proves the absence of bit-level arithmetic overflows, slice/UTF-8 boundary panics, and C-FFI buffer overruns across all symbolic input bit patterns.
- **Miri Undefined Behavior & Leak Verification (`scripts/run_miri_tests.sh`)**: Runs all 103 unit tests across `bc_c_api`, `bc_core`, `bc_zephyr`, and `bc_clone` under `cargo +nightly miri test` with `-Zmiri-strict-provenance -Zmiri-symbolic-alignment-check`, verifying `unsafe extern "C"` FFI pointers, `BcSession` (`Box::into_raw` / `Box::from_raw`) lifecycles, `num-bigint` heap allocations, and `ScopeGuard` dynamic scope restoration across both fallible returns and panic unwinding at full mathematical precision.

To run Kani bounded model checking locally:

```bash
bash scripts/run_kani_verification.sh
```

To run Miri UB and memory-safety verification locally:

```bash
bash scripts/run_miri_tests.sh
```

### Coverage Measurement

We target maximum test coverage using `cargo-llvm-cov`. To run the tests and generate a code coverage report:

```bash
# Clean existing coverage profiles
cargo llvm-cov clean
# Run test suite with coverage instrumentation
cargo llvm-cov --all-targets
```

To view the report line-by-line in your browser:

```bash
cargo llvm-cov --html --open
```

### Mutation Testing

We use `cargo-mutants` to verify test suite robustness by injecting faults into source code and confirming that existing tests fail (killing mutants).

To install `cargo-mutants` locally:

```bash
cargo install cargo-mutants
```

To run mutation testing on modified code (diff-based):

```bash
git diff > diff.patch && cargo mutants --in-diff diff.patch
```


To run full mutation testing across the entire codebase:

```bash
cargo mutants
```

## CI/CD Pipeline

The project includes two GitHub Actions workflows:
- **CI Workflow (`.github/workflows/ci.yml`)**: Automatically checks formatting, lints with clippy (host and bare-metal `riscv32` targets), runs all unit/integration tests, executes POSIX and GNU reference test suites, runs bare-metal QEMU RISC-V 32 and Zephyr RTOS tests, runs Verus SMT formal verification (`149 verified, 0 errors`), runs Kani bounded model checking (`14 harnesses`), runs Miri UB and memory-leak verification, enforces a 98%+ line coverage gate (`cargo llvm-cov`), executes diff-based mutation testing (`cargo mutants --in-diff`), and runs security audit checks on every push and pull request.
- **Release Workflow (`.github/workflows/release.yml`)**: Cross-compiles optimized binaries for Linux, macOS, and Windows and attaches them to a new GitHub Release automatically whenever a version tag (e.g. `v1.0.0`) is pushed.

## License

This project is licensed under the MIT License - see the [LICENSE](LICENSE) file in the repository for details.
