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
- **`#![no_std]` + `alloc` Core Engine**: The core calculator engine (`bc_core`) is fully decoupled from the OS and standard library (`std`), supporting embedded systems, bare-metal RISC-V 32 (`riscv32imac-unknown-none-elf`, `riscv32imc-unknown-none-elf`), WebAssembly (`wasm32-unknown-unknown`), and RTOS (Zephyr / ESP32-C3).
- **Arbitrary-Precision Arithmetic**: Implements high-performance arbitrary-precision decimal operations on top of `num-bigint` without external C library dependencies.
- **Transcendental Library**: Supports the standard math library functions (`-l` flag):
  - Sine (`s(x)`) and Cosine (`c(x)`)
  - Arctangent (`a(x)`)
  - Natural Logarithm (`l(x)`)
  - Exponential (`e(x)`)
  - Bessel function of integer order (`j(n, x)`)
- **Arbitrary Base Conversions**: Arbitrary input base (`ibase`) up to 16, and arbitrary output base (`obase`) up to any integer base.
- **Robust Interactive REPL**: Interactive mode with 70-character POSIX line wrapping, multi-line brace and backslash-newline accumulation, SIGINT (Ctrl+C) handling, and input base range warnings.
- **High-Quality Standards**: 100% warning-free under `cargo clippy -- -D warnings`, fully formatted via `cargo fmt`, and thoroughly documented with `rustdoc`.

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

We implement unit tests (78 tests embedded in modules), E2E differential integration tests (26 tests in `tests/integration_tests.rs`), official GNU `bc` 1.08.2 reference test suite validation (`scripts/run_gnu_reference_tests.sh`), and POSIX IEEE Std 1003.1 compliance test suite validation (`scripts/run_posix_compliance_tests.sh`).

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
- **CI Workflow (`.github/workflows/ci.yml`)**: Automatically checks formatting, lints with clippy, runs all unit/integration tests, measures code coverage, executes diff-based mutation testing (`cargo mutants --in-diff`), and runs audit checks on every push and pull request.
- **Release Workflow (`.github/workflows/release.yml`)**: Cross-compiles optimized binaries for Linux, macOS, and Windows and attaches them to a new GitHub Release automatically whenever a version tag (e.g. `v1.0.0`) is pushed.

## License

This project is licensed under the MIT License - see the [LICENSE](LICENSE) file in the repository for details.
