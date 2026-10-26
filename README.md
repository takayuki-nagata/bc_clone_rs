# bc_clone_rs (`bc_clone`)

[![CI](https://github.com/takayuki-nagata/bc_clone_rs/actions/workflows/ci.yml/badge.svg)](https://github.com/takayuki-nagata/bc_clone_rs/actions/workflows/ci.yml)
[![Release](https://github.com/takayuki-nagata/bc_clone_rs/actions/workflows/release.yml/badge.svg)](https://github.com/takayuki-nagata/bc_clone_rs/actions/workflows/release.yml)
[![Version](https://img.shields.io/badge/version-v0.3.0-blue.svg)](https://github.com/takayuki-nagata/bc_clone_rs/releases)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](LICENSE)

An arbitrary-precision calculator implementing the POSIX.1-2024 `bc` utility in Rust (`bc_clone_rs`), producing the `bc_clone` executable. The engine is `#![no_std]` and also runs as a C library, on Zephyr RTOS, on bare-metal RISC-V, and in the browser via WebAssembly. It is a rewrite of the earlier Python implementation [`bc_clone_py`](https://github.com/takayuki-nagata/bc_clone_py).

> [!NOTE]
> **AI Agent Notice**: This repository is developed by AI coding agents under human direction. Versions v0.1.0–v0.3.0 were written by **Antigravity** (Google DeepMind); from v0.4.0 development continues with **Claude Code** (Anthropic). See [AGENTS.md](AGENTS.md) for the design and verification architecture.

## Features

- **POSIX.1-2024 `bc`**: the behavior is specified in [docs/COMPATIBILITY.md](docs/COMPATIBILITY.md), which lists each POSIX requirement, the implementation-defined limits (`BC_SCALE_MAX`, `BC_BASE_MAX`, `BC_DIM_MAX`, …), the choices made where POSIX leaves behavior undefined, and every known difference from GNU `bc` 1.08.
- **GNU-compatible extensions and diagnostics**: multi-letter names, comparisons as statements, `return x`, one-line function bodies. `-s` rejects these extensions and `-w` warns about them, as in GNU `bc`. Error messages use GNU `bc`'s wording, and processing continues after an error. The exit status is 1 if any error occurred.
- **Exact math library (`-l`)**: `s`, `c`, `a`, `l`, `e`, `j` return the exact value truncated to `scale`, including for very large arguments (checked against a high-precision oracle).
- **`#![no_std]` + `alloc` engine** (`bc_core`) with a typed, non-panicking error API (`BcError`) and one input-unit driver shared by every front end: CLI, C API (`bc_c_api`), Zephyr (`bc_zephyr`), bare-metal RISC-V (`bc_qemu_riscv32`, `examples/m5stamp_c3`), and WebAssembly (`examples/wasm_web_app`).
- **Arbitrary-precision arithmetic** on `num-bigint`, with no C library dependencies.
- **Interactive REPL** with multi-line input, 70-column POSIX line wrapping, and Ctrl+C handling.
- **Layered verification** (details in [AGENTS.md](AGENTS.md#verification-stack--what-is-and-is-not-covered)):
  - **Verus** proves the contracts of the small kernels in `crates/bc_core/src/verified_kernels.rs`, which production code calls directly.
  - **Kani** model-checks those kernels and the C-FFI output helper.
  - **Miri** checks the unit tests for undefined behavior.
  - **Property tests** check the arithmetic against an exact reference.
  - **Differential tests** check random programs against GNU `bc`, and a **POSIX conformance suite** checks the cases derived from the standard.
  - **Mutation testing** checks that the tests detect injected faults.

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

Options (each must be a separate argument):

| Option | Meaning |
|---|---|
| `-l` | Load the math library (`s c a l e j`) and set `scale` to 20 |
| `-s` | Process exactly the POSIX language: GNU extensions are errors |
| `-w` | Warn about GNU extensions |

Pass scripts/files to evaluate sequentially (standard input is read after them):

```bash
./target/release/bc_clone -l script1.bc script2.bc
```

The exit status is 0 if all input was processed without error, and 1 otherwise.

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
       return (a)
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

The integration tests compare `bc_clone` with GNU `bc`, so `bc` (GNU `bc` 1.08) and coreutils `timeout` must be on `PATH`.

```bash
cargo test
```

This runs:
- the unit tests of every crate;
- the property tests (`crates/bc_core/tests/proptest_suite.rs`);
- the differential integration tests (`crates/bc_cli/tests/integration_tests.rs`);
- 300 random programs compared with GNU `bc` (`crates/bc_cli/tests/differential_proptest.rs`).

For a longer differential fuzzing session:

```bash
PROPTEST_CASES=100000 cargo test -p bc_clone --test differential_proptest
```

To run the POSIX.1-2024 conformance suite (each case in the default mode and with `-s`):

```bash
bash scripts/run_posix_compliance_tests.sh
BC_BIN=bc bash scripts/run_posix_compliance_tests.sh   # sanity-check the expectations against GNU bc
```

To run the official GNU `bc 1.08.2` reference test suite:

```bash
bash scripts/run_gnu_reference_tests.sh
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

### Formal Verification (Verus, Kani, Miri)

- **Verus** (`bash scripts/run_verus_verification.sh`): proves the `requires`/`ensures` contracts of the kernels in `crates/bc_core/src/verified_kernels.rs`. These include the POSIX scale rules, register clamping, the 70-column wrapping step, lexer bounds, Pratt precedence, CLI option classification, and the REPL block scanner. The kernels are defined once with `dual_verified!` and called directly by production code. The evaluator keeps every scale at most `BC_SCALE_MAX`, which establishes the kernels' preconditions at run time. `crates/bc_core/src/verus_proofs.rs` adds lemmas and *design models* of larger algorithms. Production code does not call those models; the module documentation maps each one to the code and tests that cover its production counterpart.
- **Kani** (`bash scripts/run_kani_verification.sh`): bounded model checking of the kernels over all bit patterns, of the C-FFI helper `write_c_string` (never writes beyond the caller's buffer, always NUL-terminates), and of the C-API NULL guards.
- **Miri** (`bash scripts/run_miri_tests.sh`): runs the unit tests of every host crate under strict provenance and symbolic alignment checks, and the C API again under Tree Borrows.

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
- **CI Workflow (`.github/workflows/ci.yml`)**: On every push and pull request, checks formatting and Clippy (host, RISC-V and Wasm targets), runs all tests with a 98% line-coverage gate, the GNU reference and POSIX conformance suites, the bare-metal QEMU RISC-V 32 tests, the ESP32-C3 and Wasm builds, Verus, Kani, Miri, `cargo audit`, and diff-based mutation testing (`cargo mutants --in-diff`).
- **Release Workflow (`.github/workflows/release.yml`)**: Cross-compiles optimized binaries for Linux, macOS, and Windows and attaches them to a new GitHub Release automatically whenever a version tag (e.g. `v1.0.0`) is pushed.

## License

This project is licensed under the MIT License - see the [LICENSE](LICENSE) file in the repository for details.
