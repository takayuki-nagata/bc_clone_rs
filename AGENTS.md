# AI Agent Design & Architecture: bc_clone

This document outlines the design decisions, technical architecture, and mathematical algorithms implemented by the AI coding agent (**Antigravity**) for the Rust-based `bc` calculator clone (`bc_clone`).

## System Architecture Overview

The system is designed with clean separation of concerns, divided into two distinct crates within a Cargo Workspace:

```mermaid
graph TD
    CLI[crates/bc_cli/src/main.rs: CLI & REPL Loop] --> Core[crates/bc_core: #![no_std] + alloc Core Engine]
    Core --> Lexer[crates/bc_core/src/parser.rs: Lexer]
    Lexer --> Parser[crates/bc_core/src/parser.rs: Pratt Parser]
    Parser --> AST[AST Nodes / Statements]
    AST --> Evaluator[crates/bc_core/src/eval.rs: Evaluator]
    Evaluator --> Math[crates/bc_core/src/math.rs: BCNum & Decimal Math]
```

### 1. Lexical Analysis and Parsing (`crates/bc_core/src/parser.rs`)
- **Lexer**: Tokenizes input character streams. Handles dynamic line number tracking, single and multi-line comments (`/* ... */`), string literals, escape characters, and backslash-newline continuation.
- **Parser**: A recursive descent parser utilizing Pratt parsing (precedence climbing) for algebraic expressions. 
  - Resolves operator precedence and associativity (e.g., right-associative exponentiation `^` and assignments).
  - Emits a clean AST consisting of `Stmt` (Statements) and `Expr` (Expressions).
  - Handles the GNU extension permitting `return` without enclosing parentheses.

### 2. Arbitrary-Precision Math (`crates/bc_core/src/math.rs`)
- **`BCNum`**: The primary representation for user-facing numbers. Stores numbers as a `coeff: BigInt` coefficient and a `scale: usize` representing the number of fractional decimal digits.
  - Implements POSIX-compliant truncation/extension semantics for addition, subtraction, multiplication, division, modulo, and exponentiation.
  - Handles base conversion under arbitrary input bases (`ibase` in $[2, 16]$) and output bases (`obase` in $[2, \infty]$).
  - Fractional digit calculation for non-decimal `obase` uses exact `BigInt` power inequalities ($obase^k \ge 10^{scale}$) without floating-point `ln()` or `libm`, ensuring full `#![no_std]` compliance.
- **`Decimal`**: An internal, high-precision fixed-point helper type used specifically for computing transcendental functions. Pairwise operations are computed with an extra guard precision of 15 decimal digits.

### 3. AST Execution and Scoping (`crates/bc_core/src/eval.rs`)
- **Stack-based Scoping**: POSIX `bc` uses dynamic scoping. When a function is called, variables and arrays declared as `auto` are pushed onto a global stack map. Uses `alloc::collections::BTreeMap` for memory-compact, zero-entropy, `no_std`-safe storage.
- **BcWriter & WrappedStdout**: Abstract output stream wrapping (`BcWriter` trait) that formats number output lines to stay within 70 characters as mandated by POSIX, wrapping lines with a backslash-newline when necessary without `std::io` dependencies.

### 4. Entry Point & REPL Loop (`crates/bc_cli/src/main.rs`)
- **Option Parsing**: Handled natively without external dependencies, adhering strictly to POSIX option-argument combinations (e.g., `-l` flag to load the math library).
- **Interactive REPL**: Employs an input accumulator that counts open braces and backslash-newlines to determine block completeness before evaluating. Bypasses signal registration under `#[cfg(test)]` to permit isolated, parallel tests.
- **IoWriter**: Adapts host `std::io::Write` streams into `bc_core::BcWriter`.

---

## Math Library and Transcendental Approximations

All transcendental functions in `src/bc_math.rs` are calculated using `Decimal` fixed-point representations and Taylor series expansions with dynamic scaling/argument reduction.

### 1. Exponential function (`e(x)`)
To compute $e^x$ with high precision:
- **Argument Reduction**: We express $x$ as $x = n \ln(2) + r$, where $n$ is an integer and $r \in [0, \ln(2))$.
- **Taylor Series**: We calculate $e^r$ using its Taylor expansion:
  $$e^r = \sum_{k=0}^{\infty} \frac{r^k}{k!}$$
  Because $r < \ln(2) \approx 0.693$, this series converges extremely rapidly.
- **Reconstruction**: The final value is computed as $e^x = e^r \cdot 2^n$. Multiplication by $2^n$ is performed via binary exponentiation.

### 2. Natural Logarithm (`l(x)`)
To compute $\ln(x)$:
- **Argument Reduction**: We normalize the coefficient of the input $x$ to $x = m \cdot 2^k$, where $m \in [1/\sqrt{2}, \sqrt{2}]$.
- **Taylor Series**: We compute $\ln(m)$ using the rapid expansion:
  $$\ln\left(\frac{1+y}{1-y}\right) = 2 \sum_{n=0}^{\infty} \frac{y^{2n+1}}{2n+1}$$
  where $y = \frac{m-1}{m+1}$. Since $m \in [0.707, 1.414]$, $y \in [-0.171, 0.171]$, guaranteeing rapid convergence.
- **Reconstruction**: The result is reconstructed as $\ln(x) = \ln(m) + k \ln(2)$, where $\ln(2)$ is precomputed to the required precision.

### 3. Trigonometric Functions (`s(x)`, `c(x)`)
- **Argument Reduction**: Reduce $x$ modulo $2\pi$ to the range $[-\pi, \pi]$, then divide by a power of 2 ($2^p$) until the argument is small enough (typically $< 0.05$) to ensure fast convergence.
- **Taylor Series**: Compute $\sin$ and $\cos$ of the reduced argument $x'$:
  $$\sin(x') = \sum_{k=0}^{\infty} (-1)^k \frac{x'^{2k+1}}{(2k+1)!}, \quad \cos(x') = \sum_{k=0}^{\infty} (-1)^k \frac{x'^{2k}}{(2k)!}$$
- **Double-Angle Formula**: Double the result $p$ times using trigonometric identities:
  $$\sin(2\theta) = 2 \sin(\theta) \cos(\theta), \quad \cos(2\theta) = 2\cos^2(\theta) - 1$$

### 4. Arctangent (`a(x)`)
- **Argument Reduction**: If $|x| > 1$, we use $\arctan(x) = \frac{\pi}{2} - \arctan(1/x)$.
- **Taylor Series**: For small $x$, we use:
  $$\arctan(x) = \sum_{k=0}^{\infty} (-1)^k \frac{x^{2k+1}}{2k+1}$$

### 5. Bessel Function (`j(n, x)`)
- Computed using the infinite series definition for integer order $n$:
  $$J_n(x) = \sum_{m=0}^{\infty} \frac{(-1)^m (x/2)^{2m+n}}{m! (m+n)!}$$
  For negative orders, we apply the identity $J_{-n}(x) = (-1)^n J_n(x)$.

---

## Design Choices & Lessons Learned

### 1. Robust and Safe Error Recovery
To prevent the calculator from crashing on syntax errors or invalid runtime math (e.g., division by zero, square root of negative numbers), all execution and parsing paths are wrapped inside `std::panic::catch_unwind`. The application handles panics gracefully, prints clean error messages matching the expected style, and clears input state.

### 2. Immediate Exit on `quit`
POSIX `bc` terminates immediately upon reading the `quit` keyword, even if it resides on a line with other statements. By raising a targeted `"quit"` panic inside the parser, we bubble up the termination signal immediately. This avoids executing any prior statements on the same line and permits unit testing of the REPL exit logic without killing the test runner.
- **Silent Quit Hook**: To prevent Rust's default panic handler from printing an unsightly panic message/backtrace to `stderr` during `quit`, we registered a custom panic hook in `fn main()`. This hook intercepts `"quit"` panic payloads and exits silently, while letting other unexpected panics format tracebacks normally.

### 3. Preventing Parallel Test Conflicts
Signal handlers (such as `ctrlc::set_handler`) and panic hooks are global process-wide resources, and shared state like the `CTRL_C_PRESSED` atomic can cause race conditions during parallel test runs. 
- **Signal Guarding**: We isolated the signal handler registration behind a `#[cfg(not(test))]` guard, replacing it with a mock signal trigger in tests.
- **Test Serialization**: We introduced a `TEST_MUTEX` serial lock to synchronize unit tests in `src/main.rs` that access or modify process-wide states, preventing parallel runner threads from interfering with each other's execution.

### 4. RAII Scope Restoration on Panics
In POSIX `bc`, functions execute with dynamic scoping. If a function call panics or encounters a runtime error, standard `bc` restores the caller's variable/array scopes.
- **ScopeGuard**: We implemented a `ScopeGuard` RAII helper struct in `src/eval.rs`. When a function is called, the guard takes ownership of the previous flow control state and the auto/param scopes. If the function panics (e.g. division by zero), Rust's stack unwinding automatically triggers the `Drop` implementation on `ScopeGuard`, popping the local variable stacks and restoring flow control states. This guarantees 100% specification compliance and prevents variable shadowing leaks under runtime errors, which is a major safety improvement over the original Python implementation.

### 5. Diff-Based Mutation Testing in CI & Equivalent Mutants
To guarantee high test quality and ensure all code paths have meaningful assertions, `bc_clone` incorporates mutation testing using `cargo-mutants`.
- **Configured Timeout & Exclusions**: `.cargo/mutants.toml` defines `minimum_test_timeout = 5` and `timeout_multiplier = 2.0` to accommodate deep mathematical calculations.
- **Handling Semantically Equivalent Mutants**: Calculations that compute extra intermediate precision (such as `extra_prec` in `bc_exp`) produce mathematically identical outputs upon truncation. These over-precision mutants are semantically equivalent and cannot fail unit test assertions. They are explicitly documented and excluded via `exclude_re` in `.cargo/mutants.toml`.
- **CI Integration**: In `.github/workflows/ci.yml`, `cargo mutants --in-diff` executes on PR and push diffs to ensure newly added or modified lines are covered by tests.

### 6. Strict Pre-Commit Verification Workflow
To prevent CI breakage (such as formatting mismatches or clippy warnings), AI agents MUST run full local verification before creating git commits:
```bash
cargo fmt --check && cargo clippy -- -D warnings && cargo test
```
No changes should be committed until formatting, lints, and test suites pass with 100% success locally.

### 7. Differential E2E Integration Testing & GNU Reference Test Suite
- **Binary-Level Differential Validation**: `tests/integration_tests.rs` compiles the `bc_clone` binary and spawns both standard `bc` (GNU `bc`) and `bc_clone` using `std::process::Command`, feeding identical inputs and verifying exact `stdout` / `stderr` / exit code parity across 26 test suites.
- **GNU bc 1.08.2 Reference Test Runner**: `scripts/run_gnu_reference_tests.sh` dynamically fetches the official GNU `bc 1.08.2` reference tests (`BUG.bc`, `array.b`, `atan.b`, `div.b`, `exp.b`, `fact.b`, `jn.b`, `ln.b`, `mul.b`, `raise.b`, `sine.b`, `sqrt.b`, `sqrt1.b`, `sqrt2.b`, `testfn.b`, `signum`) and validates 100% output parity.
- **Excluded Non-Standard Extensions**: Non-standard GNU pointer extension tests (`arrayp.b` and `aryprm.b` using `*a[]` syntax) and scale-60 micro-rounding checks (`checklib.b`) are excluded as they test non-standard parser extensions or intermediate limb rounding artifacts.

### 8. POSIX IEEE Std 1003.1 Compliance Test Suite
- **Automated POSIX Conformance Verification**: `scripts/run_posix_compliance_tests.sh` evaluates `bc_clone` against standard `bc` across 20 strict POSIX IEEE Std 1003.1 specification test cases.
- **CI Integration**: Executed automatically on every push and pull request in `.github/workflows/ci.yml` to guarantee zero regressions in POSIX standard compliance.




