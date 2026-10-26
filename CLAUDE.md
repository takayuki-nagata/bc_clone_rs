@AGENTS.md

## Claude Code notes

- Spec questions: POSIX.1-2024 `bc` is authoritative; implementation-defined choices and known GNU
  differences live in `docs/COMPATIBILITY.md`. GNU `bc` output is a reference, not the oracle.
- Branching: work on topic branches cut from `release/v0.4.0` (e.g. `fix/…`, `test/…`, `chore/…`).
- Quick checks while iterating:
  - `cargo test -p bc_core` / `cargo test -p bc_clone` (the integration tests need GNU `bc` on `PATH`)
  - `bash scripts/run_gnu_reference_tests.sh`, `bash scripts/run_posix_compliance_tests.sh`
- Heavy verification (run before opening a PR that touches the relevant code):
  `scripts/run_verus_verification.sh`, `scripts/run_kani_verification.sh`, `scripts/run_miri_tests.sh`,
  `scripts/run_qemu_riscv32_tests.sh`, `scripts/run_zephyr_tests.sh`, `scripts/build_wasm.sh`.
