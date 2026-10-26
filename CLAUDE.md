@AGENTS.md

## Claude Code notes

- Spec questions: POSIX.1-2024 `bc` is authoritative; implementation-defined choices and known GNU
  differences live in `docs/COMPATIBILITY.md`. GNU `bc` output is a reference, not the oracle.
- Record every user-visible change in `CHANGELOG.md`, and every behavior decision in
  `docs/COMPATIBILITY.md`.
- Quick checks while iterating:
  - `cargo test -p bc_core` / `cargo test -p bc_clone` (the integration tests need GNU `bc` 1.08 and
    coreutils `timeout` on `PATH`)
  - `PROPTEST_CASES=100000 cargo test -p bc_clone --test differential_proptest` for a long
    differential fuzzing run against GNU `bc`
  - `bash scripts/run_gnu_reference_tests.sh`, `bash scripts/run_posix_compliance_tests.sh`
- Heavy verification (run before opening a PR that touches the relevant code):
  `scripts/run_verus_verification.sh`, `scripts/run_kani_verification.sh`, `scripts/run_miri_tests.sh`,
  `scripts/run_qemu_riscv32_tests.sh`, `scripts/run_zephyr_tests.sh`, `scripts/build_wasm.sh`.
