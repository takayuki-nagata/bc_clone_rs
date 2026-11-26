// SPDX-License-Identifier: MIT

//! Links the riscv32 binary with `memory.x` (from this directory) and `riscv-rt`'s `link.x`.
//! The library's host tests are not affected: the arguments are for the binaries only.

// coverage: shim(scripts/run_qemu_riscv32_tests.sh); why: build
fn main() {
    println!("cargo:rustc-link-search={}", env!("CARGO_MANIFEST_DIR"));
    println!("cargo:rustc-link-arg-bins=-Tmemory.x");
    println!("cargo:rustc-link-arg-bins=-Tlink.x");
    println!("cargo:rerun-if-changed=memory.x");
}
