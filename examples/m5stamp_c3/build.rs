// SPDX-License-Identifier: MIT

// coverage: shim(scripts/build_m5stamp_c3.sh); why: build
/// Links the application with esp-hal's linker script. Only the binary: the library's unit tests
/// run on the host.
fn main() {
    println!("cargo:rustc-link-arg-bins=-Tlinkall.x");
}
