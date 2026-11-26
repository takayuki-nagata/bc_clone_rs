// SPDX-License-Identifier: MIT
//
// The host's prebuilt `core` and `alloc` are compiled for unwinding and refer to
// `rust_eh_personality`, which a `no_std` library does not define. The library is built with
// panic = "abort", so nothing unwinds and this is never called; embedded targets build `core`
// without unwinding and do not need it.
void rust_eh_personality(void);
void rust_eh_personality(void) {}
