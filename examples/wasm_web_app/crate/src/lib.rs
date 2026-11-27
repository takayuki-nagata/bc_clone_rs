// SPDX-License-Identifier: MIT

#![no_std]

extern crate alloc;
#[cfg(test)]
extern crate std;

use alloc::boxed::Box;
use alloc::rc::Rc;
use alloc::string::String;
use bc_core::verified_kernels::verified_extension_policy;
use bc_core::{BcWriter, Evaluator, STDIN_SOURCE};
use core::cell::RefCell;
use core::fmt::Write;
use wasm_bindgen::prelude::*;

#[derive(Clone, Default)]
struct SharedBuffer(Rc<RefCell<String>>);

unsafe impl Send for SharedBuffer {}

impl Write for SharedBuffer {
    // coverage: miri(test_shared_buffer_collects_the_output); why: trait
    fn write_str(&mut self, s: &str) -> core::fmt::Result {
        self.0.borrow_mut().push_str(s);
        Ok(())
    }
}

impl BcWriter for SharedBuffer {
    // coverage: miri(test_shared_buffer_collects_the_output); why: trait
    fn flush(&mut self) -> core::fmt::Result {
        Ok(())
    }
}

/// Nesting limit (`docs/COMPATIBILITY.md` §2). Measured in V8 by `tests/nesting_limit.mjs`: one
/// level takes at most about 480 bytes of the 1 MiB stack in linear memory, so 1000 levels use 46%
/// of it, and they also run with half of V8's default stack (492 KB). They also ran in Firefox 159,
/// up to 2000 levels. Safari is not measured. An overflow of either stack kills the instance.
const WASM_MAX_DEPTH: usize = 1000;

// coverage: miri(via eval_bc, via BcSession::new); why: dyn
fn new_evaluator(math_enabled: bool, out_buf: &SharedBuffer, err_buf: &SharedBuffer) -> Evaluator {
    let mut ev = Evaluator::new(
        math_enabled,
        Box::new(out_buf.clone()),
        Box::new(err_buf.clone()),
    );
    ev.max_depth = WASM_MAX_DEPTH;
    ev.max_eval_depth = WASM_MAX_DEPTH;
    ev
}

// coverage: miri(via eval_bc, via BcSession::eval); why: dyn
fn eval_into_wasm(code: &str, ev: &mut Evaluator) {
    ev.run_source(code.as_bytes(), STDIN_SOURCE);
}

/// One-shot evaluation function for simple calculations.
// coverage: miri(test_eval_bc_basic_and_mathlib, test_eval_bc_error_recovery); why: bindgen
#[wasm_bindgen]
pub fn eval_bc(code: &str, math_enabled: bool, default_scale: u32) -> String {
    let out_buf = SharedBuffer::default();
    let err_buf = SharedBuffer::default();

    let mut ev = new_evaluator(math_enabled, &out_buf, &err_buf);
    ev.set_scale(default_scale as usize);

    eval_into_wasm(code, &mut ev);

    let err = err_buf.0.borrow().clone();
    if !err.is_empty() {
        return err;
    }

    out_buf.0.borrow().clone()
}

/// The version line of the build, such as `bc_clone 0.5.0 (a916de2)`.
// coverage: miri(test_version_is_the_version_line); why: bindgen
#[wasm_bindgen]
pub fn version() -> String {
    String::from(bc_build_info::VERSION_LINE)
}

/// Persistent Evaluator session holding state across interactive commands.
#[wasm_bindgen]
pub struct BcSession {
    evaluator: Evaluator,
    out_buf: SharedBuffer,
    err_buf: SharedBuffer,
}

#[wasm_bindgen]
impl BcSession {
    // coverage: miri(test_bc_session_lifecycle_and_error_recovery); why: bindgen
    #[wasm_bindgen(constructor)]
    pub fn new(math_enabled: bool) -> BcSession {
        let out_buf = SharedBuffer::default();
        let err_buf = SharedBuffer::default();

        let evaluator = new_evaluator(math_enabled, &out_buf, &err_buf);

        BcSession {
            evaluator,
            out_buf,
            err_buf,
        }
    }

    /// Evaluates a code snippet within this persistent session.
    // coverage: miri(test_bc_session_lifecycle_and_error_recovery); why: bindgen
    pub fn eval(&mut self, code: &str) -> String {
        // Clear previous buffers
        self.out_buf.0.borrow_mut().clear();
        self.err_buf.0.borrow_mut().clear();

        let mut code_with_nl = String::from(code);
        if !code_with_nl.ends_with('\n') {
            code_with_nl.push('\n');
        }

        eval_into_wasm(&code_with_nl, &mut self.evaluator);
        self.evaluator.clear_quit();

        let err = self.err_buf.0.borrow().clone();
        if !err.is_empty() {
            return err;
        }

        self.out_buf.0.borrow().clone()
    }

    /// Resets the session state.
    // coverage: miri(test_bc_session_lifecycle_and_error_recovery); why: bindgen
    pub fn reset(&mut self, math_enabled: bool) {
        self.out_buf.0.borrow_mut().clear();
        self.err_buf.0.borrow_mut().clear();

        self.evaluator = new_evaluator(math_enabled, &self.out_buf, &self.err_buf);
    }

    /// Sets the nesting limit, to measure the stack use of other limits.
    // coverage: miri(test_set_max_depth_moves_the_nesting_limit); why: bindgen
    #[cfg(feature = "stack-probe")]
    pub fn set_max_depth(&mut self, max_depth: usize) {
        self.evaluator.max_depth = max_depth;
        self.evaluator.max_eval_depth = max_depth;
    }

    /// Sets the default scale precision.
    // coverage: miri(test_bc_session_lifecycle_and_error_recovery); why: bindgen
    pub fn set_scale(&mut self, scale: u32) {
        self.evaluator.set_scale(scale as usize);
    }

    /// Sets how non-POSIX syntax is treated: 0 accepts it (default), 1 warns like `bc -w`,
    /// 2 rejects it like `bc -s`. Other values are ignored.
    // coverage: miri(test_bc_session_extension_policy_and_scale_clamp); why: bindgen
    pub fn set_extension_policy(&mut self, policy: u8) {
        if let Some(policy) = verified_extension_policy(u32::from(policy)) {
            self.evaluator.extension_policy = policy;
        }
    }

    /// Gets the current scale precision.
    // coverage: miri(test_bc_session_lifecycle_and_error_recovery); why: bindgen
    pub fn get_scale(&self) -> u32 {
        self.evaluator.scale() as u32
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_shared_buffer_collects_the_output() {
        let mut buf = SharedBuffer::default();
        let other = buf.clone();
        buf.write_str("1").unwrap();
        buf.write_bytes(b"2\n").unwrap();
        buf.flush().unwrap();
        assert_eq!(*other.0.borrow(), "12\n");
    }

    #[cfg(feature = "stack-probe")]
    #[test]
    fn test_set_max_depth_moves_the_nesting_limit() {
        let deep = |n: usize| {
            let mut s = String::new();
            (0..n).for_each(|_| s.push('('));
            s.push('1');
            (0..n).for_each(|_| s.push(')'));
            s
        };
        let mut sess = BcSession::new(false);
        assert_eq!(sess.eval(&deep(20)), "1\n");
        sess.set_max_depth(10);
        assert_eq!(sess.evaluator.max_eval_depth, 10);
        assert!(sess.eval(&deep(20)).contains("nesting too deep"));
        sess.set_max_depth(30);
        assert_eq!(sess.eval(&deep(20)), "1\n");
    }

    #[test]
    fn test_version_is_the_version_line() {
        assert_eq!(version(), bc_build_info::VERSION_LINE);
        assert!(version().starts_with("bc_clone "));
    }

    #[test]
    fn test_eval_bc_basic_and_mathlib() {
        assert_eq!(eval_bc("2^10\n", false, 0).trim(), "1024");
        assert_eq!(eval_bc("4 * a(1)\n", true, 10).trim(), "3.1415926532");
        assert_eq!(eval_bc("quit\n", false, 0), "");
    }

    #[test]
    fn test_eval_bc_error_recovery() {
        assert_eq!(
            eval_bc("@\n", false, 0),
            "(standard_in) 1: illegal character: @\n"
        );
        assert_eq!(
            eval_bc("1 + * 2\n", false, 0),
            "(standard_in) 1: syntax error\n"
        );
        assert_eq!(
            eval_bc("1 / 0\n", false, 0),
            "Runtime error (func=(main)): Divide by zero\n"
        );
        assert_eq!(
            eval_bc("sqrt(-1)\n", false, 0),
            "Runtime error (func=(main)): Square root of a negative number\n"
        );
        assert_eq!(
            eval_bc("unknown_fn(1)\n", false, 0),
            "Runtime error (func=(main)): Function unknown_fn not defined.\n"
        );
    }

    #[test]
    fn test_bc_session_extension_policy_and_scale_clamp() {
        let mut sess = BcSession::new(false);
        assert_eq!(sess.eval("abc = 1; abc"), "1\n");
        sess.set_extension_policy(2);
        assert_eq!(
            sess.eval("xyz"),
            "(standard_in) 2: Error: multiple letter name - xyz\n"
        );
        sess.set_extension_policy(9);
        assert_eq!(
            sess.eval("xyz"),
            "(standard_in) 2: Error: multiple letter name - xyz\n"
        );
        sess.set_extension_policy(1);
        assert_eq!(
            sess.eval("xyz"),
            "(standard_in) 2: (Warning) multiple letter name - xyz\n"
        );
        sess.set_extension_policy(0);
        assert_eq!(sess.eval("xyz"), "0\n");
        sess.set_scale(u32::MAX);
        assert_eq!(sess.get_scale(), 1_000_000_000);
    }

    #[test]
    fn test_every_evaluator_has_the_wasm_nesting_limit() {
        let mut sess = BcSession::new(false);
        assert_eq!(sess.evaluator.max_depth, WASM_MAX_DEPTH);
        sess.evaluator.max_depth = 1;
        sess.evaluator.max_eval_depth = 1;
        sess.reset(false);
        assert_eq!(sess.evaluator.max_depth, WASM_MAX_DEPTH);
    }

    #[test]
    fn test_bc_session_lifecycle_and_error_recovery() {
        let mut sess = BcSession::new(true);
        assert_eq!(sess.get_scale(), 0);
        sess.set_scale(4);
        assert_eq!(sess.get_scale(), 4);

        assert_eq!(sess.eval("x = 20; x / 3").trim(), "6.6666");

        // Error recovery inside function call preserves session variable x = 20
        assert_eq!(
            sess.eval("define bad(x) { auto y; x = 999; y = 1 / 0; return (y); }"),
            ""
        );
        assert!(
            sess.eval("bad(5)")
                .contains("Runtime error (func=bad): Divide by zero")
        );
        assert_eq!(sess.eval("x").trim(), "20");

        // Syntax error recovery and quit
        assert!(
            sess.eval("1 + * 2")
                .contains("(standard_in) 1: syntax error")
        );
        assert_eq!(sess.eval("quit"), "");
        assert_eq!(sess.eval("x + 2").trim(), "22");

        // Reset clears variables and scale
        sess.reset(false);
        assert_eq!(sess.get_scale(), 0);
        assert_eq!(sess.eval("x").trim(), "0");
    }
}
