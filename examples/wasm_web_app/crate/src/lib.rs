// SPDX-License-Identifier: MIT

#![no_std]

extern crate alloc;
#[cfg(test)]
extern crate std;

use alloc::boxed::Box;
use alloc::rc::Rc;
use alloc::string::String;
use bc_core::{BcWriter, Evaluator, ExtensionPolicy, STDIN_SOURCE};
use core::cell::RefCell;
use core::fmt::Write;
use wasm_bindgen::prelude::*;

#[derive(Clone, Default)]
struct SharedBuffer(Rc<RefCell<String>>);

unsafe impl Send for SharedBuffer {}

impl Write for SharedBuffer {
    fn write_str(&mut self, s: &str) -> core::fmt::Result {
        self.0.borrow_mut().push_str(s);
        Ok(())
    }
}

impl BcWriter for SharedBuffer {
    fn flush(&mut self) -> core::fmt::Result {
        Ok(())
    }
}

fn eval_into_wasm(code: &str, ev: &mut Evaluator) {
    ev.run_source(code, STDIN_SOURCE);
}

/// One-shot evaluation function for simple calculations.
#[wasm_bindgen]
pub fn eval_bc(code: &str, math_enabled: bool, default_scale: u32) -> String {
    let out_buf = SharedBuffer::default();
    let err_buf = SharedBuffer::default();

    let mut ev = Evaluator::new(
        math_enabled,
        Box::new(out_buf.clone()),
        Box::new(err_buf.clone()),
    );
    ev.set_scale(default_scale as usize);

    eval_into_wasm(code, &mut ev);

    let err = err_buf.0.borrow().clone();
    if !err.is_empty() {
        return err;
    }

    out_buf.0.borrow().clone()
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
    #[wasm_bindgen(constructor)]
    pub fn new(math_enabled: bool) -> BcSession {
        let out_buf = SharedBuffer::default();
        let err_buf = SharedBuffer::default();

        let evaluator = Evaluator::new(
            math_enabled,
            Box::new(out_buf.clone()),
            Box::new(err_buf.clone()),
        );

        BcSession {
            evaluator,
            out_buf,
            err_buf,
        }
    }

    /// Evaluates a code snippet within this persistent session.
    pub fn eval(&mut self, code: &str) -> String {
        // Clear previous buffers
        self.out_buf.0.borrow_mut().clear();
        self.err_buf.0.borrow_mut().clear();

        let mut code_with_nl = String::from(code);
        if !code_with_nl.ends_with('\n') {
            code_with_nl.push('\n');
        }

        eval_into_wasm(&code_with_nl, &mut self.evaluator);
        self.evaluator.quit_flag = false;

        let err = self.err_buf.0.borrow().clone();
        if !err.is_empty() {
            return err;
        }

        self.out_buf.0.borrow().clone()
    }

    /// Resets the session state.
    pub fn reset(&mut self, math_enabled: bool) {
        self.out_buf.0.borrow_mut().clear();
        self.err_buf.0.borrow_mut().clear();

        self.evaluator = Evaluator::new(
            math_enabled,
            Box::new(self.out_buf.clone()),
            Box::new(self.err_buf.clone()),
        );
    }

    /// Sets the default scale precision.
    pub fn set_scale(&mut self, scale: u32) {
        self.evaluator.set_scale(scale as usize);
    }

    /// Sets how non-POSIX syntax is treated: 0 accepts it (default), 1 warns like `bc -w`,
    /// 2 rejects it like `bc -s`. Other values are ignored.
    pub fn set_extension_policy(&mut self, policy: u8) {
        self.evaluator.extension_policy = match policy {
            0 => ExtensionPolicy::Allow,
            1 => ExtensionPolicy::Warn,
            2 => ExtensionPolicy::Reject,
            _ => return,
        };
    }

    /// Gets the current scale precision.
    pub fn get_scale(&self) -> u32 {
        self.evaluator.scale() as u32
    }
}

#[cfg(test)]
mod tests {
    use super::*;

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
        sess.set_extension_policy(0);
        sess.set_scale(u32::MAX);
        assert_eq!(sess.get_scale(), 1_000_000_000);
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
