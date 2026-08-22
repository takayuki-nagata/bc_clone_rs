// SPDX-License-Identifier: MIT

#![no_std]

extern crate alloc;

use alloc::boxed::Box;
use alloc::rc::Rc;
use alloc::string::String;
use bc_core::{BcWriter, Evaluator, Lexer, Parser};
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
    ev.scale = default_scale as usize;

    let lexer = Lexer::new(code);
    let mut parser = Parser::new(lexer);
    let stmts = parser.parse_program();

    for stmt in &stmts {
        ev.execute(stmt);
    }
    let _ = ev.stdout_writer.flush();

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

        let lexer = Lexer::new(&code_with_nl);
        let mut parser = Parser::new(lexer);
        let stmts = parser.parse_program();

        for stmt in &stmts {
            self.evaluator.execute(stmt);
        }
        let _ = self.evaluator.stdout_writer.flush();

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
        self.evaluator.scale = scale as usize;
    }

    /// Gets the current scale precision.
    pub fn get_scale(&self) -> u32 {
        self.evaluator.scale as u32
    }
}
