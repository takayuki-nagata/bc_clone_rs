// SPDX-License-Identifier: MIT

//! C-FFI static library bindings for `bc_core`.
//!
//! Suitable for integration with Zephyr RTOS, FreeRTOS, NuttX, ESP-IDF,
//! and standard C/C++ embedded applications.

#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(feature = "std")]
extern crate std;

extern crate alloc;

use alloc::boxed::Box;
use alloc::ffi::CString;
use alloc::rc::Rc;
use alloc::string::String;
use bc_core::{BcWriter, Evaluator, Lexer, Parser};
use core::cell::RefCell;
use core::ffi::{CStr, c_char, c_void};
use core::fmt::Write;

#[cfg(not(feature = "std"))]
use embedded_alloc::LlffHeap as Heap;

#[cfg(not(feature = "std"))]
#[global_allocator]
static HEAP: Heap = Heap::empty();

#[cfg(not(feature = "std"))]
const HEAP_SIZE: usize = 2 * 1024 * 1024;
#[cfg(not(feature = "std"))]
static mut HEAP_MEM: [u8; HEAP_SIZE] = [0; HEAP_SIZE];

#[cfg(not(feature = "std"))]
struct SingleHartCs;
#[cfg(not(feature = "std"))]
unsafe impl critical_section::Impl for SingleHartCs {
    unsafe fn acquire() -> critical_section::RawRestoreState {}
    unsafe fn release(_token: critical_section::RawRestoreState) {}
}
#[cfg(not(feature = "std"))]
critical_section::set_impl!(SingleHartCs);

#[cfg(not(feature = "std"))]
fn init_heap_if_needed() {
    static mut HEAP_INITIALIZED: bool = false;
    critical_section::with(|_| unsafe {
        #[allow(static_mut_refs)]
        if !HEAP_INITIALIZED {
            HEAP_INITIALIZED = true;
            HEAP.init(HEAP_MEM.as_ptr() as usize, HEAP_SIZE);
        }
    });
}

#[cfg(feature = "std")]
fn init_heap_if_needed() {}

#[cfg(not(feature = "std"))]
#[panic_handler]
fn panic(_info: &core::panic::PanicInfo) -> ! {
    loop {
        core::hint::spin_loop();
    }
}

/// Status codes returned by C-API functions.
#[repr(C)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BcStatus {
    /// Operation succeeded.
    Ok = 0,
    /// Null pointer provided for required pointer arguments.
    ErrNullPtr = 1,
    /// Output buffer is too small to contain the result.
    ErrBufferTooSmall = 2,
    /// Evaluation or syntax error occurred.
    ErrExecution = 3,
}

/// A reference-counted, interior-mutable String buffer implementing BcWriter.
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

/// Callback function signature matching `bc_output_cb_t`.
pub type BcOutputCb = Option<unsafe extern "C" fn(str: *const c_char, user_data: *mut c_void)>;

/// A BcWriter adapter that routes output chunks to a C callback.
struct CallbackWriter {
    cb: BcOutputCb,
    user_data: *mut c_void,
}

unsafe impl Send for CallbackWriter {}

impl Write for CallbackWriter {
    fn write_str(&mut self, s: &str) -> core::fmt::Result {
        if let (Some(callback), Ok(c_str)) = (self.cb, CString::new(s)) {
            unsafe {
                callback(c_str.as_ptr(), self.user_data);
            }
        }
        Ok(())
    }
}

impl BcWriter for CallbackWriter {
    fn flush(&mut self) -> core::fmt::Result {
        Ok(())
    }
}

/// Evaluates a bc expression or script string and writes the output into a buffer.
///
/// # Safety
/// - `code` must be a valid null-terminated C string.
/// - `out_buf` must be a valid writable pointer of at least `buf_size` bytes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bc_eval(
    code: *const c_char,
    math_enabled: bool,
    default_scale: u32,
    out_buf: *mut c_char,
    buf_size: usize,
) -> BcStatus {
    init_heap_if_needed();

    if code.is_null() || out_buf.is_null() {
        return BcStatus::ErrNullPtr;
    }

    if buf_size == 0 {
        return BcStatus::ErrBufferTooSmall;
    }

    let code_cstr = unsafe { CStr::from_ptr(code) };
    let code_str = match code_cstr.to_str() {
        Ok(s) => s,
        Err(_) => return BcStatus::ErrExecution,
    };

    let out_shared = SharedBuffer::default();
    let err_shared = SharedBuffer::default();

    let mut ev = Evaluator::new(
        math_enabled,
        Box::new(out_shared.clone()),
        Box::new(err_shared),
    );
    ev.scale = default_scale as usize;

    let lexer = Lexer::new(code_str);
    let mut parser = Parser::new(lexer);
    let stmts = parser.parse_program();

    for stmt in &stmts {
        ev.execute(stmt);
    }
    let _ = ev.stdout_writer.flush();

    let captured = out_shared.0.borrow().clone();
    let bytes = captured.as_bytes();
    if bytes.len() + 1 > buf_size {
        return BcStatus::ErrBufferTooSmall;
    }

    unsafe {
        core::ptr::copy_nonoverlapping(bytes.as_ptr(), out_buf.cast::<u8>(), bytes.len());
        *out_buf.add(bytes.len()) = 0;
    }

    BcStatus::Ok
}

/// Evaluates a bc script string and sends output chunks to callback functions.
///
/// # Safety
/// - `code` must be a valid null-terminated C string.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bc_eval_callback(
    code: *const c_char,
    math_enabled: bool,
    default_scale: u32,
    stdout_cb: BcOutputCb,
    stderr_cb: BcOutputCb,
    user_data: *mut c_void,
) -> BcStatus {
    init_heap_if_needed();

    if code.is_null() {
        return BcStatus::ErrNullPtr;
    }

    let code_cstr = unsafe { CStr::from_ptr(code) };
    let code_str = match code_cstr.to_str() {
        Ok(s) => s,
        Err(_) => return BcStatus::ErrExecution,
    };

    let cb_writer_out = Box::new(CallbackWriter {
        cb: stdout_cb,
        user_data,
    });
    let cb_writer_err = Box::new(CallbackWriter {
        cb: stderr_cb,
        user_data,
    });

    let mut evaluator = Evaluator::new(math_enabled, cb_writer_out, cb_writer_err);
    evaluator.scale = default_scale as usize;

    let lexer = Lexer::new(code_str);
    let mut parser = Parser::new(lexer);
    let stmts = parser.parse_program();

    for stmt in &stmts {
        evaluator.execute(stmt);
    }
    let _ = evaluator.stdout_writer.flush();

    BcStatus::Ok
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_bc_eval_basic() {
        let code = CString::new("1 + 2 * 3\n").unwrap();
        let mut buf = [0 as c_char; 64];

        let status = unsafe { bc_eval(code.as_ptr(), false, 0, buf.as_mut_ptr(), buf.len()) };

        assert_eq!(status, BcStatus::Ok);
        let result = unsafe { CStr::from_ptr(buf.as_ptr()).to_str().unwrap() };
        assert_eq!(result.trim(), "7");
    }

    #[test]
    fn test_bc_eval_math_library() {
        let code = CString::new("scale=10; 4*a(1)\n").unwrap();
        let mut buf = [0 as c_char; 64];

        let status = unsafe { bc_eval(code.as_ptr(), true, 10, buf.as_mut_ptr(), buf.len()) };

        assert_eq!(status, BcStatus::Ok);
        let result = unsafe { CStr::from_ptr(buf.as_ptr()).to_str().unwrap() };
        assert_eq!(result.trim(), "3.1415926532");
    }

    #[test]
    fn test_bc_eval_null_pointers_and_small_buffer() {
        let code = CString::new("1 + 1\n").unwrap();
        let mut buf = [0 as c_char; 64];

        // Null code
        assert_eq!(
            unsafe { bc_eval(core::ptr::null(), false, 0, buf.as_mut_ptr(), buf.len()) },
            BcStatus::ErrNullPtr
        );

        // Null out_buf
        assert_eq!(
            unsafe { bc_eval(code.as_ptr(), false, 0, core::ptr::null_mut(), buf.len()) },
            BcStatus::ErrNullPtr
        );

        // Buffer too small (0 bytes)
        assert_eq!(
            unsafe { bc_eval(code.as_ptr(), false, 0, buf.as_mut_ptr(), 0) },
            BcStatus::ErrBufferTooSmall
        );

        // Buffer too small for result "2\n\0" (needs at least 3 bytes)
        let mut tiny_buf = [0 as c_char; 2];
        assert_eq!(
            unsafe {
                bc_eval(
                    code.as_ptr(),
                    false,
                    0,
                    tiny_buf.as_mut_ptr(),
                    tiny_buf.len(),
                )
            },
            BcStatus::ErrBufferTooSmall
        );
    }

    #[test]
    fn test_bc_eval_callback() {
        let code = CString::new("2^10\n").unwrap();
        let mut collected = String::new();

        unsafe extern "C" fn test_cb(chunk: *const c_char, user_data: *mut c_void) {
            unsafe {
                let target = &mut *(user_data as *mut String);
                let s = CStr::from_ptr(chunk).to_str().unwrap();
                target.push_str(s);
            }
        }

        let status = unsafe {
            bc_eval_callback(
                code.as_ptr(),
                false,
                0,
                Some(test_cb),
                None,
                &mut collected as *mut String as *mut c_void,
            )
        };

        assert_eq!(status, BcStatus::Ok);
        assert_eq!(collected.trim(), "1024");

        // Null code check
        assert_eq!(
            unsafe {
                bc_eval_callback(
                    core::ptr::null(),
                    false,
                    0,
                    None,
                    None,
                    core::ptr::null_mut(),
                )
            },
            BcStatus::ErrNullPtr
        );
    }
}
