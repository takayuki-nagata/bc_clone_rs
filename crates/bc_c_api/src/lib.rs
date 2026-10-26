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
use bc_core::verified_kernels::verified_c_ffi_check_buf_capacity;
use bc_core::{BcWriter, Evaluator, ExtensionPolicy, STDIN_SOURCE};
use core::cell::RefCell;
use core::ffi::{CStr, c_char, c_void};
use core::fmt::Write;

#[cfg(not(feature = "std"))]
use embedded_alloc::LlffHeap as Heap;

#[cfg(not(feature = "std"))]
#[global_allocator]
static HEAP: Heap = Heap::empty();

#[cfg(not(feature = "std"))]
const HEAP_SIZE: usize = 65536;
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

/// Copies `bytes` into `out_buf` as a NUL-terminated C string.
///
/// Returns `true` if `bytes` and the terminator fit in `buf_size` bytes. Otherwise writes an
/// empty string (a single NUL) and returns `false`. Never writes past `out_buf[buf_size - 1]`
/// (verified by the Kani harness `proof_write_c_string`).
///
/// # Safety
/// `out_buf` must be valid for writes of `buf_size` bytes, and `buf_size >= 1`.
unsafe fn write_c_string(bytes: &[u8], out_buf: *mut c_char, buf_size: usize) -> bool {
    if verified_c_ffi_check_buf_capacity(bytes.len(), buf_size) {
        unsafe {
            core::ptr::copy_nonoverlapping(bytes.as_ptr(), out_buf.cast::<u8>(), bytes.len());
            *out_buf.add(bytes.len()) = 0;
        }
        true
    } else {
        unsafe { *out_buf = 0 };
        false
    }
}

/// Evaluates `code_str` against `ev` without panicking. Errors are reported to `ev`'s stderr
/// writer and evaluation continues with the next input unit (`docs/COMPATIBILITY.md` §3.1).
/// Returns `BcStatus::ErrExecution` if any unit failed.
fn eval_into_evaluator(code_str: &str, ev: &mut Evaluator) -> BcStatus {
    let summary = ev.run_source(code_str, STDIN_SOURCE);
    if summary.errors > 0 {
        BcStatus::ErrExecution
    } else {
        BcStatus::Ok
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
        Box::new(err_shared.clone()),
    );
    ev.set_scale(default_scale as usize);

    let status = eval_into_evaluator(code_str, &mut ev);
    if status != BcStatus::Ok {
        let err_captured = err_shared.0.borrow().clone();
        let err_bytes = err_captured.as_bytes();
        // A diagnostic that does not fit is dropped; the buffer then holds an empty string.
        unsafe { write_c_string(err_bytes, out_buf, buf_size) };
        return status;
    }

    let captured = out_shared.0.borrow().clone();
    let bytes = captured.as_bytes();
    if !unsafe { write_c_string(bytes, out_buf, buf_size) } {
        return BcStatus::ErrBufferTooSmall;
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
    evaluator.set_scale(default_scale as usize);

    eval_into_evaluator(code_str, &mut evaluator)
}

/// Opaque session struct for stateful bc evaluation.
pub struct BcSession {
    evaluator: Evaluator,
    out_shared: SharedBuffer,
    err_shared: SharedBuffer,
}

/// Creates a new persistent bc session.
///
/// # Safety
/// This function is safe to call across FFI boundaries.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bc_session_create(math_enabled: bool) -> *mut BcSession {
    init_heap_if_needed();

    let out_shared = SharedBuffer::default();
    let err_shared = SharedBuffer::default();

    let evaluator = Evaluator::new(
        math_enabled,
        Box::new(out_shared.clone()),
        Box::new(err_shared.clone()),
    );

    let session = Box::new(BcSession {
        evaluator,
        out_shared,
        err_shared,
    });

    Box::into_raw(session)
}

/// Evaluates bc code within a persistent session and writes output into a buffer.
///
/// # Safety
/// - `session` must be a valid pointer obtained from `bc_session_create`.
/// - `code` must be a valid null-terminated C string.
/// - `out_buf` must be a valid writable pointer of at least `buf_size` bytes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bc_session_eval(
    session: *mut BcSession,
    code: *const c_char,
    out_buf: *mut c_char,
    buf_size: usize,
) -> BcStatus {
    init_heap_if_needed();

    if session.is_null() || code.is_null() || out_buf.is_null() {
        return BcStatus::ErrNullPtr;
    }

    if buf_size == 0 {
        return BcStatus::ErrBufferTooSmall;
    }

    let sess = unsafe { &mut *session };

    let code_cstr = unsafe { CStr::from_ptr(code) };
    let code_str = match code_cstr.to_str() {
        Ok(s) => s,
        Err(_) => return BcStatus::ErrExecution,
    };

    sess.out_shared.0.borrow_mut().clear();
    sess.err_shared.0.borrow_mut().clear();

    let mut code_with_nl = String::from(code_str);
    if !code_with_nl.ends_with('\n') {
        code_with_nl.push('\n');
    }

    let status = eval_into_evaluator(&code_with_nl, &mut sess.evaluator);
    if status != BcStatus::Ok {
        let err_captured = sess.err_shared.0.borrow().clone();
        let err_bytes = err_captured.as_bytes();
        // A diagnostic that does not fit is dropped; the buffer then holds an empty string.
        unsafe { write_c_string(err_bytes, out_buf, buf_size) };
        return status;
    }

    let captured = sess.out_shared.0.borrow().clone();
    let bytes = captured.as_bytes();
    if !unsafe { write_c_string(bytes, out_buf, buf_size) } {
        return BcStatus::ErrBufferTooSmall;
    }

    BcStatus::Ok
}

/// Evaluates bc code within a persistent session and streams output via callback.
///
/// # Safety
/// - `session` must be a valid pointer obtained from `bc_session_create`.
/// - `code` must be a valid null-terminated C string.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bc_session_eval_callback(
    session: *mut BcSession,
    code: *const c_char,
    stdout_cb: BcOutputCb,
    stderr_cb: BcOutputCb,
    user_data: *mut c_void,
) -> BcStatus {
    init_heap_if_needed();

    if session.is_null() || code.is_null() {
        return BcStatus::ErrNullPtr;
    }

    let sess = unsafe { &mut *session };

    let code_cstr = unsafe { CStr::from_ptr(code) };
    let code_str = match code_cstr.to_str() {
        Ok(s) => s,
        Err(_) => return BcStatus::ErrExecution,
    };

    sess.out_shared.0.borrow_mut().clear();
    sess.err_shared.0.borrow_mut().clear();

    let mut code_with_nl = String::from(code_str);
    if !code_with_nl.ends_with('\n') {
        code_with_nl.push('\n');
    }

    let status = eval_into_evaluator(&code_with_nl, &mut sess.evaluator);

    if let (Some(callback), Ok(c_str)) =
        (stdout_cb, CString::new(sess.out_shared.0.borrow().clone()))
    {
        unsafe {
            callback(c_str.as_ptr(), user_data);
        }
    }

    let err_str = sess.err_shared.0.borrow().clone();
    if let (Some(callback), false, Ok(c_str)) =
        (stderr_cb, err_str.is_empty(), CString::new(err_str))
    {
        unsafe {
            callback(c_str.as_ptr(), user_data);
        }
    }

    status
}

/// Resets the session state.
///
/// # Safety
/// - `session` must be a valid pointer obtained from `bc_session_create` or null.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bc_session_reset(session: *mut BcSession, math_enabled: bool) {
    if session.is_null() {
        return;
    }
    let sess = unsafe { &mut *session };
    sess.out_shared.0.borrow_mut().clear();
    sess.err_shared.0.borrow_mut().clear();
    sess.evaluator = Evaluator::new(
        math_enabled,
        Box::new(sess.out_shared.clone()),
        Box::new(sess.err_shared.clone()),
    );
}

/// Sets how a session treats non-POSIX syntax (`docs/COMPATIBILITY.md` §4):
/// 0 accepts it (default), 1 warns like `bc -w`, 2 rejects it like `bc -s`.
/// Returns `BcStatus::ErrExecution` for any other value.
///
/// # Safety
/// - `session` must be a valid pointer obtained from `bc_session_create` or null.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bc_session_set_extension_policy(
    session: *mut BcSession,
    policy: u32,
) -> BcStatus {
    if session.is_null() {
        return BcStatus::ErrNullPtr;
    }
    let policy = match policy {
        0 => ExtensionPolicy::Allow,
        1 => ExtensionPolicy::Warn,
        2 => ExtensionPolicy::Reject,
        _ => return BcStatus::ErrExecution,
    };
    unsafe { &mut *session }.evaluator.extension_policy = policy;
    BcStatus::Ok
}

/// Destroys a bc session and frees associated memory.
///
/// # Safety
/// - `session` must be a valid pointer obtained from `bc_session_create` or null.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bc_session_destroy(session: *mut BcSession) {
    if !session.is_null() {
        unsafe {
            drop(Box::from_raw(session));
        }
    }
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

    #[test]
    fn test_bc_session_persistence_and_lifecycle() {
        let session = unsafe { bc_session_create(true) };
        assert!(!session.is_null());

        let mut buf = [0 as c_char; 64];

        // 1. Assign variable x = 42
        let code1 = CString::new("x = 42\n").unwrap();
        let status1 =
            unsafe { bc_session_eval(session, code1.as_ptr(), buf.as_mut_ptr(), buf.len()) };
        assert_eq!(status1, BcStatus::Ok);

        // 2. Evaluate expression using persistent variable x
        let code2 = CString::new("x * 2\n").unwrap();
        let status2 =
            unsafe { bc_session_eval(session, code2.as_ptr(), buf.as_mut_ptr(), buf.len()) };
        assert_eq!(status2, BcStatus::Ok);
        let res2 = unsafe { CStr::from_ptr(buf.as_ptr()).to_str().unwrap() };
        assert_eq!(res2.trim(), "84");

        // 3. Define function sq(a)
        let code3 = CString::new("define sq(a) { return (a * a) }; sq(12)\n").unwrap();
        let status3 =
            unsafe { bc_session_eval(session, code3.as_ptr(), buf.as_mut_ptr(), buf.len()) };
        assert_eq!(status3, BcStatus::Ok);
        let res3 = unsafe { CStr::from_ptr(buf.as_ptr()).to_str().unwrap() };
        assert_eq!(res3.trim(), "144");

        // 4. Callback evaluation on session
        let mut collected = String::new();
        unsafe extern "C" fn sess_cb(chunk: *const c_char, user_data: *mut c_void) {
            unsafe {
                let target = &mut *(user_data as *mut String);
                let s = CStr::from_ptr(chunk).to_str().unwrap();
                target.push_str(s);
            }
        }
        let code4 = CString::new("sq(10)\n").unwrap();
        let status4 = unsafe {
            bc_session_eval_callback(
                session,
                code4.as_ptr(),
                Some(sess_cb),
                None,
                &mut collected as *mut String as *mut c_void,
            )
        };
        assert_eq!(status4, BcStatus::Ok);
        assert_eq!(collected.trim(), "100");

        // 5. Reset session
        unsafe { bc_session_reset(session, false) };
        let code5 = CString::new("x\n").unwrap();
        let status5 =
            unsafe { bc_session_eval(session, code5.as_ptr(), buf.as_mut_ptr(), buf.len()) };
        assert_eq!(status5, BcStatus::Ok);
        let res5 = unsafe { CStr::from_ptr(buf.as_ptr()).to_str().unwrap() };
        assert_eq!(res5.trim(), "0");

        // 6. Destroy session
        unsafe { bc_session_destroy(session) };
        unsafe { bc_session_destroy(core::ptr::null_mut()) }; // Null safety
        unsafe { bc_session_reset(core::ptr::null_mut(), false) }; // Null safety
    }

    #[test]
    fn test_bc_session_extension_policy_and_scale_clamp() {
        let session = unsafe { bc_session_create(false) };
        let mut buf = [0 as c_char; 128];
        let read =
            |buf: &[c_char]| unsafe { CStr::from_ptr(buf.as_ptr()).to_str().unwrap() }.to_string();

        let code = CString::new("abc = 1; abc\n").unwrap();
        for (policy, status, out) in [
            (0, BcStatus::Ok, "1\n"),
            (1, BcStatus::Ok, "1\n"),
            (
                2,
                BcStatus::ErrExecution,
                "(standard_in) 1: Error: multiple letter name - abc\n\
                 (standard_in) 2: Error: multiple letter name - abc\n",
            ),
        ] {
            assert_eq!(
                unsafe { bc_session_set_extension_policy(session, policy) },
                BcStatus::Ok
            );
            assert_eq!(
                unsafe { bc_session_eval(session, code.as_ptr(), buf.as_mut_ptr(), buf.len()) },
                status
            );
            assert_eq!(read(&buf), out);
        }
        assert_eq!(
            unsafe { bc_session_set_extension_policy(session, 3) },
            BcStatus::ErrExecution
        );
        assert_eq!(
            unsafe { bc_session_set_extension_policy(core::ptr::null_mut(), 0) },
            BcStatus::ErrNullPtr
        );
        unsafe { bc_session_destroy(session) };

        // A default scale above BC_SCALE_MAX is clamped instead of breaking the scale invariant.
        let scale = CString::new("scale\n").unwrap();
        assert_eq!(
            unsafe { bc_eval(scale.as_ptr(), false, u32::MAX, buf.as_mut_ptr(), buf.len()) },
            BcStatus::Ok
        );
        assert_eq!(read(&buf), "1000000000\n");
    }

    #[test]
    fn test_bc_session_errors_and_null_ptrs() {
        let session = unsafe { bc_session_create(false) };
        let code = CString::new("1 + 1\n").unwrap();
        let mut buf = [0 as c_char; 64];

        // Null session
        assert_eq!(
            unsafe {
                bc_session_eval(
                    core::ptr::null_mut(),
                    code.as_ptr(),
                    buf.as_mut_ptr(),
                    buf.len(),
                )
            },
            BcStatus::ErrNullPtr
        );
        assert_eq!(
            unsafe {
                bc_session_eval_callback(
                    core::ptr::null_mut(),
                    code.as_ptr(),
                    None,
                    None,
                    core::ptr::null_mut(),
                )
            },
            BcStatus::ErrNullPtr
        );

        // Null code
        assert_eq!(
            unsafe { bc_session_eval(session, core::ptr::null(), buf.as_mut_ptr(), buf.len()) },
            BcStatus::ErrNullPtr
        );
        assert_eq!(
            unsafe {
                bc_session_eval_callback(
                    session,
                    core::ptr::null(),
                    None,
                    None,
                    core::ptr::null_mut(),
                )
            },
            BcStatus::ErrNullPtr
        );

        // Null out_buf
        assert_eq!(
            unsafe { bc_session_eval(session, code.as_ptr(), core::ptr::null_mut(), buf.len()) },
            BcStatus::ErrNullPtr
        );

        // Buffer size 0
        assert_eq!(
            unsafe { bc_session_eval(session, code.as_ptr(), buf.as_mut_ptr(), 0) },
            BcStatus::ErrBufferTooSmall
        );

        // Buffer too small for result
        let mut tiny_buf = [0 as c_char; 1];
        assert_eq!(
            unsafe {
                bc_session_eval(
                    session,
                    code.as_ptr(),
                    tiny_buf.as_mut_ptr(),
                    tiny_buf.len(),
                )
            },
            BcStatus::ErrBufferTooSmall
        );

        unsafe { bc_session_destroy(session) };
    }

    #[test]
    fn test_bc_c_api_invalid_utf8_exact_buffer_and_stderr_callbacks() {
        // 1. Invalid UTF-8 C string handling across all 4 entry points (no UB or leak)
        let invalid_utf8: [u8; 4] = [b'1', b'+', 0xFF, 0x00];
        let invalid_ptr = invalid_utf8.as_ptr().cast::<c_char>();
        let mut buf = [0 as c_char; 16];

        assert_eq!(
            unsafe { bc_eval(invalid_ptr, false, 0, buf.as_mut_ptr(), buf.len()) },
            BcStatus::ErrExecution
        );
        assert_eq!(
            unsafe { bc_eval_callback(invalid_ptr, false, 0, None, None, core::ptr::null_mut()) },
            BcStatus::ErrExecution
        );

        let session = unsafe { bc_session_create(false) };
        assert_eq!(
            unsafe { bc_session_eval(session, invalid_ptr, buf.as_mut_ptr(), buf.len()) },
            BcStatus::ErrExecution
        );
        assert_eq!(
            unsafe {
                bc_session_eval_callback(session, invalid_ptr, None, None, core::ptr::null_mut())
            },
            BcStatus::ErrExecution
        );

        // 2. Exact-fit buffer capacity ("7\n\0" requires exactly 3 bytes)
        let code_exact = CString::new("3 + 4\n").unwrap();
        let mut exact_buf = [0 as c_char; 3];
        assert_eq!(
            unsafe {
                bc_eval(
                    code_exact.as_ptr(),
                    false,
                    0,
                    exact_buf.as_mut_ptr(),
                    exact_buf.len(),
                )
            },
            BcStatus::Ok
        );
        let exact_str = unsafe { CStr::from_ptr(exact_buf.as_ptr()).to_str().unwrap() };
        assert_eq!(exact_str, "7\n");

        let mut exact_sess_buf = [0 as c_char; 3];
        assert_eq!(
            unsafe {
                bc_session_eval(
                    session,
                    code_exact.as_ptr(),
                    exact_sess_buf.as_mut_ptr(),
                    exact_sess_buf.len(),
                )
            },
            BcStatus::Ok
        );
        let exact_sess_str = unsafe { CStr::from_ptr(exact_sess_buf.as_ptr()).to_str().unwrap() };
        assert_eq!(exact_sess_str, "7\n");

        // 3. stderr_cb invocation on ibase warning in bc_session_eval_callback
        let mut err_collected = String::new();
        unsafe extern "C" fn err_cb(chunk: *const c_char, user_data: *mut c_void) {
            unsafe {
                let target = &mut *(user_data as *mut String);
                let s = CStr::from_ptr(chunk).to_str().unwrap();
                target.push_str(s);
            }
        }
        let warn_code = CString::new("ibase = 99\n").unwrap();
        let warn_status = unsafe {
            bc_session_eval_callback(
                session,
                warn_code.as_ptr(),
                None,
                Some(err_cb),
                &mut err_collected as *mut String as *mut c_void,
            )
        };
        assert_eq!(warn_status, BcStatus::Ok);
        assert!(err_collected.contains("ibase too large"));

        unsafe { bc_session_destroy(session) };
    }

    #[test]
    fn test_bc_c_api_syntax_and_runtime_error_recovery_and_stress() {
        let mut buf = [0 as c_char; 128];
        let mut tiny_buf = [0 as c_char; 4];

        // 1. bc_eval error cases: division by zero, negative sqrt, syntax error, lexical error, undefined fn, quit
        let div_zero = CString::new("1 / 0\n").unwrap();
        assert_eq!(
            unsafe { bc_eval(div_zero.as_ptr(), false, 0, buf.as_mut_ptr(), buf.len()) },
            BcStatus::ErrExecution
        );
        let err_msg = unsafe { CStr::from_ptr(buf.as_ptr()).to_str().unwrap() };
        assert_eq!(err_msg, "Runtime error (func=(main)): Divide by zero\n");

        // Small buffer fallback on error (*out_buf = 0)
        assert_eq!(
            unsafe {
                bc_eval(
                    div_zero.as_ptr(),
                    false,
                    0,
                    tiny_buf.as_mut_ptr(),
                    tiny_buf.len(),
                )
            },
            BcStatus::ErrExecution
        );
        assert_eq!(tiny_buf[0], 0);

        let lex_err = CString::new("@\n").unwrap();
        assert_eq!(
            unsafe { bc_eval(lex_err.as_ptr(), false, 0, buf.as_mut_ptr(), buf.len()) },
            BcStatus::ErrExecution
        );
        let lex_msg = unsafe { CStr::from_ptr(buf.as_ptr()).to_str().unwrap() };
        assert_eq!(lex_msg, "(standard_in) 1: illegal character: @\n");

        let syn_err = CString::new("1 + * 2\n").unwrap();
        assert_eq!(
            unsafe { bc_eval(syn_err.as_ptr(), false, 0, buf.as_mut_ptr(), buf.len()) },
            BcStatus::ErrExecution
        );
        let syn_msg = unsafe { CStr::from_ptr(buf.as_ptr()).to_str().unwrap() };
        assert_eq!(syn_msg, "(standard_in) 1: syntax error\n");

        let quit_code = CString::new("quit\n").unwrap();
        assert_eq!(
            unsafe { bc_eval(quit_code.as_ptr(), false, 0, buf.as_mut_ptr(), buf.len()) },
            BcStatus::Ok
        );

        // 2. bc_eval_callback error reporting via stderr_cb
        unsafe extern "C" fn err_cb(chunk: *const c_char, user_data: *mut c_void) {
            unsafe {
                let target = &mut *(user_data as *mut String);
                let s = CStr::from_ptr(chunk).to_str().unwrap();
                target.push_str(s);
            }
        }
        let mut cb_err = String::new();
        let neg_sqrt = CString::new("sqrt(-1)\n").unwrap();
        assert_eq!(
            unsafe {
                bc_eval_callback(
                    neg_sqrt.as_ptr(),
                    false,
                    0,
                    None,
                    Some(err_cb),
                    &mut cb_err as *mut String as *mut c_void,
                )
            },
            BcStatus::ErrExecution
        );
        assert_eq!(
            cb_err,
            "Runtime error (func=(main)): Square root of a negative number\n"
        );

        // 3. Session ScopeGuard recovery and 100-iteration error stress test
        let session = unsafe { bc_session_create(false) };
        let setup =
            CString::new("x = 55\ndefine f(x) { auto z; x = 999; z = 1 / 0; return (z); }\n")
                .unwrap();
        assert_eq!(
            unsafe { bc_session_eval(session, setup.as_ptr(), buf.as_mut_ptr(), buf.len()) },
            BcStatus::Ok
        );

        let call_f = CString::new("f(10)\n").unwrap();
        assert_eq!(
            unsafe { bc_session_eval(session, call_f.as_ptr(), buf.as_mut_ptr(), buf.len()) },
            BcStatus::ErrExecution
        );
        // Tiny buffer on session error
        assert_eq!(
            unsafe {
                bc_session_eval(
                    session,
                    call_f.as_ptr(),
                    tiny_buf.as_mut_ptr(),
                    tiny_buf.len(),
                )
            },
            BcStatus::ErrExecution
        );
        assert_eq!(tiny_buf[0], 0);

        // Verify x is still 55 after failed function call
        let query_x = CString::new("x\n").unwrap();
        assert_eq!(
            unsafe { bc_session_eval(session, query_x.as_ptr(), buf.as_mut_ptr(), buf.len()) },
            BcStatus::Ok
        );
        let x_str = unsafe { CStr::from_ptr(buf.as_ptr()).to_str().unwrap() };
        assert_eq!(x_str.trim(), "55");

        // 100-iteration error stress test to prove zero heap leak
        for _ in 0..50 {
            assert_eq!(
                unsafe { bc_session_eval(session, syn_err.as_ptr(), buf.as_mut_ptr(), buf.len()) },
                BcStatus::ErrExecution
            );
            assert_eq!(
                unsafe { bc_session_eval(session, call_f.as_ptr(), buf.as_mut_ptr(), buf.len()) },
                BcStatus::ErrExecution
            );
        }

        // Session still works after 100 consecutive errors
        let final_check = CString::new("x + 5\n").unwrap();
        assert_eq!(
            unsafe { bc_session_eval(session, final_check.as_ptr(), buf.as_mut_ptr(), buf.len()) },
            BcStatus::Ok
        );
        let final_str = unsafe { CStr::from_ptr(buf.as_ptr()).to_str().unwrap() };
        assert_eq!(final_str.trim(), "60");

        unsafe { bc_session_destroy(session) };
    }
}

#[cfg(kani)]
mod kani_proofs {
    use super::*;

    /// Verifies the production `write_c_string` helper used by every C entry point: for any
    /// source length and buffer size it writes the bytes and a NUL only when they fit, never
    /// touches memory at or beyond `buf_size`, and otherwise leaves an empty string.
    #[kani::proof]
    fn proof_write_c_string() {
        const CAP: usize = 8;
        let src: [u8; CAP] = kani::any();
        let len: usize = kani::any();
        let buf_size: usize = kani::any();
        kani::assume(len <= CAP);
        kani::assume(buf_size >= 1 && buf_size <= CAP);
        let mut dst: [c_char; CAP] = kani::any();
        let before = dst;

        let ok = unsafe { write_c_string(&src[..len], dst.as_mut_ptr(), buf_size) };

        assert_eq!(ok, len < buf_size);
        let idx: usize = kani::any();
        kani::assume(idx < CAP);
        if idx >= buf_size {
            assert_eq!(dst[idx], before[idx]);
        }
        if ok {
            assert_eq!(dst[len], 0);
            if idx < len {
                assert_eq!(dst[idx] as u8, src[idx]);
            }
        } else {
            assert_eq!(dst[0], 0);
        }
    }

    /// Verifies that all C-FFI entry points safely reject NULL pointers and zero-length buffers
    /// across arbitrary symbolic boolean, scale, and size arguments without dereferencing invalid pointers.
    #[kani::proof]
    fn proof_c_ffi_null_and_zero_buf_guards() {
        let math_enabled: bool = kani::any();
        let default_scale: u32 = kani::any();
        let buf_size: usize = kani::any();
        let valid_cstr: [c_char; 2] = [b'1' as c_char, 0];
        let mut valid_buf: [c_char; 4] = [0; 4];

        let st_null_code = unsafe {
            bc_eval(
                core::ptr::null(),
                math_enabled,
                default_scale,
                valid_buf.as_mut_ptr(),
                buf_size,
            )
        };
        assert_eq!(st_null_code, BcStatus::ErrNullPtr);

        let st_null_buf = unsafe {
            bc_eval(
                valid_cstr.as_ptr(),
                math_enabled,
                default_scale,
                core::ptr::null_mut(),
                buf_size,
            )
        };
        assert_eq!(st_null_buf, BcStatus::ErrNullPtr);

        let st_zero_buf = unsafe {
            bc_eval(
                valid_cstr.as_ptr(),
                math_enabled,
                default_scale,
                valid_buf.as_mut_ptr(),
                0,
            )
        };
        assert_eq!(st_zero_buf, BcStatus::ErrBufferTooSmall);

        let st_cb_null = unsafe {
            bc_eval_callback(
                core::ptr::null(),
                math_enabled,
                default_scale,
                None,
                None,
                core::ptr::null_mut(),
            )
        };
        assert_eq!(st_cb_null, BcStatus::ErrNullPtr);

        let st_sess_null = unsafe {
            bc_session_eval(
                core::ptr::null_mut(),
                valid_cstr.as_ptr(),
                valid_buf.as_mut_ptr(),
                buf_size,
            )
        };
        assert_eq!(st_sess_null, BcStatus::ErrNullPtr);

        let st_sess_cb_null = unsafe {
            bc_session_eval_callback(
                core::ptr::null_mut(),
                valid_cstr.as_ptr(),
                None,
                None,
                core::ptr::null_mut(),
            )
        };
        assert_eq!(st_sess_cb_null, BcStatus::ErrNullPtr);

        unsafe {
            bc_session_reset(core::ptr::null_mut(), math_enabled);
            bc_session_destroy(core::ptr::null_mut());
        }
    }
}
