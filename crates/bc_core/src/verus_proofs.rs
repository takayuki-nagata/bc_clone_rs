// SPDX-License-Identifier: MIT

//! Verus *design models* for `bc_core` and its front ends.
//!
//! Verified by `scripts/run_verus_verification.sh` and compiled only under
//! `cfg(verus_keep_ghost)`.
//!
//! **What is proved here and what is not.** The executable `verified_*` functions in this file
//! are **design models**: production code does not call them. Their proofs show that an
//! *algorithm* is sound (bounds, termination, the invariants listed in each function's
//! documentation), not that the production code implements it. Production code is covered by:
//! - the kernels in `verified_kernels.rs`, which production code calls directly and which are
//!   verified with their real bodies;
//! - the production `BCNum` operations (`math.rs`), output formatting (`format.rs`), the lexer
//!   and parser (`parser/`), the evaluator and unit driver (`eval/`, `driver.rs`), verified in place against the
//!   executable specification `crates/bc_spec` (relations in `refine.rs`), and the math library
//!   (`mathlib/`), verified in place over the reals;
//! - Kani harnesses on production helpers (e.g. `bc_c_api::write_c_string`);
//! - tests that check production behavior against exact references (`tests/proptest_suite.rs`,
//!   the GNU differential and oracle tests in `bc_cli`).
//!
//! Model → production correspondence (production line numbers are not tracked):
//! `verified_c_ffi_copy_nul_terminated` →
//! `bc_c_api::write_c_string`; `verified_zephyr_repl_edit_step` → `bc_zephyr::run_repl_with`;
//! `verified_cli_parse_args` → `bc_cli::run_app`. The models of algorithms that production
//! code now proves in place (scale rules, `^`, output in other bases, line wrapping, call-frame
//! restoration, `++`/`--`, control flow) were removed.

use crate::verified_kernels::*;
use vstd::prelude::*;

verus! {

// ============================================================================
// C-FFI NUL-terminated output and the Zephyr line editor
// ============================================================================

/// Status constants matching `crates/bc_c_api/src/lib.rs` (`BcStatus`).
pub const BC_STATUS_OK: u8 = 0;
pub const BC_STATUS_ERR_BUFFER_TOO_SMALL: u8 = 2;

/// Verified C-FFI output buffer bounds check and NUL-terminated copy
/// (`crates/bc_c_api/src/lib.rs:149-190, 293-336`).
///
/// Proves:
/// 1. If `buf_size == 0` or `src.len() >= buf_size` (`src.len() + 1 > buf_size`),
///    returns `BC_STATUS_ERR_BUFFER_TOO_SMALL` without overflowing the buffer.
/// 2. On `BC_STATUS_OK`, `out_buf` has exact length `src.len() + 1 <= buf_size`,
///    its prefix matches `src@` byte-for-byte, and its final byte is guaranteed to be `0u8` (NUL).
pub fn verified_c_ffi_copy_nul_terminated(
    src: &[u8],
    out_buf: &mut alloc::vec::Vec<u8>,
    buf_size: usize,
) -> (status: u8)
    ensures
        (buf_size == 0 || src@.len() >= buf_size) ==> (
            status == BC_STATUS_ERR_BUFFER_TOO_SMALL
            && final(out_buf)@ == old(out_buf)@
        ),
        (buf_size > 0 && src@.len() < buf_size) ==> (
            status == BC_STATUS_OK
            && final(out_buf)@.len() == src@.len() + 1
            && final(out_buf)@.len() <= buf_size
            && final(out_buf)@.subrange(0, src@.len() as int) =~= src@
            && final(out_buf)@[src@.len() as int] == 0u8
        ),
{
    if !verified_c_ffi_check_buf_capacity(src.len(), buf_size) {
        return BC_STATUS_ERR_BUFFER_TOO_SMALL;
    }

    out_buf.clear();
    let len: usize = src.len();
    let mut i: usize = 0;

    while i < len
        invariant
            0 <= i <= len,
            len == src@.len(),
            len < buf_size,
            out_buf@.len() == i,
            out_buf@ =~= src@.subrange(0, i as int),
        decreases len - i,
    {
        out_buf.push(src[i]);
        i = i + 1;
    }

    out_buf.push(0u8);
    proof {
        assert(out_buf@.subrange(0, len as int) =~= src@);
    }

    BC_STATUS_OK
}

/// Action codes for the Zephyr RTOS interactive serial REPL line editor (`crates/bc_zephyr/src/lib.rs:327-358`).
pub const REPL_ACTION_NONE: u8 = 0;
pub const REPL_ACTION_EVAL_LINE: u8 = 1;
pub const REPL_ACTION_BACKSPACE: u8 = 2;
pub const REPL_ACTION_CTRL_C: u8 = 3;
pub const REPL_ACTION_APPEND_CHAR: u8 = 4;

/// Verified Zephyr RTOS interactive serial REPL line editor transition
/// (`crates/bc_zephyr/src/lib.rs:327-358`).
///
/// Proves:
/// 1. Backspace (`0x08` or `0x7F`) on an empty buffer is a safe no-op (no underflow),
///    and on a non-empty buffer removes exactly the last character.
/// 2. Ctrl+C (`0x03`) immediately clears the line buffer (`len == 0`).
/// 3. Printable ASCII (`0x20..=0x7E`) appends the character to `line_buf`.
pub fn verified_zephyr_repl_edit_step(
    line_buf: &mut alloc::vec::Vec<u8>,
    b: u8,
) -> (action: u8)
    requires
        old(line_buf)@.len() <= 1_000_000,
    ensures
        (b == b'\r' || b == b'\n') ==> (
            action == REPL_ACTION_EVAL_LINE
            && final(line_buf)@.len() == 0
        ),
        (b == 0x08 || b == 0x7F) ==> (
            action == REPL_ACTION_BACKSPACE
            && (old(line_buf)@.len() == 0 ==> final(line_buf)@.len() == 0)
            && (old(line_buf)@.len() > 0 ==> (
                final(line_buf)@.len() == old(line_buf)@.len() - 1
                && final(line_buf)@ =~= old(line_buf)@.subrange(0, (old(line_buf)@.len() - 1) as int)
            ))
        ),
        b == 0x03 ==> (
            action == REPL_ACTION_CTRL_C
            && final(line_buf)@.len() == 0
        ),
        (0x20 <= b && b <= 0x7E) ==> (
            action == REPL_ACTION_APPEND_CHAR
            && final(line_buf)@.len() == old(line_buf)@.len() + 1
            && final(line_buf)@[old(line_buf)@.len() as int] == b
        ),
{
    let kind = verified_zephyr_classify_char(b);
    if kind == 1 {
        line_buf.clear();
        REPL_ACTION_EVAL_LINE
    } else if kind == 2 {
        if line_buf.len() > 0 {
            let _ = line_buf.pop();
        }
        REPL_ACTION_BACKSPACE
    } else if kind == 3 {
        line_buf.clear();
        REPL_ACTION_CTRL_C
    } else if kind == 4 {
        line_buf.push(b);
        REPL_ACTION_APPEND_CHAR
    } else {
        REPL_ACTION_NONE
    }
}

// ============================================================================
// CLI option parsing
// ============================================================================

/// Verified POSIX CLI option and file argument parser (`crates/bc_cli/src/main.rs:run_app`).
///
/// `args` is the argument list after classification: one `CLI_ARG_OPT_L` / `_S` / `_W` /
/// `_INVALID` entry per option letter of a `CLI_ARG_OPT_CLUSTER` (as classified by
/// `verified_cli_classify_option_char`), `CLI_ARG_OPT_INVALID` for a long option,
/// `CLI_ARG_END_OF_OPTIONS` for `--`, and `CLI_ARG_FILE` for an operand.
///
/// Returns `(has_error, math_enabled, initial_scale, file_count)`.
/// Proves:
/// 1. Any invalid `-...` option immediately aborts parsing with `has_error == true`.
/// 2. When valid, `initial_scale == 20` if and only if `-l` (`math_enabled`) was specified,
///    and `initial_scale == 0` otherwise.
/// 3. The number of collected file arguments is bounded by `args.len()`.
pub fn verified_cli_parse_args(args: &[u8]) -> (res: (bool, bool, usize, usize))
    ensures
        // res = (has_error, math_enabled, initial_scale, file_count)
        !res.0 ==> (
            (res.1 ==> res.2 == 20)
            && (!res.1 ==> res.2 == 0)
            && res.3 <= args@.len()
        ),
{
    let mut math_enabled: bool = false;
    let mut file_count: usize = 0;
    let mut i: usize = 0;
    let len: usize = args.len();

    while i < len
        invariant
            0 <= i <= len,
            len == args@.len(),
            file_count <= i,
        decreases len - i,
    {
        let arg = args[i];
        if arg == CLI_ARG_OPT_L {
            math_enabled = true;
        } else if arg == CLI_ARG_OPT_S || arg == CLI_ARG_OPT_W {
            // Extension policy flags do not affect the initial scale or the file count.
        } else if arg == CLI_ARG_OPT_INVALID {
            return (true, math_enabled, 0, file_count);
        } else if arg == CLI_ARG_END_OF_OPTIONS {
            // `--` is neither an option nor an operand.
        } else {
            file_count = file_count + 1;
        }
        i = i + 1;
    }

    let initial_scale: usize = verified_cli_initial_scale(math_enabled);
    (false, math_enabled, initial_scale, file_count)
}

} // verus!
