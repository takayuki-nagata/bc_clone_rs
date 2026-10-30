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
//! - the production `BCNum` operations (`math.rs`), output formatting (`format.rs`), the
//!   evaluator and unit driver (`eval.rs`, `driver.rs`), verified in place against the
//!   executable specification `crates/bc_spec` (relations in `refine.rs`), and the math library
//!   (`mathlib/`), verified in place over the reals;
//! - Kani harnesses on production helpers (e.g. `bc_c_api::write_c_string`);
//! - tests that check production behavior against exact references (`tests/proptest_suite.rs`,
//!   the GNU differential and oracle tests in `bc_cli`).
//!
//! Model → production correspondence (production line numbers are not tracked):
//! `verified_lexer_*` → `parser::Lexer`; `verified_c_ffi_copy_nul_terminated` →
//! `bc_c_api::write_c_string`; `verified_zephyr_repl_edit_step` → `bc_zephyr::run_repl_with`;
//! `verified_cli_parse_args` → `bc_cli::run_app`. The models of algorithms that production
//! code now proves in place (scale rules, `^`, output in other bases, line wrapping, call-frame
//! restoration, `++`/`--`, control flow) were removed.

use crate::verified_kernels::*;
use vstd::prelude::*;

verus! {

// ============================================================================
// Lexer: lookahead, cursor advance and number scanning
// ============================================================================

/// Verified bounds-safe lookahead `Lexer::peek_char` (`crates/bc_core/src/parser.rs`).
///
/// Proves absence of out-of-bounds slice indexing and arithmetic overflow when peeking ahead,
/// delegating index validation to `verified_lexer_peek_char_index` in `verified_kernels.rs`.
pub fn verified_lexer_peek_byte(text: &[u8], pos: usize, offset: usize) -> (res: u8)
    requires
        pos <= text@.len(),
        text@.len() <= MAX_VERIFIED_SCALE,
        offset <= MAX_VERIFIED_SCALE,
    ensures
        pos + offset >= text@.len() ==> res == 0u8,
        pos + offset < text@.len() ==> res == text@[pos + offset],
{
    let (in_bounds, idx) = verified_lexer_peek_char_index(text.len(), pos, offset);
    if in_bounds {
        text[idx]
    } else {
        0u8
    }
}

/// Verified cursor and line advancement `Lexer::advance_char` (`crates/bc_core/src/parser.rs`).
///
/// Proves that:
/// 1. Slice indexing `text[pos]` never panics (out-of-bounds is impossible).
/// 2. `pos` advances monotonically to `min(initial_pos + steps, text.len())`.
/// 3. `line` increases monotonically and never overflows `usize`.
pub fn verified_lexer_advance_bytes(
    text: &[u8],
    initial_pos: usize,
    initial_line: usize,
    steps: usize,
) -> (res: (usize, usize))
    requires
        initial_pos <= text@.len(),
        text@.len() <= 500_000_000,
        initial_line >= 1,
        initial_line <= 500_000_000,
    ensures
        res.0 <= text@.len(),
        res.0 >= initial_pos,
        res.0 == if initial_pos + steps <= text@.len() {
            (initial_pos + steps) as usize
        } else {
            text@.len() as usize
        },
        res.1 >= initial_line,
        res.1 <= initial_line + (res.0 - initial_pos),
{
    let mut pos: usize = initial_pos;
    let mut line: usize = initial_line;
    let mut s: usize = 0;
    let len: usize = text.len();

    while s < steps
        invariant
            0 <= s <= steps,
            len == text@.len(),
            len <= 500_000_000,
            initial_pos <= pos <= len,
            initial_line <= 500_000_000,
            pos == if initial_pos + s <= len {
                (initial_pos + s) as usize
            } else {
                len
            },
            line >= initial_line,
            line <= initial_line + (pos - initial_pos),
        decreases steps - s,
    {
        if pos < len {
            let (next_pos, next_line) = verified_lexer_advance_step(pos, line, text[pos] == b'\n');
            pos = next_pos;
            line = next_line;
        }
        s = s + 1;
    }

    (pos, line)
}

/// Helper predicate for valid bc numeric literal characters (`0..=9` or `A..=F`).
pub open spec fn spec_is_bc_digit(b: u8) -> bool {
    (b'0' <= b && b <= b'9') || (b'A' <= b && b <= b'F')
}

/// Verified `Lexer` number token scanning loop (`crates/bc_core/src/parser.rs:443-468`).
///
/// Scans digits (`0-9`, `A-F`), at most one decimal point (`.`), and backslash-newline
/// continuations (`\\\n` and `\\\r\n`).
/// Proves:
/// 1. Loop termination (`decreases len - pos`) and 100% bounds-safe slice indexing.
/// 2. At most one radix point `.` is ever accepted into a single number token (`res.2 <= 1`).
/// 3. Monotonic cursor advancement (`initial_pos <= res.0 <= text.len()`).
pub fn verified_lexer_scan_number(
    text: &[u8],
    initial_pos: usize,
) -> (res: (usize, usize, usize))
    requires
        initial_pos <= text@.len(),
    ensures
        // res = (final_pos, emitted_char_count, dot_count)
        initial_pos <= res.0 && res.0 <= text@.len(),
        res.1 <= res.0 - initial_pos,
        res.2 <= 1,
{
    let mut pos: usize = initial_pos;
    let mut char_count: usize = 0;
    let mut dot_count: usize = 0;
    let mut has_dot: bool = false;
    let len: usize = text.len();

    while pos < len
        invariant
            initial_pos <= pos <= len,
            len == text@.len(),
            char_count <= pos - initial_pos,
            dot_count <= 1,
            has_dot <==> (dot_count == 1),
        decreases len - pos,
    {
        let cc = text[pos];
        if verified_is_bc_digit(cc as u32) {
            char_count = char_count + 1;
            pos = pos + 1;
        } else if cc == b'.' && !has_dot {
            has_dot = true;
            dot_count = dot_count + 1;
            char_count = char_count + 1;
            pos = pos + 1;
        } else if cc == b'\\' && len - pos >= 2 && text[pos + 1] == b'\n' {
            pos = pos + 2;
        } else if cc == b'\\' && len - pos >= 3 && text[pos + 1] == b'\r' && text[pos + 2] == b'\n' {
            pos = pos + 3;
        } else {
            break;
        }
    }

    (pos, char_count, dot_count)
}

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
