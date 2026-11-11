// SPDX-License-Identifier: MIT

//! Verus *design model* of a `bc_core` front end.
//!
//! Verified by `scripts/run_verus_verification.sh` and compiled only under
//! `cfg(verus_keep_ghost)`.
//!
//! **What is proved here and what is not.** The executable `verified_cli_parse_args` in this
//! file is a **design model**: production code does not call it. Its proof shows that an
//! *algorithm* is sound (the invariants listed in its documentation), not that the production
//! code implements it. Production code is covered by:
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
//! `verified_cli_parse_args` → `bc_cli::run_app`. The model of the C-FFI copy was replaced by
//! the Kani harness `proof_write_c_string` on the production helper, and the model of the
//! serial line editor by the kernel `verified_zephyr_repl_action`, which production calls. The
//! models of algorithms that production code now proves in place (scale rules, `^`, output in other bases, line wrapping, call-frame
//! restoration, `++`/`--`, control flow) were removed.

use crate::verified_kernels::*;
use vstd::prelude::*;

verus! {

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
