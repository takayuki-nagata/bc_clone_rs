// SPDX-License-Identifier: MIT

//! The version and commit of the `bc_clone` build, which every front end displays: the
//! `-v`/`--version` option of `bc_clone`, `bc_version()` of the C API, `version()` of the Wasm
//! module, and the banners of the embedded targets.
//!
//! The commit is recorded by `build.rs`: the first 7 hexadecimal digits of `HEAD`, followed by
//! `-dirty` if a tracked file differs from it, or the value of `BC_CLONE_GIT_COMMIT` at build
//! time, or `unknown` when neither is available. It is not part of `bc_core`, so that a new
//! commit does not rebuild the engine.

#![no_std]

/// The version of the workspace (`Cargo.toml`), such as `0.5.0`.
pub const VERSION: &str = env!("CARGO_PKG_VERSION");

/// The commit the build was made from, such as `a916de2` or `a916de2-dirty`, or `unknown`.
pub const COMMIT: &str = env!("BC_CLONE_COMMIT");

/// The line that the front ends display, such as `bc_clone 0.5.0 (a916de2)`.
pub const VERSION_LINE: &str = concat!(
    "bc_clone ",
    env!("CARGO_PKG_VERSION"),
    " (",
    env!("BC_CLONE_COMMIT"),
    ")"
);

/// [`VERSION_LINE`] followed by a NUL byte, for the C API.
pub const VERSION_LINE_NUL: &str = concat!(
    "bc_clone ",
    env!("CARGO_PKG_VERSION"),
    " (",
    env!("BC_CLONE_COMMIT"),
    ")\0"
);

#[cfg(test)]
mod tests {
    use super::*;

    /// Whether `commit` has one of the forms that `build.rs` produces without an override.
    fn is_commit(commit: &str) -> bool {
        let hash = commit.strip_suffix("-dirty").unwrap_or(commit);
        commit == "unknown"
            || (hash.len() == 7
                && hash
                    .bytes()
                    .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b)))
    }

    #[test]
    fn the_version_line_names_the_version_and_the_commit() {
        let rest = VERSION_LINE.strip_prefix("bc_clone ").unwrap_or("");
        let (version, commit) = rest.split_once(" (").unwrap_or(("", ""));
        assert_eq!(version, VERSION);
        assert_eq!(commit.strip_suffix(')'), Some(COMMIT));
        assert_eq!(VERSION_LINE_NUL.strip_suffix('\0'), Some(VERSION_LINE));
        assert!(!VERSION_LINE.contains('\0'));
    }

    #[test]
    fn the_version_and_the_commit_have_their_forms() {
        let parts: [&str; 3] = {
            let mut it = VERSION.split('.');
            [
                it.next().unwrap_or(""),
                it.next().unwrap_or(""),
                it.next().unwrap_or(""),
            ]
        };
        for part in parts {
            assert!(!part.is_empty() && part.bytes().all(|b| b.is_ascii_digit()));
        }
        // `BC_CLONE_GIT_COMMIT` may set any value; the forms are those of `build.rs` otherwise.
        if option_env!("BC_CLONE_GIT_COMMIT").is_none() {
            assert!(is_commit(COMMIT), "{COMMIT}");
        }
        assert!(is_commit("a916de2"));
        assert!(is_commit("a916de2-dirty"));
        assert!(!is_commit("A916DE2"));
        assert!(!is_commit("a916de"));
    }
}
