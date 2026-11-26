// SPDX-License-Identifier: MIT

//! The decisions of `build.rs`, which records the commit of the source tree in
//! `BC_CLONE_COMMIT`. `build.rs` includes this file with `#[path]` and passes the real
//! environment and git; the unit tests of the library include it under `cfg(test)` and pass a
//! fake one, so these decisions run under Miri.
//!
//! The value is, in order of preference:
//! 1. the environment variable `BC_CLONE_GIT_COMMIT`, if it is set (for builds without git);
//! 2. the first 7 hexadecimal digits of `HEAD`, followed by `-dirty` if a tracked file differs
//!    from `HEAD`, when this crate lies in the work tree of a git repository whose top level is
//!    the workspace root (so a copy of the sources inside another repository, such as the
//!    trees that cargo-mutants copies into `target/`, does not report that repository's commit);
//! 3. `unknown`.
//!
//! The script never fails the build: any error gives `unknown`. The `-dirty` mark is best
//! effort: cargo reruns the script when `HEAD`, the branch it points to or the index changes,
//! so an edit that has not been staged (or otherwise touched the index) is not noticed.

// The library is `no_std` and includes this file only for its tests, through `extern crate
// std`; the build script has these names in its prelude already.
use std::{format, string::String, vec, vec::Vec};

use std::path::{Path, PathBuf};

/// The environment variable that sets the commit.
pub const OVERRIDE: &str = "BC_CLONE_GIT_COMMIT";
const COMMIT_DIGITS: usize = 7;

/// What the build script needs from the system.
pub trait Host {
    /// Runs git in `dir` with `args` and returns [`git_output`] of the result.
    fn git(&self, dir: &Path, args: &[&str]) -> Option<String>;
    /// The canonical form of `path`, if it exists.
    fn canonicalize(&self, path: &Path) -> Option<PathBuf>;
    /// Whether `path` exists.
    fn exists(&self, path: &Path) -> bool;
}

/// The directives the build script prints to cargo, one per line: what to watch, then
/// `BC_CLONE_COMMIT`. `override_value` is the value of [`OVERRIDE`] if it is set and UTF-8, and
/// `manifest_dir` the value of `CARGO_MANIFEST_DIR`.
// coverage: miri(test_directives_with_an_override, test_directives_from_git, test_directives_without_git); why: string, build
pub fn directives<H: Host>(
    override_value: Option<String>,
    manifest_dir: Option<PathBuf>,
    host: &H,
) -> String {
    let mut out = String::from("cargo:rerun-if-changed=build.rs\n");
    out.push_str(&format!("cargo:rerun-if-env-changed={OVERRIDE}\n"));
    // A value with a control character (a newline would start another cargo directive) is
    // ignored, as is an empty or non-UTF-8 one.
    let commit = match override_value {
        Some(value) if !value.is_empty() && !value.chars().any(char::is_control) => value,
        _ => git_commit(manifest_dir, host, &mut out).unwrap_or_else(|| String::from("unknown")),
    };
    out.push_str(&format!("cargo:rustc-env=BC_CLONE_COMMIT={commit}\n"));
    out
}

/// The standard output of git, without its trailing line ends, if git ran (`Some`), succeeded
/// (`true`) and printed UTF-8.
// coverage: miri(test_git_output); why: string, build
pub fn git_output(output: Option<(bool, Vec<u8>)>) -> Option<String> {
    let (success, stdout) = output?;
    if !success {
        return None;
    }
    let text = String::from_utf8(stdout).ok()?;
    Some(String::from(text.trim_end_matches(['\n', '\r'])))
}

/// The commit from git, appending the files to watch to `out`; `None` if the crate is not in
/// the work tree of the workspace or git fails.
// coverage: miri(via directives); why: string, build
fn git_commit<H: Host>(
    manifest_dir: Option<PathBuf>,
    host: &H,
    out: &mut String,
) -> Option<String> {
    let root = host.canonicalize(&manifest_dir?.join("../.."))?;
    let top_level = host.canonicalize(&PathBuf::from(
        host.git(&root, &["rev-parse", "--show-toplevel"])?,
    ))?;
    if top_level != root {
        return None;
    }
    watch_git_state(&root, host, out);
    let head = host.git(&root, &["rev-parse", "--verify", "HEAD"])?;
    if head.len() < COMMIT_DIGITS || !head.bytes().all(|b| b.is_ascii_hexdigit()) {
        return None;
    }
    let mut commit = String::from(&head[..COMMIT_DIGITS]);
    let status = host.git(&root, &["status", "--porcelain", "--untracked-files=no"])?;
    if !status.is_empty() {
        commit.push_str("-dirty");
    }
    Some(commit)
}

/// Appends to `out` the directives to rerun the script when `HEAD`, the branch it points to,
/// the packed references or the index change. Only existing files are named: cargo reruns the
/// script on every build for a missing one, which would rebuild every front end each time.
// coverage: miri(via git_commit); why: string, build
fn watch_git_state<H: Host>(root: &Path, host: &H, out: &mut String) {
    let mut paths = vec![
        String::from("HEAD"),
        String::from("index"),
        String::from("packed-refs"),
    ];
    if let Some(branch) = host.git(root, &["symbolic-ref", "-q", "HEAD"]) {
        paths.push(branch);
    }
    for path in paths {
        // The path is relative to `root` unless git prints it absolute (`root.join` keeps an
        // absolute one); `--path-format=absolute` would need git 2.31.
        if let Some(file) = host.git(root, &["rev-parse", "--git-path", &path]) {
            let file = root.join(file);
            if host.exists(&file) {
                out.push_str(&format!("cargo:rerun-if-changed={}\n", file.display()));
            }
        }
    }
}
