// SPDX-License-Identifier: MIT

//! Records the commit of the source tree in `BC_CLONE_COMMIT`.
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

use std::path::{Path, PathBuf};
use std::process::Command;

const OVERRIDE: &str = "BC_CLONE_GIT_COMMIT";
const COMMIT_DIGITS: usize = 7;

fn main() {
    println!("cargo:rerun-if-changed=build.rs");
    println!("cargo:rerun-if-env-changed={OVERRIDE}");
    // A value with a control character (a newline would start another cargo directive) is
    // ignored, as is an empty or non-UTF-8 one.
    let commit = match std::env::var(OVERRIDE) {
        Ok(value) if !value.is_empty() && !value.chars().any(char::is_control) => value,
        _ => git_commit().unwrap_or_else(|| String::from("unknown")),
    };
    println!("cargo:rustc-env=BC_CLONE_COMMIT={commit}");
}

/// Runs git in `dir` and returns its trimmed standard output if it succeeds.
fn git(dir: &Path, args: &[&str]) -> Option<String> {
    // `--no-optional-locks`: `git status` must not refresh the index, which would change a file
    // that cargo watches (and rerun this script on the next build) and could take `index.lock`
    // while a `git commit` runs.
    let output = Command::new("git")
        .arg("--no-optional-locks")
        .arg("-C")
        .arg(dir)
        .args(args)
        .output()
        .ok()?;
    if !output.status.success() {
        return None;
    }
    let text = String::from_utf8(output.stdout).ok()?;
    Some(String::from(text.trim_end_matches(['\n', '\r'])))
}

fn git_commit() -> Option<String> {
    let manifest_dir = PathBuf::from(std::env::var_os("CARGO_MANIFEST_DIR")?);
    let root = manifest_dir.join("../..").canonicalize().ok()?;
    let top_level = PathBuf::from(git(&root, &["rev-parse", "--show-toplevel"])?)
        .canonicalize()
        .ok()?;
    if top_level != root {
        return None;
    }
    watch_git_state(&root);
    let head = git(&root, &["rev-parse", "--verify", "HEAD"])?;
    if head.len() < COMMIT_DIGITS || !head.bytes().all(|b| b.is_ascii_hexdigit()) {
        return None;
    }
    let mut commit = String::from(&head[..COMMIT_DIGITS]);
    let status = git(&root, &["status", "--porcelain", "--untracked-files=no"])?;
    if !status.is_empty() {
        commit.push_str("-dirty");
    }
    Some(commit)
}

/// Asks cargo to rerun this script when `HEAD`, the branch it points to, the packed
/// references or the index change. Only existing files are named: cargo reruns the script on
/// every build for a missing one, which would rebuild every front end each time.
fn watch_git_state(root: &Path) {
    let mut paths = vec![
        String::from("HEAD"),
        String::from("index"),
        String::from("packed-refs"),
    ];
    if let Some(branch) = git(root, &["symbolic-ref", "-q", "HEAD"]) {
        paths.push(branch);
    }
    for path in paths {
        // The path is relative to `root` unless git prints it absolute (`root.join` keeps an
        // absolute one); `--path-format=absolute` would need git 2.31.
        if let Some(file) = git(root, &["rev-parse", "--git-path", &path]) {
            let file = root.join(file);
            if file.exists() {
                println!("cargo:rerun-if-changed={}", file.display());
            }
        }
    }
}
