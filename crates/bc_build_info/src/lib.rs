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

// The decisions of `build.rs`, included here so that the unit tests run them. The module is
// production code of the build script, so cargo-mutants must mutate it; it skips a module marked
// `#[cfg(test)]` but not this equivalent spelling.
#[cfg(test)]
extern crate std;
#[cfg(any(test))]
#[allow(
    clippy::non_minimal_cfg,
    reason = "`cfg(test)` would hide the module from cargo-mutants"
)]
mod commit;

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
    use super::commit::{Host, directives, git_output};
    use super::*;
    use std::cell::RefCell;
    use std::path::{Path, PathBuf};
    use std::string::{String, ToString};
    use std::vec::Vec;
    use std::{format, vec};

    /// A system with a git repository at `/w` (reached from the manifest directory
    /// `/w/crates/bc_build_info`), whose answers the test chooses. It records the git commands.
    struct Fake {
        /// The answers of git: arguments joined by spaces, and the output.
        git: Vec<(&'static str, Option<&'static str>)>,
        /// The paths that exist.
        existing: Vec<&'static str>,
        calls: RefCell<Vec<String>>,
    }

    impl Fake {
        fn repo(head: &'static str, status: Option<&'static str>) -> Fake {
            Fake {
                git: vec![
                    ("rev-parse --show-toplevel", Some("/w")),
                    ("rev-parse --verify HEAD", Some(head)),
                    ("status --porcelain --untracked-files=no", status),
                    ("symbolic-ref -q HEAD", Some("refs/heads/main")),
                    ("rev-parse --git-path HEAD", Some(".git/HEAD")),
                    ("rev-parse --git-path index", Some(".git/index")),
                    ("rev-parse --git-path packed-refs", Some(".git/packed-refs")),
                    (
                        "rev-parse --git-path refs/heads/main",
                        Some("/g/refs/heads/main"),
                    ),
                ],
                existing: vec![
                    "/w/.git/HEAD",
                    "/w/.git/index",
                    "/w/.git/packed-refs",
                    "/g/refs/heads/main",
                ],
                calls: RefCell::new(Vec::new()),
            }
        }

        fn answer(&mut self, args: &'static str, out: Option<&'static str>) {
            self.git.retain(|(a, _)| *a != args);
            self.git.push((args, out));
        }
    }

    impl Host for Fake {
        fn git(&self, dir: &Path, args: &[&str]) -> Option<String> {
            assert_eq!(dir, Path::new("/w"));
            let args = args.join(" ");
            self.calls.borrow_mut().push(args.clone());
            let out = self.git.iter().find(|(a, _)| *a == args)?.1?;
            Some(out.to_string())
        }

        /// Resolves `..` textually; `/w` and the directories under it exist, and `/x` is a link
        /// to `/w`.
        fn canonicalize(&self, path: &Path) -> Option<PathBuf> {
            let mut parts: Vec<&str> = Vec::new();
            for part in path.to_str()?.split('/').filter(|p| !p.is_empty()) {
                if part == ".." {
                    parts.pop()?;
                } else {
                    parts.push(part);
                }
            }
            if parts.first() == Some(&"x") {
                parts[0] = "w";
            }
            (parts.first() == Some(&"w")).then(|| PathBuf::from(format!("/{}", parts.join("/"))))
        }

        fn exists(&self, path: &Path) -> bool {
            self.existing.iter().any(|p| Path::new(p) == path)
        }
    }

    const MANIFEST: &str = "/w/crates/bc_build_info";
    const HEAD: &str = "a916de2c0ffee0123456789abcdef0123456789a";
    const PRELUDE: &str =
        "cargo:rerun-if-changed=build.rs\ncargo:rerun-if-env-changed=BC_CLONE_GIT_COMMIT\n";
    const WATCH: &str = "cargo:rerun-if-changed=/w/.git/HEAD\n\
        cargo:rerun-if-changed=/w/.git/index\n\
        cargo:rerun-if-changed=/w/.git/packed-refs\n\
        cargo:rerun-if-changed=/g/refs/heads/main\n";

    fn text(value: Option<&str>) -> Option<String> {
        value.map(String::from)
    }

    fn path(value: Option<&str>) -> Option<PathBuf> {
        value.map(PathBuf::from)
    }

    fn env_line(commit: &str) -> String {
        format!("cargo:rustc-env=BC_CLONE_COMMIT={commit}\n")
    }

    #[test]
    fn test_directives_with_an_override() {
        let fake = Fake::repo(HEAD, Some(""));
        // A usable value is taken as it is, and git is not asked.
        let out = directives(text(Some("v1 custom")), path(Some(MANIFEST)), &fake);
        assert_eq!(out, format!("{PRELUDE}{}", env_line("v1 custom")));
        assert!(fake.calls.borrow().is_empty());
        // The manifest directory is not needed then.
        let out = directives(text(Some("v1")), path(None), &fake);
        assert_eq!(out, format!("{PRELUDE}{}", env_line("v1")));
        // An empty value, or one with a control character, is ignored.
        for bad in ["", "abc\ncargo:rustc-env=X=1", "a\tb", "\u{7f}"] {
            let out = directives(text(Some(bad)), path(Some(MANIFEST)), &fake);
            assert_eq!(
                out,
                format!("{PRELUDE}{WATCH}{}", env_line("a916de2")),
                "{bad:?}"
            );
        }
    }

    #[test]
    fn test_directives_from_git() {
        // A clean tree, through a link to the work tree: the watched files that exist, the
        // branch's absolute path kept, then the short commit.
        let fake = Fake::repo(HEAD, Some(""));
        let out = directives(text(None), path(Some("/x/crates/bc_build_info")), &fake);
        assert_eq!(out, format!("{PRELUDE}{WATCH}{}", env_line("a916de2")));
        // The top level git prints is compared in canonical form too.
        let mut fake = Fake::repo(HEAD, Some(""));
        fake.answer("rev-parse --show-toplevel", Some("/x/crates/.."));
        let out = directives(text(None), path(Some(MANIFEST)), &fake);
        assert_eq!(out, format!("{PRELUDE}{WATCH}{}", env_line("a916de2")));
        // A tracked change marks the commit.
        let fake = Fake::repo(HEAD, Some(" M src/lib.rs"));
        let out = directives(text(None), path(Some(MANIFEST)), &fake);
        assert_eq!(
            out,
            format!("{PRELUDE}{WATCH}{}", env_line("a916de2-dirty"))
        );
        // Seven hexadecimal digits are enough; upper case is accepted (and kept) as git would.
        let fake = Fake::repo("ABCDEF0", Some(""));
        assert!(
            directives(text(None), path(Some(MANIFEST)), &fake).ends_with(&env_line("ABCDEF0"))
        );
        // A detached HEAD: no branch to watch, and a missing file is not named.
        let mut fake = Fake::repo(HEAD, Some(""));
        fake.answer("symbolic-ref -q HEAD", None);
        fake.existing = vec!["/w/.git/HEAD"];
        let out = directives(text(None), path(Some(MANIFEST)), &fake);
        assert_eq!(
            out,
            format!(
                "{PRELUDE}cargo:rerun-if-changed=/w/.git/HEAD\n{}",
                env_line("a916de2")
            )
        );
        assert!(
            !fake
                .calls
                .borrow()
                .iter()
                .any(|c| c.starts_with("rev-parse --git-path refs/"))
        );
        // A path git cannot give is skipped.
        let mut fake = Fake::repo(HEAD, Some(""));
        fake.answer("rev-parse --git-path index", None);
        let out = directives(text(None), path(Some(MANIFEST)), &fake);
        assert!(!out.contains("index"));
        assert!(out.contains("/w/.git/HEAD") && out.ends_with(&env_line("a916de2")));
    }

    #[test]
    fn test_directives_without_git() {
        let unknown = env_line("unknown");
        // No manifest directory, or one outside the repository.
        let fake = Fake::repo(HEAD, Some(""));
        assert_eq!(
            directives(text(None), path(None), &fake),
            format!("{PRELUDE}{unknown}")
        );
        assert_eq!(
            directives(text(None), path(Some("/q/r/s")), &fake),
            format!("{PRELUDE}{unknown}")
        );
        assert!(fake.calls.borrow().is_empty());
        // The top level of the repository is not the workspace root (a copy of the sources in
        // another repository): nothing is watched and HEAD is not read.
        let mut fake = Fake::repo(HEAD, Some(""));
        fake.answer("rev-parse --show-toplevel", Some("/w/target"));
        assert_eq!(
            directives(text(None), path(Some(MANIFEST)), &fake),
            format!("{PRELUDE}{unknown}")
        );
        assert_eq!(*fake.calls.borrow(), ["rev-parse --show-toplevel"]);
        // Not a repository, or a top level that does not exist.
        for top in [None, Some("/nowhere")] {
            let mut fake = Fake::repo(HEAD, Some(""));
            fake.answer("rev-parse --show-toplevel", top);
            assert_eq!(
                directives(text(None), path(Some(MANIFEST)), &fake),
                format!("{PRELUDE}{unknown}")
            );
        }
        // No commit yet, a HEAD that is not a hash, or a failing `git status`: the watched
        // files are still named, so that the first commit reruns the script.
        for (head, status) in [
            (None, Some("")),
            (Some("a916de"), Some("")),
            (Some("a916dez"), Some("")),
            (Some(HEAD), None),
        ] {
            let mut fake = Fake::repo(HEAD, status);
            fake.answer("rev-parse --verify HEAD", head);
            let out = directives(text(None), path(Some(MANIFEST)), &fake);
            assert_eq!(
                out,
                format!("{PRELUDE}{WATCH}{unknown}"),
                "{head:?} {status:?}"
            );
        }
    }

    #[test]
    fn test_git_output() {
        assert_eq!(git_output(None), None);
        assert_eq!(git_output(Some((false, b"a916de2\n".to_vec()))), None);
        assert_eq!(git_output(Some((true, vec![0xff, b'\n']))), None);
        assert_eq!(
            git_output(Some((true, b" a b \r\n\n".to_vec()))).as_deref(),
            Some(" a b ")
        );
        assert_eq!(git_output(Some((true, Vec::new()))).as_deref(), Some(""));
    }

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
