// SPDX-License-Identifier: MIT

//! Records the commit of the source tree in `BC_CLONE_COMMIT`. The decisions are in
//! `src/commit.rs`, which the unit tests of the library run; this script only passes them the
//! environment, the file system and git.

use std::env;
use std::path::{Path, PathBuf};
use std::process::Command;

#[path = "src/commit.rs"]
mod commit;

/// The real system.
struct System;

impl commit::Host for System {
    // coverage: shim(crates/bc_cli/tests/integration_tests.rs); why: build, io
    fn git(&self, dir: &Path, args: &[&str]) -> Option<String> {
        // `--no-optional-locks`: `git status` must not refresh the index, which would change a
        // file that cargo watches (and rerun this script on the next build) and could take
        // `index.lock` while a `git commit` runs.
        commit::git_output(
            Command::new("git")
                .arg("--no-optional-locks")
                .arg("-C")
                .arg(dir)
                .args(args)
                .output()
                .ok()
                .map(|output| (output.status.success(), output.stdout)),
        )
    }

    // coverage: shim(crates/bc_cli/tests/integration_tests.rs); why: build, io
    fn canonicalize(&self, path: &Path) -> Option<PathBuf> {
        path.canonicalize().ok()
    }

    // coverage: shim(crates/bc_cli/tests/integration_tests.rs); why: build, io
    fn exists(&self, path: &Path) -> bool {
        path.exists()
    }
}

// coverage: shim(crates/bc_cli/tests/integration_tests.rs); why: build, io
fn main() {
    print!(
        "{}",
        commit::directives(
            env::var(commit::OVERRIDE).ok(),
            env::var_os("CARGO_MANIFEST_DIR").map(PathBuf::from),
            &System,
        )
    );
}
