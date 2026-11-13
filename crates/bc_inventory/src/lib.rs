// SPDX-License-Identifier: MIT

//! `bc_inventory`: which tool covers each production function of `bc_clone_rs`.
//!
//! Every production function of the workspace and the examples belongs to one tier: verified
//! by Verus, assumed by Verus (in a `trusted*` file, with a test of its body), covered by a Kani
//! harness, covered by tests run under Miri, or a branch-free shim run by an integration test.
//! A function outside Verus carries a `// coverage:` comment that names what covers it and why a
//! higher tier cannot:
//!
//! ```text
//! // coverage: kani(proof_write_c_string); why: ffi
//! // coverage: miri(test_run_app, via run_app); why: io
//! // coverage: shim(scripts/run_qemu_riscv32_tests.sh); why: hw
//! ```
//!
//! `cargo run -p bc_inventory` writes `docs/VERIFICATION_INVENTORY.md`; with `--check` it fails
//! when that file is out of date or an enforced rule is broken. The rules are `spec fn`s in
//! [`rules`], and the decisions are verified against them by Verus
//! (`cargo verus verify -p bc_inventory`). Reading the sources ([`scan`]) and writing the
//! document ([`render`]) are checked by tests.

pub mod render;
pub mod rules;
pub mod scan;

use rules::{Fact, ROLE_PRODUCT, V_NONE, verified_tier, verified_tier_counts, verified_violations};
use scan::{CRATES, Item, Source};
use std::path::Path;

/// Where the inventory is written, relative to the repository root.
pub const OUTPUT: &str = "docs/VERIFICATION_INVENTORY.md";

/// Whether the violations of each role (`ROLE_*`) make `--check` fail. Until the tiers are in
/// place, the violations are only reported; the rules for the front ends become enforced as
/// each one is brought into the tiers.
const ENFORCED: [bool; 4] = [false, false, false, false];

/// Whether the violations of the crates of `role` make `--check` fail.
pub fn enforced(role: u8) -> bool {
    role != ROLE_PRODUCT && ENFORCED.get(usize::from(role)).copied().unwrap_or(true)
}

/// The inventory of a repository.
pub struct Report {
    /// The items, sorted by crate, file and name.
    pub items: Vec<Item>,
    /// `TIER_*` of each item.
    pub tiers: Vec<u8>,
    /// The items that break a rule: (index into `items`, `V_*`).
    pub violations: Vec<(usize, u8)>,
    /// For each crate of [`CRATES`], the number of its items in each tier.
    pub counts: Vec<Vec<usize>>,
    /// Problems reading the sources.
    pub errors: Vec<String>,
}

/// Reads the repository and decides the tier and the violations of every item.
pub fn build(src: &dyn Source) -> Report {
    let mut s = scan::scan_all(src);
    scan::resolve(&mut s, src);
    s.items.sort_by(|a, b| {
        (a.krate, &a.file, &a.name, a.line).cmp(&(b.krate, &b.file, &b.name, b.line))
    });
    let facts: Vec<Fact> = scan::facts(&s);
    let tiers = facts.iter().map(|f| verified_tier(f.kind, f.tag)).collect();
    let violations = verified_violations(&facts);
    let counts = (0..CRATES.len())
        .map(|k| {
            let lo = s.items.partition_point(|it| it.krate < k);
            let hi = s.items.partition_point(|it| it.krate <= k);
            verified_tier_counts(&facts[lo..hi])
        })
        .collect();
    let mut errors = s.errors;
    errors.extend(scan::check_lists(src));
    Report {
        items: s.items,
        tiers,
        violations,
        counts,
        errors,
    }
}

/// The violations of the enforced roles.
pub fn enforced_violations(r: &Report) -> Vec<(usize, u8)> {
    r.violations
        .iter()
        .copied()
        .filter(|&(i, v)| v != V_NONE && enforced(CRATES[r.items[i].krate].role))
        .collect()
}

/// Runs the command: no argument writes the inventory, `--check` checks it. Returns the exit
/// status; messages go to `out` and `err`.
pub fn run(
    args: &[String],
    root: &Path,
    out: &mut dyn std::io::Write,
    err: &mut dyn std::io::Write,
) -> i32 {
    let check = match args {
        [] => false,
        [a] if a == "--check" => true,
        _ => {
            let _ = writeln!(err, "usage: bc_inventory [--check]");
            return 2;
        }
    };
    let src = scan::FsSource(root.to_path_buf());
    let report = build(&src);
    for e in &report.errors {
        let _ = writeln!(err, "bc_inventory: {e}");
    }
    let text = render::render(&report);
    let path = root.join(OUTPUT);
    let mut status = i32::from(!report.errors.is_empty());
    if check {
        if std::fs::read_to_string(&path).ok().as_deref() != Some(text.as_str()) {
            let _ = writeln!(
                err,
                "bc_inventory: {OUTPUT} is out of date; run `cargo run -p bc_inventory`"
            );
            status = 1;
        }
        let enforced = enforced_violations(&report);
        for &(i, v) in &enforced {
            let it = &report.items[i];
            let _ = writeln!(
                err,
                "bc_inventory: {}:{}: {}: {}",
                it.file,
                it.line,
                it.name,
                render::violation_text(v)
            );
        }
        if !enforced.is_empty() {
            status = 1;
        }
    } else if let Err(e) = std::fs::write(&path, &text) {
        let _ = writeln!(err, "bc_inventory: cannot write {OUTPUT}: {e}");
        status = 1;
    }
    let _ = writeln!(
        out,
        "{} items, {} violations ({} enforced)",
        report.items.len(),
        report.violations.len(),
        enforced_violations(&report).len()
    );
    status
}

#[cfg(test)]
mod tests;
