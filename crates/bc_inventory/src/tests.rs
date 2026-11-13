// SPDX-License-Identifier: MIT

//! Tests of the inventory as a whole: the repository itself, the document and the command.

use super::*;
use std::path::PathBuf;

fn repo() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

#[test]
fn the_repository_is_read_without_errors() {
    let r = build(&scan::FsSource(repo()));
    assert!(r.errors.is_empty(), "{:?}", r.errors);
    assert_eq!(r.tiers.len(), r.items.len());
    assert_eq!(
        r.counts
            .iter()
            .map(|c| c.iter().sum::<usize>())
            .sum::<usize>(),
        r.items.len()
    );
    // The engine has verified functions, trusted assumptions and partial-correctness loops.
    let core = &r.counts[0];
    for t in [
        rules::TIER_VERUS,
        rules::TIER_ASSUMED,
        rules::TIER_VERUS_PARTIAL,
        rules::TIER_PROOF,
    ] {
        assert!(core[usize::from(t)] > 0, "tier {t}");
    }
    // No crate calls `assume` or `admit`.
    assert!(
        r.counts
            .iter()
            .all(|c| c[usize::from(rules::TIER_ASSUME_CALL)] == 0)
    );
}

#[test]
fn the_document_has_every_section() {
    let text = render::render(&build(&scan::FsSource(repo())));
    for h in [
        "# Verification inventory",
        "## Summary",
        "## Functions outside Verus",
        "## Assumptions",
        "## Partial correctness",
        "## Violations",
    ] {
        assert!(text.contains(h), "{h}");
    }
    for c in CRATES {
        assert!(text.contains(&format!("| `{}` |", c.name)), "{}", c.name);
    }
}

#[test]
fn every_violation_has_a_message() {
    for v in 1..=rules::V_MALFORMED_TAG {
        assert!(!render::violation_text(v).is_empty(), "{v}");
    }
    assert!(render::violation_text(rules::V_NONE).is_empty());
}

#[test]
fn the_products_are_not_enforced_yet() {
    assert!(!enforced(rules::ROLE_PRODUCT));
}

#[test]
fn a_wrong_argument_is_a_usage_error() {
    let (mut out, mut err) = (Vec::new(), Vec::new());
    assert_eq!(
        run(&["--bogus".to_string()], &repo(), &mut out, &mut err),
        2
    );
    assert!(String::from_utf8_lossy(&err).contains("usage"));
}

#[test]
fn a_tree_without_the_crates_fails_the_check() {
    let dir = std::env::temp_dir().join(format!("bc_inventory_test_{}", std::process::id()));
    let _ = std::fs::create_dir_all(dir.join("docs"));
    let (mut out, mut err) = (Vec::new(), Vec::new());
    assert_eq!(run(&["--check".to_string()], &dir, &mut out, &mut err), 1);
    let err = String::from_utf8_lossy(&err).into_owned();
    assert!(err.contains("cannot read"), "{err}");
    assert!(err.contains("out of date"), "{err}");
    let _ = std::fs::remove_dir_all(&dir);
}
