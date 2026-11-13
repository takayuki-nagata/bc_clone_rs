// SPDX-License-Identifier: MIT

//! Examples of the rules. Verus proves the functions equal to the `spec fn`s for all inputs;
//! these tests show that the `spec fn`s say what the crate documentation says.

use super::*;

fn fact(file: &str, role: u8, kind: u8, tag: u8) -> Fact {
    Fact {
        file: file.as_bytes().to_vec(),
        role,
        kind,
        tag,
        why_ok: true,
        targets_ok: true,
        branch_free: true,
    }
}

fn v(f: &Fact) -> u8 {
    verified_violation(f)
}

#[test]
fn file_classes_come_from_the_name() {
    assert_eq!(verified_file_class(b"trusted_io.rs"), FILE_TRUSTED);
    assert_eq!(verified_file_class(b"trusted"), FILE_TRUSTED);
    assert_eq!(verified_file_class(b"trustee.rs"), FILE_OTHER);
    assert_eq!(verified_file_class(b"unverified.rs"), FILE_UNVERIFIED);
    assert_eq!(verified_file_class(b"verified_kernels.rs"), FILE_OTHER);
    assert_eq!(verified_file_class(b""), FILE_OTHER);
}

#[test]
fn verified_code_needs_nothing_and_takes_no_tag() {
    for kind in [KIND_EXEC, KIND_EXEC_PARTIAL, KIND_GHOST, KIND_EXT_TYPE] {
        assert_eq!(v(&fact("eval.rs", ROLE_CORE, kind, TAG_NONE)), V_NONE);
        assert_eq!(
            v(&fact("eval.rs", ROLE_CORE, kind, TAG_MIRI)),
            V_TAG_ON_VERIFIED
        );
    }
}

#[test]
fn assumptions_live_in_trusted_files_and_wrappers_are_tested() {
    for kind in [
        KIND_AXIOM,
        KIND_ASSUME_SPEC,
        KIND_UNINTERP,
        KIND_OPAQUE_TYPE,
        KIND_MACRO,
    ] {
        assert_eq!(
            v(&fact("trusted_math.rs", ROLE_CORE, kind, TAG_NONE)),
            V_NONE
        );
        assert_eq!(
            v(&fact("math.rs", ROLE_CORE, kind, TAG_NONE)),
            V_ASSUMED_OUTSIDE_TRUSTED
        );
        assert_eq!(
            v(&fact("math.rs", ROLE_SPEC, kind, TAG_NONE)),
            V_ASSUMED_OUTSIDE_TRUSTED
        );
        assert_eq!(v(&fact("math.rs", ROLE_TOOL, kind, TAG_NONE)), V_NONE);
    }
    assert_eq!(
        v(&fact(
            "trusted_io.rs",
            ROLE_CORE,
            KIND_EXT_BODY_SPEC,
            TAG_NONE
        )),
        V_WRAPPER_UNTESTED
    );
    assert_eq!(
        v(&fact(
            "trusted_io.rs",
            ROLE_CORE,
            KIND_EXT_BODY_SPEC,
            TAG_MIRI
        )),
        V_NONE
    );
    assert_eq!(
        v(&fact(
            "trusted_io.rs",
            ROLE_CORE,
            KIND_EXT_BODY_SPEC,
            TAG_KANI
        )),
        V_NONE
    );
    assert_eq!(
        v(&fact(
            "trusted_io.rs",
            ROLE_CORE,
            KIND_EXT_BODY_SPEC,
            TAG_SHIM
        )),
        V_WRAPPER_UNTESTED
    );
    let mut untested = fact("trusted_io.rs", ROLE_CORE, KIND_EXT_BODY_SPEC, TAG_MIRI);
    untested.targets_ok = false;
    assert_eq!(v(&untested), V_WRAPPER_UNTESTED);
}

#[test]
fn code_outside_verus_needs_a_valid_tag_in_a_product() {
    for kind in [KIND_OUTSIDE, KIND_EXT_BODY_BARE] {
        assert_eq!(
            v(&fact("main.rs", ROLE_PRODUCT, kind, TAG_NONE)),
            V_UNCOVERED
        );
        assert_eq!(v(&fact("main.rs", ROLE_PRODUCT, kind, TAG_MIRI)), V_NONE);
        assert_eq!(v(&fact("main.rs", ROLE_SPEC, kind, TAG_NONE)), V_NONE);
        assert_eq!(v(&fact("main.rs", ROLE_TOOL, kind, TAG_NONE)), V_NONE);
    }
    let mut f = fact("main.rs", ROLE_PRODUCT, KIND_OUTSIDE, TAG_KANI);
    f.why_ok = false;
    assert_eq!(v(&f), V_WHY);
    f.why_ok = true;
    f.targets_ok = false;
    assert_eq!(v(&f), V_TARGETS);
    let mut shim = fact("main.rs", ROLE_PRODUCT, KIND_OUTSIDE, TAG_SHIM);
    assert_eq!(v(&shim), V_NONE);
    shim.branch_free = false;
    assert_eq!(v(&shim), V_SHIM_BRANCHES);
    let mut miri = fact("main.rs", ROLE_PRODUCT, KIND_OUTSIDE, TAG_MIRI);
    miri.branch_free = false;
    assert_eq!(v(&miri), V_NONE);
}

#[test]
fn the_engine_keeps_code_outside_verus_in_unverified_files() {
    assert_eq!(
        v(&fact("driver.rs", ROLE_CORE, KIND_OUTSIDE, TAG_MIRI)),
        V_CORE_PLACEMENT
    );
    assert_eq!(
        v(&fact("unverified.rs", ROLE_CORE, KIND_OUTSIDE, TAG_MIRI)),
        V_NONE
    );
    assert_eq!(
        v(&fact("trusted_io.rs", ROLE_CORE, KIND_OUTSIDE, TAG_MIRI)),
        V_CORE_PLACEMENT
    );
    assert_eq!(
        v(&fact("driver.rs", ROLE_PRODUCT, KIND_OUTSIDE, TAG_MIRI)),
        V_NONE
    );
}

#[test]
fn assume_calls_and_malformed_tags_are_always_reported() {
    for role in [ROLE_CORE, ROLE_PRODUCT, ROLE_SPEC, ROLE_TOOL] {
        assert_eq!(
            v(&fact("x.rs", role, KIND_ASSUME_CALL, TAG_NONE)),
            V_ASSUME_CALL
        );
        assert_eq!(
            v(&fact("x.rs", role, KIND_EXEC, TAG_MALFORMED)),
            V_MALFORMED_TAG
        );
    }
}

#[test]
fn violations_and_counts_cover_every_fact() {
    let facts = [
        fact("a.rs", ROLE_PRODUCT, KIND_OUTSIDE, TAG_NONE),
        fact("a.rs", ROLE_CORE, KIND_EXEC, TAG_NONE),
        fact("a.rs", ROLE_CORE, KIND_AXIOM, TAG_NONE),
        fact("a.rs", ROLE_CORE, KIND_EXEC, TAG_NONE),
    ];
    assert_eq!(
        verified_violations(&facts),
        vec![(0, V_UNCOVERED), (2, V_ASSUMED_OUTSIDE_TRUSTED)]
    );
    let counts = verified_tier_counts(&facts);
    assert_eq!(counts.len(), TIER_COUNT);
    assert_eq!(
        (
            counts[usize::from(TIER_VERUS)],
            counts[usize::from(TIER_UNCOVERED)],
            counts[usize::from(TIER_ASSUMED)]
        ),
        (2, 1, 1)
    );
    assert_eq!(counts.iter().sum::<usize>(), facts.len());
}
