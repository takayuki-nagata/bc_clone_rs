// SPDX-License-Identifier: MIT

//! The rules of the verification tiers, as `spec fn`s, and their verified implementation.
//!
//! The scanner (`scan.rs`, not verified) reduces every item it finds to a [`Fact`]: the name of
//! its file, the role of its crate, what kind of item it is, the `// coverage:` tag it carries
//! and three facts the scanner checked about that tag. Everything decided from those facts is
//! here and proved equal to the specification:
//!
//! - [`verified_tier`] is [`tier`]: which tier covers the item;
//! - [`verified_violation`] is [`violation`]: which rule, if any, the item breaks;
//! - [`verified_violations`] lists exactly the items that break a rule, in order;
//! - [`verified_tier_counts`] counts the items of each tier.
//!
//! The rules, in words:
//!
//! - an item that Verus assumes (an axiom, an `assume_specification`, an `external_body`
//!   function with a contract, an uninterpreted or opaque item, `dual_verified!`) is in a file
//!   whose name starts with `trusted`, except in a tool crate; in a product crate, such a
//!   function with a body is tied to a Kani harness or a Miri test that runs it;
//! - every other production function of a product crate is verified by Verus, or carries a tag
//!   naming the Kani harness, the Miri tests or (for a shim) the integration test that covers
//!   it, with the reasons it cannot be covered by a higher tier; a shim has no branches;
//! - in `bc_core`, a function outside Verus is in a file whose name starts with `trusted` or
//!   `unverified`;
//! - a verified, ghost or bridging item carries no tag;
//! - no crate calls `assume` or `admit`.

use vstd::prelude::*;

verus! {

/// The crate is `bc_core`, where the file placement rules apply.
pub const ROLE_CORE: u8 = 0;
/// Another crate that is part of a product (a front end, an example application).
pub const ROLE_PRODUCT: u8 = 1;
/// The executable specification `bc_spec`.
pub const ROLE_SPEC: u8 = 2;
/// A verification tool (`bc_inventory` itself).
pub const ROLE_TOOL: u8 = 3;

/// An executable function inside `verus!`, with no trusted attribute.
pub const KIND_EXEC: u8 = 0;
/// An executable function inside `verus!` that need not terminate (`exec_allows_no_decreases_clause`).
pub const KIND_EXEC_PARTIAL: u8 = 1;
/// A `spec` or `proof` function.
pub const KIND_GHOST: u8 = 2;
/// An `external_body` executable function with `requires` or `ensures`: Verus assumes its contract.
pub const KIND_EXT_BODY_SPEC: u8 = 3;
/// An `external_body` executable function without a contract: not verified, and assumed nothing.
pub const KIND_EXT_BODY_BARE: u8 = 4;
/// An `axiom fn`, or an `external_body` proof function.
pub const KIND_AXIOM: u8 = 5;
/// An `assume_specification` (or `external_fn_specification`).
pub const KIND_ASSUME_SPEC: u8 = 6;
/// An uninterpreted or `external_body` spec function: a model of something Verus cannot see.
pub const KIND_UNINTERP: u8 = 7;
/// An `external_body` struct or enum, opaque to Verus.
pub const KIND_OPAQUE_TYPE: u8 = 8;
/// An `external_type_specification`, which makes a type declared outside `verus!` visible.
pub const KIND_EXT_TYPE: u8 = 9;
/// The definition of `dual_verified!`, which Verus trusts to expand the body it checked unchanged
/// in a normal build.
pub const KIND_MACRO: u8 = 10;
/// A function outside `verus!` (or `#[verifier::external]`).
pub const KIND_OUTSIDE: u8 = 11;
/// A call of `assume` or `admit` inside `verus!`.
pub const KIND_ASSUME_CALL: u8 = 12;

/// No `// coverage:` tag.
pub const TAG_NONE: u8 = 0;
/// `// coverage: kani(...)`.
pub const TAG_KANI: u8 = 1;
/// `// coverage: miri(...)`.
pub const TAG_MIRI: u8 = 2;
/// `// coverage: shim(...)`.
pub const TAG_SHIM: u8 = 3;
/// A `// coverage:` line that could not be read, or more than one.
pub const TAG_MALFORMED: u8 = 4;

/// Verified by Verus.
pub const TIER_VERUS: u8 = 0;
/// Verified by Verus, partial correctness (termination not proved).
pub const TIER_VERUS_PARTIAL: u8 = 1;
/// A `spec` or `proof` item.
pub const TIER_PROOF: u8 = 2;
/// Assumed by Verus.
pub const TIER_ASSUMED: u8 = 3;
/// A type made visible to Verus.
pub const TIER_BRIDGE: u8 = 4;
/// Covered by a Kani harness.
pub const TIER_KANI: u8 = 5;
/// Covered by tests run under Miri.
pub const TIER_MIRI: u8 = 6;
/// A branch-free shim, run by an integration test.
pub const TIER_SHIM: u8 = 7;
/// Covered by nothing.
pub const TIER_UNCOVERED: u8 = 8;
/// A call of `assume` or `admit`.
pub const TIER_ASSUME_CALL: u8 = 9;
/// The number of tiers.
pub const TIER_COUNT: usize = 10;

/// Any other file.
pub const FILE_OTHER: u8 = 0;
/// A file whose name starts with `trusted`.
pub const FILE_TRUSTED: u8 = 1;
/// A file whose name starts with `unverified`.
pub const FILE_UNVERIFIED: u8 = 2;

/// No rule is broken.
pub const V_NONE: u8 = 0;
/// A production function of a product crate covered by nothing.
pub const V_UNCOVERED: u8 = 1;
/// A tag on an item that Verus verifies (or a ghost or bridging item).
pub const V_TAG_ON_VERIFIED: u8 = 2;
/// An assumption outside a `trusted*` file.
pub const V_ASSUMED_OUTSIDE_TRUSTED: u8 = 3;
/// A trusted wrapper of a product crate not tied to a Kani harness or Miri test that runs it.
pub const V_WRAPPER_UNTESTED: u8 = 4;
/// A function of `bc_core` outside Verus, in a file not named `unverified*`.
pub const V_CORE_PLACEMENT: u8 = 5;
/// A Kani, Miri or shim tag without valid reasons (`why:`).
pub const V_WHY: u8 = 6;
/// A tag naming a harness, test or integration test that does not exist or does not cover the item.
pub const V_TARGETS: u8 = 7;
/// A shim with a branch.
pub const V_SHIM_BRANCHES: u8 = 8;
/// A call of `assume` or `admit`.
pub const V_ASSUME_CALL: u8 = 9;
/// A malformed tag.
pub const V_MALFORMED_TAG: u8 = 10;

/// What the scanner found about one item.
pub struct Fact {
    /// The name of the file (without its directory).
    pub file: Vec<u8>,
    /// `ROLE_*` of its crate.
    pub role: u8,
    /// `KIND_*`.
    pub kind: u8,
    /// `TAG_*`.
    pub tag: u8,
    /// The tag gives reasons, all from the vocabulary.
    pub why_ok: bool,
    /// Every harness, test or integration test the tag names exists and covers the item.
    pub targets_ok: bool,
    /// The body has no branch.
    pub branch_free: bool,
}

/// `trusted`.
pub open spec fn trusted_word() -> Seq<u8> {
    seq![116u8, 114, 117, 115, 116, 101, 100]
}

/// `unverified`.
pub open spec fn unverified_word() -> Seq<u8> {
    seq![117u8, 110, 118, 101, 114, 105, 102, 105, 101, 100]
}

/// `s` starts with `p`.
pub open spec fn has_prefix(s: Seq<u8>, p: Seq<u8>) -> bool {
    p.len() <= s.len() && s.subrange(0, p.len() as int) == p
}

/// The class of a file, from its name.
pub open spec fn file_class(name: Seq<u8>) -> u8 {
    if has_prefix(name, trusted_word()) {
        FILE_TRUSTED
    } else if has_prefix(name, unverified_word()) {
        FILE_UNVERIFIED
    } else {
        FILE_OTHER
    }
}

/// The kinds that Verus assumes.
pub open spec fn is_assumed_kind(kind: u8) -> bool {
    kind == KIND_EXT_BODY_SPEC || kind == KIND_AXIOM || kind == KIND_ASSUME_SPEC || kind == KIND_UNINTERP
        || kind == KIND_OPAQUE_TYPE || kind == KIND_MACRO
}

/// The tier of an item of kind `kind` with tag `tag`.
pub open spec fn tier(kind: u8, tag: u8) -> u8 {
    if kind == KIND_EXEC {
        TIER_VERUS
    } else if kind == KIND_EXEC_PARTIAL {
        TIER_VERUS_PARTIAL
    } else if kind == KIND_GHOST {
        TIER_PROOF
    } else if is_assumed_kind(kind) {
        TIER_ASSUMED
    } else if kind == KIND_EXT_TYPE {
        TIER_BRIDGE
    } else if kind == KIND_ASSUME_CALL {
        TIER_ASSUME_CALL
    } else if tag == TAG_KANI {
        TIER_KANI
    } else if tag == TAG_MIRI {
        TIER_MIRI
    } else if tag == TAG_SHIM {
        TIER_SHIM
    } else {
        TIER_UNCOVERED
    }
}

/// A tier of code that Verus checks or that has no code (no tag allowed).
pub open spec fn is_verified_tier(t: u8) -> bool {
    t == TIER_VERUS || t == TIER_VERUS_PARTIAL || t == TIER_PROOF || t == TIER_BRIDGE
}

/// A tier given by a tag.
pub open spec fn is_tagged_tier(t: u8) -> bool {
    t == TIER_KANI || t == TIER_MIRI || t == TIER_SHIM
}

/// The rule an item breaks (`V_NONE` if none). The first rule that applies is reported.
pub open spec fn violation(file: Seq<u8>, role: u8, kind: u8, tag: u8, why_ok: bool, targets_ok: bool, branch_free: bool) -> u8 {
    let t = tier(kind, tag);
    let product = role == ROLE_CORE || role == ROLE_PRODUCT;
    if tag == TAG_MALFORMED {
        V_MALFORMED_TAG
    } else if t == TIER_ASSUME_CALL {
        V_ASSUME_CALL
    } else if is_verified_tier(t) && tag != TAG_NONE {
        V_TAG_ON_VERIFIED
    } else if t == TIER_ASSUMED && role != ROLE_TOOL && file_class(file) != FILE_TRUSTED {
        V_ASSUMED_OUTSIDE_TRUSTED
    } else if !product {
        V_NONE
    } else if kind == KIND_EXT_BODY_SPEC && !((tag == TAG_KANI || tag == TAG_MIRI) && targets_ok) {
        V_WRAPPER_UNTESTED
    } else if t == TIER_UNCOVERED {
        V_UNCOVERED
    } else if is_tagged_tier(t) && role == ROLE_CORE && file_class(file) != FILE_UNVERIFIED {
        V_CORE_PLACEMENT
    } else if is_tagged_tier(t) && !why_ok {
        V_WHY
    } else if is_tagged_tier(t) && !targets_ok {
        V_TARGETS
    } else if t == TIER_SHIM && !branch_free {
        V_SHIM_BRANCHES
    } else {
        V_NONE
    }
}

/// [`violation`] of a fact.
pub open spec fn fact_violation(f: Fact) -> u8 {
    violation(f.file@, f.role, f.kind, f.tag, f.why_ok, f.targets_ok, f.branch_free)
}

/// The violations among the first `n` facts: (index, rule), in order.
pub open spec fn violations_upto(facts: Seq<Fact>, n: int) -> Seq<(usize, u8)>
    decreases n,
{
    if n <= 0 {
        seq![]
    } else {
        let prev = violations_upto(facts, n - 1);
        let v = fact_violation(facts[n - 1]);
        if v == V_NONE {
            prev
        } else {
            prev.push(((n - 1) as usize, v))
        }
    }
}

/// The number of the first `n` facts whose tier is `t`.
pub open spec fn count_upto(facts: Seq<Fact>, n: int, t: u8) -> nat
    decreases n,
{
    if n <= 0 {
        0
    } else {
        count_upto(facts, n - 1, t) + (if tier(facts[n - 1].kind, facts[n - 1].tag) == t { 1nat } else { 0nat })
    }
}

/// `name` starts with `p`.
fn starts_with(name: &[u8], p: &[u8]) -> (r: bool)
    ensures
        r == has_prefix(name@, p@),
{
    if p.len() > name.len() {
        return false;
    }
    let mut i: usize = 0;
    while i < p.len()
        invariant
            p@.len() <= name@.len(),
            0 <= i <= p@.len(),
            forall|j: int| 0 <= j < i ==> name@[j] == p@[j],
        decreases p@.len() - i,
    {
        if name[i] != p[i] {
            assert(name@.subrange(0, p@.len() as int)[i as int] != p@[i as int]);
            return false;
        }
        i += 1;
    }
    assert(name@.subrange(0, p@.len() as int) =~= p@);
    true
}

/// [`file_class`] of a file name.
pub fn verified_file_class(name: &[u8]) -> (r: u8)
    ensures
        r == file_class(name@),
{
    let trusted: [u8; 7] = [116, 114, 117, 115, 116, 101, 100];
    let unverified: [u8; 10] = [117, 110, 118, 101, 114, 105, 102, 105, 101, 100];
    assert(trusted@ =~= trusted_word());
    assert(unverified@ =~= unverified_word());
    if starts_with(name, &trusted) {
        FILE_TRUSTED
    } else if starts_with(name, &unverified) {
        FILE_UNVERIFIED
    } else {
        FILE_OTHER
    }
}

/// [`tier`].
pub fn verified_tier(kind: u8, tag: u8) -> (r: u8)
    ensures
        r == tier(kind, tag),
        (r as usize) < TIER_COUNT,
{
    if kind == KIND_EXEC {
        TIER_VERUS
    } else if kind == KIND_EXEC_PARTIAL {
        TIER_VERUS_PARTIAL
    } else if kind == KIND_GHOST {
        TIER_PROOF
    } else if kind == KIND_EXT_BODY_SPEC || kind == KIND_AXIOM || kind == KIND_ASSUME_SPEC || kind == KIND_UNINTERP
        || kind == KIND_OPAQUE_TYPE || kind == KIND_MACRO {
        TIER_ASSUMED
    } else if kind == KIND_EXT_TYPE {
        TIER_BRIDGE
    } else if kind == KIND_ASSUME_CALL {
        TIER_ASSUME_CALL
    } else if tag == TAG_KANI {
        TIER_KANI
    } else if tag == TAG_MIRI {
        TIER_MIRI
    } else if tag == TAG_SHIM {
        TIER_SHIM
    } else {
        TIER_UNCOVERED
    }
}

/// [`fact_violation`].
pub fn verified_violation(f: &Fact) -> (r: u8)
    ensures
        r == fact_violation(*f),
{
    let t = verified_tier(f.kind, f.tag);
    let product = f.role == ROLE_CORE || f.role == ROLE_PRODUCT;
    let verified = t == TIER_VERUS || t == TIER_VERUS_PARTIAL || t == TIER_PROOF || t == TIER_BRIDGE;
    let tagged = t == TIER_KANI || t == TIER_MIRI || t == TIER_SHIM;
    if f.tag == TAG_MALFORMED {
        V_MALFORMED_TAG
    } else if t == TIER_ASSUME_CALL {
        V_ASSUME_CALL
    } else if verified && f.tag != TAG_NONE {
        V_TAG_ON_VERIFIED
    } else if t == TIER_ASSUMED && f.role != ROLE_TOOL && verified_file_class(f.file.as_slice()) != FILE_TRUSTED {
        V_ASSUMED_OUTSIDE_TRUSTED
    } else if !product {
        V_NONE
    } else if f.kind == KIND_EXT_BODY_SPEC && !((f.tag == TAG_KANI || f.tag == TAG_MIRI) && f.targets_ok) {
        V_WRAPPER_UNTESTED
    } else if t == TIER_UNCOVERED {
        V_UNCOVERED
    } else if tagged && f.role == ROLE_CORE && verified_file_class(f.file.as_slice()) != FILE_UNVERIFIED {
        V_CORE_PLACEMENT
    } else if tagged && !f.why_ok {
        V_WHY
    } else if tagged && !f.targets_ok {
        V_TARGETS
    } else if t == TIER_SHIM && !f.branch_free {
        V_SHIM_BRANCHES
    } else {
        V_NONE
    }
}

/// The facts that break a rule, with the rule, in order: exactly [`violations_upto`] of all of them.
pub fn verified_violations(facts: &[Fact]) -> (r: Vec<(usize, u8)>)
    ensures
        r@ == violations_upto(facts@, facts@.len() as int),
{
    let mut r: Vec<(usize, u8)> = Vec::new();
    let mut i: usize = 0;
    while i < facts.len()
        invariant
            0 <= i <= facts@.len(),
            r@ == violations_upto(facts@, i as int),
        decreases facts@.len() - i,
    {
        let v = verified_violation(&facts[i]);
        if v != V_NONE {
            r.push((i, v));
        }
        i += 1;
    }
    r
}

/// The number of facts of each tier: exactly [`count_upto`] of all of them.
pub fn verified_tier_counts(facts: &[Fact]) -> (r: Vec<usize>)
    ensures
        r@.len() == TIER_COUNT,
        forall|t: int| 0 <= t < TIER_COUNT ==> r@[t] as nat == count_upto(facts@, facts@.len() as int, t as u8),
{
    let mut r: Vec<usize> = Vec::new();
    let mut k: usize = 0;
    while k < TIER_COUNT
        invariant
            0 <= k <= TIER_COUNT,
            r@.len() == k,
            forall|t: int| 0 <= t < k ==> r@[t] == 0,
        decreases TIER_COUNT - k,
    {
        r.push(0);
        k += 1;
    }
    let mut i: usize = 0;
    while i < facts.len()
        invariant
            0 <= i <= facts@.len(),
            r@.len() == TIER_COUNT,
            forall|t: int| 0 <= t < TIER_COUNT ==> r@[t] as nat == count_upto(facts@, i as int, t as u8),
            forall|t: int| 0 <= t < TIER_COUNT ==> r@[t] <= i,
        decreases facts@.len() - i,
    {
        let t = verified_tier(facts[i].kind, facts[i].tag);
        let ghost before = r@;
        let c = r[t as usize];
        r.set(t as usize, c + 1);
        assert forall|u: int| 0 <= u < TIER_COUNT implies r@[u] as nat == count_upto(facts@, i as int + 1, u as u8)
            && r@[u] <= i + 1 by {
            assert(before[u] as nat == count_upto(facts@, i as int, u as u8));
            if u == t as int {
                assert(r@[u] == before[u] + 1);
            } else {
                assert(r@[u] == before[u]);
                assert((u as u8) != t);
            }
        }
        i += 1;
    }
    r
}

} // verus!

#[cfg(test)]
mod tests;
