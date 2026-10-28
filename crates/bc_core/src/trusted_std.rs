// SPDX-License-Identifier: MIT

//! Trusted facts about the standard library that `vstd` does not provide, used by the
//! refinement proofs. Each is an `axiom fn`: Verus assumes it without proof, so
//! together with `trusted_bigint.rs` this file lists the trusted base of those proofs beyond
//! Verus, `vstd`, rustc and Z3. Compiled only under Verus.

use crate::parser::FunctionDef;
use alloc::string::String;
use vstd::prelude::*;

verus! {

/// `String`'s `Ord` is a total order consistent with its `Eq` (lexicographic on the bytes), as
/// `vstd`'s `BTreeMap` specifications require of a key type.
pub axiom fn axiom_string_obeys_cmp()
    ensures
        vstd::laws_cmp::obeys_cmp::<String>(),
;

/// A `String` is determined by its characters.
pub axiom fn axiom_string_view_injective(a: String, b: String)
    ensures
        a@ == b@ ==> a == b,
;

/// The derived `Clone` of a function definition gives an equal value.
pub assume_specification[ <FunctionDef as Clone>::clone ](f: &FunctionDef) -> (r: FunctionDef)
    ensures
        r == *f,
;

} // verus!
