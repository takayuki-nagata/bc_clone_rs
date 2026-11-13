// SPDX-License-Identifier: MIT

//! One-line wrappers of the standard library that Verus trusts: their contracts are assumed,
//! and the tests below run each one.

use alloc::rc::Rc;
use alloc::string::String;
use alloc::vec::Vec;

use super::Code;
#[cfg(verus_keep_ghost)]
use super::all_ascii;
#[cfg(verus_keep_ghost)]
use crate::refine::text_view;
#[cfg(not(verus_keep_ghost))]
use verus_builtin_macros::verus;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

verus! {

/// Trusted: a `char` below 0x80 is one UTF-8 byte of the same value.
// coverage: miri(wrappers_keep_their_contracts)
#[verifier::external_body]
pub(crate) fn ascii_string(b: &[u8]) -> (r: String)
    requires
        all_ascii(b@),
    ensures
        text_view(r) == b@,
{
    b.iter().map(|&x| char::from(x)).collect()
}

/// Trusted: cloning an `Rc` shares the same value.
// coverage: miri(wrappers_keep_their_contracts)
#[verifier::external_body]
pub(crate) fn share_code(c: &Rc<Code>) -> (r: Rc<Code>)
    ensures
        *r == **c,
{
    Rc::clone(c)
}

/// Trusted: `to_vec` copies the slice.
// coverage: miri(wrappers_keep_their_contracts)
#[verifier::external_body]
pub(super) fn copy_bytes(text: &[u8]) -> (r: Vec<u8>)
    ensures
        r@ == text@,
{
    text.to_vec()
}

} // verus!

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn wrappers_keep_their_contracts() {
        let all: Vec<u8> = (0..0x80u8).collect();
        let s = ascii_string(&all);
        assert_eq!(s.as_bytes(), all.as_slice());
        assert_eq!(s.chars().count(), all.len());

        let text = b"a\xff\x00z";
        assert_eq!(copy_bytes(text), text.to_vec());
        assert_eq!(copy_bytes(b""), Vec::<u8>::new());

        let code = Rc::new(Code { nodes: Vec::new() });
        let shared = share_code(&code);
        assert!(Rc::ptr_eq(&code, &shared));
    }
}
