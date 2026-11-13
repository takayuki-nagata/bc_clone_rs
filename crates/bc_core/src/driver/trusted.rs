// SPDX-License-Identifier: MIT

//! One-line wrappers of the standard library that Verus trusts: their contracts are assumed,
//! and the tests below run each one.

use alloc::vec::Vec;
#[cfg(not(verus_keep_ghost))]
use verus_builtin_macros::verus;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

verus! {

/// Trusted: `extend_from_slice` appends the slice.
// coverage: miri(driver::trusted::tests::wrappers_keep_their_contracts)
#[verifier::external_body]
pub(super) fn append_bytes(buf: &mut Vec<u8>, line: &[u8])
    ensures
        final(buf)@ == old(buf)@.add(line@),
{
    buf.extend_from_slice(line);
}

/// Trusted: the subslice of `text` from `a` to `b`.
// coverage: miri(driver::trusted::tests::wrappers_keep_their_contracts)
#[verifier::external_body]
pub(super) fn subslice(text: &[u8], a: usize, b: usize) -> (r: &[u8])
    requires
        a <= b <= text@.len(),
    ensures
        r@ == text@.subrange(a as int, b as int),
{
    &text[a..b]
}

} // verus!

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn wrappers_keep_their_contracts() {
        let mut buf = b"ab".to_vec();
        append_bytes(&mut buf, b"c\xff\n");
        assert_eq!(buf, b"abc\xff\n");
        append_bytes(&mut buf, b"");
        assert_eq!(buf, b"abc\xff\n");

        let text = b"0123456789";
        assert_eq!(subslice(text, 2, 5), b"234");
        assert_eq!(subslice(text, 0, 10), text);
        assert_eq!(subslice(text, 10, 10), b"");
    }
}
