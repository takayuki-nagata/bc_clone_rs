// SPDX-License-Identifier: MIT

//! The output of numbers: `BCNum::format_bytes`, proved to write `l0_format` of the value, the
//! integer-level output definition of the specification (`crates/bc_spec/src/format.rs`), for
//! every `obase` from 2 to `BC_BASE_MAX`.
//!
//! The integer digits are computed least significant first and written in reverse; the fraction
//! digits are written as they are computed. Each digit is written as the specification's
//! `out_digit`: a character for `obase <= 16`, otherwise a separator and the zero-padded decimal
//! value.

use crate::math::{BCNum, pow10_within};
#[cfg(verus_keep_ghost)]
use crate::spec_num::*;
#[cfg(verus_keep_ghost)]
use crate::trusted_bigint::big_view;
use crate::trusted_bigint::{
    big_abs, big_cmp, big_from_usize, big_is_negative, big_is_zero, big_mul, big_mul_add_small,
    big_tdiv, big_to_u64_small, big_trem,
};
use crate::verified_kernels::verified_multi_digit_obase_pad_zeros;
#[cfg(verus_keep_ghost)]
use crate::verified_kernels::{BC_BASE_MAX, BC_SCALE_MAX};
use alloc::string::String;
use alloc::vec::Vec;
#[cfg(verus_keep_ghost)]
use bc_spec::format::*;
#[cfg(verus_keep_ghost)]
use bc_spec::output::{dec_str, hex_digit, out_digit, padded, zeros};
#[cfg(verus_keep_ghost)]
use bc_spec::power::{lemma_pow_add, lemma_pow_positive};
use core::cmp::Ordering;
use num_bigint::BigInt;
#[cfg(not(verus_keep_ghost))]
use verus_builtin_macros::verus;
#[cfg(verus_keep_ghost)]
use vstd::arithmetic::div_mod::lemma_fundamental_div_mod;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

verus! {

/// The digits of `s` in reverse order, as integers.
pub open spec fn rev_ints(s: Seq<u64>) -> Seq<int> {
    Seq::new(s.len(), |i: int| s[s.len() - 1 - i] as int)
}

/// Appends the decimal digits of `x` (`dec_str`).
#[allow(clippy::cast_possible_truncation, reason = "a decimal digit is below 10")]
fn push_dec(out: &mut Vec<u8>, x: u64)
    ensures
        final(out)@ == old(out)@.add(dec_str(x)),
    decreases x,
{
    if x < 10 {
        out.push((48 + x) as u8);
        proof {
            assert(dec_str(x) == seq![(48 + x) as u8]);
            assert(old(out)@.push((48 + x) as u8) =~= old(out)@.add(seq![(48 + x) as u8]));
        }
    } else {
        push_dec(out, x / 10);
        let ghost mid = out@;
        out.push((48 + x % 10) as u8);
        proof {
            assert(old(out)@.add(dec_str(x / 10)).push((48 + x % 10) as u8)
                =~= old(out)@.add(dec_str(x / 10).push((48 + x % 10) as u8)));
        }
    }
}

/// The number of decimal digits of `x` (`dec_str(x).len()`).
fn dec_len(x: u64) -> (r: usize)
    ensures
        r == dec_str(x).len(),
    decreases x,
{
    proof {
        lemma_u64_dec_len(x);
    }
    if x < 10 {
        1
    } else {
        proof {
            lemma_u64_dec_len(x / 10);
        }
        dec_len(x / 10) + 1
    }
}

/// `dec_str(x)` has at most `k` digits when `x < 10^k`.
proof fn lemma_dec_len_bound(x: u64, k: nat)
    requires
        k >= 1,
        x < pow10(k),
    ensures
        dec_str(x).len() <= k,
    decreases x,
{
    if x >= 10 {
        assert(pow10(k) == 10 * pow10((k - 1) as nat));
        assert(k >= 2) by {
            if k == 1 {
                assert(pow10(0) == 1);
            }
        }
        assert((x / 10) < pow10((k - 1) as nat));
        lemma_dec_len_bound(x / 10, (k - 1) as nat);
    }
}

/// A `u64` has at most 20 decimal digits.
proof fn lemma_u64_dec_len(x: u64)
    ensures
        dec_str(x).len() <= 20,
{
    reveal_with_fuel(pow10, 21);
    assert(pow10(20) == 100_000_000_000_000_000_000);
    lemma_dec_len_bound(x, 20);
}

/// Appends one output digit `d < obase` as `out_digit` writes it, with separator `sep`.
#[allow(clippy::cast_possible_truncation, reason = "a digit below 16 plus 55 is below 256")]
fn push_digit(out: &mut Vec<u8>, d: u64, obase: usize, sep: u8)
    requires
        d < obase,
        2 <= obase <= BC_BASE_MAX,
    ensures
        final(out)@ == old(out)@.add(out_digit(d, obase as u32, sep)),
{
    if obase <= 16 {
        let c = if d < 10 { (48 + d) as u8 } else { (55 + d) as u8 };
        out.push(c);
        proof {
            assert(c == hex_digit(d));
            assert(old(out)@.push(c) =~= old(out)@.add(seq![c]));
        }
    } else {
        out.push(sep);
        let width = dec_len((obase - 1) as u64);
        let len = dec_len(d);
        let pad = verified_multi_digit_obase_pad_zeros(width, len);
        let ghost base = out@;
        let mut i: usize = 0;
        while i < pad
            invariant
                i <= pad,
                out@ == base.add(zeros(i as u64)),
            decreases pad - i,
        {
            out.push(48);
            i += 1;
            proof {
                assert(zeros(i as u64) == zeros((i - 1) as u64).push(48u8));
                assert(base.add(zeros((i - 1) as u64)).push(48u8) =~= base.add(zeros(i as u64)));
            }
        }
        push_dec(out, d);
        proof {
            let w = dec_str((obase - 1) as u64).len() as u64;
            assert(padded(d, w) == zeros(pad as u64).add(dec_str(d)));
            assert(old(out)@.push(sep).add(zeros(pad as u64)).add(dec_str(d))
                =~= old(out)@.add(seq![sep].add(padded(d, w))));
        }
    }
}

/// `pow(ob, k) >= pow(2, k)` for `ob >= 2`.
proof fn lemma_pow_ge_pow2(ob: int, k: nat)
    requires
        ob >= 2,
    ensures
        spec_pow_int(ob, k) >= spec_pow_int(2, k),
        spec_pow_int(2, k) >= 1,
    decreases k,
{
    if k > 0 {
        lemma_pow_ge_pow2(ob, (k - 1) as nat);
        let (a, b) = (spec_pow_int(ob, (k - 1) as nat), spec_pow_int(2, (k - 1) as nat));
        assert(ob * a >= 2 * b && 2 * b >= 1) by (nonlinear_arith)
            requires
                ob >= 2,
                a >= b,
                b >= 1;
    }
}

/// The number of fraction digits printed in base `obase` for `scale` digits
/// (`l0_frac_count`): `scale` for base 10, otherwise the smallest `k` with
/// `obase^k >= 10^scale`.
fn frac_digit_count(den: &BigInt, obase: usize, scale: usize) -> (r: usize)
    requires
        big_view(den) == pow10(scale as nat),
        1 <= scale <= BC_SCALE_MAX,
        2 <= obase <= BC_BASE_MAX,
    ensures
        r == l0_frac_count(scale as nat, obase as int),
        r <= 4 * scale,
{
    if obase == 10 {
        return scale;
    }
    let ghost (ob, p, lim) = (obase as int, pow10(scale as nat), (4 * scale + 4) as nat);
    let ob_big = big_from_usize(obase);
    let mut current = big_from_usize(1);
    let mut k: usize = 0;
    proof {
        lemma_pow10_le_pow2(scale as nat);
        assert(spec_pow_int(ob, 0) == 1);
    }
    let mut below = matches!(big_cmp(&current, den), Ordering::Less);
    while below
        invariant
            below == (big_view(&current) < p),
            big_view(&ob_big) == ob,
            2 <= ob,
            big_view(&current) == spec_pow_int(ob, k as nat),
            big_view(den) == p,
            p <= spec_pow_int(2, (4 * scale) as nat),
            k <= 4 * scale,
            1 <= scale <= BC_SCALE_MAX,
            lim == 4 * scale + 4,
            l0_least_k(big_view(&current), p, ob, k as nat, lim) == l0_least_k(1, p, ob, 0, lim),
        decreases 4 * scale - k,
    {
        proof {
            let c = big_view(&current);
            assert(c < p);
            lemma_pow_ge_pow2(ob, k as nat);
            lemma_pow_positive(ob, k as nat);
            if k >= 4 * scale {
                let a = (4 * scale) as nat;
                let b = (k - 4 * scale) as nat;
                lemma_pow_add(2, a, b);
                lemma_pow_ge_pow2(2, b);
                lemma_pow_ge_pow2(2, a);
                assert(a + b == k as nat);
                assert(spec_pow_int(2, k as nat) == spec_pow_int(2, a) * spec_pow_int(2, b));
                assert(spec_pow_int(2, k as nat) >= spec_pow_int(2, a)) by (nonlinear_arith)
                    requires
                        spec_pow_int(2, k as nat) == spec_pow_int(2, a) * spec_pow_int(2, b),
                        spec_pow_int(2, b) >= 1,
                        spec_pow_int(2, a) >= 1;
                assert(c >= p);
            }
            assert(k < 4 * scale);
            assert(c * ob > c) by (nonlinear_arith)
                requires
                    c >= 1,
                    ob >= 2;
            assert(spec_pow_int(ob, (k + 1) as nat) == ob * spec_pow_int(ob, k as nat));
        }
        current = big_mul(&current, &ob_big);
        k += 1;
        below = matches!(big_cmp(&current, den), Ordering::Less);
    }
    k
}

/// Appends the integer digits of `n >= 0` in base `obase` (`l0_int_text` of `l0_int_digits`).
fn push_int_digits(out: &mut Vec<u8>, n: BigInt, obase: usize)
    requires
        big_view(&n) >= 0,
        2 <= obase <= BC_BASE_MAX,
    ensures
        final(out)@ == old(out)@.add(l0_int_text(l0_int_digits(big_view(&n), obase as int), obase as u32)),
{
    let ghost (n0, ob) = (big_view(&n), obase as int);
    let ob_big = big_from_usize(obase);
    let mut rev: Vec<u64> = Vec::new();
    let mut temp = n;
    proof {
        assert(rev_ints(rev@) =~= Seq::<int>::empty());
        assert(l0_int_digits(n0, ob).add(Seq::<int>::empty()) =~= l0_int_digits(n0, ob));
    }
    while !big_is_zero(&temp)
        invariant
            big_view(&ob_big) == ob,
            2 <= obase <= BC_BASE_MAX,
            ob == obase as int,
            big_view(&temp) >= 0,
            l0_int_digits(n0, ob) == l0_int_digits(big_view(&temp), ob).add(rev_ints(rev@)),
            forall|i: int| 0 <= i < rev.len() ==> #[trigger] rev@[i] < obase,
        decreases big_view(&temp),
    {
        let ghost t = big_view(&temp);
        let r = big_trem(&temp, &ob_big);
        let q = big_tdiv(&temp, &ob_big);
        proof {
            lemma_fundamental_div_mod(t, ob);
            assert(0 <= t % ob < ob);
            assert(spec_tdiv(t, ob) == t / ob);
            assert(big_view(&q) == t / ob);
            assert(t - (t / ob) * ob == t % ob) by (nonlinear_arith)
                requires
                    t == ob * (t / ob) + t % ob;
            assert(big_view(&r) == t % ob);
            assert(0 <= t / ob < t) by (nonlinear_arith)
                requires
                    t > 0,
                    ob >= 2;
        }
        let d = big_to_u64_small(&r);
        let ghost old_rev = rev@;
        rev.push(d);
        proof {
            assert(rev_ints(rev@) =~= seq![d as int].add(rev_ints(old_rev)));
            assert(l0_int_digits(t, ob) == l0_int_digits(t / ob, ob).push(t % ob));
            assert(l0_int_digits(t / ob, ob).push(t % ob).add(rev_ints(old_rev))
                =~= l0_int_digits(t / ob, ob).add(seq![d as int].add(rev_ints(old_rev))));
        }
        temp = q;
    }
    proof {
        assert(l0_int_digits(0, ob) == Seq::<int>::empty());
        assert(Seq::<int>::empty().add(rev_ints(rev@)) =~= rev_ints(rev@));
    }
    let ghost ds = rev_ints(rev@);
    let ghost base = out@;
    let mut i: usize = 0;
    proof {
        assert(ds.take(0) =~= Seq::<int>::empty());
        assert(base.add(Seq::<u8>::empty()) =~= base);
    }
    while i < rev.len()
        invariant
            i <= rev.len(),
            ds == rev_ints(rev@),
            ds.len() == rev.len(),
            2 <= obase <= BC_BASE_MAX,
            forall|j: int| 0 <= j < rev.len() ==> #[trigger] rev@[j] < obase,
            out@ == base.add(l0_int_text(ds.take(i as int), obase as u32)),
        decreases rev.len() - i,
    {
        let d = rev[rev.len() - 1 - i];
        push_digit(out, d, obase, 32);
        proof {
            assert(ds[i as int] == d as int);
            assert(ds.take(i as int + 1) =~= ds.take(i as int).push(d as int));
            lemma_int_text_push(ds.take(i as int), d as int, obase as u32);
            let t = l0_int_text(ds.take(i as int), obase as u32);
            assert(base.add(t).add(out_digit(d, obase as u32, 32u8)) =~= base.add(t.add(out_digit(d, obase as u32, 32u8))));
        }
        i += 1;
    }
    proof {
        assert(ds.take(i as int) =~= ds);
    }
}

/// Appends the fraction of `num / 10^scale` (`0 <= num < 10^scale`) as `l0_format` writes it.
fn push_frac_digits(out: &mut Vec<u8>, num: BigInt, den: &BigInt, obase: usize, scale: usize)
    requires
        0 <= big_view(&num) < big_view(den),
        big_view(den) == pow10(scale as nat),
        1 <= scale <= BC_SCALE_MAX,
        2 <= obase <= BC_BASE_MAX,
    ensures
        final(out)@ == old(out)@.add({
            let fd = l0_frac_text(
                l0_frac_digits(big_view(&num), big_view(den), obase as int, l0_frac_count(scale as nat, obase as int)),
                obase as u32,
                true,
            );
            if obase <= 16 { seq![46u8].add(fd) } else { fd }
        }),
{
    let ghost (ob, p, x0) = (obase as int, big_view(den), big_view(&num));
    let k = frac_digit_count(den, obase, scale);
    let ghost fd = l0_frac_text(l0_frac_digits(x0, p, ob, k as nat), obase as u32, true);
    let ghost target = old(out)@.add(if obase <= 16 { seq![46u8].add(fd) } else { fd });
    if obase <= 16 {
        out.push(46);
    }
    proof {
        if obase <= 16 {
            assert(old(out)@.push(46u8).add(fd) =~= target);
        } else {
            assert(old(out)@.add(fd) == target);
        }
    }
    let mut x = num;
    let mut i: usize = 0;
    while i < k
        invariant
            i <= k,
            2 <= obase <= BC_BASE_MAX,
            ob == obase as int,
            big_view(den) == p,
            p >= 1,
            0 <= big_view(&x) < p,
            out@.add(l0_frac_text(l0_frac_digits(big_view(&x), p, ob, (k - i) as nat), obase as u32, i == 0)) == target,
        decreases k - i,
    {
        let ghost xv = big_view(&x);
        let m = big_mul_add_small(x, obase, 0);
        let q = big_tdiv(&m, den);
        let r = big_trem(&m, den);
        let ghost mv = xv * ob;
        proof {
            lemma_fundamental_div_mod(mv, p);
            assert(big_view(&m) == mv);
            assert(mv >= 0) by (nonlinear_arith)
                requires
                    mv == xv * ob,
                    xv >= 0,
                    ob >= 2;
            assert(spec_tdiv(mv, p) == mv / p);
            assert(big_view(&q) == mv / p);
            assert(mv - (mv / p) * p == mv % p) by (nonlinear_arith)
                requires
                    mv == p * (mv / p) + mv % p;
            assert(big_view(&r) == mv % p);
            assert(mv / p < ob) by (nonlinear_arith)
                requires
                    mv == xv * ob,
                    0 <= xv < p,
                    ob >= 2,
                    mv == p * (mv / p) + mv % p,
                    0 <= mv % p;
            assert(0 <= mv / p) by (nonlinear_arith)
                requires
                    mv >= 0,
                    p >= 1;
        }
        let d = big_to_u64_small(&q);
        let sep = if i == 0 { 46u8 } else { 32u8 };
        let ghost before = out@;
        push_digit(out, d, obase, sep);
        proof {
            let n = (k - i) as nat;
            let tail = l0_frac_digits(mv % p, p, ob, (n - 1) as nat);
            let ds = l0_frac_digits(xv, p, ob, n);
            assert(ds == seq![mv / p].add(tail));
            assert(ds[0] == mv / p);
            assert(ds.drop_first() =~= tail);
            let o = out_digit(d, obase as u32, sep);
            let rest = l0_frac_text(tail, obase as u32, false);
            assert(l0_frac_text(ds, obase as u32, i == 0) == o.add(rest));
            assert(before.add(o.add(rest)) =~= before.add(o).add(rest));
        }
        x = r;
        i += 1;
    }
    proof {
        assert(l0_frac_digits(big_view(&x), p, ob, 0) == Seq::<int>::empty());
        assert(out@.add(Seq::<u8>::empty()) =~= out@);
    }
}

impl BCNum {
    /// The output of the value in `obase` (without the newline): `l0_format` of the value.
    pub fn format_bytes(&self, obase: usize) -> (r: Vec<u8>)
        requires
            2 <= obase <= BC_BASE_MAX,
            self.scale <= BC_SCALE_MAX,
        ensures
            r@ == l0_format(self.val(), obase as u32),
    {
        let mut out: Vec<u8> = Vec::new();
        if big_is_zero(&self.coeff) {
            out.push(48);
            proof {
                assert(out@ =~= seq![48u8]);
            }
            return out;
        }
        let negative = big_is_negative(&self.coeff);
        if negative {
            out.push(45);
        }
        let ghost sign = out@;
        let coeff_abs = big_abs(&self.coeff);
        let divisor = pow10_within(self.scale);
        proof {
            lemma_pow10_pos(self.scale as nat);
        }
        let int_part = big_tdiv(&coeff_abs, &divisor);
        let frac_coeff = big_trem(&coeff_abs, &divisor);
        let ghost (a, p) = (big_view(&coeff_abs), pow10(self.scale as nat));
        proof {
            lemma_fundamental_div_mod(a, p);
            assert(spec_tdiv(a, p) == a / p);
            assert(big_view(&int_part) == a / p);
            assert(a - (a / p) * p == a % p) by (nonlinear_arith)
                requires
                    a == p * (a / p) + a % p;
            assert(big_view(&frac_coeff) == a % p);
            assert(0 <= a / p) by (nonlinear_arith)
                requires
                    a >= 0,
                    p >= 1;
        }
        push_int_digits(&mut out, int_part, obase);
        let ghost after_int = out@;
        if self.scale > 0 {
            push_frac_digits(&mut out, frac_coeff, &divisor, obase, self.scale);
        }
        proof {
            let ob = obase as u32;
            let int_str = l0_int_text(l0_int_digits(a / p, ob as int), ob);
            let frac_str = if self.scale == 0 {
                Seq::<u8>::empty()
            } else {
                let fd = l0_frac_text(l0_frac_digits(a % p, p, ob as int, l0_frac_count(self.scale as nat, ob as int)), ob, true);
                if ob <= 16 { seq![46u8].add(fd) } else { fd }
            };
            if self.scale == 0 {
                assert(out@ =~= sign.add(int_str).add(frac_str));
            }
            assert(out@ =~= sign.add(int_str.add(frac_str)));
            if negative {
                assert(sign =~= seq![45u8]);
            } else {
                assert(sign =~= Seq::<u8>::empty());
                assert(Seq::<u8>::empty().add(int_str.add(frac_str)) =~= int_str.add(frac_str));
            }
        }
        out
    }
}

} // verus!

impl BCNum {
    /// Formats the BCNum value as a string in `obase` (2 to `BC_BASE_MAX`): `format_bytes`,
    /// whose bytes are ASCII, as characters.
    pub fn format_obase(&self, obase: usize) -> String {
        self.format_bytes(obase)
            .into_iter()
            .map(char::from)
            .collect()
    }
}
