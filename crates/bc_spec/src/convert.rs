// SPDX-License-Identifier: MIT

//! `length`, `scale` and the value of a numeric constant under `ibase` (L1), with proofs against
//! the integer definitions (L0).

use crate::num::*;
use crate::power::*;
use crate::spec_num::*;
use vstd::contrib::exec_spec::*;
use vstd::prelude::*;

verus! {

exec_spec_verified! {

/// The number of significant digits of `m` (0 for zero).
pub open spec fn sig_len(m: Seq<u8>) -> u64
    decreases m.len()
{
    if m.len() == 0 {
        0u64
    } else {
        let r = sig_len(m.drop_first());
        if r > 0 {
            if r < 0xffff_ffff_ffff_ffffu64 { (r + 1) as u64 } else { r }
        } else if m[0] != 0 {
            1u64
        } else {
            0u64
        }
    }
}

/// `length(a)` (`BCNum::length`): the significant digits of the integer part plus the scale,
/// or `max(scale, 1)` when the integer part is zero.
pub open spec fn num_length(a: Num) -> Num {
    let k = sig_len(drop_mag(a.mag, a.scale));
    let v = if k == 0 {
        if a.scale >= 1 { a.scale as u64 } else { 1u64 }
    } else if k <= 0x1000_0000_0000_0000u64 {
        (k + a.scale as u64) as u64
    } else {
        // Not reached for values below 2^value_bits() (`lemma_num_length`).
        0u64
    };
    Num { neg: false, mag: u64_mag(v), scale: 0u32 }
}

/// `scale(a)`.
pub open spec fn num_scale(a: Num) -> Num {
    Num { neg: false, mag: u64_mag(a.scale as u64), scale: 0u32 }
}

/// The digit values of a constant after the `ibase` rule: in a multi-digit constant a digit
/// `>= ibase` counts as `ibase - 1` (`docs/COMPATIBILITY.md` §3.3).
pub open spec fn clamp_digits(ds: Seq<u8>, ib: u8, multi: bool) -> Seq<u8>
    decreases ds.len()
{
    if ds.len() == 0 {
        seq![]
    } else {
        let d = if multi && ds[0] >= ib && ib >= 1 { (ib - 1) as u8 } else { ds[0] };
        seq![d].add(clamp_digits(ds.drop_first(), ib, multi))
    }
}

/// `acc · ib^len(ds) + value(ds)` for big-endian digits `ds` in base `ib`.
pub open spec fn horner_mag(acc: Seq<u8>, ds: Seq<u8>, ib: u8) -> Seq<u8>
    decreases ds.len()
{
    if ds.len() == 0 {
        acc
    } else {
        horner_mag(add_mag(scale_mag(acc, ib), u64_mag(ds[0] as u64), 0u8), ds.drop_first(), ib)
    }
}

/// The value of a constant with integer digits `ds` and fraction digits `fs` (digit values,
/// most significant first) under `ibase = ib` (`BCNum::from_string`): the fraction is
/// converted exactly and truncated to `len(fs)` decimal digits.
pub open spec fn num_from_digits(ds: Seq<u8>, fs: Seq<u8>, ib: u8) -> Num {
    let multi = ds.len() > 1 || fs.len() > 1 || (ds.len() == 1 && fs.len() == 1);
    let iv = horner_mag(seq![], clamp_digits(ds, ib, multi), ib);
    if fs.len() == 0 {
        Num { neg: false, mag: iv, scale: 0u32 }
    } else {
        let f = if fs.len() <= 0xffff_ffffusize { fs.len() as u32 } else { 0u32 };
        let den = pow_mag(u64_mag(ib as u64), u64_mag(f as u64));
        let fnum = horner_mag(seq![], clamp_digits(fs, ib, multi), ib);
        let num = shift_mag(add_mag(mul_mag(iv, den), fnum, 0u8), f);
        Num { neg: false, mag: divmod_mag(num, den).0, scale: f }
    }
}

} // exec_spec_verified!

pub proof fn lemma_sig_len(m: Seq<u8>)
    requires wf_mag(m), m.len() <= 0xffff_ffff,
    ensures
        sig_len(m) <= m.len(),
        mag_val(m) == 0 <==> sig_len(m) == 0,
        mag_val(m) > 0 ==> is_digit_count(mag_val(m), sig_len(m) as nat),
    decreases m.len()
{
    lemma_split(m);
    lemma_mag_bounds(m);
    if m.len() > 0 {
        let rm = m.drop_first();
        lemma_sig_len(rm);
        lemma_mag_bounds(rm);
        let r = sig_len(rm);
        if r > 0 {
            let k = r as nat;
            assert(pow10(k) == 10 * pow10((k - 1) as nat));
            assert(pow10((k + 1) as nat) == 10 * pow10(k));
            assert(((k + 1) - 1) as nat == k);
        } else {
            assert(pow10(1) == 10 * pow10(0));
        }
    }
}

/// The size of the values the proofs about digit counts cover: below `2^value_bits()` (`2^60`
/// bits, 128 PiB), which every number that fits in memory satisfies.
pub open spec fn value_bits() -> nat {
    0x1000_0000_0000_0000
}

/// `2^k <= 10^k`.
pub proof fn lemma_pow2_le_pow10(k: nat)
    ensures
        spec_pow_int(2, k) <= pow10(k),
        spec_pow_int(2, k) >= 1,
    decreases k,
{
    if k > 0 {
        lemma_pow2_le_pow10((k - 1) as nat);
        assert(pow10(k) == 10 * pow10((k - 1) as nat));
        assert(spec_pow_int(2, k) == 2 * spec_pow_int(2, (k - 1) as nat));
    }
}

/// `2^a < 2^b` implies `a < b`.
pub proof fn lemma_pow2_lt(a: nat, b: nat)
    requires
        spec_pow_int(2, a) < spec_pow_int(2, b),
    ensures
        a < b,
{
    if a >= b {
        lemma_pow_add(2, b, (a - b) as nat);
        assert(b + (a - b) as nat == a);
        lemma_pow2_le_pow10(b);
        lemma_pow2_le_pow10((a - b) as nat);
        assert(spec_pow_int(2, b) * spec_pow_int(2, (a - b) as nat) >= spec_pow_int(2, b)) by (nonlinear_arith)
            requires
                spec_pow_int(2, (a - b) as nat) >= 1,
                spec_pow_int(2, b) >= 1;
    }
}

/// `sig_len` counts the digits of any value below `2^value_bits()`, whatever the length of the
/// digit sequence (leading zeros do not count).
pub proof fn lemma_sig_len_value(m: Seq<u8>)
    requires
        wf_mag(m),
        mag_val(m) < spec_pow_int(2, value_bits()),
    ensures
        mag_val(m) == 0 <==> sig_len(m) == 0,
        mag_val(m) > 0 ==> is_digit_count(mag_val(m), sig_len(m) as nat),
        sig_len(m) <= value_bits(),
    decreases m.len(),
{
    lemma_split(m);
    lemma_mag_bounds(m);
    if m.len() > 0 {
        let rm = m.drop_first();
        lemma_mag_bounds(rm);
        assert(mag_val(rm) <= mag_val(m));
        lemma_sig_len_value(rm);
        let r = sig_len(rm);
        if r > 0 {
            let k = r as nat;
            assert(r < 0xffff_ffff_ffff_ffffu64);
            assert(pow10(k) == 10 * pow10((k - 1) as nat));
            assert(pow10((k + 1) as nat) == 10 * pow10(k));
            assert(((k + 1) - 1) as nat == k);
            // The value is at least 10^k >= 2^k, so k < value_bits().
            lemma_pow2_le_pow10(k);
            assert(pow10(k) <= mag_val(m));
            lemma_pow2_lt(k, value_bits());
        } else {
            assert(pow10(1) == 10 * pow10(0));
        }
    }
}

pub proof fn lemma_num_length(a: Num)
    requires wf_num(a), scale_ok(a.scale), mag_val(a.mag) < spec_pow_int(2, value_bits()),
    ensures
        ({
            let r = num_length(a);
            let ip = mag_val(a.mag) / pow10(a.scale as nat);
            &&& wf_num(r) && !r.neg && r.scale == 0
            &&& ip == 0 ==> mag_val(r.mag) == (if a.scale >= 1 { a.scale as int } else { 1 })
            &&& ip > 0 ==> mag_val(r.mag) > a.scale
                && is_digit_count(ip, (mag_val(r.mag) - a.scale) as nat)
        }),
{
    let d = drop_mag(a.mag, a.scale);
    lemma_drop_mag(a.mag, a.scale);
    lemma_pow10_pos(a.scale as nat);
    lemma_mag_bounds(a.mag);
    assert(mag_val(d) <= mag_val(a.mag)) by (nonlinear_arith)
        requires
            mag_val(d) == mag_val(a.mag) / pow10(a.scale as nat),
            mag_val(a.mag) >= 0,
            pow10(a.scale as nat) >= 1;
    lemma_sig_len_value(d);
    let k = sig_len(d);
    let v = if k == 0 {
        if a.scale >= 1 { a.scale as u64 } else { 1u64 }
    } else {
        (k + a.scale as u64) as u64
    };
    assert(k <= 0x1000_0000_0000_0000u64);
    lemma_u64_mag(v);
}

pub proof fn lemma_drop_len(a: Seq<u8>, k: u32)
    ensures drop_mag(a, k).len() <= a.len(),
    decreases k
{
    if k > 0 && a.len() > 0 {
        lemma_drop_len(a.drop_first(), (k - 1) as u32);
    }
}

pub proof fn lemma_num_scale(a: Num)
    ensures mag_val(num_scale(a).mag) == a.scale, wf_num(num_scale(a)), num_scale(a).scale == 0,
{
    lemma_u64_mag(a.scale as u64);
}

pub proof fn lemma_horner_mag(acc: Seq<u8>, ds: Seq<u8>, ib: u8)
    requires wf_mag(acc),
    ensures
        mag_val(horner_mag(acc, ds, ib)) == spec_horner(mag_val(acc), ds, ib as int),
        wf_mag(horner_mag(acc, ds, ib)),
    decreases ds.len()
{
    if ds.len() > 0 {
        lemma_scale_mag(acc, ib);
        lemma_u64_mag(ds[0] as u64);
        lemma_add_mag(scale_mag(acc, ib), u64_mag(ds[0] as u64), 0u8);
        lemma_horner_mag(add_mag(scale_mag(acc, ib), u64_mag(ds[0] as u64), 0u8), ds.drop_first(), ib);
    }
}

pub proof fn lemma_horner_nonneg(acc: int, ds: Seq<u8>, base: int)
    requires acc >= 0, base >= 0,
    ensures spec_horner(acc, ds, base) >= 0,
    decreases ds.len()
{
    if ds.len() > 0 {
        assert(acc * base >= 0) by (nonlinear_arith) requires acc >= 0, base >= 0;
        lemma_horner_nonneg(acc * base + ds[0], ds.drop_first(), base);
    }
}

pub proof fn lemma_num_from_digits(ds: Seq<u8>, fs: Seq<u8>, ib: u8)
    requires 2 <= ib <= 16, fs.len() <= 1_000_000_000,
    ensures
        ({
            let multi = ds.len() + fs.len() > 1;
            let iv = spec_horner(0, clamp_digits(ds, ib, multi), ib as int);
            let fv = spec_horner(0, clamp_digits(fs, ib, multi), ib as int);
            let f = fs.len();
            let den = spec_pow_int(ib as int, f);
            let r = num_from_digits(ds, fs, ib);
            &&& wf_num(r) && !r.neg && r.scale == f
            &&& mag_val(r.mag) == if f == 0 { iv } else { (iv * den + fv) * pow10(f) / den }
        }),
{
    let multi = ds.len() + fs.len() > 1;
    assert(multi == (ds.len() > 1 || fs.len() > 1 || (ds.len() == 1 && fs.len() == 1)));
    lemma_cons_digit(0u8, seq![]);
    assert(mag_val(Seq::<u8>::empty()) == 0);
    let cd = clamp_digits(ds, ib, multi);
    lemma_horner_mag(seq![], cd, ib);
    let iv = horner_mag(seq![], cd, ib);
    if fs.len() > 0 {
        let f = fs.len() as u32;
        lemma_u64_mag(ib as u64);
        lemma_u64_mag(f as u64);
        lemma_pow_mag(u64_mag(ib as u64), u64_mag(f as u64));
        let den = pow_mag(u64_mag(ib as u64), u64_mag(f as u64));
        lemma_pow_positive(ib as int, f as nat);
        let cf = clamp_digits(fs, ib, multi);
        lemma_horner_mag(seq![], cf, ib);
        let fnum = horner_mag(seq![], cf, ib);
        lemma_mul_mag(iv, den);
        lemma_add_mag(mul_mag(iv, den), fnum, 0u8);
        lemma_shift_mag(add_mag(mul_mag(iv, den), fnum, 0u8), f);
        lemma_div_quot(shift_mag(add_mag(mul_mag(iv, den), fnum, 0u8), f), den);
    }
}

} // verus!
