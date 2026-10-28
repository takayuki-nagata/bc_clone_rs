// SPDX-License-Identifier: MIT

//! The output of a number as a function of its L0 value (`l0_format`), and the proof that the
//! executable `format_num` computes it (`lemma_format_num`).
//!
//! `l0_format` works on integers: the integer part's digits in base `obase` come from repeated
//! division (`l0_int_digits`), the fraction's from repeated multiplication (`l0_frac_digits`),
//! and the number of fraction digits is `scale` for base 10 and otherwise the smallest `k` with
//! `obase^k >= 10^scale` (`l0_frac_count`). Each digit is written as `out_digit` writes it.
//!
//! Consequences: `format_num` depends only on the value of a number (so `R_num` of the
//! refinement proofs can relate numbers by value), and `bc_core`'s `format_obase` can be proved
//! against `l0_format` without the digit sequences of the executable layer.

#[cfg(verus_keep_ghost)]
use crate::convert::{lemma_sig_len_value, sig_len, value_bits};
use crate::num::*;
use crate::output::*;
use crate::power::*;
use crate::spec_num::*;
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------------------------
// Definitions
// ---------------------------------------------------------------------------------------------


/// The digits of `n >= 0` in base `ob >= 2`, most significant first; none for 0.
pub open spec fn l0_int_digits(n: int, ob: int) -> Seq<int>
    decreases n
    via l0_int_digits_decreases
{
    if n <= 0 || ob < 2 {
        seq![]
    } else {
        l0_int_digits(n / ob, ob).push(n % ob)
    }
}

#[verifier::decreases_by]
proof fn l0_int_digits_decreases(n: int, ob: int) {
    if !(n <= 0 || ob < 2) {
        assert(0 <= n / ob < n) by (nonlinear_arith)
            requires
                n > 0,
                ob >= 2;
    }
}

/// `k` fraction digits of `num / den` in base `ob`: multiply by `ob`, take the quotient digit,
/// keep the remainder.
pub open spec fn l0_frac_digits(num: int, den: int, ob: int, k: nat) -> Seq<int>
    decreases k,
{
    if k == 0 {
        seq![]
    } else {
        let m = num * ob;
        seq![m / den].add(l0_frac_digits(m % den, den, ob, (k - 1) as nat))
    }
}

/// The smallest `j >= k` with `cur·ob^(j-k) >= target`, searched up to `limit`.
pub open spec fn l0_least_k(cur: int, target: int, ob: int, k: nat, limit: nat) -> nat
    decreases limit - k,
{
    if k >= limit || cur >= target {
        k
    } else {
        l0_least_k(cur * ob, target, ob, k + 1, limit)
    }
}

/// The number of fraction digits printed in base `ob` for scale `s`.
pub open spec fn l0_frac_count(s: nat, ob: int) -> nat {
    if ob == 10 {
        s
    } else {
        l0_least_k(1, pow10(s), ob, 0, 4 * s + 4)
    }
}

/// The text of integer digits (each preceded by a space for `ob > 16`).
pub open spec fn l0_int_text(ds: Seq<int>, ob: u32) -> Seq<u8>
    decreases ds.len(),
{
    if ds.len() == 0 {
        seq![]
    } else {
        out_digit(ds[0] as u64, ob, 32u8).add(l0_int_text(ds.drop_first(), ob))
    }
}

/// The text of fraction digits; for `ob > 16` the first is preceded by `.` and the others by a
/// space.
pub open spec fn l0_frac_text(ds: Seq<int>, ob: u32, first: bool) -> Seq<u8>
    decreases ds.len(),
{
    if ds.len() == 0 {
        seq![]
    } else {
        out_digit(ds[0] as u64, ob, if first { 46u8 } else { 32u8 }).add(l0_frac_text(ds.drop_first(), ob, false))
    }
}

/// The output of `v` in base `ob` (without the newline).
pub open spec fn l0_format(v: SpecBCNum, ob: u32) -> Seq<u8> {
    if v.coeff == 0 {
        seq![48u8]
    } else {
        let a = if v.coeff >= 0 { v.coeff } else { -v.coeff };
        let p = pow10(v.scale);
        let int_str = l0_int_text(l0_int_digits(a / p, ob as int), ob);
        let frac_str = if v.scale == 0 {
            seq![]
        } else {
            let fd = l0_frac_text(l0_frac_digits(a % p, p, ob as int, l0_frac_count(v.scale, ob as int)), ob, true);
            if ob <= 16 { seq![46u8].add(fd) } else { fd }
        };
        let body = int_str.add(frac_str);
        if v.coeff < 0 { seq![45u8].add(body) } else { body }
    }
}

// ---------------------------------------------------------------------------------------------
// Integer digits
// ---------------------------------------------------------------------------------------------

pub proof fn lemma_int_text_push(ds: Seq<int>, d: int, ob: u32)
    ensures
        l0_int_text(ds.push(d), ob) == l0_int_text(ds, ob).add(out_digit(d as u64, ob, 32u8)),
    decreases ds.len(),
{
    if ds.len() == 0 {
        assert(ds.push(d).drop_first() =~= Seq::<int>::empty());
        assert(l0_int_text(Seq::<int>::empty(), ob) == Seq::<u8>::empty());
        assert(out_digit(d as u64, ob, 32u8).add(Seq::<u8>::empty()) =~= out_digit(d as u64, ob, 32u8));
        assert(Seq::<u8>::empty().add(out_digit(d as u64, ob, 32u8)) =~= out_digit(d as u64, ob, 32u8));
    } else {
        assert(ds.push(d).drop_first() =~= ds.drop_first().push(d));
        lemma_int_text_push(ds.drop_first(), d, ob);
        let h = out_digit(ds[0] as u64, ob, 32u8);
        let t = l0_int_text(ds.drop_first(), ob);
        let o = out_digit(d as u64, ob, 32u8);
        assert(h.add(t.add(o)) =~= h.add(t).add(o));
    }
}

/// A value below `2^k` has at most `k` digits in any base `ob >= 2`.
pub proof fn lemma_int_digits_len(n: int, ob: int, k: nat)
    requires
        0 <= n < spec_pow_int(2, k),
        ob >= 2,
    ensures
        l0_int_digits(n, ob).len() <= k,
    decreases k,
{
    if n > 0 {
        if k == 0 {
            assert(spec_pow_int(2, 0) == 1);
        } else {
            let q = n / ob;
            assert(q <= n / 2) by (nonlinear_arith)
                requires
                    n > 0,
                    ob >= 2,
                    q == n / ob;
            assert(spec_pow_int(2, k) == 2 * spec_pow_int(2, (k - 1) as nat));
            assert(q < spec_pow_int(2, (k - 1) as nat)) by (nonlinear_arith)
                requires
                    q <= n / 2,
                    n < 2 * spec_pow_int(2, (k - 1) as nat),
                    n > 0;
            assert(0 <= q) by (nonlinear_arith)
                requires
                    n > 0,
                    ob >= 2,
                    q == n / ob;
            lemma_int_digits_len(q, ob, (k - 1) as nat);
        }
    }
}

/// `10^len <= 2^(4·len)`.
pub proof fn lemma_pow10_le_pow2(len: nat)
    ensures
        pow10(len) <= spec_pow_int(2, 4 * len),
    decreases len,
{
    if len > 0 {
        lemma_pow10_le_pow2((len - 1) as nat);
        let k = (4 * (len - 1)) as nat;
        assert(4 * len == k + 4);
        reveal_with_fuel(spec_pow_int, 5);
        lemma_pow_add(2, k, 4);
        assert(spec_pow_int(2, 4) == 16);
        assert(pow10(len) == 10 * pow10((len - 1) as nat));
        lemma_pow10_pos((len - 1) as nat);
        assert(10 * pow10((len - 1) as nat) <= spec_pow_int(2, k) * 16) by (nonlinear_arith)
            requires
                pow10((len - 1) as nat) <= spec_pow_int(2, k),
                pow10((len - 1) as nat) >= 1;
    }
}

/// `int_digits` writes the digits of the value of `m`, given enough steps.
pub proof fn lemma_int_digits(m: Seq<u8>, ob: u32, steps: u64, acc: Seq<u8>)
    requires
        wf_mag(m),
        2 <= ob,
        ob < 0x8000_0000,
        steps >= l0_int_digits(mag_val(m), ob as int).len(),
    ensures
        int_digits(m, ob, steps, acc) == l0_int_text(l0_int_digits(mag_val(m), ob as int), ob).add(acc),
    decreases steps,
{
    let n = mag_val(m);
    lemma_is_zero_mag(m);
    lemma_mag_bounds(m);
    if is_zero_mag(m) {
        assert(l0_int_digits(n, ob as int) == Seq::<int>::empty());
        assert(Seq::<u8>::empty().add(acc) =~= acc);
    } else {
        lemma_u64_mag(ob as u64);
        let b = u64_mag(ob as u64);
        lemma_divmod_mag(m, b);
        lemma_div_quot(m, b);
        let qr = divmod_mag(m, b);
        let r = mag_val(qr.1);
        lemma_floor_div_unique(n, ob as int, mag_val(qr.0));
        assert(n % (ob as int) == r) by (nonlinear_arith)
            requires
                n == mag_val(qr.0) * ob + r,
                0 <= r < ob,
                n / (ob as int) == mag_val(qr.0);
        lemma_mag_to_u64(qr.1);
        let d = out_digit(mag_to_u64(qr.1), ob, 32u8);
        assert(steps >= 1);
        lemma_int_digits(qr.0, ob, (steps - 1) as u64, d.add(acc));
        lemma_int_text_push(l0_int_digits(n / (ob as int), ob as int), n % (ob as int), ob);
        let t = l0_int_text(l0_int_digits(n / (ob as int), ob as int), ob);
        assert(t.add(d.add(acc)) =~= t.add(d).add(acc));
    }
}

// ---------------------------------------------------------------------------------------------
// Fraction digits
// ---------------------------------------------------------------------------------------------

pub proof fn lemma_frac_count(cur: Seq<u8>, target: Seq<u8>, ob: u32, k: u64, limit: u64)
    requires
        wf_mag(cur),
        wf_mag(target),
    ensures
        frac_count(cur, target, ob, k, limit) as nat
            == l0_least_k(mag_val(cur), mag_val(target), ob as int, k as nat, limit as nat),
    decreases limit - k,
{
    lemma_cmp_mag(cur, target);
    if k < limit && cmp_mag(cur, target) < 0 {
        lemma_u64_mag(ob as u64);
        lemma_mul_mag(cur, u64_mag(ob as u64));
        lemma_frac_count(mul_mag(cur, u64_mag(ob as u64)), target, ob, (k + 1) as u64, limit);
    }
}

pub proof fn lemma_frac_digits(num: Seq<u8>, den: Seq<u8>, ob: u32, n: u64, first: bool, acc: Seq<u8>)
    requires
        wf_mag(num),
        wf_mag(den),
        0 <= mag_val(num) < mag_val(den),
        2 <= ob,
        ob < 0x8000_0000,
    ensures
        frac_digits(num, den, ob, n, first, acc)
            == acc.add(l0_frac_text(l0_frac_digits(mag_val(num), mag_val(den), ob as int, n as nat), ob, first)),
    decreases n,
{
    let (x, y) = (mag_val(num), mag_val(den));
    if n == 0 {
        assert(acc.add(Seq::<u8>::empty()) =~= acc);
    } else {
        lemma_u64_mag(ob as u64);
        lemma_mul_mag(num, u64_mag(ob as u64));
        let m = mul_mag(num, u64_mag(ob as u64));
        lemma_divmod_mag(m, den);
        lemma_div_quot(m, den);
        let qr = divmod_mag(m, den);
        let mv = x * ob;
        assert(x * (ob as int) < y * (ob as int)) by (nonlinear_arith)
            requires
                x < y,
                ob >= 2;
        assert(mag_val(qr.0) < ob) by (nonlinear_arith)
            requires
                mv == mag_val(qr.0) * y + mag_val(qr.1),
                mv == x * ob,
                mv < y * (ob as int),
                0 <= mag_val(qr.1),
                y > 0,
                mag_val(qr.0) >= 0;
        lemma_floor_div_unique(mv, y, mag_val(qr.0));
        assert(mv % y == mag_val(qr.1)) by (nonlinear_arith)
            requires
                mv == mag_val(qr.0) * y + mag_val(qr.1),
                0 <= mag_val(qr.1) < y,
                mv / y == mag_val(qr.0);
        lemma_mag_bounds(qr.0);
        lemma_mag_to_u64(qr.0);
        let d = out_digit(mag_to_u64(qr.0), ob, if first { 46u8 } else { 32u8 });
        lemma_frac_digits(qr.1, den, ob, (n - 1) as u64, false, acc.add(d));
        let tail = l0_frac_digits(mv % y, y, ob as int, (n - 1) as nat);
        let ds = l0_frac_digits(x, y, ob as int, n as nat);
        assert(ds == seq![mv / y].add(tail));
        assert(ds[0] == mv / y);
        assert(ds.drop_first() =~= tail);
        assert(mag_to_u64(qr.0) == (mv / y) as u64);
        assert(l0_frac_text(ds, ob, first) == d.add(l0_frac_text(tail, ob, false)));
        let rest = l0_frac_text(tail, ob, false);
        assert(acc.add(d).add(rest) =~= acc.add(d.add(rest)));
    }
}

/// `low_digits(m, k)` is `m mod 10^k`.
pub proof fn lemma_low_digits(m: Seq<u8>, k: u32)
    requires
        wf_mag(m),
    ensures
        mag_val(low_digits(m, k)) == mag_val(m) % pow10(k as nat),
        wf_mag(low_digits(m, k)),
    decreases k,
{
    lemma_split(m);
    lemma_pow10_pos(k as nat);
    if k == 0 || m.len() == 0 {
        lemma_mag_bounds(m);
        assert(mag_val(Seq::<u8>::empty()) == 0);
        if k == 0 {
            assert(pow10(0) == 1);
            assert(mag_val(m) % 1 == 0);
        } else {
            assert(mag_val(m) == 0);
            assert(0int % pow10(k as nat) == 0) by (nonlinear_arith)
                requires
                    pow10(k as nat) >= 1;
        }
    } else {
        let rest = m.drop_first();
        let k1 = (k - 1) as u32;
        lemma_low_digits(rest, k1);
        let low = low_digits(rest, k1);
        lemma_cons_digit(m[0], low);
        let t = seq![m[0]].add(low);
        assert forall|i: int| 0 <= i < t.len() implies t[i] <= 9 by {
            if i > 0 {
                assert(t[i] == low[i - 1]);
            }
        }
        let p1 = pow10(k1 as nat);
        lemma_pow10_pos(k1 as nat);
        assert(pow10(k as nat) == 10 * p1);
        let (d, r) = (m[0] as int, mag_val(rest));
        let q = r / p1;
        let lo = r % p1;
        assert(r == q * p1 + lo && 0 <= lo < p1) by (nonlinear_arith)
            requires
                p1 >= 1,
                q == r / p1,
                lo == r % p1;
        assert(mag_val(m) == d + 10 * r);
        assert(0 <= d + 10 * lo < 10 * p1) by (nonlinear_arith)
            requires
                0 <= d <= 9,
                0 <= lo < p1;
        let v = mag_val(m);
        assert(v == q * (10 * p1) + (d + 10 * lo)) by (nonlinear_arith)
            requires
                v == d + 10 * r,
                r == q * p1 + lo;
        lemma_floor_div_unique(v, 10 * p1, q);
        assert(v % (10 * p1) == d + 10 * lo) by (nonlinear_arith)
            requires
                v == q * (10 * p1) + (d + 10 * lo),
                v / (10 * p1) == q,
                10 * p1 >= 1;
    }
}

// ---------------------------------------------------------------------------------------------
// The output of a number
// ---------------------------------------------------------------------------------------------

/// `format_num` writes `l0_format` of the value, for every base `2..=BC_BASE_MAX`.
pub proof fn lemma_format_num(v: Num, obase: u32)
    requires
        wf_num(v),
        2 <= obase <= 2147483647,
        scale_ok(v.scale),
        mag_val(v.mag) < spec_pow_int(2, value_bits()),
    ensures
        format_num(v, obase) == l0_format(to_l0(v), obase),
{
    let c = num_coeff(v);
    let mv = mag_val(v.mag);
    lemma_is_zero_mag(v.mag);
    lemma_mag_bounds(v.mag);
    if !is_zero_mag(v.mag) {
        let s = v.scale;
        let p = pow10(s as nat);
        lemma_pow10_pos(s as nat);
        assert((if c >= 0 { c } else { -c }) == mv);
        // Integer part.
        let ip = drop_mag(v.mag, s);
        lemma_drop_mag(v.mag, s);
        assert(mag_val(ip) <= mv) by (nonlinear_arith)
            requires
                mag_val(ip) == mv / p,
                mv >= 0,
                p >= 1;
        lemma_mag_bounds(ip);
        lemma_sig_len_value(ip);
        let sig = sig_len(ip);
        let steps = if sig < 0x1000_0000_0000_0000u64 { (4 * sig + 4) as u64 } else { 0xffff_ffff_ffff_ffffu64 };
        assert(sig < 0x1000_0000_0000_0000u64 || sig == value_bits());
        if mag_val(ip) > 0 {
            // ip < 10^sig <= 2^(4 sig).
            lemma_pow10_le_pow2(sig as nat);
            lemma_int_digits_len(mag_val(ip), obase as int, (4 * sig) as nat);
        } else {
            assert(l0_int_digits(mag_val(ip), obase as int) == Seq::<int>::empty());
        }
        if sig == value_bits() {
            lemma_int_digits_len(mag_val(ip), obase as int, value_bits());
        }
        assert(steps >= l0_int_digits(mag_val(ip), obase as int).len());
        lemma_int_digits(ip, obase, steps, seq![]);
        assert(l0_int_text(l0_int_digits(mag_val(ip), obase as int), obase).add(Seq::<u8>::empty())
            =~= l0_int_text(l0_int_digits(mag_val(ip), obase as int), obase));
        // Fraction.
        if s != 0 {
            lemma_one_mag();
            lemma_shift_mag(seq![1u8], s);
            let den = shift_mag(seq![1u8], s);
            assert(mag_val(den) == p);
            lemma_low_digits(v.mag, s);
            let low = low_digits(v.mag, s);
            assert(0 <= mag_val(low) < p) by (nonlinear_arith)
                requires
                    mag_val(low) == mv % p,
                    p >= 1;
            if obase != 10 {
                lemma_frac_count(seq![1u8], den, obase, 0u64, (4 * (s as u64) + 4) as u64);
            }
            let n = if obase == 10 { s as u64 } else { frac_count(seq![1u8], den, obase, 0u64, (4 * (s as u64) + 4) as u64) };
            assert(n as nat == l0_frac_count(s as nat, obase as int));
            lemma_frac_digits(low, den, obase, n, true, seq![]);
            let fd = l0_frac_text(l0_frac_digits(mv % p, p, obase as int, n as nat), obase, true);
            assert(Seq::<u8>::empty().add(fd) =~= fd);
        }
    }
}

/// `format_num` gives the same text for numbers with the same value.
pub proof fn lemma_format_num_congruent(v: Num, w: Num, obase: u32)
    requires
        wf_num(v),
        wf_num(w),
        to_l0(v) == to_l0(w),
        2 <= obase <= 2147483647,
        scale_ok(v.scale),
        mag_val(v.mag) < spec_pow_int(2, value_bits()),
    ensures
        format_num(v, obase) == format_num(w, obase),
{
    crate::values::lemma_same_value(v, w);
    lemma_format_num(v, obase);
    lemma_format_num(w, obase);
}

} // verus!
