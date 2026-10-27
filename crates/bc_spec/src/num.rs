// SPDX-License-Identifier: MIT

//! Executable (L1) arithmetic on decimal digit sequences, with proofs that it computes the
//! integer (L0) operations of `spec_num.rs`.
//!
//! A magnitude is a little-endian sequence of decimal digits (`mag[0]` is the units digit);
//! `mag_val` is the natural number it denotes. Leading zeros (at the end of the sequence) are
//! allowed everywhere, so no operation needs a normalized input.
//!
//! A number (`Num`) is a sign, a magnitude and a scale, denoting `±mag_val(mag) × 10^-scale`
//! like `BCNum { coeff, scale }`; `to_l0` maps it to `SpecBCNum`. Constructors keep zero
//! non-negative, as `BigInt` has no negative zero.

use crate::spec_num::*;
use vstd::contrib::exec_spec::*;
use vstd::prelude::*;

verus! {

exec_spec_verified! {

/// `a + b + carry`.
pub open spec fn add_mag(a: Seq<u8>, b: Seq<u8>, carry: u8) -> Seq<u8>
    decreases a.len() + b.len()
{
    if a.len() == 0 && b.len() == 0 {
        if carry == 0 { seq![] } else { seq![carry] }
    } else {
        let x = if a.len() > 0 { a[0] } else { 0u8 };
        let y = if b.len() > 0 { b[0] } else { 0u8 };
        let s = (x as u32 + y as u32 + carry as u32) as u32;
        let ra = if a.len() > 0 { a.drop_first() } else { a };
        let rb = if b.len() > 0 { b.drop_first() } else { b };
        seq![(s % 10) as u8].add(add_mag(ra, rb, (s / 10) as u8))
    }
}

/// `a - b - borrow` as digits, padded to the longer length, and the final borrow: when
/// `a < b + borrow` the digits denote `10^len + a - b - borrow` and the borrow is 1.
pub open spec fn sub_mag(a: Seq<u8>, b: Seq<u8>, borrow: u8) -> (Seq<u8>, u8)
    decreases a.len() + b.len()
{
    if a.len() == 0 && b.len() == 0 {
        (seq![], borrow)
    } else {
        let x = if a.len() > 0 { a[0] } else { 0u8 };
        let y = if b.len() > 0 { b[0] } else { 0u8 };
        let ra = if a.len() > 0 { a.drop_first() } else { a };
        let rb = if b.len() > 0 { b.drop_first() } else { b };
        let t = (y as u32 + borrow as u32) as u32;
        if (x as u32) >= t {
            let rest = sub_mag(ra, rb, 0u8);
            (seq![(x as u32 - t) as u8].add(rest.0), rest.1)
        } else {
            let rest = sub_mag(ra, rb, 1u8);
            // `x + 10 >= t` for digit inputs; the guard only keeps the exec code overflow-free.
            let d = if x as u32 + 10 >= t { (x as u32 + 10 - t) as u8 } else { 0u8 };
            (seq![d].add(rest.0), rest.1)
        }
    }
}

/// `a * k` by repeated addition (`exec_spec_verified!` cannot prove `*` on machine integers).
pub open spec fn scale_mag(a: Seq<u8>, k: u8) -> Seq<u8>
    decreases k
{
    if k == 0 { seq![] } else { add_mag(a, scale_mag(a, (k - 1) as u8), 0u8) }
}

/// `a * b`, schoolbook over the digits of `b`.
pub open spec fn mul_mag(a: Seq<u8>, b: Seq<u8>) -> Seq<u8>
    decreases b.len()
{
    if b.len() == 0 {
        seq![]
    } else {
        add_mag(scale_mag(a, b[0]), seq![0u8].add(mul_mag(a, b.drop_first())), 0u8)
    }
}

/// Whether every digit is zero.
pub open spec fn is_zero_mag(a: Seq<u8>) -> bool
    decreases a.len()
{
    if a.len() == 0 { true } else if a[0] != 0 { false } else { is_zero_mag(a.drop_first()) }
}

/// The sign of `a - b`: -1, 0 or 1.
pub open spec fn cmp_mag(a: Seq<u8>, b: Seq<u8>) -> i8 {
    let d = sub_mag(a, b, 0u8);
    if d.1 != 0 { -1i8 } else if is_zero_mag(d.0) { 0i8 } else { 1i8 }
}

/// Subtracts `b` from `r` while `r >= b`, at most `9 - k` more times; returns the count
/// (starting at `k`) and the remainder.
pub open spec fn fit_mag(r: Seq<u8>, b: Seq<u8>, k: u8) -> (u8, Seq<u8>)
    decreases 9 - k when k <= 9
{
    if k < 9 && cmp_mag(r, b) >= 0 { fit_mag(sub_mag(r, b, 0u8).0, b, (k + 1) as u8) } else { (k, r) }
}

/// Quotient and remainder of `a / b` for `b > 0` (long division; the recursion reaches the
/// most significant digit first).
pub open spec fn divmod_mag(a: Seq<u8>, b: Seq<u8>) -> (Seq<u8>, Seq<u8>)
    decreases a.len()
{
    if a.len() == 0 {
        (seq![], seq![])
    } else {
        let qr = divmod_mag(a.drop_first(), b);
        let f = fit_mag(seq![a[0]].add(qr.1), b, 0u8);
        (seq![f.0].add(qr.0), f.1)
    }
}

/// `a × 10^k`.
pub open spec fn shift_mag(a: Seq<u8>, k: u32) -> Seq<u8>
    decreases k
{
    if k == 0 { a } else { seq![0u8].add(shift_mag(a, (k - 1) as u32)) }
}

/// `a / 10^k` (dropping the `k` lowest digits).
pub open spec fn drop_mag(a: Seq<u8>, k: u32) -> Seq<u8>
    decreases k
{
    if k == 0 || a.len() == 0 { a } else { drop_mag(a.drop_first(), (k - 1) as u32) }
}

/// A `bc` number: `±mag × 10^-scale`.
pub struct Num {
    pub neg: bool,
    pub mag: Seq<u8>,
    pub scale: u32,
}

/// Builds a number, making zero non-negative.
pub open spec fn mk_num(neg: bool, mag: Seq<u8>, scale: u32) -> Num {
    Num { neg: neg && !is_zero_mag(mag), mag: mag, scale: scale }
}

/// `sa·a + sb·b` for signs `sa`, `sb` (true = negative), as a sign and a magnitude.
pub open spec fn signed_add(na: bool, a: Seq<u8>, nb: bool, b: Seq<u8>) -> (bool, Seq<u8>) {
    if na == nb {
        (na, add_mag(a, b, 0u8))
    } else if cmp_mag(a, b) >= 0 {
        (na, sub_mag(a, b, 0u8).0)
    } else {
        (nb, sub_mag(b, a, 0u8).0)
    }
}

/// `a + b` (`BCNum::add`).
pub open spec fn num_add(a: Num, b: Num) -> Num {
    let sr = if a.scale >= b.scale { a.scale } else { b.scale };
    let r = signed_add(
        a.neg, shift_mag(a.mag, (sr - a.scale) as u32),
        b.neg, shift_mag(b.mag, (sr - b.scale) as u32),
    );
    mk_num(r.0, r.1, sr)
}

/// `a - b` (`BCNum::sub`).
pub open spec fn num_sub(a: Num, b: Num) -> Num {
    num_add(a, Num { neg: !b.neg, mag: b.mag, scale: b.scale })
}

/// The POSIX multiplication scale `min(a + b, max(scale, a, b))`.
pub open spec fn mul_scale(a: u32, b: u32, gs: u32) -> u32 {
    let max_ab = if a >= b { a } else { b };
    let max_all = if gs >= max_ab { gs } else { max_ab };
    if a as u64 + b as u64 <= max_all as u64 { (a as u64 + b as u64) as u32 } else { max_all }
}

/// `a * b` at `scale = gs` (`BCNum::mul`).
pub open spec fn num_mul(a: Num, b: Num, gs: u32) -> Num {
    let sr = mul_scale(a.scale, b.scale, gs);
    let diff = (a.scale as u64 + b.scale as u64 - sr as u64) as u32;
    mk_num(a.neg != b.neg, drop_mag(mul_mag(a.mag, b.mag), diff), sr)
}

/// `a / b` at `scale = gs` for `b != 0` (`BCNum::try_div`).
pub open spec fn num_div(a: Num, b: Num, gs: u32) -> Num {
    let q = if b.scale as u64 + gs as u64 >= a.scale as u64 {
        divmod_mag(shift_mag(a.mag, (b.scale as u64 + gs as u64 - a.scale as u64) as u32), b.mag).0
    } else {
        divmod_mag(a.mag, shift_mag(b.mag, (a.scale as u64 - b.scale as u64 - gs as u64) as u32)).0
    };
    mk_num(a.neg != b.neg, q, gs)
}

/// `a % b` at `scale = gs` for `b != 0` and `gs + scale(b)` within `u32` (`BCNum::try_mod_op`).
pub open spec fn num_mod(a: Num, b: Num, gs: u32) -> Num {
    let q = num_div(a, b, gs);
    num_sub(a, Num {
        neg: q.neg != b.neg,
        mag: mul_mag(q.mag, b.mag),
        scale: if gs as u64 + b.scale as u64 <= 0xffff_ffffu64 { (gs as u64 + b.scale as u64) as u32 } else { 0u32 },
    })
}

/// The sign of `a - b` (relational operators).
pub open spec fn num_cmp(a: Num, b: Num) -> i8 {
    let d = num_sub(a, b);
    if is_zero_mag(d.mag) { 0i8 } else if d.neg { -1i8 } else { 1i8 }
}

} // exec_spec_verified!

/// The natural number denoted by little-endian decimal digits.
pub open spec fn mag_val(s: Seq<u8>) -> int
    decreases s.len()
{
    if s.len() == 0 { 0 } else { s[0] as int + 10 * mag_val(s.drop_first()) }
}

/// Every element is a decimal digit.
pub open spec fn wf_mag(s: Seq<u8>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> s[i] <= 9
}

/// The longer of two lengths.
pub open spec fn max_len(a: Seq<u8>, b: Seq<u8>) -> nat {
    if a.len() >= b.len() { a.len() } else { b.len() }
}


pub proof fn lemma_cons_digit(d: u8, r: Seq<u8>)
    ensures
        mag_val(seq![d].add(r)) == d as int + 10 * mag_val(r),
        seq![d].add(r).len() == r.len() + 1,
{
    let s = seq![d].add(r);
    assert(s.drop_first() =~= r);
    assert(s[0] == d);
}

pub proof fn lemma_split(a: Seq<u8>)
    requires wf_mag(a),
    ensures
        a.len() > 0 ==> mag_val(a) == a[0] as int + 10 * mag_val(a.drop_first()),
        a.len() > 0 ==> wf_mag(a.drop_first()),
        a.len() == 0 ==> mag_val(a) == 0,
{
    if a.len() > 0 {
        assert forall|i: int| 0 <= i < a.drop_first().len() implies a.drop_first()[i] <= 9 by {
            assert(a.drop_first()[i] == a[i + 1]);
        }
    }
}

pub proof fn lemma_add_mag(a: Seq<u8>, b: Seq<u8>, carry: u8)
    requires wf_mag(a), wf_mag(b), carry <= 1,
    ensures
        mag_val(add_mag(a, b, carry)) == mag_val(a) + mag_val(b) + carry,
        wf_mag(add_mag(a, b, carry)),
    decreases a.len() + b.len()
{
    if a.len() == 0 && b.len() == 0 {
        if carry != 0 { lemma_cons_digit(carry, seq![]); }
    } else {
        let x = if a.len() > 0 { a[0] } else { 0u8 };
        let y = if b.len() > 0 { b[0] } else { 0u8 };
        let s = (x as u32 + y as u32 + carry as u32) as u32;
        let ra = if a.len() > 0 { a.drop_first() } else { a };
        let rb = if b.len() > 0 { b.drop_first() } else { b };
        lemma_split(a);
        lemma_split(b);
        assert(x <= 9 && y <= 9);
        lemma_add_mag(ra, rb, (s / 10) as u8);
        let rest = add_mag(ra, rb, (s / 10) as u8);
        lemma_cons_digit((s % 10) as u8, rest);
        let r = seq![(s % 10) as u8].add(rest);
        assert forall|i: int| 0 <= i < r.len() implies r[i] <= 9 by {
            if i > 0 { assert(r[i] == rest[i - 1]); }
        }
    }
}

pub proof fn lemma_sub_mag(a: Seq<u8>, b: Seq<u8>, borrow: u8)
    requires wf_mag(a), wf_mag(b), borrow <= 1,
    ensures
        wf_mag(sub_mag(a, b, borrow).0),
        sub_mag(a, b, borrow).0.len() == max_len(a, b),
        sub_mag(a, b, borrow).1 <= 1,
        mag_val(sub_mag(a, b, borrow).0) - sub_mag(a, b, borrow).1 * pow10(max_len(a, b))
            == mag_val(a) - mag_val(b) - borrow,
    decreases a.len() + b.len()
{
    if a.len() == 0 && b.len() == 0 {
    } else {
        let x = if a.len() > 0 { a[0] } else { 0u8 };
        let y = if b.len() > 0 { b[0] } else { 0u8 };
        let ra = if a.len() > 0 { a.drop_first() } else { a };
        let rb = if b.len() > 0 { b.drop_first() } else { b };
        let t = (y as u32 + borrow as u32) as u32;
        lemma_split(a);
        lemma_split(b);
        assert(max_len(a, b) == max_len(ra, rb) + 1);
        assert(t <= 10 && x as u32 + 10 >= t);
        let nb: u8 = if (x as u32) >= t { 0 } else { 1 };
        lemma_sub_mag(ra, rb, nb);
        let rest = sub_mag(ra, rb, nb);
        let dig: u8 = if (x as u32) >= t { (x as u32 - t) as u8 } else { (x as u32 + 10 - t) as u8 };
        lemma_cons_digit(dig, rest.0);
        let r = seq![dig].add(rest.0);
        assert forall|i: int| 0 <= i < r.len() implies r[i] <= 9 by {
            if i > 0 { assert(r[i] == rest.0[i - 1]); }
        }
        assert(pow10(max_len(a, b)) == 10 * pow10(max_len(ra, rb)));
        assert(rest.1 * pow10(max_len(a, b)) == 10 * (rest.1 * pow10(max_len(ra, rb))))
            by (nonlinear_arith)
            requires pow10(max_len(a, b)) == 10 * pow10(max_len(ra, rb));
    }
}

pub proof fn lemma_mag_bounds(a: Seq<u8>)
    requires wf_mag(a),
    ensures 0 <= mag_val(a) < pow10(a.len()),
    decreases a.len()
{
    lemma_split(a);
    if a.len() > 0 {
        lemma_mag_bounds(a.drop_first());
        assert(a.drop_first().len() + 1 == a.len());
        assert(pow10(a.len()) == 10 * pow10(a.drop_first().len()));
    }
}

pub proof fn lemma_scale_mag(a: Seq<u8>, k: u8)
    requires wf_mag(a),
    ensures mag_val(scale_mag(a, k)) == mag_val(a) * k, wf_mag(scale_mag(a, k)),
    decreases k
{
    if k > 0 {
        lemma_scale_mag(a, (k - 1) as u8);
        lemma_add_mag(a, scale_mag(a, (k - 1) as u8), 0u8);
        assert(mag_val(a) * k == mag_val(a) + mag_val(a) * (k - 1)) by (nonlinear_arith);
    }
}

pub proof fn lemma_mul_mag(a: Seq<u8>, b: Seq<u8>)
    requires wf_mag(a), wf_mag(b),
    ensures mag_val(mul_mag(a, b)) == mag_val(a) * mag_val(b), wf_mag(mul_mag(a, b)),
    decreases b.len()
{
    lemma_split(b);
    if b.len() > 0 {
        let rb = b.drop_first();
        lemma_mul_mag(a, rb);
        lemma_scale_mag(a, b[0]);
        let m = mul_mag(a, rb);
        lemma_cons_digit(0u8, m);
        let sh = seq![0u8].add(m);
        assert forall|i: int| 0 <= i < sh.len() implies sh[i] <= 9 by {
            if i > 0 { assert(sh[i] == m[i - 1]); }
        }
        lemma_add_mag(scale_mag(a, b[0]), sh, 0u8);
        let va = mag_val(a);
        let vr = mag_val(rb);
        assert(va * b[0] + 10 * (va * vr) == va * (b[0] + 10 * vr)) by (nonlinear_arith);
    }
}

pub proof fn lemma_is_zero_mag(a: Seq<u8>)
    requires wf_mag(a),
    ensures is_zero_mag(a) <==> mag_val(a) == 0,
    decreases a.len()
{
    lemma_split(a);
    if a.len() > 0 {
        lemma_is_zero_mag(a.drop_first());
        lemma_mag_bounds(a.drop_first());
    }
}

pub proof fn lemma_cmp_mag(a: Seq<u8>, b: Seq<u8>)
    requires wf_mag(a), wf_mag(b),
    ensures
        cmp_mag(a, b) == -1 <==> mag_val(a) < mag_val(b),
        cmp_mag(a, b) == 0 <==> mag_val(a) == mag_val(b),
        cmp_mag(a, b) == 1 <==> mag_val(a) > mag_val(b),
{
    lemma_sub_mag(a, b, 0u8);
    let d = sub_mag(a, b, 0u8);
    lemma_mag_bounds(d.0);
    lemma_is_zero_mag(d.0);
    lemma_mag_bounds(a);
    lemma_mag_bounds(b);
    let p = pow10(max_len(a, b));
    if d.1 == 0 {
        assert(d.1 * p == 0);
    } else {
        assert(d.1 * p == p);
    }
}

proof fn lemma_fit_mag(r: Seq<u8>, b: Seq<u8>, k: u8)
    requires
        wf_mag(r), wf_mag(b), k <= 9, mag_val(b) > 0,
        mag_val(r) < (10 - k) * mag_val(b),
    ensures
        ({
            let f = fit_mag(r, b, k);
            &&& wf_mag(f.1)
            &&& k <= f.0 <= 9
            &&& 0 <= mag_val(f.1) < mag_val(b)
            &&& mag_val(r) == (f.0 - k) * mag_val(b) + mag_val(f.1)
        }),
    decreases 9 - k
{
    lemma_cmp_mag(r, b);
    lemma_mag_bounds(r);
    if k < 9 && cmp_mag(r, b) >= 0 {
        lemma_sub_mag(r, b, 0u8);
        let r2 = sub_mag(r, b, 0u8).0;
        let vb = mag_val(b);
        assert(mag_val(r) - vb < (10 - (k + 1)) * vb) by (nonlinear_arith)
            requires mag_val(r) < (10 - k) * vb;
        lemma_fit_mag(r2, b, (k + 1) as u8);
        let f = fit_mag(r2, b, (k + 1) as u8);
        assert((f.0 - (k + 1)) * vb + vb == (f.0 - k) * vb) by (nonlinear_arith);
    } else {
        if k == 9 {
            assert((10 - k) * mag_val(b) == mag_val(b)) by (nonlinear_arith) requires k == 9;
        }
        assert((k - k) * mag_val(b) == 0) by (nonlinear_arith);
    }
}

pub proof fn lemma_divmod_mag(a: Seq<u8>, b: Seq<u8>)
    requires wf_mag(a), wf_mag(b), mag_val(b) > 0,
    ensures
        ({
            let qr = divmod_mag(a, b);
            &&& wf_mag(qr.0) && wf_mag(qr.1)
            &&& 0 <= mag_val(qr.1) < mag_val(b)
            &&& mag_val(a) == mag_val(qr.0) * mag_val(b) + mag_val(qr.1)
        }),
    decreases a.len()
{
    lemma_split(a);
    if a.len() > 0 {
        let ra = a.drop_first();
        lemma_divmod_mag(ra, b);
        let qr = divmod_mag(ra, b);
        let r2 = seq![a[0]].add(qr.1);
        lemma_cons_digit(a[0], qr.1);
        assert forall|i: int| 0 <= i < r2.len() implies r2[i] <= 9 by {
            if i > 0 { assert(r2[i] == qr.1[i - 1]); }
        }
        let vb = mag_val(b);
        assert(mag_val(r2) < 10 * vb) by (nonlinear_arith)
            requires mag_val(r2) == a[0] as int + 10 * mag_val(qr.1), a[0] <= 9, mag_val(qr.1) < vb, mag_val(qr.1) >= 0;
        lemma_fit_mag(r2, b, 0u8);
        let f = fit_mag(r2, b, 0u8);
        lemma_cons_digit(f.0, qr.0);
        let q = seq![f.0].add(qr.0);
        assert forall|i: int| 0 <= i < q.len() implies q[i] <= 9 by {
            if i > 0 { assert(q[i] == qr.0[i - 1]); }
        }
        let vq = mag_val(qr.0);
        assert((f.0 + 10 * vq) * vb + mag_val(f.1) == a[0] as int + 10 * (vq * vb + mag_val(qr.1)))
            by (nonlinear_arith)
            requires mag_val(r2) == f.0 * vb + mag_val(f.1), mag_val(r2) == a[0] as int + 10 * mag_val(qr.1);
    }
}

/// The signed integer coefficient of a number.
pub open spec fn num_coeff(n: Num) -> int {
    if n.neg { -mag_val(n.mag) } else { mag_val(n.mag) }
}

/// The L0 meaning of a number.
pub open spec fn to_l0(n: Num) -> SpecBCNum {
    SpecBCNum { coeff: num_coeff(n), scale: n.scale as nat }
}

pub open spec fn wf_num(n: Num) -> bool {
    wf_mag(n.mag)
}

pub open spec fn signed(neg: bool, v: int) -> int {
    if neg { -v } else { v }
}

pub proof fn lemma_shift_mag(a: Seq<u8>, k: u32)
    requires wf_mag(a),
    ensures mag_val(shift_mag(a, k)) == mag_val(a) * pow10(k as nat), wf_mag(shift_mag(a, k)),
    decreases k
{
    if k > 0 {
        lemma_shift_mag(a, (k - 1) as u32);
        let r = shift_mag(a, (k - 1) as u32);
        lemma_cons_digit(0u8, r);
        let t = seq![0u8].add(r);
        assert forall|i: int| 0 <= i < t.len() implies t[i] <= 9 by {
            if i > 0 { assert(t[i] == r[i - 1]); }
        }
        assert(pow10(k as nat) == 10 * pow10((k - 1) as nat));
        assert(10 * (mag_val(a) * pow10((k - 1) as nat)) == mag_val(a) * (10 * pow10((k - 1) as nat)))
            by (nonlinear_arith);
    }
}

pub proof fn lemma_drop_mag(a: Seq<u8>, k: u32)
    requires wf_mag(a),
    ensures mag_val(drop_mag(a, k)) == mag_val(a) / pow10(k as nat), wf_mag(drop_mag(a, k)),
    decreases k
{
    lemma_pow10_pos(k as nat);
    lemma_split(a);
    if k == 0 {
    } else if a.len() == 0 {
        assert(0int / pow10(k as nat) == 0) by (nonlinear_arith) requires pow10(k as nat) >= 1;
    } else {
        let ra = a.drop_first();
        lemma_drop_mag(ra, (k - 1) as u32);
        lemma_mag_bounds(ra);
        let m = pow10((k - 1) as nat);
        lemma_pow10_pos((k - 1) as nat);
        assert(pow10(k as nat) == 10 * m);
        let q = mag_val(ra) / m;
        // a = a0 + 10·ra and q·m <= ra < q·m + m, so q·10m <= a < q·10m + 10m.
        assert(q * m <= mag_val(ra) && mag_val(ra) < q * m + m) by (nonlinear_arith)
            requires m >= 1, q == mag_val(ra) / m;
        assert(q * (10 * m) <= mag_val(a) && mag_val(a) < q * (10 * m) + 10 * m) by (nonlinear_arith)
            requires
                q * m <= mag_val(ra), mag_val(ra) < q * m + m,
                mag_val(a) == a[0] as int + 10 * mag_val(ra), 0 <= a[0] <= 9;
        lemma_floor_div_unique(mag_val(a), 10 * m, q);
    }
}

pub proof fn lemma_mk_num(neg: bool, m: Seq<u8>, scale: u32)
    requires wf_mag(m),
    ensures
        num_coeff(mk_num(neg, m, scale)) == signed(neg, mag_val(m)),
        wf_num(mk_num(neg, m, scale)),
{
    lemma_is_zero_mag(m);
}

/// Subtracting a smaller or equal magnitude leaves no borrow.
pub proof fn lemma_sub_no_borrow(a: Seq<u8>, b: Seq<u8>)
    requires wf_mag(a), wf_mag(b), mag_val(a) >= mag_val(b),
    ensures
        sub_mag(a, b, 0u8).1 == 0,
        mag_val(sub_mag(a, b, 0u8).0) == mag_val(a) - mag_val(b),
        wf_mag(sub_mag(a, b, 0u8).0),
{
    lemma_sub_mag(a, b, 0u8);
    let d = sub_mag(a, b, 0u8);
    lemma_mag_bounds(d.0);
    let p = pow10(max_len(a, b));
    if d.1 != 0 {
        assert(d.1 == 1);
        assert(d.1 * p == p);
        lemma_mag_bounds(a);
        lemma_mag_bounds(b);
        assert(false);
    }
    assert(d.1 * p == 0);
}

pub proof fn lemma_signed_add(na: bool, a: Seq<u8>, nb: bool, b: Seq<u8>)
    requires wf_mag(a), wf_mag(b),
    ensures
        ({
            let r = signed_add(na, a, nb, b);
            &&& wf_mag(r.1)
            &&& signed(r.0, mag_val(r.1)) == signed(na, mag_val(a)) + signed(nb, mag_val(b))
        }),
{
    lemma_mag_bounds(a);
    lemma_mag_bounds(b);
    if na == nb {
        lemma_add_mag(a, b, 0u8);
    } else {
        lemma_cmp_mag(a, b);
        if cmp_mag(a, b) >= 0 {
            lemma_sub_no_borrow(a, b);
        } else {
            lemma_sub_no_borrow(b, a);
        }
    }
}

pub proof fn lemma_num_add(a: Num, b: Num)
    requires wf_num(a), wf_num(b),
    ensures to_l0(num_add(a, b)) == to_l0(a).spec_add(to_l0(b)), wf_num(num_add(a, b)),
{
    let sr = if a.scale >= b.scale { a.scale } else { b.scale };
    let ka = (sr - a.scale) as u32;
    let kb = (sr - b.scale) as u32;
    lemma_shift_mag(a.mag, ka);
    lemma_shift_mag(b.mag, kb);
    let ma = shift_mag(a.mag, ka);
    let mb = shift_mag(b.mag, kb);
    lemma_signed_add(a.neg, ma, b.neg, mb);
    let r = signed_add(a.neg, ma, b.neg, mb);
    lemma_mk_num(r.0, r.1, sr);
    let pa = pow10(ka as nat);
    let pb = pow10(kb as nat);
    assert(signed(a.neg, mag_val(a.mag) * pa) == signed(a.neg, mag_val(a.mag)) * pa) by (nonlinear_arith);
    assert(signed(b.neg, mag_val(b.mag) * pb) == signed(b.neg, mag_val(b.mag)) * pb) by (nonlinear_arith);
}

pub proof fn lemma_num_sub(a: Num, b: Num)
    requires wf_num(a), wf_num(b),
    ensures to_l0(num_sub(a, b)) == to_l0(a).spec_sub(to_l0(b)), wf_num(num_sub(a, b)),
{
    let nb = Num { neg: !b.neg, mag: b.mag, scale: b.scale };
    lemma_num_add(a, nb);
    let sr = if a.scale >= b.scale { a.scale } else { b.scale } as nat;
    assert(to_l0(nb).scaled_coeff(sr) == -to_l0(b).scaled_coeff(sr)) by (nonlinear_arith)
        requires
            to_l0(nb).coeff == -to_l0(b).coeff,
            to_l0(nb).scale == to_l0(b).scale,
            to_l0(nb).scaled_coeff(sr) == to_l0(nb).coeff * pow10((sr - to_l0(nb).scale) as nat),
            to_l0(b).scaled_coeff(sr) == to_l0(b).coeff * pow10((sr - to_l0(b).scale) as nat);
}

/// `BC_SCALE_MAX`: every scale the evaluator creates is at most this (AGENTS.md).
pub open spec fn scale_ok(s: u32) -> bool {
    s <= 1_000_000_000
}

pub proof fn lemma_signed_mul(na: bool, x: int, nb: bool, y: int)
    ensures signed(na, x) * signed(nb, y) == signed(na != nb, x * y),
{
    assert((-x) * y == -(x * y) && x * (-y) == -(x * y) && (-x) * (-y) == x * y) by (nonlinear_arith);
}

pub proof fn lemma_tdiv_signs(na: bool, x: int, nb: bool, y: int)
    requires x >= 0, y > 0,
    ensures spec_tdiv(signed(na, x), signed(nb, y)) == signed(na != nb, x / y),
{
    assert(x / y >= 0) by (nonlinear_arith) requires x >= 0, y > 0;
    if x == 0 {
        assert(0int / y == 0) by (nonlinear_arith) requires y > 0;
    }
}

/// The quotient of `divmod_mag` is the floor quotient.
pub proof fn lemma_div_quot(a: Seq<u8>, b: Seq<u8>)
    requires wf_mag(a), wf_mag(b), mag_val(b) > 0,
    ensures
        mag_val(divmod_mag(a, b).0) == mag_val(a) / mag_val(b),
        wf_mag(divmod_mag(a, b).0),
{
    lemma_divmod_mag(a, b);
    let qr = divmod_mag(a, b);
    lemma_floor_div_unique(mag_val(a), mag_val(b), mag_val(qr.0));
}

pub proof fn lemma_mul_scale(a: u32, b: u32, gs: u32)
    ensures
        mul_scale(a, b, gs) as nat == spec_posix_mul_scale(a as nat, b as nat, gs as nat),
        mul_scale(a, b, gs) as u64 <= a as u64 + b as u64,
        a as u64 + b as u64 - mul_scale(a, b, gs) as u64 <= 0xffff_ffffu64,
{
}

pub proof fn lemma_num_mul(a: Num, b: Num, gs: u32)
    requires wf_num(a), wf_num(b),
    ensures
        to_l0(num_mul(a, b, gs)) == spec_mul(to_l0(a), to_l0(b), gs as nat),
        wf_num(num_mul(a, b, gs)),
{
    lemma_mul_scale(a.scale, b.scale, gs);
    let sr = mul_scale(a.scale, b.scale, gs);
    let diff = (a.scale as u64 + b.scale as u64 - sr as u64) as u32;
    lemma_mul_mag(a.mag, b.mag);
    let m = mul_mag(a.mag, b.mag);
    lemma_drop_mag(m, diff);
    lemma_mk_num(a.neg != b.neg, drop_mag(m, diff), sr);
    lemma_signed_mul(a.neg, mag_val(a.mag), b.neg, mag_val(b.mag));
    lemma_pow10_pos(diff as nat);
    lemma_mag_bounds(m);
    lemma_tdiv_signs(a.neg != b.neg, mag_val(m), false, pow10(diff as nat));
    assert(diff as nat == (a.scale as nat + b.scale as nat - sr as nat) as nat);
}

pub proof fn lemma_num_div(a: Num, b: Num, gs: u32)
    requires
        wf_num(a), wf_num(b), mag_val(b.mag) > 0,
        scale_ok(a.scale), scale_ok(b.scale), scale_ok(gs),
    ensures
        to_l0(num_div(a, b, gs)) == spec_div(to_l0(a), to_l0(b), gs as nat),
        wf_num(num_div(a, b, gs)),
{
    let va = mag_val(a.mag);
    let vb = mag_val(b.mag);
    lemma_mag_bounds(a.mag);
    if b.scale as u64 + gs as u64 >= a.scale as u64 {
        let k = (b.scale as u64 + gs as u64 - a.scale as u64) as u32;
        assert(k as int == b.scale + gs - a.scale);
        lemma_shift_mag(a.mag, k);
        lemma_pow10_pos(k as nat);
        lemma_div_quot(shift_mag(a.mag, k), b.mag);
        let q = divmod_mag(shift_mag(a.mag, k), b.mag).0;
        lemma_mk_num(a.neg != b.neg, q, gs);
        assert(signed(a.neg, va) * pow10(k as nat) == signed(a.neg, va * pow10(k as nat)))
            by (nonlinear_arith);
        assert(va * pow10(k as nat) >= 0) by (nonlinear_arith) requires va >= 0, pow10(k as nat) >= 1;
        lemma_tdiv_signs(a.neg, va * pow10(k as nat), b.neg, vb);
    } else {
        let k = (a.scale as u64 - b.scale as u64 - gs as u64) as u32;
        assert(k as int == -(b.scale + gs - a.scale));
        lemma_shift_mag(b.mag, k);
        lemma_pow10_pos(k as nat);
        assert(vb * pow10(k as nat) > 0) by (nonlinear_arith) requires vb > 0, pow10(k as nat) >= 1;
        lemma_div_quot(a.mag, shift_mag(b.mag, k));
        let q = divmod_mag(a.mag, shift_mag(b.mag, k)).0;
        lemma_mk_num(a.neg != b.neg, q, gs);
        assert(signed(b.neg, vb) * pow10(k as nat) == signed(b.neg, vb * pow10(k as nat)))
            by (nonlinear_arith);
        lemma_tdiv_signs(a.neg, va, b.neg, vb * pow10(k as nat));
    }
}

pub proof fn lemma_num_mod(a: Num, b: Num, gs: u32)
    requires
        wf_num(a), wf_num(b), mag_val(b.mag) > 0,
        scale_ok(a.scale), scale_ok(b.scale), scale_ok(gs),
    ensures
        to_l0(num_mod(a, b, gs)) == spec_mod(to_l0(a), to_l0(b), gs as nat),
        wf_num(num_mod(a, b, gs)),
{
    lemma_num_div(a, b, gs);
    let q = num_div(a, b, gs);
    lemma_mul_mag(q.mag, b.mag);
    let prod = Num {
        neg: q.neg != b.neg,
        mag: mul_mag(q.mag, b.mag),
        scale: (gs as u64 + b.scale as u64) as u32,
    };
    lemma_signed_mul(q.neg, mag_val(q.mag), b.neg, mag_val(b.mag));
    lemma_num_sub(a, prod);
}

pub proof fn lemma_num_cmp(a: Num, b: Num)
    requires wf_num(a), wf_num(b),
    ensures
        num_cmp(a, b) == -1 <==> spec_bcnum_lt(to_l0(a), to_l0(b)),
        num_cmp(a, b) == 0 <==> spec_bcnum_eq(to_l0(a), to_l0(b)),
        num_cmp(a, b) == 1 <==> spec_bcnum_gt(to_l0(a), to_l0(b)),
{
    lemma_num_sub(a, b);
    lemma_bcnum_relational_total_order(to_l0(a), to_l0(b));
    let d = num_sub(a, b);
    lemma_is_zero_mag(d.mag);
    lemma_mag_bounds(d.mag);
}

} // verus!
