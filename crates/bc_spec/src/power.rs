// SPDX-License-Identifier: MIT

//! `^` and `sqrt` on numbers (L1), with proofs against `spec_pow` and `is_isqrt` (L0).

use crate::num::*;
use crate::spec_num::*;
use vstd::contrib::exec_spec::*;
use vstd::prelude::*;

verus! {

exec_spec_verified! {

/// The runtime errors of arithmetic (`RuntimeError` in `bc_core`).
pub enum NumErr {
    DivideByZero,
    ModuloByZero,
    NegativePowerOfZero,
    ExponentTooLarge,
    ScaleTooLarge,
    NegativeSqrt,
}

/// A number or an arithmetic error.
pub enum NumRes {
    Ok(Num),
    Err(NumErr),
}

/// The decimal digits of `x`.
pub open spec fn u64_mag(x: u64) -> Seq<u8>
    decreases x
{
    if x == 0 { seq![] } else { seq![(x % 10) as u8].add(u64_mag(x / 10)) }
}

/// The value of `m`, or `u64::MAX` if it does not fit.
pub open spec fn mag_to_u64(m: Seq<u8>) -> u64
    decreases m.len()
{
    if m.len() == 0 {
        0u64
    } else {
        let r = mag_to_u64(m.drop_first());
        if r <= 1844674407370955160u64 && m[0] <= 9 {
            (r * 10 + m[0] as u64) as u64
        } else {
            0xffff_ffff_ffff_ffffu64
        }
    }
}

/// `x^k` for a single digit `k`.
pub open spec fn pow_small(x: Seq<u8>, k: u8) -> Seq<u8>
    decreases k
{
    if k == 0 { seq![1u8] } else { mul_mag(x, pow_small(x, (k - 1) as u8)) }
}

/// `x^e`, over the decimal digits of `e`: `x^(d + 10·e') = x^d · (x^e')^10`.
pub open spec fn pow_mag(x: Seq<u8>, e: Seq<u8>) -> Seq<u8>
    decreases e.len()
{
    if e.len() == 0 {
        seq![1u8]
    } else {
        mul_mag(pow_small(x, e[0]), pow_small(pow_mag(x, e.drop_first()), 10u8))
    }
}

/// Whether the number denoted by `e` is odd.
pub open spec fn is_odd_mag(e: Seq<u8>) -> bool {
    e.len() > 0 && e[0] % 2 == 1
}

/// `a ^ b` at `scale = gs` (`BCNum::try_pow`).
pub open spec fn num_pow(a: Num, b: Num, gs: u32) -> NumRes {
    let e = drop_mag(b.mag, b.scale);
    let eneg = b.neg && !is_zero_mag(e);
    let lim = if eneg { u64_mag(9223372036854775808u64) } else { u64_mag(9223372036854775807u64) };
    let exact_mag = mul_mag(u64_mag(a.scale as u64), e);
    if cmp_mag(e, lim) > 0 {
        NumRes::Err(NumErr::ExponentTooLarge)
    } else if cmp_mag(exact_mag, u64_mag(1000000000u64)) > 0 {
        NumRes::Err(NumErr::ScaleTooLarge)
    } else {
        let exact = mag_to_u64(exact_mag) as u32;
        let r = pow_mag(a.mag, e);
        let rneg = a.neg && is_odd_mag(e);
        if !eneg {
            let maxga = if gs >= a.scale { gs } else { a.scale };
            let sr = if exact <= maxga { exact } else { maxga };
            NumRes::Ok(mk_num(rneg, drop_mag(r, (exact - sr) as u32), sr))
        } else if is_zero_mag(r) {
            NumRes::Err(NumErr::NegativePowerOfZero)
        } else {
            NumRes::Ok(num_div(
                Num { neg: false, mag: seq![1u8], scale: 0u32 },
                Num { neg: rneg, mag: r, scale: exact },
                gs,
            ))
        }
    }
}

/// The largest digit `d >= start` with `(10·r + d)^2 <= n` (`[d] ++ r` is `10·r + d`).
pub open spec fn sqrt_digit(n: Seq<u8>, r: Seq<u8>, d: u8) -> u8
    decreases 9 - d when d <= 9
{
    let c = seq![(d + 1) as u8].add(r);
    if d < 9 && cmp_mag(mul_mag(c, c), n) <= 0 { sqrt_digit(n, r, (d + 1) as u8) } else { d }
}

/// The integer square root of `n`, two digits at a time from the most significant pair.
pub open spec fn isqrt_mag(n: Seq<u8>) -> Seq<u8>
    decreases n.len()
{
    if n.len() == 0 {
        seq![]
    } else {
        let rest = if n.len() >= 2 { n.drop_first().drop_first() } else { seq![] };
        let r = isqrt_mag(rest);
        let d = sqrt_digit(n, r, 0u8);
        seq![d].add(r)
    }
}

/// `sqrt(a)` at `scale = gs` (`BCNum::try_sqrt`).
pub open spec fn num_sqrt(a: Num, gs: u32) -> NumRes {
    if a.neg && !is_zero_mag(a.mag) {
        NumRes::Err(NumErr::NegativeSqrt)
    } else {
        let sr = if a.scale >= gs { a.scale } else { gs };
        let shift = (sr as u64 + sr as u64 - a.scale as u64) as u32;
        NumRes::Ok(mk_num(false, isqrt_mag(shift_mag(a.mag, shift)), sr))
    }
}

} // exec_spec_verified!

pub proof fn lemma_u64_mag(x: u64)
    ensures mag_val(u64_mag(x)) == x, wf_mag(u64_mag(x)),
    decreases x
{
    if x > 0 {
        lemma_u64_mag(x / 10);
        let r = u64_mag(x / 10);
        lemma_cons_digit((x % 10) as u8, r);
        let t = seq![(x % 10) as u8].add(r);
        assert forall|i: int| 0 <= i < t.len() implies t[i] <= 9 by {
            if i > 0 { assert(t[i] == r[i - 1]); }
        }
    }
}

pub proof fn lemma_mag_to_u64(m: Seq<u8>)
    requires wf_mag(m), mag_val(m) <= 1_000_000_000_000_000_000,
    ensures mag_to_u64(m) == mag_val(m),
    decreases m.len()
{
    lemma_split(m);
    if m.len() > 0 {
        lemma_mag_bounds(m.drop_first());
        lemma_mag_to_u64(m.drop_first());
    }
}

pub proof fn lemma_pow_add(b: int, m: nat, n: nat)
    ensures spec_pow_int(b, m + n) == spec_pow_int(b, m) * spec_pow_int(b, n),
    decreases m
{
    if m > 0 {
        lemma_pow_add(b, (m - 1) as nat, n);
        assert((m - 1) as nat + n == (m + n - 1) as nat);
        let x = spec_pow_int(b, (m - 1) as nat);
        let y = spec_pow_int(b, n);
        assert(b * (x * y) == (b * x) * y) by (nonlinear_arith);
    }
}

pub proof fn lemma_pow_mul(b: int, n: nat, k: nat)
    ensures spec_pow_int(b, n * k) == spec_pow_int(spec_pow_int(b, n), k),
    decreases k
{
    if k == 0 {
        assert(n * 0 == 0) by (nonlinear_arith);
    } else {
        lemma_pow_mul(b, n, (k - 1) as nat);
        assert(n * k == n + n * ((k - 1) as nat)) by (nonlinear_arith) requires k >= 1;
        lemma_pow_add(b, n, n * ((k - 1) as nat));
    }
}

pub proof fn lemma_pow_nonneg(v: int, n: nat)
    requires v >= 0,
    ensures spec_pow_int(v, n) >= 0,
    decreases n
{
    if n > 0 {
        lemma_pow_nonneg(v, (n - 1) as nat);
        assert(v * spec_pow_int(v, (n - 1) as nat) >= 0) by (nonlinear_arith)
            requires v >= 0, spec_pow_int(v, (n - 1) as nat) >= 0;
    }
}

pub proof fn lemma_pow_zero_base(n: nat)
    ensures spec_pow_int(0, n) == (if n == 0 { 1int } else { 0int }),
    decreases n
{
    if n > 0 { lemma_pow_zero_base((n - 1) as nat); }
}

pub proof fn lemma_pow_positive(v: int, n: nat)
    requires v > 0,
    ensures spec_pow_int(v, n) > 0,
    decreases n
{
    if n > 0 {
        lemma_pow_positive(v, (n - 1) as nat);
        assert(v * spec_pow_int(v, (n - 1) as nat) > 0) by (nonlinear_arith)
            requires v > 0, spec_pow_int(v, (n - 1) as nat) > 0;
    }
}

pub proof fn lemma_pow_sign(neg: bool, v: int, n: nat)
    ensures spec_pow_int(signed(neg, v), n) == signed(neg && n % 2 == 1, spec_pow_int(v, n)),
    decreases n
{
    if n > 0 {
        lemma_pow_sign(neg, v, (n - 1) as nat);
        lemma_signed_mul(neg, v, neg && (n - 1) as nat % 2 == 1, spec_pow_int(v, (n - 1) as nat));
    }
}

pub proof fn lemma_pow_small(x: Seq<u8>, k: u8)
    requires wf_mag(x),
    ensures mag_val(pow_small(x, k)) == spec_pow_int(mag_val(x), k as nat), wf_mag(pow_small(x, k)),
    decreases k
{
    if k == 0 {
        lemma_cons_digit(1u8, seq![]);
        assert(seq![1u8] =~= seq![1u8].add(Seq::<u8>::empty()));
    } else {
        lemma_pow_small(x, (k - 1) as u8);
        lemma_mul_mag(x, pow_small(x, (k - 1) as u8));
    }
}

pub proof fn lemma_one_mag()
    ensures mag_val(seq![1u8]) == 1, wf_mag(seq![1u8]),
{
    lemma_cons_digit(1u8, seq![]);
    assert(seq![1u8] =~= seq![1u8].add(Seq::<u8>::empty()));
}

pub proof fn lemma_pow_mag(x: Seq<u8>, e: Seq<u8>)
    requires wf_mag(x), wf_mag(e),
    ensures mag_val(pow_mag(x, e)) == spec_pow_int(mag_val(x), mag_val(e) as nat), wf_mag(pow_mag(x, e)),
    decreases e.len()
{
    lemma_split(e);
    lemma_one_mag();
    if e.len() > 0 {
        let re = e.drop_first();
        lemma_mag_bounds(re);
        lemma_pow_mag(x, re);
        let p = pow_mag(x, re);
        lemma_pow_small(x, e[0]);
        lemma_pow_small(p, 10u8);
        lemma_mul_mag(pow_small(x, e[0]), pow_small(p, 10u8));
        let v = mag_val(x);
        let n = mag_val(re) as nat;
        lemma_pow_mul(v, n, 10);
        assert(n * 10 == 10 * n) by (nonlinear_arith);
        lemma_pow_add(v, e[0] as nat, 10 * n);
        assert(mag_val(e) as nat == e[0] as nat + 10 * n);
    }
}

pub proof fn lemma_is_odd_mag(e: Seq<u8>)
    requires wf_mag(e),
    ensures is_odd_mag(e) <==> mag_val(e) % 2 == 1,
{
    lemma_split(e);
    if e.len() > 0 {
        lemma_mag_bounds(e.drop_first());
        let r = mag_val(e.drop_first());
        assert((e[0] as int + 10 * r) % 2 == (e[0] as int) % 2) by (nonlinear_arith) requires r >= 0;
    }
}

pub proof fn lemma_num_pow(a: Num, b: Num, gs: u32)
    requires
        wf_num(a), wf_num(b), scale_ok(a.scale), scale_ok(b.scale), scale_ok(gs),
    ensures
        ({
            let e = spec_int_part(to_l0(b));
            let n = if e >= 0 { e } else { -e };
            match num_pow(a, b, gs) {
                NumRes::Err(NumErr::ExponentTooLarge) => e > 9223372036854775807 || e < -9223372036854775808,
                NumRes::Err(NumErr::ScaleTooLarge) =>
                    -9223372036854775808 <= e <= 9223372036854775807 && a.scale * n > 1_000_000_000,
                NumRes::Err(NumErr::NegativePowerOfZero) =>
                    -9223372036854775808 <= e <= 9223372036854775807 && a.scale * n <= 1_000_000_000
                    && e < 0 && num_coeff(a) == 0,
                NumRes::Ok(r) =>
                    -9223372036854775808 <= e <= 9223372036854775807 && a.scale * n <= 1_000_000_000
                    && !(e < 0 && num_coeff(a) == 0)
                    && to_l0(r) == spec_pow(to_l0(a), to_l0(b), gs as nat) && wf_num(r),
                _ => false,
            }
        }),
{
    let em = drop_mag(b.mag, b.scale);
    lemma_drop_mag(b.mag, b.scale);
    lemma_pow10_pos(b.scale as nat);
    let vb = mag_val(b.mag);
    lemma_mag_bounds(b.mag);
    lemma_tdiv_signs(b.neg, vb, false, pow10(b.scale as nat));
    let ve = mag_val(em);
    assert(ve >= 0) by (nonlinear_arith) requires vb >= 0, pow10(b.scale as nat) >= 1, ve == vb / pow10(b.scale as nat);
    lemma_is_zero_mag(em);
    let e = spec_int_part(to_l0(b));
    assert(e == signed(b.neg, ve));
    let eneg = b.neg && !is_zero_mag(em);
    assert(eneg <==> e < 0);
    let n = if e >= 0 { e } else { -e };
    assert(n == ve);
    lemma_u64_mag(9223372036854775808u64);
    lemma_u64_mag(9223372036854775807u64);
    let lim = if eneg { u64_mag(9223372036854775808u64) } else { u64_mag(9223372036854775807u64) };
    lemma_cmp_mag(em, lim);
    lemma_u64_mag(a.scale as u64);
    lemma_mul_mag(u64_mag(a.scale as u64), em);
    let exact_mag = mul_mag(u64_mag(a.scale as u64), em);
    lemma_u64_mag(1000000000u64);
    lemma_cmp_mag(exact_mag, u64_mag(1000000000u64));
    if cmp_mag(em, lim) <= 0 && cmp_mag(exact_mag, u64_mag(1000000000u64)) <= 0 {
        lemma_mag_to_u64(exact_mag);
        let exact = mag_to_u64(exact_mag) as u32;
        assert(exact as int == a.scale * n);
        lemma_pow_mag(a.mag, em);
        let r = pow_mag(a.mag, em);
        let va = mag_val(a.mag);
        lemma_mag_bounds(a.mag);
        lemma_is_odd_mag(em);
        let rneg = a.neg && is_odd_mag(em);
        lemma_pow_sign(a.neg, va, ve as nat);
        assert(spec_pow_int(num_coeff(a), n as nat) == signed(rneg, mag_val(r)));
        lemma_pow_nonneg(va, ve as nat);
        if !eneg {
            let maxga = if gs >= a.scale { gs } else { a.scale };
            let sr = if exact <= maxga { exact } else { maxga };
            lemma_drop_mag(r, (exact - sr) as u32);
            lemma_mk_num(rneg, drop_mag(r, (exact - sr) as u32), sr);
            lemma_pow10_pos((exact - sr) as nat);
            lemma_tdiv_signs(rneg, mag_val(r), false, pow10((exact - sr) as nat));
            assert(sr as nat == spec_posix_pow_scale(a.scale as nat, n as nat, gs as nat));
        } else {
            lemma_is_zero_mag(r);
            if va == 0 {
                lemma_pow_zero_base(ve as nat);
            } else {
                lemma_pow_positive(va, ve as nat);
            }
            if !is_zero_mag(r) {
                lemma_one_mag();
                lemma_num_div(
                    Num { neg: false, mag: seq![1u8], scale: 0u32 },
                    Num { neg: rneg, mag: r, scale: exact },
                    gs,
                );
            }
        }
    }
}

proof fn lemma_sqrt_digit(n: Seq<u8>, r: Seq<u8>, d: u8)
    requires
        wf_mag(n), wf_mag(r), d <= 9,
        (10 * mag_val(r) + d) * (10 * mag_val(r) + d) <= mag_val(n),
        mag_val(n) < (10 * mag_val(r) + 10) * (10 * mag_val(r) + 10),
    ensures
        ({
            let k = sqrt_digit(n, r, d);
            &&& d <= k <= 9
            &&& is_isqrt(mag_val(n), 10 * mag_val(r) + k)
        }),
    decreases 9 - d
{
    lemma_mag_bounds(r);
    let c = seq![(d + 1) as u8].add(r);
    if d < 9 {
        lemma_cons_digit((d + 1) as u8, r);
        assert forall|i: int| 0 <= i < c.len() implies c[i] <= 9 by {
            if i > 0 { assert(c[i] == r[i - 1]); }
        }
        lemma_mul_mag(c, c);
        lemma_cmp_mag(mul_mag(c, c), n);
        if cmp_mag(mul_mag(c, c), n) <= 0 {
            lemma_sqrt_digit(n, r, (d + 1) as u8);
        }
    }
}

pub proof fn lemma_isqrt_mag(n: Seq<u8>)
    requires wf_mag(n),
    ensures is_isqrt(mag_val(n), mag_val(isqrt_mag(n))), wf_mag(isqrt_mag(n)),
    decreases n.len()
{
    lemma_split(n);
    if n.len() > 0 {
        let rest = if n.len() >= 2 { n.drop_first().drop_first() } else { seq![] };
        let n1 = n.drop_first();
        lemma_split(n1);
        let lo: int = if n.len() >= 2 { n[0] as int + 10 * n1[0] as int } else { n[0] as int };
        assert(mag_val(n) == lo + 100 * mag_val(rest) && 0 <= lo < 100) by {
            if n.len() >= 2 {
                assert(mag_val(n1) == n1[0] as int + 10 * mag_val(rest));
            } else {
                assert(n1.len() == 0);
            }
        }
        lemma_isqrt_mag(rest);
        let r = isqrt_mag(rest);
        let vr = mag_val(r);
        let vn = mag_val(rest);
        assert((10 * vr) * (10 * vr) <= mag_val(n)) by (nonlinear_arith)
            requires vr * vr <= vn, mag_val(n) == lo + 100 * vn, lo >= 0;
        assert(mag_val(n) < (10 * vr + 10) * (10 * vr + 10)) by (nonlinear_arith)
            requires vn < (vr + 1) * (vr + 1), mag_val(n) == lo + 100 * vn, lo < 100;
        assert((10 * vr + 0) * (10 * vr + 0) <= mag_val(n));
        lemma_sqrt_digit(n, r, 0u8);
        let k = sqrt_digit(n, r, 0u8);
        lemma_cons_digit(k, r);
        let t = seq![k].add(r);
        assert forall|i: int| 0 <= i < t.len() implies t[i] <= 9 by {
            if i > 0 { assert(t[i] == r[i - 1]); }
        }
    } else {
        assert(is_isqrt(0, 0));
    }
}

pub proof fn lemma_num_sqrt(a: Num, gs: u32)
    requires wf_num(a), scale_ok(a.scale), scale_ok(gs),
    ensures
        match num_sqrt(a, gs) {
            NumRes::Err(NumErr::NegativeSqrt) => num_coeff(a) < 0,
            NumRes::Ok(r) => {
                let sr = if a.scale >= gs { a.scale } else { gs };
                &&& num_coeff(a) >= 0
                &&& r.scale == sr
                &&& is_isqrt(num_coeff(a) * pow10((2 * sr - a.scale) as nat), num_coeff(r))
                &&& wf_num(r)
            },
            _ => false,
        },
{
    lemma_is_zero_mag(a.mag);
    lemma_mag_bounds(a.mag);
    if !(a.neg && !is_zero_mag(a.mag)) {
        let sr = if a.scale >= gs { a.scale } else { gs };
        let shift = (sr as u64 + sr as u64 - a.scale as u64) as u32;
        lemma_shift_mag(a.mag, shift);
        lemma_isqrt_mag(shift_mag(a.mag, shift));
        lemma_mk_num(false, isqrt_mag(shift_mag(a.mag, shift)), sr);
        assert(num_coeff(a) == mag_val(a.mag));
    }
}

} // verus!
