// SPDX-License-Identifier: MIT

//! `s(x)` and `c(x)`: reduction by multiples of 2π, then the Taylor series.

use super::*;

verus! {

/// x − k·2π.
pub(crate) open spec fn shift_2pi(x: real, k: int) -> real {
    x - 2real * (k as real) * pi_r()
}

/// The ball contains x − k·2π for some integer k.
pub(crate) open spec fn reduced_by_2pi(b: Ball, x: real) -> bool {
    exists|k: int| #![trigger shift_2pi(x, k)] b.contains(shift_2pi(x, k))
}

/// A witness k for `reduced_by_2pi`.
pub(crate) proof fn lemma_reduced(b: Ball, x: real, k: int)
    requires
        b.contains(shift_2pi(x, k)),
    ensures
        reduced_by_2pi(b, x),
{
}

/// x − k·2π for the integer k nearest x / 2π (any integer k leaves sin and cos unchanged), at
/// precision `prec`. π carries as many extra digits as x has integer digits, so k·rad(2π) stays
/// within a few ulps at `prec`. `None` if that working precision would exceed `u32::MAX`.
#[allow(
    clippy::cast_possible_truncation,
    reason = "the digit count is cast to usize only below u32::MAX - prec"
)]
pub(crate) fn reduce_angle(x: &BCNum, prec: usize) -> (r: Option<Ball>)
    requires
        prec <= u32::MAX,
        x.scale <= u32::MAX,
    ensures
        r is Some ==> r->Some_0.wf() && r->Some_0.prec == prec,
        r is Some ==> reduced_by_2pi(r->Some_0, bcnum_real(x)),
{
    let ghost xv = bcnum_real(x);
    let digits = int_digits(x);
    if digits == 0 {
        let b = Ball::from_bcnum(x, prec);
        proof {
            let k0: int = 0;
            assert(xv - 2real * (k0 as real) * pi_r() == xv) by (nonlinear_arith)
                requires
                    k0 == 0,
            ;
            assert(b.contains(shift_2pi(xv, k0)));
            lemma_reduced(b, xv, k0);
        }
        return Some(b);
    }
    if digits >= (u32::MAX as usize - prec) as u64 {
        return None;
    }
    let work = prec + digits as usize + 1;
    let xb = Ball::from_bcnum(x, work);
    let two_pi = pi(work).mul_int(&big_from_i64(2));
    proof {
        assert(spec_pow_int(2, 0) == 1);
        assert(spec_pow_int(2, 1) == 2);
    }
    // Any integer k is valid; the nearest one keeps r small. The midpoint of 2π is positive.
    let k = if matches!(big_cmp(&two_pi.mid, &big_from_i64(0)), Ordering::Greater) {
        big_div_mod_floor(
            &big_add(&big_shl(&xb.mid, 1), &two_pi.mid),
            &big_shl(&two_pi.mid, 1),
        ).0
    } else {
        big_from_i64(0)
    };
    let b = xb.sub(&two_pi.mul_int(&k)).reduce_prec(prec);
    proof {
        let kv = big_view(&k);
        assert(pi_r() * 2real * (kv as real) == 2real * (kv as real) * pi_r())
            by (nonlinear_arith);
        assert(b.contains(shift_2pi(xv, kv)));
        lemma_reduced(b, xv, kv);
    }
    Some(b)
}

/// sin 0 = 0 and cos 0 = 1, from the tail bound of their series after one term.
/// Term 0 of the sine and cosine series: r (sin) and 1 (cos); and at r = 0 term 1 is 0.
pub(crate) proof fn lemma_sin_cos_first_terms(r: real)
    ensures
        sin_cos_term(r, 1, 0) == r,
        sin_cos_term(r, 0, 0) == 1real,
        sin_cos_term(0real, 1, 1) == 0real,
        sin_cos_term(0real, 0, 1) == 0real,
{
    assert(pow_r(r, 0) == 1real);
    assert(pow_r(r, 1) == r * pow_r(r, 0));
    let z = 0real;
    assert(pow_r(z, 0) == 1real);
    assert(pow_r(z, 1) == z * pow_r(z, 0));
    assert(pow_r(z, 2) == z * pow_r(z, 1));
    assert(pow_r(z, 3) == z * pow_r(z, 2));
    assert(fact(0) == 1);
    assert(fact(1) == 1 * fact(0));
    assert(fact(2) == 2 * fact(1));
    assert(fact(3) == 3 * fact(2));
    assert(sign_r(0) == 1real && sign_r(1) == -1real);
    let (p1, p0) = (pow_r(r, 1), pow_r(r, 0));
    assert(sign_r(0) * p1 / (fact(1) as real) == r) by (nonlinear_arith)
        requires
            sign_r(0) == 1real,
            p1 == r,
            fact(1) as real == 1real,
    ;
    assert(sign_r(0) * p0 / (fact(0) as real) == 1real) by (nonlinear_arith)
        requires
            sign_r(0) == 1real,
            p0 == 1real,
            fact(0) as real == 1real,
    ;
    let (z3, z2) = (pow_r(z, 3), pow_r(z, 2));
    assert(sign_r(1) * z3 / (fact(3) as real) == 0real) by (nonlinear_arith)
        requires
            z3 == 0real,
            fact(3) as real == 6real,
    ;
    assert(sign_r(1) * z2 / (fact(2) as real) == 0real) by (nonlinear_arith)
        requires
            z2 == 0real,
            fact(2) as real == 2real,
    ;
}

/// sin 0 = 0 and cos 0 = 1, from the tail bound of their series after one term.
pub(crate) proof fn lemma_sin_cos_zero()
    ensures
        sin_r(0real) == 0real,
        cos_r(0real) == 1real,
{
    let z = 0real;
    lemma_sin_cos_first_terms(z);
    let ts = |j: nat| sin_cos_term(z, 1, j);
    let tc = |j: nat| sin_cos_term(z, 0, j);
    assert(partial_sum(ts, 1) == partial_sum(ts, 0) + ts(0));
    assert(partial_sum(tc, 1) == partial_sum(tc, 0) + tc(0));
    axiom_sin_cos_series(z, 1, 1);
    axiom_sin_cos_series(z, 0, 1);
    lemma_partial_sum_ext(ts, |j: nat| sin_cos_term(z, 1nat, j), 1);
    lemma_partial_sum_ext(tc, |j: nat| sin_cos_term(z, 0nat, j), 1);
}

/// The value of a `BCNum` with coefficient 0 is 0.
pub(crate) proof fn lemma_bcnum_real_zero(x: &BCNum)
    requires
        big_view(&x.coeff) == 0,
    ensures
        bcnum_real(x) == 0real,
{
    lemma_pow10_pos(x.scale as nat);
    let d = spec_num::pow10(x.scale as nat) as real;
    assert((0int as real) / d == 0real) by (nonlinear_arith)
        requires
            d >= 1real,
    ;
}

/// sin(x) (or cos(x)) by the Taylor series of the reduced argument r = x − k·2π. The terms
/// r^k/k! decrease once (k+1)(k+2) >= r² (checked by `Series::decreasing`).
pub(crate) fn sin_cos_ball(x: &BCNum, prec: usize, cos: bool) -> (r: Option<Ball>)
    requires
        prec <= u32::MAX,
        x.scale <= u32::MAX,
    ensures
        r is Some ==> r->Some_0.wf() && r->Some_0.prec == prec && r->Some_0.contains(
            if cos {
                cos_r(bcnum_real(x))
            } else {
                sin_r(bcnum_real(x))
            },
        ),
{
    let r = reduce_angle(x, prec)?;
    let ghost xv = bcnum_real(x);
    let ghost k = choose|k: int| #![trigger shift_2pi(xv, k)] r.contains(shift_2pi(xv, k));
    let ghost v = shift_2pi(xv, k);
    let r_sq = r.mul(&r);
    let (first, odd) = if cos {
        (Ball::int(1, prec), 0)
    } else {
        (r, 1)
    };
    let series = Series::SinCos { r_sq, odd };
    proof {
        lemma_sin_cos_first_terms(v);
        assert(series_term(series, v, 0) == (if cos { 1real } else { v }));
        axiom_sin_cos_periodic(v, k);
        assert(v + 2real * (k as real) * pi_r() == xv);
    }
    sum_series(first, &series, Ghost(v))
}

/// Math sine function: sin x truncated toward zero at `global_scale` digits.
pub fn bc_sin(x: &BCNum, global_scale: usize) -> (r: Result<BCNum, RuntimeError>)
    requires
        x.scale <= MAX_VERIFIED_SCALE,
        global_scale <= MAX_VERIFIED_SCALE,
    ensures
        r is Ok ==> r->Ok_0.scale == global_scale && big_view(&r->Ok_0.coeff) == trunc_r(
            sin_r(bcnum_real(x)) * (spec_num::pow10(global_scale as nat) as real),
        ),
{
    if big_is_zero(&x.coeff) {
        proof {
            lemma_sin_cos_zero();
            lemma_bcnum_real_zero(x);
        }
        return Ok(exact_result(0, global_scale));
    }
    let f = |p: usize| -> (b: Option<Ball>)
        requires
            p <= u32::MAX,
            x.scale <= u32::MAX,
        ensures
            b is Some ==> b->Some_0.wf() && b->Some_0.prec == p && b->Some_0.contains(
                sin_r(bcnum_real(x)),
            ),
        { sin_cos_ball(x, p, false) };
    let r = certify(x.scale, global_scale, 0, f);
    proof {
        assert(all_contain(f, sin_r(bcnum_real(x))));
    }
    r
}

/// Math cosine function: cos x truncated toward zero at `global_scale` digits.
pub fn bc_cos(x: &BCNum, global_scale: usize) -> (r: Result<BCNum, RuntimeError>)
    requires
        x.scale <= MAX_VERIFIED_SCALE,
        global_scale <= MAX_VERIFIED_SCALE,
    ensures
        r is Ok ==> r->Ok_0.scale == global_scale && big_view(&r->Ok_0.coeff) == trunc_r(
            cos_r(bcnum_real(x)) * (spec_num::pow10(global_scale as nat) as real),
        ),
{
    if big_is_zero(&x.coeff) {
        proof {
            lemma_sin_cos_zero();
            lemma_bcnum_real_zero(x);
            lemma_pow10_pos(global_scale as nat);
            let pr = spec_num::pow10(global_scale as nat) as real;
            assert(1real * pr == pr);
            assert(pr.floor() == spec_num::pow10(global_scale as nat));
        }
        return Ok(exact_result(1, global_scale));
    }
    let f = |p: usize| -> (b: Option<Ball>)
        requires
            p <= u32::MAX,
            x.scale <= u32::MAX,
        ensures
            b is Some ==> b->Some_0.wf() && b->Some_0.prec == p && b->Some_0.contains(
                cos_r(bcnum_real(x)),
            ),
        { sin_cos_ball(x, p, true) };
    let r = certify(x.scale, global_scale, 0, f);
    proof {
        assert(all_contain(f, cos_r(bcnum_real(x))));
    }
    r
}

} // verus!
