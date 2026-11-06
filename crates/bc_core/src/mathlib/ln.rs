// SPDX-License-Identifier: MIT

//! `l(x)`: x = m·2^k with m near 1, ln m = 2·artanh((m−1)/(m+1)), plus k·ln 2.

use super::*;

verus! {

/// ln 1 = 0.
pub(crate) proof fn lemma_ln_one()
    ensures
        ln_r(1real) == 0real,
{
    axiom_ln_mul(1real, 1real);
    assert(1real * 1real == 1real);
}

/// 2^n > 0 and ln(2^n) = n·ln 2.
pub(crate) proof fn lemma_ln_pow2(n: nat)
    ensures
        spec_pow_int(2, n) > 0,
        ln_r(spec_pow_int(2, n) as real) == (n as real) * ln2_r(),
    decreases n,
{
    if n == 0 {
        assert(spec_pow_int(2, 0) == 1);
        lemma_ln_one();
        assert((1int as real) == 1real);
        assert(ln_r(spec_pow_int(2, n) as real) == 0real);
        assert((0nat as real) * ln2_r() == 0real) by (nonlinear_arith);
    } else {
        lemma_ln_pow2((n - 1) as nat);
        let p = spec_pow_int(2, (n - 1) as nat);
        assert(spec_pow_int(2, n) == 2 * p);
        lemma_cast_mul(2, p);
        let pr = p as real;
        axiom_ln_mul(2real, pr);
        assert(2real * pr == (spec_pow_int(2, n) as real));
        let l2 = ln2_r();
        let nm = ((n - 1) as nat) as real;
        let nr = n as real;
        assert(nr == nm + 1real);
        assert(l2 + nm * l2 == nr * l2) by (nonlinear_arith)
            requires
                nr == nm + 1real,
        ;
        assert(ln_r(2real * pr) == l2 + ln_r(pr));
        assert(ln_r(pr) == nm * l2);
        assert(ln_r(spec_pow_int(2, n) as real) == ln_r(2real * pr));
    }
}

/// The value of `ln_ball`'s scaled argument: x / 2^k for k >= 0 and x·2^−k for k < 0.
pub(crate) open spec fn scaled_by_pow2(x: real, k: int) -> real {
    if k >= 0 {
        x / (spec_pow_int(2, k as nat) as real)
    } else {
        x * (spec_pow_int(2, (-k) as nat) as real)
    }
}

/// ln x = ln m + k·ln 2 for m = x·2^−k > 0.
pub(crate) proof fn lemma_ln_scaled(x: real, k: int)
    requires
        x > 0real,
    ensures
        scaled_by_pow2(x, k) > 0real,
        ln_r(x) == ln_r(scaled_by_pow2(x, k)) + (k as real) * ln2_r(),
{
    let m = scaled_by_pow2(x, k);
    if k >= 0 {
        lemma_ln_pow2(k as nat);
        let p = spec_pow_int(2, k as nat) as real;
        assert(m > 0real && m * p == x) by (nonlinear_arith)
            requires
                p > 0real,
                x > 0real,
                m == x / p,
        ;
        axiom_ln_mul(m, p);
        assert((k as nat) as real == k as real);
    } else {
        lemma_ln_pow2((-k) as nat);
        let q = spec_pow_int(2, (-k) as nat) as real;
        assert(m > 0real) by (nonlinear_arith)
            requires
                q > 0real,
                x > 0real,
                m == x * q,
        ;
        axiom_ln_mul(x, q);
        let kr = k as real;
        let l2 = ln2_r();
        assert(((-k) as nat as real) == -kr);
        assert((-kr) * l2 == -(kr * l2)) by (nonlinear_arith);
    }
}

/// With y = (m − 1)/(m + 1), 2·artanh y = ln m (artanh is defined from ln).
pub(crate) proof fn lemma_artanh_of_cayley(m: real, y: real)
    requires
        m + 1real != 0real,
        y == (m - 1real) / (m + 1real),
    ensures
        artanh_r(y) * 2real == ln_r(m),
{
    assert((1real + y) / (1real - y) == m) by (nonlinear_arith)
        requires
            m + 1real != 0real,
            y == (m - 1real) / (m + 1real),
    ;
}

/// Term 0 of the artanh series is y.
pub(crate) proof fn lemma_artanh_first_term(y: real)
    ensures
        artanh_term(y, 0) == y,
{
    assert(pow_r(y, 0) == 1real);
    assert(pow_r(y, 1) == y * pow_r(y, 0));
    let p1 = pow_r(y, 1);
    assert(p1 / (1nat as real) == y) by (nonlinear_arith)
        requires
            p1 == y,
    ;
}

/// x·2^−k at precision `prec`, as a ball (exact up to the floor of `shr`).
#[allow(
    clippy::cast_sign_loss,
    reason = "k >= 0 in the first branch, and -k > 0 in the second (k > i64::MIN); Verus checks both"
)]
pub(crate) fn shifted(xb: &Ball, k: i64) -> (r: Ball)
    requires
        xb.wf(),
        k > i64::MIN,
    ensures
        r.wf(),
        r.prec == xb.prec,
        forall|v: real| #[trigger] xb.contains(v) ==> r.contains(scaled_by_pow2(v, k as int)),
{
    if k >= 0 {
        xb.shr(k as u64)
    } else {
        xb.shl((-k) as u64)
    }
}

/// ln(x) for x > 0: x = m·2^k with m in [0.7, 1.43); ln m = 2·artanh(y) with
/// y = (m − 1)/(m + 1), |y| < 0.18, so the terms y^(2j+1)/(2j+1) decrease and the positive tail
/// is at most 1/(1 − y²) < 2 times the first omitted term. ln x = ln m + k·ln 2, with ln 2
/// carrying as many extra digits as k has. Any k gives the right value (`lemma_ln_scaled`); the
/// search only keeps y small.
#[verifier::exec_allows_no_decreases_clause]
#[allow(
    clippy::cast_possible_wrap,
    clippy::cast_possible_truncation,
    reason = "both bit counts are at most i64::MAX, checked just before, and the digit count of k \
              is cast to usize only below u32::MAX - prec; Verus checks the casts"
)]
pub(crate) fn ln_ball(x: &BCNum, prec: usize) -> (r: Option<Ball>)
    requires
        prec <= u32::MAX,
        x.scale <= u32::MAX,
        big_view(&x.coeff) > 0,
    ensures
        r is Some ==> r->Some_0.wf() && r->Some_0.prec == prec && r->Some_0.contains(
            ln_r(bcnum_real(x)),
        ),
{
    let ghost xv = bcnum_real(x);
    proof {
        lemma_sign_positive(x, 1);
        assert(xv * (1int as real) == xv);
    }
    let xb = Ball::from_bcnum(x, prec);
    let one = Ball::int(1, prec);
    proof {
        assert((1i64 as real) == 1real);
    }
    let unit = pow10_within(prec);
    let low = big_tdiv(&big_mul(&big_from_i64(7), &unit), &big_from_i64(10));
    let high = big_tdiv(&big_mul(&big_from_i64(143), &unit), &big_from_i64(100));
    let bx = big_bits(&xb.mid);
    let b1 = big_bits(&one.mid);
    if bx > i64::MAX as u64 || b1 > i64::MAX as u64 {
        return None;
    }
    let mut k: i64 = bx as i64 - b1 as i64;
    let mut m = shifted(&xb, k);
    let mut done = false;
    while !done
        invariant
            k > i64::MIN,
            xb.wf() && xb.prec == prec && xb.contains(xv),
            m.wf() && m.prec == prec && m.contains(scaled_by_pow2(xv, k as int)),
    {
        if matches!(big_cmp(&m.mid, &low), Ordering::Less) {
            if k == i64::MIN + 1 {
                return None;
            }
            k -= 1;
            m = shifted(&xb, k);
        } else if !matches!(big_cmp(&m.mid, &high), Ordering::Less) {
            if k == i64::MAX {
                return None;
            }
            k += 1;
            m = shifted(&xb, k);
        } else {
            done = true;
        }
    }
    let ghost mv = scaled_by_pow2(xv, k as int);
    let y = m.sub(&one).div(&m.add(&one))?;
    let ghost yv = (mv - 1real) / (mv + 1real);
    let y_sq = y.mul(&y);
    proof {
        lemma_artanh_first_term(yv);
    }
    let artanh = sum_series(y, &Series::Artanh { y_sq }, Ghost(yv))?;
    let k_big = big_from_i64(k);
    let extra: u64 = if k == 0 {
        1
    } else {
        big_decimal_digits(&big_abs(&k_big))
    };
    if extra >= (u32::MAX as usize - prec) as u64 {
        return None;
    }
    let k_ln2 = ln2(prec + extra as usize).mul_int(&k_big).reduce_prec(prec);
    let r = artanh.mul_int(&big_from_i64(2)).add(&k_ln2);
    proof {
        lemma_ln_scaled(xv, k as int);
        lemma_artanh_of_cayley(mv, yv);
        assert(ln2_r() * (k as real) == (k as real) * ln2_r()) by (nonlinear_arith);
    }
    Some(r)
}

/// Math natural logarithm function: ln x truncated toward zero at `global_scale` digits for
/// x > 0. For x <= 0 it returns 1 − 10^scale (GNU's library value).
pub fn bc_ln(x: &BCNum, global_scale: usize) -> (r: Result<BCNum, RuntimeError>)
    requires
        x.scale <= MAX_VERIFIED_SCALE,
        global_scale <= MAX_VERIFIED_SCALE,
    ensures
        r is Ok ==> r->Ok_0.scale == global_scale,
        r is Ok && big_view(&x.coeff) > 0 ==> big_view(&r->Ok_0.coeff) == trunc_r(
            ln_r(bcnum_real(x)) * (spec_num::pow10(global_scale as nat) as real),
        ),
        r is Ok && big_view(&x.coeff) <= 0 ==> big_view(&r->Ok_0.coeff) == (1 - spec_num::pow10(
            global_scale as nat,
        )) * spec_num::pow10(global_scale as nat),
{
    if big_is_negative(&x.coeff) || big_is_zero(&x.coeff) {
        // Like GNU's library, l(x) for x <= 0 returns (1 - 10^scale) at the caller's scale.
        let coeff = big_mul(
            &big_sub(&big_from_i64(1), &pow10_within(global_scale)),
            &pow10_within(global_scale),
        );
        return Ok(BCNum::new(coeff, global_scale));
    }
    if matches!(big_cmp(&x.coeff, &pow10_within(x.scale)), Ordering::Equal) {
        proof {
            lemma_ln_one();
            lemma_pow10_pos(x.scale as nat);
            let d = spec_num::pow10(x.scale as nat) as real;
            assert(d / d == 1real) by (nonlinear_arith)
                requires
                    d >= 1real,
            ;
            assert(bcnum_real(x) == 1real);
        }
        return Ok(exact_result(0, global_scale));
    }
    let f = |p: usize| -> (b: Option<Ball>)
        requires
            p <= u32::MAX,
            x.scale <= u32::MAX,
            big_view(&x.coeff) > 0,
        ensures
            b is Some ==> b->Some_0.wf() && b->Some_0.prec == p && b->Some_0.contains(
                ln_r(bcnum_real(x)),
            ),
        { ln_ball(x, p) };
    let r = certify(x.scale, global_scale, 0, f);
    proof {
        assert(all_contain(f, ln_r(bcnum_real(x))));
    }
    r
}

} // verus!
