// SPDX-License-Identifier: MIT

//! `a(x)`: inversion for |x| > 1, four argument halvings, then the Taylor series.

use super::*;

verus! {

/// atan 0 = 0 (atan is odd).
pub(crate) proof fn lemma_atan_zero()
    ensures
        atan_r(0real) == 0real,
{
    axiom_atan_odd(0real);
    assert(-0real == 0real);
}

/// Term 0 of the atan series is y.
pub(crate) proof fn lemma_atan_first_term(y: real)
    ensures
        atan_term(y, 0) == y,
{
    assert(pow_r(y, 0) == 1real);
    assert(pow_r(y, 1) == y * pow_r(y, 0));
    assert(sign_r(0) == 1real);
    let p1 = pow_r(y, 1);
    assert(sign_r(0) * p1 / (1nat as real) == y) by (nonlinear_arith)
        requires
            sign_r(0) == 1real,
            p1 == y,
    ;
}

/// A nonzero coefficient times its sign is positive, and so is the value times the sign.
pub(crate) proof fn lemma_sign_positive(x: &BCNum, sgn: int)
    requires
        big_view(&x.coeff) != 0,
        sgn == (if big_view(&x.coeff) > 0 {
            1int
        } else {
            -1int
        }),
    ensures
        bcnum_real(x) * (sgn as real) > 0real,
{
    lemma_pow10_pos(x.scale as nat);
    let c = big_view(&x.coeff) as real;
    let d = spec_num::pow10(x.scale as nat) as real;
    assert((c / d) * (sgn as real) > 0real) by (nonlinear_arith)
        requires
            d >= 1real,
            c != 0real,
            c > 0real ==> sgn as real == 1real,
            c < 0real ==> sgn as real == -1real,
    ;
}

/// atan(x): for |x| > 1 use π/2 − atan(1/|x|); four half-angle steps y → y / (1 + √(1 + y²))
/// bring |y| below tan(π/64) < 0.05; then the alternating series y − y³/3 + …, times 16. atan is
/// odd, so the sign is applied last.
pub(crate) fn atan_ball(x: &BCNum, prec: usize) -> (r: Option<Ball>)
    requires
        prec <= u32::MAX,
        x.scale <= u32::MAX,
        big_view(&x.coeff) != 0,
    ensures
        r is Some ==> r->Some_0.wf() && r->Some_0.prec == prec && r->Some_0.contains(
            atan_r(bcnum_real(x)),
        ),
{
    let sgn = big_signum(&x.coeff);
    let ghost xv = bcnum_real(x);
    let ghost sv = big_view(&sgn) as real;
    let ghost a = xv * sv;
    proof {
        lemma_sign_positive(x, big_view(&sgn));
    }
    let ax = Ball::from_bcnum(x, prec).mul_int(&sgn);
    let one = Ball::int(1, prec);
    proof {
        assert((1i64 as real) == 1real);
    }
    let inverted = matches!(big_cmp(&ax.mid, &one.mid), Ordering::Greater);
    let mut y = if inverted {
        one.div(&ax)?
    } else {
        ax
    };
    let ghost y0 = if inverted {
        1real / a
    } else {
        a
    };
    let ghost mut yv = y0;
    let mut i: u32 = 0;
    proof {
        assert(spec_pow_int(2, 0) == 1);
        assert(atan_r(y0) == (1int as real) * atan_r(yv));
    }
    while i < 4
        invariant
            i <= 4,
            prec <= u32::MAX,
            one.wf() && one.prec == prec && one.contains(1real),
            y.wf() && y.prec == prec && y.contains(yv),
            atan_r(y0) == (spec_pow_int(2, i as nat) as real) * atan_r(yv),
        decreases 4 - i,
    {
        let root = one.add(&y.mul(&y)).sqrt()?;
        y = y.div(&one.add(&root))?;
        proof {
            let y1 = yv / (1real + sqrt_r(1real + yv * yv));
            axiom_atan_half(yv);
            let p = spec_pow_int(2, i as nat);
            assert(spec_pow_int(2, (i + 1) as nat) == 2 * p);
            lemma_cast_mul(2, p);
            let pr = p as real;
            let (ay, ay1) = (atan_r(yv), atan_r(y1));
            assert(pr * ay == (2int * p) as real * ay1) by (nonlinear_arith)
                requires
                    ay == 2real * ay1,
                    (2int * p) as real == 2real * pr,
            ;
            yv = y1;
        }
        i += 1;
    }
    let y_sq = y.mul(&y);
    proof {
        lemma_atan_first_term(yv);
    }
    let series = sum_series(y, &Series::Atan { y_sq }, Ghost(yv))?;
    let mut value = series.mul_int(&big_from_i64(16));
    proof {
        assert(spec_pow_int(2, 1) == 2 * spec_pow_int(2, 0));
        assert(spec_pow_int(2, 2) == 2 * spec_pow_int(2, 1));
        assert(spec_pow_int(2, 3) == 2 * spec_pow_int(2, 2));
        assert(spec_pow_int(2, 4) == 2 * spec_pow_int(2, 3));
        assert(spec_pow_int(2, 4) == 16);
        let (ay, ay0) = (atan_r(yv), atan_r(y0));
        assert(ay * 16real == ay0) by (nonlinear_arith)
            requires
                ay0 == (16int as real) * ay,
        ;
    }
    if inverted {
        value = pi(prec).div_int(&big_from_i64(2)).sub(&value);
        proof {
            axiom_atan_inverse(a);
            assert(pi_r() / 2real - atan_r(y0) == atan_r(a));
        }
    }
    let r = value.mul_int(&sgn);
    proof {
        axiom_atan_odd(xv);
        if big_view(&x.coeff) > 0 {
            assert(sv == 1real);
            assert(a == xv) by (nonlinear_arith)
                requires
                    a == xv * sv,
                    sv == 1real,
            ;
        } else {
            assert(sv == -1real);
            assert(a == -xv) by (nonlinear_arith)
                requires
                    a == xv * sv,
                    sv == -1real,
            ;
        }
        let at = atan_r(a);
        assert(at * sv == atan_r(xv)) by (nonlinear_arith)
            requires
                sv == 1real ==> at == atan_r(xv),
                sv == -1real ==> at == -atan_r(xv),
                sv == 1real || sv == -1real,
        ;
    }
    Some(r)
}

/// Math arctangent function: atan x truncated toward zero at `global_scale` digits.
pub fn bc_atan(x: &BCNum, global_scale: usize) -> (r: Result<BCNum, RuntimeError>)
    requires
        x.scale <= MAX_VERIFIED_SCALE,
        global_scale <= MAX_VERIFIED_SCALE,
    ensures
        r is Ok ==> r->Ok_0.scale == global_scale && big_view(&r->Ok_0.coeff) == trunc_r(
            atan_r(bcnum_real(x)) * (spec_num::pow10(global_scale as nat) as real),
        ),
{
    if big_is_zero(&x.coeff) {
        proof {
            lemma_atan_zero();
            lemma_bcnum_real_zero(x);
        }
        return Ok(exact_result(0, global_scale));
    }
    let f = |p: usize| -> (b: Option<Ball>)
        requires
            p <= u32::MAX,
            x.scale <= u32::MAX,
            big_view(&x.coeff) != 0,
        ensures
            b is Some ==> b->Some_0.wf() && b->Some_0.prec == p && b->Some_0.contains(
                atan_r(bcnum_real(x)),
            ),
        { atan_ball(x, p) };
    let r = certify(x.scale, global_scale, 0, f);
    proof {
        assert(all_contain(f, atan_r(bcnum_real(x))));
    }
    r
}

} // verus!
