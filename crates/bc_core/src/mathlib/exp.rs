// SPDX-License-Identifier: MIT

//! `e(x)`: x = n·ln 2 + r, the Taylor series of e^r, times 2^n.

use super::*;

verus! {

/// Largest integer part of the argument of `e(x)` and of `x` in `j(n,x)` (`docs/COMPATIBILITY.md`
/// §2). e^x then has at most about 0.4343·x ≈ 8.7·10^8 integer digits, and the extra working
/// precision x/2 stays within `MAX_VERIFIED_SCALE`, the precondition of
/// `verified_transcendental_guard_prec`.
pub const EXP_ARG_MAX: u64 = 2_000_000_000;

/// e^0 = 1.
pub(crate) proof fn lemma_exp_zero()
    ensures
        exp_r(0real) == 1real,
{
    lemma_ln_one();
    axiom_exp_ln(1real);
}

/// e^z > 0 and e^z·e^−z = 1.
pub(crate) proof fn lemma_exp_pos(z: real)
    ensures
        exp_r(z) > 0real,
        exp_r(z) * exp_r(-z) == 1real,
{
    lemma_exp_zero();
    axiom_exp_add(z, -z);
    assert(z + (-z) == 0real);
    axiom_exp_add(z / 2real, z / 2real);
    assert(z / 2real + z / 2real == z);
    let h = exp_r(z / 2real);
    assert(h * h >= 0real) by (nonlinear_arith);
    let (e, f) = (exp_r(z), exp_r(-z));
    assert(e > 0real) by (nonlinear_arith)
        requires
            e == h * h,
            h * h >= 0real,
            e * f == 1real,
    ;
}

/// e^a <= e^b for a <= b.
pub(crate) proof fn lemma_exp_mono(a: real, b: real)
    requires
        a <= b,
    ensures
        exp_r(a) <= exp_r(b),
{
    lemma_exp_pos(a);
    axiom_exp_add(a, b - a);
    assert(a + (b - a) == b);
    axiom_exp_ge(b - a);
    let (ea, ed) = (exp_r(a), exp_r(b - a));
    assert(ea <= ea * ed) by (nonlinear_arith)
        requires
            ea > 0real,
            ed >= 1real + (b - a),
            b - a >= 0real,
    ;
}

/// e^(K·z) = (e^z)^K.
pub(crate) proof fn lemma_exp_mul_nat(z: real, k: nat)
    ensures
        exp_r((k as real) * z) == pow_r(exp_r(z), k),
    decreases k,
{
    if k == 0 {
        lemma_exp_zero();
        assert((0nat as real) * z == 0real) by (nonlinear_arith);
    } else {
        lemma_exp_mul_nat(z, (k - 1) as nat);
        let km = ((k - 1) as nat) as real;
        assert((k as real) * z == km * z + z) by (nonlinear_arith)
            requires
                (k as real) == km + 1real,
        ;
        axiom_exp_add(km * z, z);
        let (a, b) = (exp_r(km * z), exp_r(z));
        assert(a * b == b * a) by (nonlinear_arith);
    }
}

/// e^(n·ln 2) = 2^n for n >= 0, and 1/2^−n for n < 0.
pub(crate) proof fn lemma_exp_n_ln2(n: int)
    ensures
        exp_r(ln2_r() * (n as real)) == (if n >= 0 {
            spec_pow_int(2, n as nat) as real
        } else {
            1real / (spec_pow_int(2, (-n) as nat) as real)
        }),
{
    axiom_exp_ln(2real);
    let l2 = ln2_r();
    let m: nat = if n >= 0 {
        n as nat
    } else {
        (-n) as nat
    };
    lemma_exp_mul_nat(l2, m);
    lemma_pow_r_int(2, m);
    lemma_ln_pow2(m);
    let mr = m as real;
    if n >= 0 {
        assert(l2 * (n as real) == mr * l2) by (nonlinear_arith)
            requires
                mr == n as real,
        ;
    } else {
        assert(l2 * (n as real) == -(mr * l2)) by (nonlinear_arith)
            requires
                mr == -(n as real),
        ;
        lemma_exp_pos(mr * l2);
        let p = spec_pow_int(2, m) as real;
        let e = exp_r(-(mr * l2));
        assert(e == 1real / p) by (nonlinear_arith)
            requires
                p * e == 1real,
                p > 0real,
        ;
    }
}

/// e^2.3026 > 10 (2.3026 > ln 10). With z = 2.3026/4, the exponential series' tail bound after
/// nine terms gives e^z >= 1.778284, and 1.778284^4 > 10.
pub(crate) proof fn lemma_exp_23026()
    ensures
        exp_r(23026real / 10000real) > 10real,
{
    let z = 11513real / 20000real;
    let t = |j: nat| exp_term(z, j);
    axiom_exp_series(z, 9);
    lemma_partial_sum_ext(t, |j: nat| exp_term(z, j), 9);
    assert(pow_r(z, 0) == 1real);
    assert(fact(0) == 1);
    assert(pow_r(z, 1) == z * pow_r(z, 0));
    assert(fact(1) == 1 * fact(0));
    assert(pow_r(z, 2) == z * pow_r(z, 1));
    assert(fact(2) == 2 * fact(1));
    assert(pow_r(z, 3) == z * pow_r(z, 2));
    assert(fact(3) == 3 * fact(2));
    assert(pow_r(z, 4) == z * pow_r(z, 3));
    assert(fact(4) == 4 * fact(3));
    assert(pow_r(z, 5) == z * pow_r(z, 4));
    assert(fact(5) == 5 * fact(4));
    assert(pow_r(z, 6) == z * pow_r(z, 5));
    assert(fact(6) == 6 * fact(5));
    assert(pow_r(z, 7) == z * pow_r(z, 6));
    assert(fact(7) == 7 * fact(6));
    assert(pow_r(z, 8) == z * pow_r(z, 7));
    assert(fact(8) == 8 * fact(7));
    assert(pow_r(z, 9) == z * pow_r(z, 8));
    assert(fact(9) == 9 * fact(8));
    let p0 = pow_r(z, 0);
    assert(p0 == 1real / 1real);
    assert(t(0) == p0 / (1int as real));
    assert(p0 / (1int as real) == 1real / 1real) by (nonlinear_arith)
        requires
            p0 == 1real / 1real,
    ;
    let p1 = pow_r(z, 1);
    assert(p1 == 11513real / 20000real);
    assert(t(1) == p1 / (1int as real));
    assert(p1 / (1int as real) == 11513real / 20000real) by (nonlinear_arith)
        requires
            p1 == 11513real / 20000real,
    ;
    let p2 = pow_r(z, 2);
    assert(p2 == 132549169real / 400000000real);
    assert(t(2) == p2 / (2int as real));
    assert(p2 / (2int as real) == 132549169real / 800000000real) by (nonlinear_arith)
        requires
            p2 == 132549169real / 400000000real,
    ;
    let p3 = pow_r(z, 3);
    assert(p3 == 1526038582697real / 8000000000000real);
    assert(t(3) == p3 / (6int as real));
    assert(p3 / (6int as real) == 1526038582697real / 48000000000000real) by (nonlinear_arith)
        requires
            p3 == 1526038582697real / 8000000000000real,
    ;
    let p4 = pow_r(z, 4);
    assert(p4 == 17569282202590561real / 160000000000000000real);
    assert(t(4) == p4 / (24int as real));
    assert(p4 / (24int as real) == 17569282202590561real / 3840000000000000000real) by (nonlinear_arith)
        requires
            p4 == 17569282202590561real / 160000000000000000real,
    ;
    let p5 = pow_r(z, 5);
    assert(p5 == 202275145998425128793real / 3200000000000000000000real);
    assert(t(5) == p5 / (120int as real));
    assert(p5 / (120int as real) == 202275145998425128793real / 384000000000000000000000real) by (nonlinear_arith)
        requires
            p5 == 202275145998425128793real / 3200000000000000000000real,
    ;
    let p6 = pow_r(z, 6);
    assert(p6 == 2328793755879868507793809real / 64000000000000000000000000real);
    assert(t(6) == p6 / (720int as real));
    assert(p6 / (720int as real) == 2328793755879868507793809real / 46080000000000000000000000000real) by (nonlinear_arith)
        requires
            p6 == 2328793755879868507793809real / 64000000000000000000000000real,
    ;
    let p7 = pow_r(z, 7);
    assert(p7 == 26811402511444926130230123017real / 1280000000000000000000000000000real);
    assert(t(7) == p7 / (5040int as real));
    assert(p7 / (5040int as real) == 26811402511444926130230123017real / 6451200000000000000000000000000000real) by (nonlinear_arith)
        requires
            p7 == 26811402511444926130230123017real / 1280000000000000000000000000000real,
    ;
    let p8 = pow_r(z, 8);
    assert(p8 == 308679677114265434537339406294721real / 25600000000000000000000000000000000real);
    assert(t(8) == p8 / (40320int as real));
    assert(p8 / (40320int as real) == 308679677114265434537339406294721real / 1032192000000000000000000000000000000000real) by (nonlinear_arith)
        requires
            p8 == 308679677114265434537339406294721real / 25600000000000000000000000000000000real,
    ;
    let p9 = pow_r(z, 9);
    assert(p9 == 3553829122616537947828388584671122873real / 512000000000000000000000000000000000000real);
    assert(t(9) == p9 / (362880int as real));
    assert(p9 / (362880int as real) == 3553829122616537947828388584671122873real / 185794560000000000000000000000000000000000000real) by (nonlinear_arith)
        requires
            p9 == 3553829122616537947828388584671122873real / 512000000000000000000000000000000000000real,
    ;
    assert(partial_sum(t, 1) == partial_sum(t, 0) + t(0));
    assert(partial_sum(t, 2) == partial_sum(t, 1) + t(1));
    assert(partial_sum(t, 3) == partial_sum(t, 2) + t(2));
    assert(partial_sum(t, 4) == partial_sum(t, 3) + t(3));
    assert(partial_sum(t, 5) == partial_sum(t, 4) + t(4));
    assert(partial_sum(t, 6) == partial_sum(t, 5) + t(5));
    assert(partial_sum(t, 7) == partial_sum(t, 6) + t(6));
    assert(partial_sum(t, 8) == partial_sum(t, 7) + t(7));
    assert(partial_sum(t, 9) == partial_sum(t, 8) + t(8));
    assert(partial_sum(t, 9) == 1835532600425587052051185539480689014721real / 1032192000000000000000000000000000000000real);
    let e = exp_r(z);
    assert(e >= 1778284real / 1000000real);
    lemma_exp_mul_nat(z, 4);
    assert((4nat as real) * z == 23026real / 10000real);
    assert(pow_r(e, 1) == e * pow_r(e, 0));
    assert(pow_r(e, 2) == e * pow_r(e, 1));
    assert(pow_r(e, 3) == e * pow_r(e, 2));
    assert(pow_r(e, 4) == e * pow_r(e, 3));
    assert(pow_r(e, 4) == e * (e * (e * (e * pow_r(e, 0)))));
    assert(e * (e * (e * e)) > 10real) by (nonlinear_arith)
        requires
            e >= 1778284real / 1000000real,
    ;
}

/// e^x truncated at `scale` digits is 0 for x <= −2.3026·(scale + 1): then
/// 0 < e^x < 10^−(scale+1).
pub(crate) proof fn lemma_exp_tiny(x: real, scale: nat)
    requires
        x <= -(23026real / 10000real) * ((scale + 1) as real),
    ensures
        trunc_r(exp_r(x) * (spec_num::pow10(scale) as real)) == 0,
{
    let k = (scale + 1) as nat;
    let c = 23026real / 10000real;
    let kr = k as real;
    lemma_exp_23026();
    lemma_exp_mul_nat(c, k);
    lemma_pow_r_gt(exp_r(c), 10real, k);
    lemma_pow_r_int(10, k);
    lemma_pow10_is_pow(k);
    lemma_exp_pos(kr * c);
    lemma_exp_pos(x);
    assert(-(c * kr) == -(kr * c)) by (nonlinear_arith);
    assert(kr == ((scale + 1) as real));
    assert(-(kr * c) == -(c) * ((scale + 1) as real)) by (nonlinear_arith)
        requires
            kr == ((scale + 1) as real),
    ;
    lemma_exp_mono(x, -(kr * c));
    lemma_pow10_pos(scale);
    lemma_pow10_add(scale, 1);
    let ps = spec_num::pow10(scale) as real;
    let pk = spec_num::pow10(k) as real;
    lemma_cast_mul(spec_num::pow10(scale), 10);
    assert(spec_num::pow10(0) == 1);
    assert(spec_num::pow10(1) == 10);
    assert(pk == ps * 10real);
    let (ex, ek, emk) = (exp_r(x), exp_r(kr * c), exp_r(-(kr * c)));
    let y = ex * ps;
    assert(0real < y && y < 1real) by (nonlinear_arith)
        requires
            ex > 0real,
            ex <= emk,
            ek * emk == 1real,
            ek > pk,
            pk == ps * 10real,
            ps >= 1real,
            y == ex * ps,
    ;
}

/// Term 0 of the exponential series is 1.
pub(crate) proof fn lemma_exp_first_term(r: real)
    ensures
        exp_term(r, 0) == 1real,
{
    assert(pow_r(r, 0) == 1real);
    assert(fact(0) == 1);
    let p0 = pow_r(r, 0);
    assert(p0 / (1int as real) == 1real) by (nonlinear_arith)
        requires
            p0 == 1real,
    ;
}

/// e^x = e^r·2^n with n = floor(x / ln 2) (any integer n is valid) and r = x − n·ln 2, so
/// |r| < 1. The Taylor terms r^k/k! satisfy |term k+1| <= |term k|/2 for k >= 1, so the tail is
/// at most twice the first omitted term (`Series::tail_applies` checks |r| <= 1).
#[allow(
    clippy::cast_sign_loss,
    reason = "n >= 0 in the first branch, and -n > 0 in the last (n > i64::MIN); Verus checks both"
)]
pub(crate) fn exp_ball(x: &BCNum, prec: usize) -> (r: Option<Ball>)
    requires
        prec <= u32::MAX,
        x.scale <= u32::MAX,
    ensures
        r is Some ==> r->Some_0.wf() && r->Some_0.prec == prec && r->Some_0.contains(
            exp_r(bcnum_real(x)),
        ),
{
    // |x| <= 2.31·10^9, so |n| < 3.4·10^9 has at most 10 digits.
    if prec > u32::MAX as usize - 11 {
        return None;
    }
    let work = prec + 11;
    let l2 = ln2(work);
    let xb = Ball::from_bcnum(x, work);
    // Any integer n is valid; floor(x / ln 2) keeps r small. The midpoint of ln 2 is positive.
    let n = if matches!(big_cmp(&l2.mid, &big_from_i64(0)), Ordering::Greater) {
        big_div_mod_floor(&xb.mid, &l2.mid).0
    } else {
        big_from_i64(0)
    };
    let r = xb.sub(&l2.mul_int(&n)).reduce_prec(prec);
    let ghost xv = bcnum_real(x);
    let ghost nv = big_view(&n);
    let ghost rv = xv - ln2_r() * (nv as real);
    proof {
        lemma_exp_first_term(rv);
        assert((1i64 as real) == 1real);
    }
    let series = sum_series(Ball::int(1, prec), &Series::Exp { r }, Ghost(rv))?;
    let n = big_to_i64(&n)?;
    proof {
        axiom_exp_add(rv, ln2_r() * (nv as real));
        assert(rv + ln2_r() * (nv as real) == xv);
        lemma_exp_n_ln2(nv);
    }
    if n >= 0 {
        Some(series.shl(n as u64))
    } else if n == i64::MIN {
        None
    } else {
        let b = series.shr((-n) as u64);
        proof {
            let p = spec_pow_int(2, (-nv) as nat) as real;
            let er = exp_r(rv);
            lemma_ln_pow2((-nv) as nat);
            assert(er / p == er * (1real / p)) by (nonlinear_arith)
                requires
                    p > 0real,
            ;
        }
        Some(b)
    }
}

/// The integer test of `bc_exp`'s shortcut: −c·10^4 >= 23026·(scale + 1)·10^x.scale means
/// x <= −2.3026·(scale + 1).
pub(crate) proof fn lemma_exp_shortcut_bound(x: &BCNum, lhs: int, rhs: int, scale: nat)
    requires
        lhs == (-big_view(&x.coeff)) * 10000,
        rhs == (23026 * (scale + 1)) * spec_num::pow10(x.scale as nat),
        lhs >= rhs,
    ensures
        bcnum_real(x) <= -(23026real / 10000real) * ((scale + 1) as real),
{
    let c = big_view(&x.coeff);
    let d = spec_num::pow10(x.scale as nat);
    let k: int = scale as int + 1;
    lemma_pow10_pos(x.scale as nat);
    lemma_cast_mul(-c, 10000);
    lemma_cast_mul(23026 * k, d);
    lemma_cast_mul(23026, k);
    let (cr, dr, kr) = (c as real, d as real, k as real);
    let (lr, rr) = (lhs as real, rhs as real);
    assert(lr >= rr);
    assert(lr == (-cr) * 10000real);
    assert(rr == 23026real * kr * dr) by (nonlinear_arith)
        requires
            rr == ((23026 * k) as real) * dr,
            (23026 * k) as real == 23026real * kr,
    ;
    assert(cr / dr <= -(23026real / 10000real) * kr) by (nonlinear_arith)
        requires
            (-cr) * 10000real >= 23026real * kr * dr,
            dr >= 1real,
    ;
}

/// Math exponential function: e^x truncated toward zero at `global_scale` digits.
///
/// For x <= -2.3026·(scale+1) the result is below 10^-(scale+1), because 2.3026 > ln 10, so
/// its truncation is exactly 0 and nothing is computed (`lemma_exp_tiny`). An argument whose
/// integer part exceeds `EXP_ARG_MAX` is a `MathArgumentTooLarge` error.
#[allow(
    clippy::cast_sign_loss,
    clippy::cast_possible_truncation,
    clippy::cast_possible_wrap,
    reason = "EXP_ARG_MAX < 2^31, and 0 <= int_part <= EXP_ARG_MAX, so int_part fits u64 and \
              int_part / 2 fits usize; Verus checks the casts"
)]
pub fn bc_exp(x: &BCNum, global_scale: usize) -> (r: Result<BCNum, RuntimeError>)
    requires
        x.scale <= MAX_VERIFIED_SCALE,
        global_scale <= MAX_VERIFIED_SCALE,
    ensures
        r is Ok ==> r->Ok_0.scale == global_scale && big_view(&r->Ok_0.coeff) == trunc_r(
            exp_r(bcnum_real(x)) * (spec_num::pow10(global_scale as nat) as real),
        ),
{
    if big_is_zero(&x.coeff) {
        proof {
            lemma_exp_zero();
            lemma_bcnum_real_zero(x);
            lemma_pow10_pos(global_scale as nat);
            let pr = spec_num::pow10(global_scale as nat) as real;
            assert(1real * pr == pr);
            assert(pr.floor() == spec_num::pow10(global_scale as nat));
        }
        return Ok(exact_result(1, global_scale));
    }
    let negative = big_is_negative(&x.coeff);
    if negative {
        // -x >= 2.3026·(scale+1)  <=>  -coeff·10^4 >= 23026·(scale+1)·10^x.scale
        let lhs = big_mul(&big_neg(&x.coeff), &big_from_i64(10_000));
        let rhs = big_mul(
            &big_mul(&big_from_i64(23_026), &big_add_i64(big_from_usize(global_scale), 1)),
            &pow10_within(x.scale),
        );
        if !matches!(big_cmp(&lhs, &rhs), Ordering::Less) {
            proof {
                lemma_exp_shortcut_bound(x, big_view(&lhs), big_view(&rhs), global_scale as nat);
                lemma_exp_tiny(bcnum_real(x), global_scale as nat);
                lemma_cast_mul(0, spec_num::pow10(global_scale as nat));
            }
            return Ok(exact_result(0, global_scale));
        }
    }
    let int_part = match big_to_i64(&abs_int_part(x)) {
        Some(v) if v <= EXP_ARG_MAX as i64 => v as u64,
        _ => return Err(RuntimeError::MathArgumentTooLarge),
    };
    // For x >= 0, shifting by 2^n multiplies the radius by e^x, whose 0.4343·x integer digits
    // the guard must cover; x/2 digits do. For x < 0 the shift divides it instead. Both stay
    // within MAX_VERIFIED_SCALE because int_part <= EXP_ARG_MAX.
    let extra = if negative {
        0
    } else {
        (int_part / 2) as usize
    };
    proof {
        assert(extra <= MAX_VERIFIED_SCALE);
    }
    let f = |p: usize| -> (b: Option<Ball>)
        requires
            p <= u32::MAX,
            x.scale <= u32::MAX,
        ensures
            b is Some ==> b->Some_0.wf() && b->Some_0.prec == p && b->Some_0.contains(
                exp_r(bcnum_real(x)),
            ),
        { exp_ball(x, p) };
    let r = certify(x.scale, global_scale, extra, f);
    proof {
        assert(all_contain(f, exp_r(bcnum_real(x))));
    }
    r
}

} // verus!
