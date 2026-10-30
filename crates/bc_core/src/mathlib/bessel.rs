// SPDX-License-Identifier: MIT

//! `j(n,x)`: the power series of J_n, with J_{−n} = (−1)^n J_n.

use super::*;

verus! {

/// e <= 2.75 < 3, from the tail bound of the exponential series after four terms.
pub(crate) proof fn lemma_e_le_3()
    ensures
        exp_r(1real) <= 3real,
{
    let t = |j: nat| exp_term(1real, j);
    axiom_exp_series(1real, 4);
    lemma_partial_sum_ext(t, |j: nat| exp_term(1real, j), 4);
    assert(pow_r(1real, 0) == 1real);
    assert(pow_r(1real, 1) == 1real * pow_r(1real, 0));
    assert(pow_r(1real, 2) == 1real * pow_r(1real, 1));
    assert(pow_r(1real, 3) == 1real * pow_r(1real, 2));
    assert(pow_r(1real, 4) == 1real * pow_r(1real, 3));
    assert(fact(0) == 1);
    assert(fact(1) == 1 * fact(0));
    assert(fact(2) == 2 * fact(1));
    assert(fact(3) == 3 * fact(2));
    assert(fact(4) == 4 * fact(3));
    assert(t(0) == 1real / (1int as real));
    assert(t(1) == 1real / (1int as real));
    assert(t(2) == 1real / (2int as real));
    assert(t(3) == 1real / (6int as real));
    assert(t(4) == 1real / (24int as real));
    assert(partial_sum(t, 1) == partial_sum(t, 0) + t(0));
    assert(partial_sum(t, 2) == partial_sum(t, 1) + t(1));
    assert(partial_sum(t, 3) == partial_sum(t, 2) + t(2));
    assert(partial_sum(t, 4) == partial_sum(t, 3) + t(3));
}

/// (n+1)^n <= 3·n^n for n >= 1: (1 + 1/n)^n <= (e^(1/n))^n = e <= 3.
pub(crate) proof fn lemma_pow_ratio(n: nat)
    requires
        n >= 1,
    ensures
        pow_r((n + 1) as real, n) <= 3real * pow_r(n as real, n),
{
    let nr = n as real;
    let u = 1real / nr;
    let q = 1real + u;
    axiom_exp_ge(u);
    assert(u > 0real && q > 0real) by (nonlinear_arith)
        requires
            nr >= 1real,
            u == 1real / nr,
            q == 1real + u,
    ;
    lemma_pow_r_mono(q, exp_r(u), n);
    lemma_exp_mul_nat(u, n);
    assert(nr * u == 1real) by (nonlinear_arith)
        requires
            nr >= 1real,
            u == 1real / nr,
    ;
    lemma_e_le_3();
    assert(((n + 1) as real) == nr + 1real);
    assert(q * nr == (n + 1) as real) by (nonlinear_arith)
        requires
            ((n + 1) as real) == nr + 1real,
            nr >= 1real,
            u == 1real / nr,
            q == 1real + u,
    ;
    lemma_pow_r_mul(q, nr, n);
    lemma_pow_r_mono(0real, nr, n);
    let (pq, pn) = (pow_r(q, n), pow_r(nr, n));
    assert(pq * pn <= 3real * pn) by (nonlinear_arith)
        requires
            pq <= 3real,
            pn >= 0real,
    ;
}

/// n^n <= 3^n·n!.
pub(crate) proof fn lemma_fact_lower(n: nat)
    ensures
        pow_r(n as real, n) <= pow_r(3real, n) * (fact(n) as real),
    decreases n,
{
    if n == 0 {
        assert(fact(0) == 1);
    } else {
        let m = (n - 1) as nat;
        lemma_fact_lower(m);
        lemma_fact_pos(m);
        lemma_pow_r_mono(0real, m as real, m);
        lemma_pow_r_mono(0real, 3real, m);
        let (pm, p3, fm) = (pow_r(m as real, m), pow_r(3real, m), fact(m) as real);
        // (m+1)^m <= 3·m^m (or 1 <= 3 when m = 0).
        let pn = pow_r(n as real, m);
        if m >= 1 {
            lemma_pow_ratio(m);
        } else {
            assert(pn == 1real && pm == 1real);
        }
        assert(fact(n) == n * fact(m));
        lemma_cast_mul(n as int, fact(m) as int);
        let nr = n as real;
        assert(nr * pn <= (3real * p3) * (nr * fm)) by (nonlinear_arith)
            requires
                pn <= 3real * pm,
                pm <= p3 * fm,
                nr >= 1real,
                pm >= 0real,
        ;
    }
}

/// (1/2)^(4K)·10^K <= 5/8 for K >= 1.
pub(crate) proof fn lemma_half_pow(k: nat)
    requires
        k >= 1,
    ensures
        pow_r(1real / 2real, 4 * k) * pow_r(10real, k) <= 5real / 8real,
    decreases k,
{
    let h = 1real / 2real;
    let m = (4 * (k - 1)) as nat;
    assert(4 * k == m + 4);
    assert(pow_r(h, m + 4) == h * pow_r(h, (m + 3) as nat));
    assert(pow_r(h, (m + 3) as nat) == h * pow_r(h, (m + 2) as nat));
    assert(pow_r(h, (m + 2) as nat) == h * pow_r(h, (m + 1) as nat));
    assert(pow_r(h, (m + 1) as nat) == h * pow_r(h, m));
    assert(pow_r(10real, k) == 10real * pow_r(10real, (k - 1) as nat));
    let (ph, pt) = (pow_r(h, m), pow_r(10real, (k - 1) as nat));
    if k == 1 {
        assert(ph == 1real && pt == 1real);
    } else {
        lemma_half_pow((k - 1) as nat);
    }
    lemma_pow_r_mono(0real, h, m);
    lemma_pow_r_mono(0real, 10real, (k - 1) as nat);
    assert((h * (h * (h * (h * ph)))) * (10real * pt) <= 5real / 8real) by (nonlinear_arith)
        requires
            h == 1real / 2real,
            ph * pt <= 5real / 8real || (ph == 1real && pt == 1real),
            ph >= 0real,
            pt >= 0real,
    ;
}

/// For |n| >= 3·|x| and |n| >= 4·(scale + 1), J_n(x) truncates to 0 at `scale` digits:
/// |J_n(x)| <= (|x|/2)^n / n! <= (n/6)^n / n! <= 2^−n <= 2^−4(scale+1) < 10^−(scale+1).
pub(crate) proof fn lemma_bessel_tiny(n: nat, x: real, scale: nat)
    requires
        (n as real) >= 3real * abs_r(x),
        n >= 4 * (scale + 1),
    ensures
        abs_r(bessel_r(n, x) * (spec_num::pow10(scale) as real)) < 1real,
{
    let nr = n as real;
    let a = abs_r(x / 2real);
    axiom_bessel_bound(n, x);
    lemma_fact_pos(n);
    lemma_fact_lower(n);
    let fr = fact(n) as real;
    assert(a <= nr / 6real) by (nonlinear_arith)
        requires
            nr >= 3real * abs_r(x),
            a == abs_r(x / 2real),
            abs_r(x) >= 0real,
            a == abs_r(x) / 2real,
    ;
    assert(nr / 6real == (nr * (1real / 3real)) * (1real / 2real));
    lemma_pow_r_mono(a, nr / 6real, n);
    lemma_pow_r_mul(nr * (1real / 3real), 1real / 2real, n);
    lemma_pow_r_mul(nr, 1real / 3real, n);
    lemma_pow_r_mul(3real, 1real / 3real, n);
    assert(3real * (1real / 3real) == 1real);
    lemma_pow_r_one(n);
    lemma_pow_r_mono(0real, nr, n);
    lemma_pow_r_mono(0real, 1real / 3real, n);
    lemma_pow_r_mono(0real, 1real / 2real, n);
    let (pa, pn, p3, pt, p2) = (
        pow_r(a, n),
        pow_r(nr, n),
        pow_r(3real, n),
        pow_r(1real / 3real, n),
        pow_r(1real / 2real, n),
    );
    // |J| <= pa / n! <= pn·pt·p2 / n! <= 3^n·n!·pt·p2 / n! = p2.
    let b = abs_r(bessel_r(n, x));
    assert(b <= p2) by (nonlinear_arith)
        requires
            b <= pa / fr,
            pa <= (pn * pt) * p2,
            pn <= p3 * fr,
            p3 * pt == 1real,
            fr >= 1real,
            pt >= 0real,
            p2 >= 0real,
            pn >= 0real,
    ;
    let k = (scale + 1) as nat;
    lemma_pow_r_le_one(1real / 2real, 4 * k, n);
    lemma_half_pow(k);
    lemma_pow_r_int(10, k);
    lemma_pow10_is_pow(k);
    lemma_pow10_pos(scale);
    lemma_pow10_add(scale, 1);
    assert(spec_num::pow10(0) == 1);
    assert(spec_num::pow10(1) == 10);
    lemma_cast_mul(spec_num::pow10(scale), 10);
    let ps = spec_num::pow10(scale) as real;
    let p16 = pow_r(1real / 2real, 4 * k);
    let pk = pow_r(10real, k);
    assert(pk == ps * 10real);
    lemma_abs_mul(bessel_r(n, x), ps);
    assert(b * ps < 1real) by (nonlinear_arith)
        requires
            b <= p2,
            p2 <= p16,
            p16 * pk <= 5real / 8real,
            pk == ps * 10real,
            ps >= 1real,
            b >= 0real,
    ;
}

/// J_n(0) is 1 for n = 0 and 0 otherwise, from the tail bound of the series after one term.
pub(crate) proof fn lemma_bessel_zero(n: nat)
    ensures
        bessel_r(n, 0real) == (if n == 0 {
            1real
        } else {
            0real
        }),
{
    let z = 0real;
    let t = |m: nat| bessel_term(n, z / 2real, m);
    assert(z / 2real == 0real);
    axiom_bessel_series(n, z, 1);
    lemma_partial_sum_ext(t, |m: nat| bessel_term(n, z / 2real, m), 1);
    assert(partial_sum(t, 1) == partial_sum(t, 0) + t(0));
    lemma_fact_pos(n);
    lemma_fact_pos(n + 1);
    assert(fact(0) == 1 && fact(1) == 1 * fact(0));
    assert(pow_r(z, n + 2) == z * pow_r(z, n + 1));
    let p0 = pow_r(z, n);
    if n == 0 {
        assert(p0 == 1real);
    } else {
        assert(p0 == z * pow_r(z, (n - 1) as nat));
    }
    let (f0n, f1n) = ((fact(0) * fact(n)) as real, (fact(1) * fact(n + 1)) as real);
    lemma_cast_mul(fact(0) as int, fact(n) as int);
    lemma_cast_mul(fact(1) as int, fact(n + 1) as int);
    assert(sign_r(0) == 1real && sign_r(1) == -1real);
    assert(t(0) == sign_r(0) * p0 / f0n);
    assert(t(1) == sign_r(1) * pow_r(z, n + 2) / f1n);
    assert(t(1) == 0real) by (nonlinear_arith)
        requires
            t(1) == sign_r(1) * pow_r(z, n + 2) / f1n,
            pow_r(z, n + 2) == z * pow_r(z, n + 1),
            z == 0real,
            f1n >= 1real,
    ;
    assert(t(0) == (if n == 0 { 1real } else { 0real })) by (nonlinear_arith)
        requires
            t(0) == sign_r(0) * p0 / f0n,
            sign_r(0) == 1real,
            n == 0 ==> p0 == 1real && f0n == 1real,
            n != 0 ==> p0 == 0real,
            f0n >= 1real,
    ;
}

/// The term (x/2)^i / i!, one step further.
pub(crate) proof fn lemma_bessel_first_step(h: real, i: nat)
    requires
        i >= 1,
    ensures
        (pow_r(h, (i - 1) as nat) / (fact((i - 1) as nat) as real)) * h / (i as real) == pow_r(h, i)
            / (fact(i) as real),
{
    let j = (i - 1) as nat;
    lemma_fact_pos(j);
    assert(pow_r(h, i) == h * pow_r(h, j));
    assert(fact(i) == i * fact(j));
    lemma_cast_mul(i as int, fact(j) as int);
    let (p, f, ir) = (pow_r(h, j), fact(j) as real, i as real);
    assert((p / f) * h / ir == (h * p) / (ir * f)) by (nonlinear_arith)
        requires
            f >= 1real,
            ir >= 1real,
    ;
}

/// J_n(x) for n >= 0 by the power series Σ_m (−1)^m (x/2)^(2m+n) / (m!·(m+n)!). The terms
/// decrease once (m+1)(m+n+1) >= (x/2)², after which the tail is at most the first omitted term.
pub(crate) fn bessel_ball(n: u64, x: &BCNum, prec: usize) -> (r: Option<Ball>)
    requires
        n < 0x8000_0000_0000_0000,
        prec <= u32::MAX,
        x.scale <= u32::MAX,
    ensures
        r is Some ==> r->Some_0.wf() && r->Some_0.prec == prec && r->Some_0.contains(
            bessel_r(n as nat, bcnum_real(x)),
        ),
{
    let half = Ball::from_bcnum(x, prec).div_int(&big_from_i64(2));
    let ghost h = bcnum_real(x) / 2real;
    let mut first = Ball::int(1, prec);
    proof {
        assert((1i64 as real) == 1real);
        assert(pow_r(h, 0) == 1real && fact(0) == 1);
        let (p0, f0) = (pow_r(h, 0), fact(0) as real);
        assert(1real == p0 / f0) by (nonlinear_arith)
            requires
                p0 == 1real,
                f0 == 1real,
        ;
    }
    let mut i: u64 = 1;
    while i <= n
        invariant
            1 <= i <= n + 1,
            n < 0x8000_0000_0000_0000,
            half.wf() && half.prec == prec && half.contains(h),
            first.wf() && first.prec == prec,
            first.contains(pow_r(h, (i - 1) as nat) / (fact((i - 1) as nat) as real)),
        decreases n + 1 - i,
    {
        first = first.mul(&half).div_int(&big_from_u64(i));
        proof {
            lemma_bessel_first_step(h, i as nat);
        }
        i += 1;
    }
    let half_sq = half.mul(&half);
    proof {
        lemma_fact_pos(n as nat);
        let (p, f) = (pow_r(h, n as nat), fact(n as nat) as real);
        assert(fact(0) == 1);
        lemma_cast_mul(1, fact(n as nat) as int);
        assert(sign_r(0) == 1real);
        assert(bessel_term(n as nat, h, 0) == sign_r(0) * p / ((fact(0) * fact(n as nat)) as real));
        assert(sign_r(0) * p / ((fact(0) * fact(n as nat)) as real) == p / f) by (nonlinear_arith)
            requires
                sign_r(0) == 1real,
                ((fact(0) * fact(n as nat)) as real) == f,
                f >= 1real,
        ;
        assert(2real * h == bcnum_real(x));
    }
    sum_series(first, &Series::Bessel { half_sq, n }, Ghost(h))
}

/// The order of `j(n, x)`: n truncated toward zero to an integer.
pub open spec fn bessel_order(n_num: &BCNum) -> int {
    spec_tdiv(big_view(&n_num.coeff), spec_num::pow10(n_num.scale as nat))
}

/// Bessel function of the first kind J_n(x), with `n` truncated to an integer, truncated toward
/// zero at `global_scale` digits.
///
/// For |n| >= 3·ceil(|x|) and |n| >= 4·(scale+1), |J_n(x)| <= (|x|/2)^|n| / |n|!
/// <= (3·|x| / |n|)^|n|·2^-|n| <= 2^-|n| < 10^-scale (using |n|! >= (|n|/3)^|n|,
/// `lemma_fact_lower`), so the truncated result is exactly 0 (`lemma_bessel_tiny`). Any other
/// order outside the range of `i64`, or an x whose integer part exceeds `EXP_ARG_MAX`, cannot be
/// computed and is a `MathArgumentTooLarge` error.
#[allow(
    clippy::cast_sign_loss,
    clippy::cast_possible_truncation,
    clippy::cast_possible_wrap,
    reason = "n_abs >= 0, EXP_ARG_MAX < 2^31, and 0 <= int_part <= EXP_ARG_MAX, so int_part / 2 \
              fits usize; Verus checks the casts"
)]
pub fn bc_bessel(n_num: &BCNum, x: &BCNum, global_scale: usize) -> (r: Result<BCNum, RuntimeError>)
    requires
        n_num.scale <= MAX_VERIFIED_SCALE,
        x.scale <= MAX_VERIFIED_SCALE,
        global_scale <= MAX_VERIFIED_SCALE,
    ensures
        r is Ok ==> r->Ok_0.scale == global_scale && big_view(&r->Ok_0.coeff) == trunc_r(
            bessel_int_r(bessel_order(n_num), bcnum_real(x)) * (spec_num::pow10(
                global_scale as nat,
            ) as real),
        ),
{
    proof {
        lemma_pow10_pos(n_num.scale as nat);
        lemma_pow10_pos(x.scale as nat);
    }
    let n = big_tdiv(&n_num.coeff, &pow10_within(n_num.scale));
    let n_abs_big = big_abs(&n);
    let x_ceil = big_tdiv(
        &big_add_i64(big_add(&big_abs(&x.coeff), &pow10_within(x.scale)), -1),
        &pow10_within(x.scale),
    );
    if !matches!(big_cmp(&n_abs_big, &big_mul(&big_from_i64(3), &x_ceil)), Ordering::Less)
        && !matches!(
            big_cmp(
                &n_abs_big,
                &big_mul(&big_from_i64(4), &big_add_i64(big_from_usize(global_scale), 1)),
            ),
            Ordering::Less
        )
    {
        proof {
            let na = big_view(&n_abs_big);
            let xv = bcnum_real(x);
            lemma_bessel_ceil(x, big_view(&x_ceil));
            lemma_cast_mul(3, big_view(&x_ceil));
            assert((na as real) >= 3real * abs_r(xv));
            lemma_bessel_tiny(na as nat, xv, global_scale as nat);
            let j = bessel_int_r(big_view(&n), xv);
            let ps = spec_num::pow10(global_scale as nat) as real;
            if big_view(&n) < 0 {
                lemma_abs_mul(bessel_r(na as nat, xv), ps);
                lemma_abs_mul(j, ps);
                let s = sign_r(na as nat);
                assert(abs_r(j) == abs_r(bessel_r(na as nat, xv))) by (nonlinear_arith)
                    requires
                        j == s * bessel_r(na as nat, xv),
                        s == 1real || s == -1real,
                ;
            }
            lemma_trunc_small(j * ps);
            lemma_cast_mul(0, spec_num::pow10(global_scale as nat));
        }
        return Ok(exact_result(0, global_scale));
    }
    let n_i64 = match big_to_i64(&n) {
        Some(v) if v > i64::MIN => v,
        _ => return Err(RuntimeError::MathArgumentTooLarge),
    };
    if big_is_zero(&x.coeff) {
        proof {
            lemma_bcnum_real_zero(x);
            let na: nat = if n_i64 >= 0 {
                n_i64 as nat
            } else {
                (-n_i64) as nat
            };
            lemma_bessel_zero(na);
            lemma_pow10_pos(global_scale as nat);
            let ps = spec_num::pow10(global_scale as nat) as real;
            if n_i64 == 0 {
                assert(1real * ps == ps);
                assert(ps.floor() == spec_num::pow10(global_scale as nat));
            } else {
                let s = sign_r(na);
                assert(s * 0real == 0real) by (nonlinear_arith);
                assert(0real * ps == 0real) by (nonlinear_arith);
                lemma_cast_mul(0, spec_num::pow10(global_scale as nat));
            }
        }
        return Ok(exact_result(if n_i64 == 0 { 1 } else { 0 }, global_scale));
    }
    let int_part = match big_to_i64(&abs_int_part(x)) {
        Some(v) if v <= EXP_ARG_MAX as i64 => v as u64,
        _ => return Err(RuntimeError::MathArgumentTooLarge),
    };
    let (n_abs, sign) = verified_bessel_negative_order_parity(n_i64);
    let n_abs = n_abs as u64;
    // The terms grow to about e^|x| before they decrease, and their radii with them; |x|/2 extra
    // digits cover that (and stay within MAX_VERIFIED_SCALE because int_part <= EXP_ARG_MAX).
    let extra = (int_part / 2) as usize;
    let ghost target = bessel_int_r(n_i64 as int, bcnum_real(x));
    proof {
        let s = sign as real;
        if n_i64 < 0 {
            if (-(n_i64 as int)) % 2 == 1 {
                assert(sign_r(n_abs as nat) == -1real);
            } else {
                assert(sign_r(n_abs as nat) == 1real);
            }
        }
        let jv = bessel_r(n_abs as nat, bcnum_real(x));
        if n_i64 >= 0 {
            assert(s == 1real);
            assert(target == jv);
            assert(jv * s == target) by (nonlinear_arith)
                requires
                    s == 1real,
                    target == jv,
            ;
        } else {
            let sr = sign_r(n_abs as nat);
            assert(s == sr);
            assert(target == sr * jv);
            assert(jv * s == target) by (nonlinear_arith)
                requires
                    s == sr,
                    target == sr * jv,
            ;
        }
    }
    let f = |p: usize| -> (b: Option<Ball>)
        requires
            p <= u32::MAX,
            x.scale <= u32::MAX,
            n_abs < 0x8000_0000_0000_0000,
        ensures
            b is Some ==> b->Some_0.wf() && b->Some_0.prec == p && b->Some_0.contains(
                bessel_r(n_abs as nat, bcnum_real(x)) * (sign as real),
            ),
        {
            let b = bessel_ball(n_abs, x, p)?;
            Some(b.mul_int(&big_from_i64(sign)))
        };
    let r = certify(x.scale, global_scale, extra, f);
    proof {
        assert(all_contain(f, target));
    }
    r
}

/// ⌈|x|⌉ as `bc_bessel` computes it bounds |x|.
pub(crate) proof fn lemma_bessel_ceil(x: &BCNum, c: int)
    requires
        c == (abs_i(big_view(&x.coeff)) + spec_num::pow10(x.scale as nat) - 1) / spec_num::pow10(
            x.scale as nat,
        ),
    ensures
        (c as real) >= abs_r(bcnum_real(x)),
{
    let d = spec_num::pow10(x.scale as nat);
    let a = abs_i(big_view(&x.coeff));
    lemma_pow10_pos(x.scale as nat);
    lemma_ceil_div(a, d);
    lemma_cast_abs(big_view(&x.coeff));
    let (ar, dr, cr) = (a as real, d as real, c as real);
    assert(cr * dr >= ar);
    let cv = big_view(&x.coeff) as real;
    assert(abs_r(cv / dr) == abs_r(cv) / dr) by (nonlinear_arith)
        requires
            dr >= 1real,
    ;
    assert(cr >= ar / dr) by (nonlinear_arith)
        requires
            cr * dr >= ar,
            dr >= 1real,
    ;
}

/// A real of magnitude below 1 truncates to 0.
pub(crate) proof fn lemma_trunc_small(y: real)
    requires
        abs_r(y) < 1real,
    ensures
        trunc_r(y) == 0,
{
}

} // verus!
