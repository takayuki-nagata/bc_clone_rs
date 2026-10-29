// SPDX-License-Identifier: MIT

//! Proved facts about `real` for the math-library proofs: integer casts, the
//! ball predicate `in_ball`, the containment of each ball operation of `mathlib::Ball`, and
//! the certified-truncation decision over the reals. Nothing here is assumed; the trusted facts
//! about the functions themselves are in `trusted_math.rs`. Compiled only under Verus.
//!
//! A ball at precision p is a midpoint and a radius in ulps of 10^−p; it contains the real v if
//! |v·10^p − mid| <= rad. The lemmas take the unit u = 10^p as an integer argument, so that they
//! do not depend on how u is computed.

use crate::spec_num::{pow10, spec_pow_int, spec_tdiv, trunc_div};
use crate::trusted_math::{
    abs_r, artanh_term, atan_term, axiom_sqrt, bessel_term, exp_term, fact, partial_sum, pow_r,
    sign_r, sin_cos_term, sqrt_r,
};
use vstd::prelude::*;

verus! {

/// The ball (mid, rad) at unit u (= 10^p) contains v.
pub open spec fn in_ball(mid: int, rad: int, u: int, v: real) -> bool {
    abs_r(v * (u as real) - (mid as real)) <= rad as real
}

/// The truncation of y toward zero.
pub open spec fn trunc_r(y: real) -> int {
    if y >= 0real {
        y.floor()
    } else {
        -((-y).floor())
    }
}

/// |a|.
pub open spec fn abs_i(a: int) -> int {
    if a < 0 {
        -a
    } else {
        a
    }
}

/// ⌈a / b⌉ for a >= 0 and b > 0, as `mathlib::ceil_div` computes it.
pub open spec fn ceil_div_i(a: int, b: int) -> int {
    (a + b - 1) / b
}

pub proof fn lemma_cast_add(a: int, b: int)
    ensures
        (a + b) as real == (a as real) + (b as real),
        (a - b) as real == (a as real) - (b as real),
        (-a) as real == -(a as real),
{
}

pub proof fn lemma_cast_mul(a: int, b: int)
    ensures
        (a * b) as real == (a as real) * (b as real),
{
    assert((a * b) as real == (a as real) * (b as real)) by (nonlinear_arith);
}

pub proof fn lemma_cast_abs(a: int)
    ensures
        abs_r(a as real) == abs_i(a) as real,
{
}

/// |x·y| = |x|·|y|.
pub proof fn lemma_abs_mul(x: real, y: real)
    ensures
        abs_r(x * y) == abs_r(x) * abs_r(y),
{
    if x >= 0real && y >= 0real {
        assert(x * y >= 0real) by (nonlinear_arith)
            requires
                x >= 0real,
                y >= 0real,
        ;
    } else if x >= 0real {
        assert(x * y <= 0real && -(x * y) == x * (-y)) by (nonlinear_arith)
            requires
                x >= 0real,
                y < 0real,
        ;
    } else if y >= 0real {
        assert(x * y <= 0real && -(x * y) == (-x) * y) by (nonlinear_arith)
            requires
                x < 0real,
                y >= 0real,
        ;
    } else {
        assert(x * y > 0real && x * y == (-x) * (-y)) by (nonlinear_arith)
            requires
                x < 0real,
                y < 0real,
        ;
    }
}

/// The truncating quotient is within 1 of the real quotient.
pub proof fn lemma_trunc_div_close(a: int, b: int)
    requires
        b > 0,
    ensures
        abs_r((a as real) / (b as real) - (trunc_div(a, b) as real)) < 1real,
{
    let q = trunc_div(a, b);
    if a >= 0 {
        assert(q * b <= a && a < q * b + b) by (nonlinear_arith)
            requires
                b > 0,
                a >= 0,
                q == a / b,
        ;
    } else {
        let q2 = (-a) / b;
        assert(q2 * b <= -a && -a < q2 * b + b) by (nonlinear_arith)
            requires
                b > 0,
                a < 0,
                q2 == (-a) / b,
        ;
        assert(q * b == -(q2 * b)) by (nonlinear_arith)
            requires
                q == -q2,
        ;
    }
    lemma_cast_mul(q, b);
    let ar = a as real;
    let br = b as real;
    let qr = q as real;
    assert(abs_r(ar / br - qr) < 1real) by (nonlinear_arith)
        requires
            br > 0real,
            ar - br < qr * br,
            qr * br < ar + br,
    ;
}

/// `BigInt`'s truncating quotient (for a divisor of either sign) is within 1 of the real
/// quotient.
pub proof fn lemma_spec_tdiv_close(a: int, b: int)
    requires
        b != 0,
    ensures
        abs_r((a as real) / (b as real) - (spec_tdiv(a, b) as real)) < 1real,
{
    if b > 0 {
        assert(spec_tdiv(a, b) == trunc_div(a, b));
        lemma_trunc_div_close(a, b);
    } else {
        assert(spec_tdiv(a, b) == -trunc_div(a, -b));
        lemma_trunc_div_close(a, -b);
        let ar = a as real;
        let br = b as real;
        assert(ar / br == -(ar / (-br))) by (nonlinear_arith)
            requires
                br < 0real,
        ;
    }
}

/// The floor quotient (Verus's `/` for a positive divisor) is at most the real quotient and
/// within 1 of it.
pub proof fn lemma_floor_div_close(a: int, b: int)
    requires
        b > 0,
    ensures
        ((a / b) as real) <= (a as real) / (b as real),
        (a as real) / (b as real) < ((a / b) as real) + 1real,
{
    let q = a / b;
    assert(q * b <= a && a < q * b + b) by (nonlinear_arith)
        requires
            b > 0,
            q == a / b,
    ;
    lemma_cast_mul(q, b);
    let ar = a as real;
    let br = b as real;
    let qr = q as real;
    assert(qr <= ar / br && ar / br < qr + 1real) by (nonlinear_arith)
        requires
            br > 0real,
            qr * br <= ar,
            ar < qr * br + br,
    ;
}

pub proof fn lemma_ceil_div(r: int, k: int)
    requires
        r >= 0,
        k > 0,
    ensures
        ceil_div_i(r, k) >= 0,
        (ceil_div_i(r, k) as real) * (k as real) >= r as real,
{
    let c = ceil_div_i(r, k);
    assert(c >= 0 && c * k >= r) by (nonlinear_arith)
        requires
            k > 0,
            r >= 0,
            c == (r + k - 1) / k,
    ;
    lemma_cast_mul(c, k);
}

// --- Ball operations (`mathlib::Ball`, docs/MATH_ERROR_BOUNDS.md §2) ---

/// A ± B: radii add.
pub proof fn lemma_ball_add(ma: int, ra: int, mb: int, rb: int, u: int, va: real, vb: real)
    requires
        u > 0,
        in_ball(ma, ra, u, va),
        in_ball(mb, rb, u, vb),
    ensures
        in_ball(ma + mb, ra + rb, u, va + vb),
        in_ball(ma - mb, ra + rb, u, va - vb),
{
    lemma_cast_add(ma, mb);
    lemma_cast_add(ra, rb);
    let ur = u as real;
    assert((va + vb) * ur == va * ur + vb * ur) by (nonlinear_arith);
    assert((va - vb) * ur == va * ur - vb * ur) by (nonlinear_arith);
}

/// −A.
pub proof fn lemma_ball_neg(ma: int, ra: int, u: int, va: real)
    requires
        in_ball(ma, ra, u, va),
    ensures
        in_ball(-ma, ra, u, -va),
{
    let ur = u as real;
    assert((-va) * ur == -(va * ur)) by (nonlinear_arith);
}

/// k·A for an integer k.
pub proof fn lemma_ball_mul_int(ma: int, ra: int, u: int, va: real, k: int)
    requires
        in_ball(ma, ra, u, va),
    ensures
        in_ball(ma * k, ra * abs_i(k), u, va * (k as real)),
{
    lemma_cast_mul(ma, k);
    lemma_cast_mul(ra, abs_i(k));
    let ur = u as real;
    let kr = k as real;
    let d = va * ur - (ma as real);
    assert(va * kr * ur - (ma as real) * kr == d * kr) by (nonlinear_arith)
        requires
            d == va * ur - (ma as real),
    ;
    assert(abs_r(d * kr) <= (ra as real) * (abs_i(k) as real)) by (nonlinear_arith)
        requires
            abs_r(d) <= ra as real,
            abs_i(k) as real == abs_r(kr),
    ;
}

/// A / k for an integer k > 0, with the quotient of the midpoint truncated toward zero.
pub proof fn lemma_ball_div_int(ma: int, ra: int, u: int, va: real, k: int)
    requires
        u > 0,
        ra >= 0,
        k > 0,
        in_ball(ma, ra, u, va),
    ensures
        in_ball(trunc_div(ma, k), ceil_div_i(ra, k) + 1, u, va / (k as real)),
{
    lemma_trunc_div_close(ma, k);
    lemma_ceil_div(ra, k);
    lemma_cast_add(ceil_div_i(ra, k), 1);
    let ur = u as real;
    let kr = k as real;
    let a = va * ur;
    let m = ma as real;
    let q = trunc_div(ma, k) as real;
    let c = ceil_div_i(ra, k) as real;
    assert(va / kr * ur == a / kr) by (nonlinear_arith)
        requires
            kr > 0real,
            a == va * ur,
    ;
    assert(abs_r(a / kr - q) <= c + 1real) by (nonlinear_arith)
        requires
            kr > 0real,
            abs_r(a - m) <= ra as real,
            abs_r(m / kr - q) < 1real,
            c * kr >= ra as real,
    ;
}

/// A / k for an integer k > 0, with the quotient of the midpoint rounded down (as an arithmetic
/// right shift does).
pub proof fn lemma_ball_div_int_floor(ma: int, ra: int, u: int, va: real, k: int)
    requires
        u > 0,
        ra >= 0,
        k > 0,
        in_ball(ma, ra, u, va),
    ensures
        in_ball(ma / k, ceil_div_i(ra, k) + 1, u, va / (k as real)),
{
    lemma_floor_div_close(ma, k);
    lemma_ceil_div(ra, k);
    lemma_cast_add(ceil_div_i(ra, k), 1);
    let ur = u as real;
    let kr = k as real;
    let a = va * ur;
    let m = ma as real;
    let q = (ma / k) as real;
    let c = ceil_div_i(ra, k) as real;
    assert(va / kr * ur == a / kr) by (nonlinear_arith)
        requires
            kr > 0real,
            a == va * ur,
    ;
    assert(abs_r(a / kr - q) <= c + 1real) by (nonlinear_arith)
        requires
            kr > 0real,
            abs_r(a - m) <= ra as real,
            q <= m / kr,
            m / kr < q + 1real,
            c * kr >= ra as real,
    ;
}

/// A·B at unit u: |A·B − MA·MB| <= |MA|·RB + |MB|·RA + RA·RB in units of u², and the midpoint
/// MA·MB / u is truncated toward zero.
pub proof fn lemma_ball_mul(ma: int, ra: int, mb: int, rb: int, u: int, va: real, vb: real)
    requires
        u > 0,
        ra >= 0,
        rb >= 0,
        in_ball(ma, ra, u, va),
        in_ball(mb, rb, u, vb),
    ensures
        in_ball(
            trunc_div(ma * mb, u),
            ceil_div_i(abs_i(ma) * rb + abs_i(mb) * ra + ra * rb, u) + 1,
            u,
            va * vb,
        ),
{
    let ur = u as real;
    let a = va * ur;
    let b = vb * ur;
    let mar = ma as real;
    let rar = ra as real;
    let mbr = mb as real;
    let rbr = rb as real;
    let da = a - mar;
    let db = b - mbr;
    assert(a * b - mar * mbr == mar * db + mbr * da + da * db) by (nonlinear_arith)
        requires
            da == a - mar,
            db == b - mbr,
    ;
    assert(abs_r(mar * db) <= abs_r(mar) * rbr) by (nonlinear_arith)
        requires
            abs_r(db) <= rbr,
            rbr >= 0real,
    ;
    assert(abs_r(mbr * da) <= abs_r(mbr) * rar) by (nonlinear_arith)
        requires
            abs_r(da) <= rar,
            rar >= 0real,
    ;
    assert(abs_r(da * db) <= rar * rbr) by (nonlinear_arith)
        requires
            abs_r(da) <= rar,
            abs_r(db) <= rbr,
            rar >= 0real,
            rbr >= 0real,
    ;
    let spread = abs_i(ma) * rb + abs_i(mb) * ra + ra * rb;
    lemma_cast_mul(abs_i(ma), rb);
    lemma_cast_mul(abs_i(mb), ra);
    lemma_cast_mul(ra, rb);
    lemma_cast_mul(ma, mb);
    lemma_cast_abs(ma);
    lemma_cast_abs(mb);
    let sr = spread as real;
    let p = (ma * mb) as real;
    assert(abs_r(a * b - p) <= sr);
    lemma_trunc_div_close(ma * mb, u);
    assert(spread >= 0) by (nonlinear_arith)
        requires
            ra >= 0,
            rb >= 0,
            abs_i(ma) >= 0,
            abs_i(mb) >= 0,
            spread == abs_i(ma) * rb + abs_i(mb) * ra + ra * rb,
    ;
    lemma_ceil_div(spread, u);
    lemma_cast_add(ceil_div_i(spread, u), 1);
    let m = trunc_div(ma * mb, u) as real;
    let c = ceil_div_i(spread, u) as real;
    assert(va * vb * ur == a * b / ur) by (nonlinear_arith)
        requires
            ur > 0real,
            a == va * ur,
            b == vb * ur,
    ;
    assert(abs_r(a * b / ur - m) <= c + 1real) by (nonlinear_arith)
        requires
            ur > 0real,
            abs_r(a * b - p) <= sr,
            abs_r(p / ur - m) < 1real,
            c * ur >= sr,
    ;
}

/// A / B (|MB| > RB, so B is not 0): with N = RA·|MB| + |MA|·RB and D = (|MB| − RB)·|MB|,
/// |A/B − MA/MB| = |δA·MB − MA·δB| / (|B|·|MB|) <= N / D since |B| >= |MB| − RB. The
/// midpoint MA·u / MB is truncated toward zero.
pub proof fn lemma_ball_div(ma: int, ra: int, mb: int, rb: int, u: int, va: real, vb: real)
    requires
        u > 0,
        ra >= 0,
        rb >= 0,
        abs_i(mb) > rb,
        in_ball(ma, ra, u, va),
        in_ball(mb, rb, u, vb),
    ensures
        vb != 0real,
        in_ball(
            spec_tdiv(ma * u, mb),
            ceil_div_i((ra * abs_i(mb) + abs_i(ma) * rb) * u, (abs_i(mb) - rb) * abs_i(mb)) + 1,
            u,
            va / vb,
        ),
{
    let ur = u as real;
    let a = va * ur;
    let b = vb * ur;
    let mar = ma as real;
    let mbr = mb as real;
    let rar = ra as real;
    let rbr = rb as real;
    let amb = abs_r(mbr);
    lemma_cast_abs(mb);
    lemma_cast_abs(ma);
    // |B| >= |MB| − RB > 0.
    assert(abs_r(b) >= amb - rbr && amb - rbr > 0real) by (nonlinear_arith)
        requires
            abs_r(b - mbr) <= rbr,
            amb == abs_r(mbr),
            amb > rbr,
    ;
    assert(vb != 0real) by (nonlinear_arith)
        requires
            b == vb * ur,
            abs_r(b) > 0real,
    ;
    let n = rar * amb + abs_r(mar) * rbr;
    let d = (amb - rbr) * amb;
    // |a·MB − MA·b| <= N.
    assert(abs_r(a * mbr - mar * b) <= n) by (nonlinear_arith)
        requires
            abs_r(a - mar) <= rar,
            abs_r(b - mbr) <= rbr,
            rar >= 0real,
            rbr >= 0real,
            amb == abs_r(mbr),
            n == rar * amb + abs_r(mar) * rbr,
    ;
    let e = a / b - mar / mbr;
    assert(e == (a * mbr - mar * b) / (b * mbr)) by (nonlinear_arith)
        requires
            b != 0real,
            mbr != 0real,
            e == a / b - mar / mbr,
    ;
    lemma_abs_mul(b, mbr);
    assert(abs_r(b * mbr) >= d && d > 0real) by (nonlinear_arith)
        requires
            abs_r(b * mbr) == abs_r(b) * amb,
            abs_r(b) >= amb - rbr,
            amb - rbr > 0real,
            rbr >= 0real,
            amb == abs_r(mbr),
            d == (amb - rbr) * amb,
    ;
    assert(abs_r(e) <= n / d) by (nonlinear_arith)
        requires
            e == (a * mbr - mar * b) / (b * mbr),
            abs_r(a * mbr - mar * b) <= n,
            abs_r(b * mbr) >= d,
            d > 0real,
            n >= 0real,
    ;
    // In ulps: (va/vb)·u = (a/b)·u and the midpoint approximates (MA/MB)·u = MA·u / MB.
    assert(va / vb * ur == (a / b) * ur) by (nonlinear_arith)
        requires
            a == va * ur,
            b == vb * ur,
            ur > 0real,
            vb != 0real,
    ;
    let ni = (ra * abs_i(mb) + abs_i(ma) * rb) * u;
    let di = (abs_i(mb) - rb) * abs_i(mb);
    lemma_cast_mul(ra, abs_i(mb));
    lemma_cast_mul(abs_i(ma), rb);
    lemma_cast_mul(ra * abs_i(mb) + abs_i(ma) * rb, u);
    lemma_cast_mul(abs_i(mb) - rb, abs_i(mb));
    lemma_cast_mul(ma, u);
    assert(ni as real == n * ur && di as real == d);
    assert(ni >= 0 && di > 0) by (nonlinear_arith)
        requires
            ra >= 0,
            rb >= 0,
            u > 0,
            abs_i(mb) > rb,
            abs_i(ma) >= 0,
            ni == (ra * abs_i(mb) + abs_i(ma) * rb) * u,
            di == (abs_i(mb) - rb) * abs_i(mb),
    ;
    lemma_ceil_div(ni, di);
    lemma_cast_add(ceil_div_i(ni, di), 1);
    lemma_spec_tdiv_close(ma * u, mb);
    let m = spec_tdiv(ma * u, mb) as real;
    let c = ceil_div_i(ni, di) as real;
    let p = (ma * u) as real;
    assert(p / mbr == (mar / mbr) * ur) by (nonlinear_arith)
        requires
            p == mar * ur,
            mbr != 0real,
    ;
    assert(abs_r((a / b) * ur - m) <= c + 1real) by (nonlinear_arith)
        requires
            ur > 0real,
            abs_r(a / b - mar / mbr) <= n / d,
            d > 0real,
            abs_r(p / mbr - m) < 1real,
            p / mbr == (mar / mbr) * ur,
            c * d >= n * ur,
    ;
}

/// √A at unit u for MA >= RA and root = isqrt(MA·u) >= 1: |√(A·u) − √(MA·u)| <= RA·u /
/// √(MA·u) <= RA·u / root, and |√(MA·u) − root| < 1. A ball value va is then >= 0, and
/// √va·u = √(A·u).
pub proof fn lemma_ball_sqrt(ma: int, ra: int, u: int, va: real, root: int)
    requires
        u > 0,
        ra >= 0,
        ma >= ra,
        root >= 1,
        root * root <= ma * u,
        ma * u < (root + 1) * (root + 1),
        in_ball(ma, ra, u, va),
    ensures
        va >= 0real,
        in_ball(root, ceil_div_i(ra * u, root) + 1, u, sqrt_r(va)),
{
    let ur = u as real;
    let a = va * ur;
    let mar = ma as real;
    let rar = ra as real;
    assert(va >= 0real) by (nonlinear_arith)
        requires
            abs_r(a - mar) <= rar,
            mar >= rar,
            a == va * ur,
            ur > 0real,
    ;
    axiom_sqrt(va);
    let s = sqrt_r(va);
    let sa = s * ur;
    assert(sa * sa == a * ur) by (nonlinear_arith)
        requires
            s * s == va,
            sa == s * ur,
            a == va * ur,
    ;
    lemma_cast_mul(ma, u);
    let mu = (ma * u) as real;
    assert(mu >= 1real) by (nonlinear_arith)
        requires
            root >= 1,
            root * root <= ma * u,
            mu == (ma * u) as real,
    ;
    axiom_sqrt(mu);
    let t = sqrt_r(mu);
    let rr = root as real;
    lemma_cast_mul(root, root);
    lemma_cast_mul(root + 1, root + 1);
    lemma_cast_add(root, 1);
    assert(rr * rr <= mu && mu < (rr + 1real) * (rr + 1real));
    assert(rr <= t && t < rr + 1real) by (nonlinear_arith)
        requires
            t >= 0real,
            t * t == mu,
            rr >= 1real,
            rr * rr <= mu,
            mu < (rr + 1real) * (rr + 1real),
    ;
    assert(sa >= 0real) by (nonlinear_arith)
        requires
            s >= 0real,
            ur > 0real,
            sa == s * ur,
    ;
    assert(a * ur >= 0real) by (nonlinear_arith)
        requires
            va >= 0real,
            ur > 0real,
            a == va * ur,
    ;
    lemma_sqrt_close(a * ur, mu, sa, t);
    assert(abs_r(a * ur - mu) <= rar * ur) by (nonlinear_arith)
        requires
            abs_r(a - mar) <= rar,
            mu == mar * ur,
            ur > 0real,
    ;
    lemma_cast_mul(ra, u);
    assert(ra * u >= 0) by (nonlinear_arith)
        requires
            ra >= 0,
            u > 0,
    ;
    lemma_ceil_div(ra * u, root);
    lemma_cast_add(ceil_div_i(ra * u, root), 1);
    let c = ceil_div_i(ra * u, root) as real;
    assert(abs_r(sa - rr) <= c + 1real) by (nonlinear_arith)
        requires
            abs_r(sa - t) * t <= abs_r(a * ur - mu),
            abs_r(a * ur - mu) <= rar * ur,
            rr <= t,
            t < rr + 1real,
            rr >= 1real,
            c * rr >= rar * ur,
    ;
}

/// The core of √A: for A >= 0 and MA > 0 with square roots sa and sma,
/// |sa − sma|·sma <= |A − MA|.
pub proof fn lemma_sqrt_close(a: real, ma: real, sa: real, sma: real)
    requires
        a >= 0real,
        sa >= 0real,
        sma > 0real,
        sa * sa == a,
        sma * sma == ma,
    ensures
        abs_r(sa - sma) * sma <= abs_r(a - ma),
{
    assert((sa - sma) * (sa + sma) == a - ma) by (nonlinear_arith)
        requires
            sa * sa == a,
            sma * sma == ma,
    ;
    assert(abs_r(sa - sma) * sma <= abs_r(sa - sma) * (sa + sma)) by (nonlinear_arith)
        requires
            sa >= 0real,
            sma > 0real,
    ;
    assert(abs_r(sa - sma) * (sa + sma) == abs_r(a - ma)) by (nonlinear_arith)
        requires
            (sa - sma) * (sa + sma) == a - ma,
            sa >= 0real,
            sma > 0real,
    ;
}

// --- Powers and series (`mathlib::arc_inv` and the series) ---

/// (1/n)^m = 1/n^m for n > 0.
pub proof fn lemma_pow_r_inv(n: int, m: nat)
    requires
        n > 0,
    ensures
        spec_pow_int(n, m) > 0,
        pow_r(1real / (n as real), m) == 1real / (spec_pow_int(n, m) as real),
    decreases m,
{
    if m > 0 {
        lemma_pow_r_inv(n, (m - 1) as nat);
        let q = spec_pow_int(n, (m - 1) as nat);
        assert(n * q > 0) by (nonlinear_arith)
            requires
                n > 0,
                q > 0,
        ;
        lemma_cast_mul(n, q);
        let nr = n as real;
        let qr = q as real;
        assert((1real / nr) * (1real / qr) == 1real / (nr * qr)) by (nonlinear_arith)
            requires
                nr > 0real,
                qr > 0real,
        ;
        assert(pow_r(1real / nr, m) == (1real / nr) * pow_r(1real / nr, (m - 1) as nat));
        assert(spec_pow_int(n, m) == n * q);
        assert((spec_pow_int(n, m) as real) == nr * qr);
    } else {
        assert(pow_r(1real / (n as real), 0) == 1real);
        assert(spec_pow_int(n, 0) == 1);
        assert(1real / (1int as real) == 1real);
    }
}

/// n^m >= 2^m for n >= 2.
pub proof fn lemma_pow_ge_pow2(n: int, m: nat)
    requires
        n >= 2,
    ensures
        spec_pow_int(n, m) >= spec_pow_int(2, m),
        spec_pow_int(2, m) >= 1,
    decreases m,
{
    if m > 0 {
        lemma_pow_ge_pow2(n, (m - 1) as nat);
        let a = spec_pow_int(n, (m - 1) as nat);
        let b = spec_pow_int(2, (m - 1) as nat);
        assert(n * a >= 2 * b && 2 * b >= 1) by (nonlinear_arith)
            requires
                n >= 2,
                a >= b,
                b >= 1,
        ;
    }
}

/// 10^p <= 2^(4p).
pub proof fn lemma_pow10_le_pow2(p: nat)
    ensures
        pow10(p) <= spec_pow_int(2, 4 * p),
    decreases p,
{
    if p > 0 {
        lemma_pow10_le_pow2((p - 1) as nat);
        let m = (4 * (p - 1)) as nat;
        assert(4 * p == m + 4);
        let b = spec_pow_int(2, m);
        assert(spec_pow_int(2, m + 4) == 2 * spec_pow_int(2, (m + 3) as nat));
        assert(spec_pow_int(2, (m + 3) as nat) == 2 * spec_pow_int(2, (m + 2) as nat));
        assert(spec_pow_int(2, (m + 2) as nat) == 2 * spec_pow_int(2, (m + 1) as nat));
        assert(spec_pow_int(2, (m + 1) as nat) == 2 * b);
        lemma_pow_ge_pow2(2, m);
    }
}

/// 2^a < 2^c for a < c.
pub proof fn lemma_pow2_strict(a: nat, c: nat)
    requires
        a < c,
    ensures
        spec_pow_int(2, a) < spec_pow_int(2, c),
    decreases c,
{
    lemma_pow_ge_pow2(2, (c - 1) as nat);
    if a < c - 1 {
        lemma_pow2_strict(a, (c - 1) as nat);
    }
}

/// Partial sums depend only on the terms they add.
pub proof fn lemma_partial_sum_ext(t1: spec_fn(nat) -> real, t2: spec_fn(nat) -> real, k: nat)
    requires
        forall|j: nat| j < k ==> #[trigger] t1(j) == t2(j),
    ensures
        partial_sum(t1, k) == partial_sum(t2, k),
    decreases k,
{
    if k > 0 {
        lemma_partial_sum_ext(t1, t2, (k - 1) as nat);
    }
}

/// One term of `arc_inv`: with p = ⌊u / nn⌋ and term = ⌊p / d⌋, the true term
/// x = u / (nn·d) satisfies term <= x < term + 2.
pub proof fn lemma_arc_term(u: int, nn: int, d: int)
    requires
        u >= 0,
        nn > 0,
        d > 0,
    ensures
        nn * d > 0,
        ((u / nn / d) as real) <= (u as real) / ((nn * d) as real),
        (u as real) / ((nn * d) as real) < ((u / nn / d) as real) + 2real,
{
    let p = u / nn;
    assert(p >= 0) by (nonlinear_arith)
        requires
            u >= 0,
            nn > 0,
            p == u / nn,
    ;
    lemma_floor_div_close(u, nn);
    lemma_floor_div_close(p, d);
    lemma_cast_mul(nn, d);
    lemma_cast_add(p, 1);
    let ur = u as real;
    let nr = nn as real;
    let dr = d as real;
    let pr = p as real;
    let tr = (p / d) as real;
    assert(nn * d > 0) by (nonlinear_arith)
        requires
            nn > 0,
            d > 0,
    ;
    assert(ur / (nr * dr) == (ur / nr) / dr) by (nonlinear_arith)
        requires
            nr > 0real,
            dr > 0real,
    ;
    assert(tr <= (ur / nr) / dr && (ur / nr) / dr < tr + 2real) by (nonlinear_arith)
        requires
            nr > 0real,
            dr >= 1real,
            pr <= ur / nr,
            ur / nr < pr + 1real,
            tr <= pr / dr,
            pr / dr < tr + 1real,
    ;
}

// --- Series terms (`mathlib::Series`) ---

/// k! >= 1.
pub proof fn lemma_fact_pos(k: nat)
    ensures
        fact(k) >= 1,
    decreases k,
{
    if k > 0 {
        lemma_fact_pos((k - 1) as nat);
        assert(k * fact((k - 1) as nat) >= 1) by (nonlinear_arith)
            requires
                k >= 1,
                fact((k - 1) as nat) >= 1,
        ;
    }
}

/// x^(m+2) = x^m·(x·x).
pub proof fn lemma_pow_r_step2(x: real, m: nat)
    ensures
        pow_r(x, m + 2) == pow_r(x, m) * (x * x),
{
    assert(pow_r(x, m + 2) == x * pow_r(x, m + 1));
    assert(pow_r(x, m + 1) == x * pow_r(x, m));
    assert(x * (x * pow_r(x, m)) == pow_r(x, m) * (x * x)) by (nonlinear_arith);
}

/// The ratio of consecutive Taylor terms of sin and cos: term k+1 = −term k·r² / ((m+1)(m+2))
/// with m = 2k + odd.
pub proof fn lemma_sin_cos_term_step(r: real, odd: nat, k: nat)
    ensures
        sin_cos_term(r, odd, k + 1) == -((sin_cos_term(r, odd, k) * (r * r)) / (((2 * k + odd
            + 1) * (2 * k + odd + 2)) as real)),
{
    let m = 2 * k + odd;
    assert(2 * (k + 1) + odd == m + 2);
    lemma_pow_r_step2(r, m);
    lemma_fact_pos(m);
    assert(fact(m + 2) == (m + 2) * fact(m + 1));
    assert(fact(m + 1) == (m + 1) * fact(m));
    lemma_cast_mul((m + 2) as int, (m + 1) as int);
    lemma_cast_mul(((m + 2) * (m + 1)) as int, fact(m) as int);
    lemma_cast_mul((m + 1) as int, (m + 2) as int);
    assert(fact(m + 2) == ((m + 2) * (m + 1)) * fact(m)) by (nonlinear_arith)
        requires
            fact(m + 2) == (m + 2) * fact(m + 1),
            fact(m + 1) == (m + 1) * fact(m),
    ;
    let s = sign_r(k);
    assert(sign_r(k + 1) == -s);
    let p = pow_r(r, m);
    let f = fact(m) as real;
    let a = (m + 1) as real;
    let b = (m + 2) as real;
    assert(fact(m + 2) as real == b * a * f);
    assert((((m + 1) * (m + 2)) as int) as real == a * b);
    assert((-s) * (p * (r * r)) / (b * a * f) == -((s * p / f) * (r * r) / (a * b)))
        by (nonlinear_arith)
        requires
            f >= 1real,
            a >= 1real,
            b >= 1real,
    ;
}

/// term k of the exponential series = term k−1·r / k.
pub proof fn lemma_exp_term_step(r: real, k: nat)
    requires
        k >= 1,
    ensures
        exp_term(r, k) == exp_term(r, (k - 1) as nat) * r / (k as real),
{
    let j = (k - 1) as nat;
    lemma_fact_pos(j);
    assert(pow_r(r, k) == r * pow_r(r, j));
    assert(fact(k) == k * fact(j));
    lemma_cast_mul(k as int, fact(j) as int);
    let p = pow_r(r, j);
    let f = fact(j) as real;
    let kr = k as real;
    assert(fact(k) as real == kr * f);
    assert((r * p) / (kr * f) == (p / f) * r / kr) by (nonlinear_arith)
        requires
            f >= 1real,
            kr >= 1real,
    ;
}

/// term m of the Bessel series = −term m−1·h² / (m·(m+n)).
pub proof fn lemma_bessel_term_step(n: nat, h: real, m: nat)
    requires
        m >= 1,
    ensures
        bessel_term(n, h, m) == -((bessel_term(n, h, (m - 1) as nat) * (h * h)) / ((m * (m
            + n)) as real)),
{
    let j = (m - 1) as nat;
    assert(2 * m + n == (2 * j + n) + 2);
    lemma_pow_r_step2(h, 2 * j + n);
    lemma_fact_pos(j);
    lemma_fact_pos(j + n);
    assert(fact(m) == m * fact(j));
    assert(m + n == (j + n) + 1);
    assert(fact(m + n) == (m + n) * fact(j + n));
    let fj = fact(j) as real;
    let fjn = fact(j + n) as real;
    let mr = m as real;
    let mnr = (m + n) as real;
    lemma_cast_mul(m as int, fact(j) as int);
    lemma_cast_mul((m + n) as int, fact(j + n) as int);
    lemma_cast_mul(fact(m) as int, fact(m + n) as int);
    lemma_cast_mul(fact(j) as int, fact(j + n) as int);
    lemma_cast_mul(m as int, (m + n) as int);
    assert((fact(m) * fact(m + n)) as real == (mr * fj) * (mnr * fjn));
    assert((fact(j) * fact(j + n)) as real == fj * fjn);
    assert((m * (m + n)) as real == mr * mnr);
    let s = sign_r(j);
    assert(sign_r(m) == -s);
    let p = pow_r(h, 2 * j + n);
    assert((-s) * (p * (h * h)) / ((mr * fj) * (mnr * fjn)) == -((s * p / (fj * fjn)) * (h * h)
        / (mr * mnr))) by (nonlinear_arith)
        requires
            fj >= 1real,
            fjn >= 1real,
            mr >= 1real,
            mnr >= 1real,
    ;
}

/// The atan series' `power` (−1)^k·y^(2k+1) after one more factor −y².
pub proof fn lemma_atan_power_step(y: real, k: nat)
    requires
        k >= 1,
    ensures
        sign_r(k) * pow_r(y, 2 * k + 1) == -((sign_r((k - 1) as nat) * pow_r(
            y,
            2 * ((k - 1) as nat) + 1,
        )) * (y * y)),
        pow_r(y, 2 * k + 1) == pow_r(y, 2 * ((k - 1) as nat) + 1) * (y * y),
        atan_term(y, k) == (sign_r(k) * pow_r(y, 2 * k + 1)) / ((2 * k + 1) as real),
        artanh_term(y, k) == pow_r(y, 2 * k + 1) / ((2 * k + 1) as real),
{
    let j = (k - 1) as nat;
    assert(2 * k + 1 == (2 * j + 1) + 2);
    lemma_pow_r_step2(y, 2 * j + 1);
    assert(sign_r(k) == -sign_r(j));
    let p = pow_r(y, 2 * j + 1);
    assert((-sign_r(j)) * (p * (y * y)) == -((sign_r(j) * p) * (y * y))) by (nonlinear_arith);
}

/// The ball of a partial sum, widened by a bound on the tail, contains the series' value: if
/// the ball contains s, |v − s| <= c·|t|, and |t|·u <= bound, the ball widened by c·bound
/// contains v.
pub proof fn lemma_widen_tail(mid: int, rad: int, u: int, s: real, v: real, t: real, c: int, bound: int)
    requires
        u > 0,
        c >= 0,
        in_ball(mid, rad, u, s),
        abs_r(v - s) <= (c as real) * abs_r(t),
        abs_r(t * (u as real)) <= bound as real,
    ensures
        in_ball(mid, rad + c * bound, u, v),
{
    let ur = u as real;
    let cr = c as real;
    lemma_cast_mul(c, bound);
    lemma_cast_add(rad, c * bound);
    lemma_abs_mul(t, ur);
    assert(abs_r(v * ur - s * ur) <= cr * abs_r(t) * ur) by (nonlinear_arith)
        requires
            abs_r(v - s) <= cr * abs_r(t),
            ur > 0real,
    ;
    assert(cr * abs_r(t) * ur <= cr * (bound as real)) by (nonlinear_arith)
        requires
            abs_r(t * ur) == abs_r(t) * abs_r(ur),
            abs_r(ur) == ur,
            abs_r(t * ur) <= bound as real,
            cr >= 0real,
    ;
}

/// Every value in a ball is at most its `upper` bound in magnitude: |v·u| <= |mid| + rad.
pub proof fn lemma_in_ball_upper(mid: int, rad: int, u: int, v: real)
    requires
        in_ball(mid, rad, u, v),
    ensures
        abs_r(v * (u as real)) <= (abs_i(mid) + rad) as real,
{
    lemma_cast_add(abs_i(mid), rad);
    lemma_cast_abs(mid);
}

/// x² <= c implies |x| <= 1 when c <= 1, and 1 − x² >= 1/2 when c <= 1/2.
pub proof fn lemma_square_bound(x: real)
    ensures
        x * x <= 1real ==> abs_r(x) <= 1real,
        x * x <= 1real / 2real ==> abs_r(x) < 1real,
{
    if x * x <= 1real && abs_r(x) > 1real {
        assert(x * x > 1real) by (nonlinear_arith)
            requires
                abs_r(x) > 1real,
                abs_r(x) == x || abs_r(x) == -x,
        ;
    }
    if x * x <= 1real / 2real && abs_r(x) >= 1real {
        assert(x * x >= 1real) by (nonlinear_arith)
            requires
                abs_r(x) >= 1real,
                abs_r(x) == x || abs_r(x) == -x,
        ;
    }
}

// --- Certified truncation (`mathlib::certified_trunc`) ---

/// The decision of `certified_trunc` over the reals. The ball (mid, rad) at unit u = s·unit
/// contains v; with q = ⌊mid / unit⌋ and r = mid mod unit, if rad < r and r + rad < unit, then
/// v·s lies strictly between q and q + 1, so its truncation toward zero is q when q >= 0 and
/// q + 1 when q < 0.
pub proof fn lemma_certified_trunc_real(mid: int, rad: int, s: int, unit: int, v: real)
    requires
        s > 0,
        unit > 0,
        in_ball(mid, rad, s * unit, v),
        rad < mid % unit,
        mid % unit + rad < unit,
    ensures
        trunc_r(v * (s as real)) == (if mid / unit >= 0 {
            mid / unit
        } else {
            mid / unit + 1
        }),
{
    let q = mid / unit;
    let r = mid % unit;
    assert(mid == q * unit + r && 0 <= r < unit) by (nonlinear_arith)
        requires
            unit > 0,
            q == mid / unit,
            r == mid % unit,
    ;
    lemma_cast_mul(s, unit);
    lemma_cast_mul(q, unit);
    let sr = s as real;
    let unr = unit as real;
    let qr = q as real;
    let y = v * sr;
    // q·unit < v·s·unit < (q + 1)·unit.
    assert(qr * unr < y * unr && y * unr < qr * unr + unr) by (nonlinear_arith)
        requires
            abs_r(v * (sr * unr) - (mid as real)) <= rad as real,
            (mid as real) == qr * unr + (r as real),
            (rad as real) < (r as real),
            (r as real) + (rad as real) < unr,
            y == v * sr,
    ;
    assert(qr < y && y < qr + 1real) by (nonlinear_arith)
        requires
            unr > 0real,
            qr * unr < y * unr,
            y * unr < qr * unr + unr,
    ;
    if q >= 0 {
        assert(y.floor() == q);
    } else {
        assert((-y).floor() == -q - 1);
    }
}

/// The exact case of `certified_trunc`: a ball of radius 0 on a multiple of `unit`.
pub proof fn lemma_certified_trunc_real_exact(mid: int, s: int, unit: int, v: real)
    requires
        s > 0,
        unit > 0,
        in_ball(mid, 0, s * unit, v),
        mid % unit == 0,
    ensures
        trunc_r(v * (s as real)) == mid / unit,
{
    let q = mid / unit;
    assert(mid == q * unit) by (nonlinear_arith)
        requires
            unit > 0,
            q == mid / unit,
            mid % unit == 0,
    ;
    lemma_cast_mul(s, unit);
    lemma_cast_mul(q, unit);
    let sr = s as real;
    let unr = unit as real;
    let qr = q as real;
    assert(v * sr == qr) by (nonlinear_arith)
        requires
            unr > 0real,
            v * (sr * unr) == (mid as real),
            (mid as real) == qr * unr,
    ;
}

} // verus!
