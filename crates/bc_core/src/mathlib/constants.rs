// SPDX-License-Identifier: MIT

//! π and ln 2 as balls, summed from exact integer terms (`arc_inv`).

use super::*;

verus! {

/// Term k of the series that `arc_inv(n, alternating, _)` sums: atan's (alternating) or
/// artanh's at y = 1/n.
pub(crate) open spec fn arc_term(n: int, alternating: bool, k: nat) -> real {
    let y = 1real / (n as real);
    if alternating {
        atan_term(y, k)
    } else {
        artanh_term(y, k)
    }
}

/// The value that `arc_inv(n, alternating, _)` approximates: atan(1/n) or artanh(1/n).
pub(crate) open spec fn arc_value(n: int, alternating: bool) -> real {
    let y = 1real / (n as real);
    if alternating {
        atan_r(y)
    } else {
        artanh_r(y)
    }
}

/// atan(1/n) (`alternating`) or artanh(1/n) for n >= 3, from exact integer terms.
///
/// `power` is floor(10^p / n^(2k+1)) exactly (nested floor divisions compose), so each term
/// floor(power / (2k+1)) is below the true term by less than 2 ulps (`lemma_arc_term`). When
/// `power` reaches 0 the next true term is below 1 ulp, and the omitted tail is at most 9/8 of
/// it (`axiom_atan_series`, `axiom_artanh_series`). So the radius is 2 ulps per term plus 2.
pub(crate) fn arc_inv(n: u32, alternating: bool, prec: usize) -> (r: Ball)
    requires
        n >= 3,
        prec <= u32::MAX,
    ensures
        r.wf(),
        r.prec == prec,
        r.contains(arc_value(n as int, alternating)),
{
    let ghost ni = n as int;
    let ghost u = spec_num::pow10(prec as nat);
    let ghost t = |j: nat| arc_term(ni, alternating, j);
    proof {
        assert((n as u64) * (n as u64) <= u64::MAX) by (nonlinear_arith)
            requires
                n <= u32::MAX,
        ;
        assert(ni * ni >= 9) by (nonlinear_arith)
            requires
                ni >= 3,
        ;
    }
    let n_sq = big_from_u64(n as u64 * n as u64);
    let mut power = big_tdiv(&pow10_within(prec), &big_from_u64(n as u64));
    let mut sum = big_from_i64(0);
    let mut k: u64 = 0;
    proof {
        lemma_pow10_pos(prec as nat);
        assert(spec_pow_int(ni, 0) == 1);
        assert(spec_pow_int(ni, 1) == ni);
        assert(partial_sum(t, 0) == 0real);
    }
    let mut done = big_is_zero(&power);
    while !done
        invariant
            n >= 3,
            ni == n as int,
            prec <= u32::MAX,
            u == spec_num::pow10(prec as nat),
            u >= 1,
            t == (|j: nat| arc_term(ni, alternating, j)),
            big_view(&n_sq) == ni * ni,
            big_view(&power) == u / spec_pow_int(ni, (2 * k + 1) as nat),
            done == (big_view(&power) == 0),
            k <= 4 * prec,
            abs_r((u as real) * partial_sum(t, k as nat) - (big_view(&sum) as real)) <= (2
                * k) as real,
        decreases big_view(&power),
    {
        let ghost kk = k as nat;
        let ghost d = 2 * kk + 1;
        let ghost nn = spec_pow_int(ni, d);
        proof {
            lemma_pow_positive(ni, d);
            if u < nn {
                assert(u / nn == 0) by (nonlinear_arith)
                    requires
                        0 <= u < nn,
                ;
            }
            lemma_pow_ge_pow2(ni, d);
            lemma_pow10_le_pow2(prec as nat);
            if d > 4 * prec {
                lemma_pow2_strict((4 * prec) as nat, d);
            }
        }
        let term = big_tdiv_u64(&power, 2 * k + 1);
        let ghost sum0 = big_view(&sum);
        if alternating && k % 2 == 1 {
            sum = big_sub(&sum, &term);
        } else {
            sum = big_add(&sum, &term);
        }
        proof {
            // The term in ulps is ±x with x = u / (n^(2k+1)·(2k+1)), and term <= x < term + 2.
            lemma_arc_term(u, nn, d as int);
            assert(big_view(&power) >= 0);
            assert(big_view(&term) == u / nn / (d as int));
            let x = (u as real) / ((nn * d) as real);
            let tv = big_view(&term) as real;
            lemma_pow_r_inv(ni, d);
            lemma_cast_mul(nn, d as int);
            let nr = nn as real;
            let dr = d as real;
            let ur = u as real;
            let neg = alternating && kk % 2 == 1;
            let sg = if neg {
                -1real
            } else {
                1real
            };
            assert(t(kk) == sg * (1real / nr) / dr);
            assert(ur * t(kk) == sg * x) by (nonlinear_arith)
                requires
                    t(kk) == sg * (1real / nr) / dr,
                    x == ur / (nr * dr),
                    nr > 0real,
                    dr > 0real,
            ;
            assert(partial_sum(t, kk + 1) == partial_sum(t, kk) + t(kk));
            let e0 = ur * partial_sum(t, kk) - (sum0 as real);
            assert(ur * partial_sum(t, kk + 1) == ur * partial_sum(t, kk) + ur * t(kk))
                by (nonlinear_arith);
            lemma_cast_add(sum0, big_view(&term));
            if neg {
                assert(abs_r(e0 - (x - tv)) <= (2 * kk) as real + 2real);
            } else {
                assert(abs_r(e0 + (x - tv)) <= (2 * kk) as real + 2real);
            }
            assert(ni * ni >= 9) by (nonlinear_arith)
                requires
                    ni >= 3,
            ;
            lemma_div_denominator(u, nn, ni * ni);
            assert(spec_pow_int(ni, d + 2) == ni * spec_pow_int(ni, d + 1));
            assert(spec_pow_int(ni, d + 1) == ni * nn);
            assert(nn * (ni * ni) == ni * (ni * nn)) by (nonlinear_arith);
            assert((2 * (kk + 1) + 1) as nat == d + 2);
        }
        power = big_tdiv(&power, &n_sq);
        proof {
            assert(big_view(&power) < big_view(&power) * 9 || big_view(&power) == 0);
            let p0 = u / nn;
            assert(p0 / (ni * ni) < p0) by (nonlinear_arith)
                requires
                    p0 >= 1,
                    ni * ni >= 9,
            ;
            assert(ni * ni >= 9) by (nonlinear_arith)
                requires
                    ni >= 3,
            ;
        }
        k += 1;
        done = big_is_zero(&power);
    }
    let r = Ball { mid: sum, rad: big_from_u64(2 * k + 2), prec };
    proof {
        let kk = k as nat;
        let d = 2 * kk + 1;
        let nn = spec_pow_int(ni, d);
        lemma_pow_positive(ni, d);
        if u >= nn {
            assert(u / nn >= 1) by (nonlinear_arith)
                requires
                    u >= nn,
                    nn > 0,
            ;
        }
        // The first omitted term is x / u ulps with x = u / (n^(2k+1)·(2k+1)) < 1.
        lemma_pow_r_inv(ni, d);
        lemma_cast_mul(nn, d as int);
        let nr = nn as real;
        let dr = d as real;
        let ur = u as real;
        let x = ur / (nr * dr);
        assert(x < 1real && x >= 0real) by (nonlinear_arith)
            requires
                ur < nr,
                ur >= 1real,
                dr >= 1real,
                x == ur / (nr * dr),
        ;
        let y = 1real / (ni as real);
        assert(0real < y && y <= 1real / 3real) by (nonlinear_arith)
            requires
                y == 1real / (ni as real),
                ni as real >= 3real,
        ;
        let neg = alternating && kk % 2 == 1;
        let sg = if neg {
            -1real
        } else {
            1real
        };
        let q = (1real / nr) / dr;
        assert(q > 0real) by (nonlinear_arith)
            requires
                q == (1real / nr) / dr,
                nr > 0real,
                dr > 0real,
        ;
        assert(t(kk) == sg * (1real / nr) / dr);
        assert(t(kk) == sg * q) by (nonlinear_arith)
            requires
                t(kk) == sg * (1real / nr) / dr,
                q == (1real / nr) / dr,
                dr > 0real,
        ;
        if neg {
            assert(t(kk) == -q);
        } else {
            assert(t(kk) == q);
        }
        assert(abs_r(t(kk)) == q);
        let s = partial_sum(t, kk);
        let v = arc_value(ni, alternating);
        let e = ur * s - (big_view(&r.mid) as real);
        assert(abs_r(ur * t(kk)) == x) by (nonlinear_arith)
            requires
                abs_r(t(kk)) == (1real / nr) / dr,
                x == ur / (nr * dr),
                ur > 0real,
                nr > 0real,
                dr > 0real,
        ;
        if alternating {
            axiom_atan_series(y, kk);
            lemma_partial_sum_ext(t, |j: nat| atan_term(y, j), kk);
            assert(abs_r(v - s) <= abs_r(t(kk)));
            assert(abs_r(v * ur - (big_view(&r.mid) as real)) <= (2 * kk) as real + 2real)
                by (nonlinear_arith)
                requires
                    abs_r(v - s) <= abs_r(t(kk)),
                    abs_r(ur * t(kk)) == x,
                    x < 1real,
                    abs_r(e) <= (2 * kk) as real,
                    e == ur * s - (big_view(&r.mid) as real),
                    ur > 0real,
            ;
        } else {
            axiom_artanh_series(y, kk);
            lemma_partial_sum_ext(t, |j: nat| artanh_term(y, j), kk);
            assert(1real - y * y >= 8real / 9real) by (nonlinear_arith)
                requires
                    y == 1real / (ni as real),
                    ni as real >= 3real,
            ;
            let w = abs_r(t(kk)) / (1real - y * y);
            assert(abs_r(v - s) <= w);
            assert(ur * w <= 9real / 8real * x) by (nonlinear_arith)
                requires
                    w == abs_r(t(kk)) / (1real - y * y),
                    1real - y * y >= 8real / 9real,
                    abs_r(ur * t(kk)) == x,
                    ur > 0real,
            ;
            assert(abs_r(v * ur - (big_view(&r.mid) as real)) <= (2 * kk) as real + 2real)
                by (nonlinear_arith)
                requires
                    abs_r(v - s) <= w,
                    ur * w <= 9real / 8real * x,
                    x < 1real,
                    abs_r(e) <= (2 * kk) as real,
                    e == ur * s - (big_view(&r.mid) as real),
                    ur > 0real,
            ;
        }
        lemma_cast_add((2 * kk) as int, 2);
    }
    r
}

/// π by Machin's formula, π = 16·atan(1/5) − 4·atan(1/239).
pub(crate) fn pi(prec: usize) -> (r: Ball)
    requires
        prec <= u32::MAX,
    ensures
        r.wf(),
        r.prec == prec,
        r.contains(pi_r()),
{
    let a = arc_inv(5, true, prec).mul_int(&big_from_i64(16));
    let r = a.sub(&arc_inv(239, true, prec).mul_int(&big_from_i64(4)));
    proof {
        axiom_machin();
        assert(arc_value(5, true) == atan_r(1real / 5real));
        assert(arc_value(239, true) == atan_r(1real / 239real));
    }
    r
}

/// ln 2 = 2·artanh(1/3).
pub(crate) fn ln2(prec: usize) -> (r: Ball)
    requires
        prec <= u32::MAX,
    ensures
        r.wf(),
        r.prec == prec,
        r.contains(ln2_r()),
{
    let r = arc_inv(3, false, prec).mul_int(&big_from_i64(2));
    proof {
        let y = 1real / 3real;
        assert((1real + y) / (1real - y) == 2real) by (nonlinear_arith)
            requires
                y == 1real / 3real,
        ;
        assert(arc_value(3, false) * 2real == ln2_r());
    }
    r
}

} // verus!
