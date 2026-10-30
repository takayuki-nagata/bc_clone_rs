// SPDX-License-Identifier: MIT

//! Summation of the library's power series with a bound on the omitted tail.

use super::*;

verus! {

/// Series stop after at most this many terms (so that the factors below fit in `u64`); no
/// series of the library comes close.
pub(crate) const MAX_SERIES_TERMS: u64 = 0x100_0000_0000;

/// A series that `sum_series` sums, with the balls its terms are built from. The true
/// argument x of each series is a ghost value: r for sin and cos, y for atan and artanh, r for
/// exp, and h = x/2 for J_n.
pub(crate) enum Series {
    /// sin (`odd == 1`) or cos (`odd == 0`); `r_sq` contains r². Term k is term k−1·(−r²) /
    /// ((2k−1+odd)(2k+odd)).
    SinCos { r_sq: Ball, odd: u64 },
    /// atan; `y_sq` contains y². Term k is (−1)^k y^(2k+1) / (2k+1).
    Atan { y_sq: Ball },
    /// artanh; `y_sq` contains y². Term k is y^(2k+1) / (2k+1).
    Artanh { y_sq: Ball },
    /// exp; `r` contains r. Term k is term k−1·r / k.
    Exp { r: Ball },
    /// J_n; `half_sq` contains h² = (x/2)². Term m is term m−1·(−h²) / (m(m+n)).
    Bessel { half_sq: Ball, n: u64 },
}

/// Term k of the true series at x.
pub(crate) open spec fn series_term(s: Series, x: real, k: nat) -> real {
    match s {
        Series::SinCos { odd, .. } => sin_cos_term(x, odd as nat, k),
        Series::Atan { .. } => atan_term(x, k),
        Series::Artanh { .. } => artanh_term(x, k),
        Series::Exp { .. } => exp_term(x, k),
        Series::Bessel { n, .. } => bessel_term(n as nat, x, k),
    }
}

/// The value of the true series at x.
pub(crate) open spec fn series_value(s: Series, x: real) -> real {
    match s {
        Series::SinCos { odd, .. } => if odd == 1 {
            sin_r(x)
        } else {
            cos_r(x)
        },
        Series::Atan { .. } => atan_r(x),
        Series::Artanh { .. } => artanh_r(x),
        Series::Exp { .. } => exp_r(x),
        Series::Bessel { n, .. } => bessel_r(n as nat, 2real * x),
    }
}

/// The value that `sum_series` keeps in `power` before term k: (−1)^k y^(2k+1) for atan and
/// y^(2k+1) for artanh (unused otherwise).
pub(crate) open spec fn power_value(s: Series, x: real, k: nat) -> real {
    match s {
        Series::Atan { .. } => sign_r(k) * pow_r(x, 2 * k + 1),
        _ => pow_r(x, 2 * k + 1),
    }
}

impl Series {
    /// The balls are well formed at precision `p`, and the parameters are in range.
    pub(crate) open spec fn wf(&self, p: usize) -> bool {
        match *self {
            Series::SinCos { r_sq, odd } => r_sq.wf() && r_sq.prec == p && odd <= 1,
            Series::Atan { y_sq } => y_sq.wf() && y_sq.prec == p,
            Series::Artanh { y_sq } => y_sq.wf() && y_sq.prec == p,
            Series::Exp { r } => r.wf() && r.prec == p,
            Series::Bessel { half_sq, n } => half_sq.wf() && half_sq.prec == p && n < 0x8000_0000_0000_0000,
        }
    }

    /// The balls contain what they stand for at the argument x.
    pub(crate) open spec fn holds(&self, x: real) -> bool {
        match *self {
            Series::SinCos { r_sq, .. } => r_sq.contains(x * x),
            Series::Atan { y_sq } => y_sq.contains(x * x),
            Series::Artanh { y_sq } => y_sq.contains(x * x),
            Series::Exp { r } => r.contains(x),
            Series::Bessel { half_sq, .. } => half_sq.contains(x * x),
        }
    }

    /// The multiple of the first omitted term that bounds the tail: 2 for the geometric tails
    /// of artanh (y² <= 1/2) and exp (|r| <= 1), 1 for the alternating series.
    pub(crate) fn tail_factor(&self) -> (r: u64)
        ensures
            r == (if self is Artanh || self is Exp { 2u64 } else { 1u64 }),
    {
        match self {
            Series::Artanh { .. } | Series::Exp { .. } => 2,
            _ => 1,
        }
    }

    /// Checks the argument bound that the tail bound needs: |y| <= 1 for atan, y² <= 1/2 for
    /// artanh, |r| <= 1 for exp. The callers' arguments are far inside these bounds.
    pub(crate) fn tail_applies(&self) -> (r: bool)
        requires
            self.wf(self.prec_of()),
        ensures
            r ==> forall|x: real| #[trigger] self.holds(x) ==> self.tail_ok(x),
    {
        match self {
            Series::Atan { y_sq } => bounded(y_sq, &big_from_i64(1), 1),
            Series::Artanh { y_sq } => bounded(y_sq, &big_from_i64(1), 2),
            Series::Exp { r } => bounded(r, &big_from_i64(1), 1),
            _ => true,
        }
    }

    /// The precision of the balls.
    pub(crate) open spec fn prec_of(&self) -> usize {
        match *self {
            Series::SinCos { r_sq, .. } => r_sq.prec,
            Series::Atan { y_sq } => y_sq.prec,
            Series::Artanh { y_sq } => y_sq.prec,
            Series::Exp { r } => r.prec,
            Series::Bessel { half_sq, .. } => half_sq.prec,
        }
    }

    /// What `tail_applies` establishes about x.
    pub(crate) open spec fn tail_ok(&self, x: real) -> bool {
        match *self {
            Series::Atan { .. } => abs_r(x * x) <= 1real,
            Series::Artanh { .. } => abs_r(x * x) <= 1real / 2real,
            Series::Exp { .. } => abs_r(x) <= 1real,
            _ => true,
        }
    }

    /// Whether the terms decrease in magnitude from term k on: the factor dividing term k+1
    /// is at least r² (sin, cos) or h² (J_n). The series of atan, artanh and exp decrease from
    /// the start for the arguments that `tail_applies` admits.
    pub(crate) fn decreasing(&self, k: u64) -> (r: bool)
        requires
            self.wf(self.prec_of()),
            k < MAX_SERIES_TERMS,
        ensures
            r ==> forall|x: real| #[trigger] self.holds(x) ==> self.decreasing_at(x, k as nat),
    {
        match self {
            Series::SinCos { r_sq, odd } => {
                let f = big_mul(&big_from_u64(2 * k + 1 + *odd), &big_from_u64(2 * k + 2 + *odd));
                bounded(r_sq, &f, 1)
            },
            Series::Bessel { half_sq, n } => {
                let f = big_mul(&big_from_u64(k + 1), &big_from_u64(k + 1 + *n));
                bounded(half_sq, &f, 1)
            },
            _ => true,
        }
    }

    /// What `decreasing(k)` establishes about x: the precondition of the tail axiom.
    pub(crate) open spec fn decreasing_at(&self, x: real, k: nat) -> bool {
        match *self {
            Series::SinCos { odd, .. } => (((2 * k + odd + 1) * (2 * k + odd + 2)) as real) >= abs_r(x * x),
            Series::Bessel { n, .. } => (((k + 1) * (k + n + 1)) as real) >= abs_r(x * x),
            _ => true,
        }
    }

    /// Term k from term k−1 (and `power`, which carries (−1)^k y^(2k+1) or y^(2k+1)).
    pub(crate) fn next(&self, term: &Ball, power: &mut Ball, k: u64, Ghost(x): Ghost<real>) -> (r: Ball)
        requires
            1 <= k < MAX_SERIES_TERMS,
            self.wf(term.prec),
            self.holds(x),
            term.wf(),
            old(power).wf(),
            old(power).prec == term.prec,
            term.contains(series_term(*self, x, (k - 1) as nat)),
            (*self is Atan || *self is Artanh) ==> old(power).contains(
                power_value(*self, x, (k - 1) as nat),
            ),
        ensures
            r.wf(),
            r.prec == term.prec,
            final(power).wf(),
            final(power).prec == term.prec,
            r.contains(series_term(*self, x, k as nat)),
            (*self is Atan || *self is Artanh) ==> final(power).contains(
                power_value(*self, x, k as nat),
            ),
    {
        let ghost kk = k as nat;
        let ghost j = (k - 1) as nat;
        match self {
            Series::SinCos { r_sq, odd } => {
                let f = big_mul(&big_from_u64(2 * k - 1 + *odd), &big_from_u64(2 * k + *odd));
                proof {
                    assert(big_view(&f) > 0) by (nonlinear_arith)
                        requires
                            big_view(&f) == (2 * k - 1 + *odd) * (2 * k + *odd),
                            k >= 1,
                    ;
                }
                let r = term.mul(r_sq).div_int(&f).neg();
                proof {
                    lemma_sin_cos_term_step(x, *odd as nat, j);
                    assert((2 * j + *odd + 1) * (2 * j + *odd + 2) == big_view(&f));
                }
                r
            },
            Series::Atan { y_sq } => {
                let p = power.mul(y_sq).neg();
                *power = p;
                let r = power.div_int(&big_from_u64(2 * k + 1));
                proof {
                    lemma_atan_power_step(x, kk);
                }
                r
            },
            Series::Artanh { y_sq } => {
                let p = power.mul(y_sq);
                *power = p;
                let r = power.div_int(&big_from_u64(2 * k + 1));
                proof {
                    lemma_atan_power_step(x, kk);
                }
                r
            },
            Series::Exp { r } => {
                let t = term.mul(r).div_int(&big_from_u64(k));
                proof {
                    lemma_exp_term_step(x, kk);
                }
                t
            },
            Series::Bessel { half_sq, n } => {
                let f = big_mul(&big_from_u64(k), &big_from_u64(k + *n));
                proof {
                    assert(big_view(&f) > 0) by (nonlinear_arith)
                        requires
                            big_view(&f) == k * (k + *n),
                            k >= 1,
                    ;
                }
                let r = term.mul(half_sq).div_int(&f).neg();
                proof {
                    lemma_bessel_term_step(*n as nat, x, kk);
                    assert(kk * (kk + *n as nat) == big_view(&f));
                }
                r
            },
        }
    }
}

/// Whether `num·10^p >= den·b.upper()`, so that every value v in `b` has |v| <= num/den. With
/// `num` the factor dividing the next term and `b` the ball of a square, the terms decrease
/// from there on.
pub(crate) fn bounded(b: &Ball, num: &BigInt, den: u64) -> (r: bool)
    requires
        b.wf(),
        den >= 1,
    ensures
        r ==> forall|v: real| #[trigger] b.contains(v) ==> abs_r(v) <= (big_view(num) as real) / (
        den as real),
{
    let r = !matches!(
        big_cmp(&big_mul(num, &pow10_within(b.prec)), &big_mul(&big_from_u64(den), &b.upper())),
        Ordering::Less
    );
    proof {
        if r {
            assert forall|v: real| #[trigger] b.contains(v) implies abs_r(v) <= (big_view(num) as real)
                / (den as real) by {
                lemma_pow10_pos(b.prec as nat);
                lemma_in_ball_upper(big_view(&b.mid), big_view(&b.rad), b.unit(), v);
                let u = b.unit();
                let up = abs_i(big_view(&b.mid)) + big_view(&b.rad);
                lemma_cast_mul(big_view(num), u);
                lemma_cast_mul(den as int, up);
                lemma_abs_mul(v, u as real);
                let ur = u as real;
                let nr = big_view(num) as real;
                let dr = den as real;
                assert(abs_r(v) <= nr / dr) by (nonlinear_arith)
                    requires
                        abs_r(v * ur) == abs_r(v) * ur,
                        abs_r(v * ur) <= up as real,
                        nr * ur >= dr * (up as real),
                        ur > 0real,
                        dr >= 1real,
                ;
            }
        }
    }
    r
}

/// Sums a series from its first term `first` (term 0). It stops at the first term k whose
/// bound |mid| + rad is at most `TAIL_ULPS` and from which the terms decrease, and adds that
/// bound times the tail factor (the tail of such a series is at most the first omitted term,
/// or twice it for a geometric tail). `None` if the argument is outside the range where the
/// tail bound holds (`Series::tail_applies`), which does not happen for the library's
/// arguments.
#[verifier::exec_allows_no_decreases_clause]
pub(crate) fn sum_series(first: Ball, series: &Series, Ghost(x): Ghost<real>) -> (r: Option<Ball>)
    requires
        first.wf(),
        series.wf(first.prec),
        series.holds(x),
        first.contains(series_term(*series, x, 0)),
    ensures
        r is Some ==> r->Some_0.wf() && r->Some_0.prec == first.prec && r->Some_0.contains(
            series_value(*series, x),
        ),
{
    if !series.tail_applies() {
        return None;
    }
    let ghost t = |j: nat| series_term(*series, x, j);
    let ghost p = first.prec;
    // atan's and artanh's `power` starts at y, which is term 0.
    let mut power = first.copy();
    let mut sum = first.copy();
    let mut term = first;
    let mut k: u64 = 0;
    proof {
        assert(partial_sum(t, 1) == partial_sum(t, 0) + t(0));
        assert(pow_r(x, 1) == x * pow_r(x, 0));
        assert(sign_r(0) == 1real);
        assert(atan_term(x, 0) == x / 1real);
        assert(artanh_term(x, 0) == x / 1real);
    }
    loop
        invariant
            k < MAX_SERIES_TERMS,
            p == first.prec,
            series.wf(p),
            series.holds(x),
            series.tail_ok(x),
            t == (|j: nat| series_term(*series, x, j)),
            term.wf() && term.prec == p,
            sum.wf() && sum.prec == p,
            power.wf() && power.prec == p,
            term.contains(series_term(*series, x, k as nat)),
            sum.contains(partial_sum(t, (k + 1) as nat)),
            (series is Atan || series is Artanh) ==> power.contains(power_value(*series, x, k as nat)),
    {
        if k + 1 >= MAX_SERIES_TERMS {
            return None;
        }
        k += 1;
        term = series.next(&term, &mut power, k, Ghost(x));
        let bound = term.upper();
        if !matches!(big_cmp(&bound, &big_from_i64(TAIL_ULPS as i64)), Ordering::Greater)
            && series.decreasing(k)
        {
            let tf = series.tail_factor();
            let tail = big_mul(&bound, &big_from_u64(tf));
            let ghost s = partial_sum(t, k as nat);
            let ghost tk = t(k as nat);
            let ghost v = series_value(*series, x);
            proof {
                lemma_pow10_pos(p as nat);
                assert(series.decreasing_at(x, k as nat));
                assert((tf as int) as real == (if *series is Artanh || *series is Exp {
                    2real
                } else {
                    1real
                }));
                lemma_in_ball_upper(big_view(&term.mid), big_view(&term.rad), term.unit(), tk);
                assert(series.prec_of() == p);
                lemma_series_tail(*series, x, k as nat);
                lemma_widen_tail(
                    big_view(&sum.mid),
                    big_view(&sum.rad),
                    sum.unit(),
                    s,
                    v,
                    tk,
                    tf as int,
                    big_view(&bound),
                );
                let (bv, ti) = (big_view(&bound), tf as int);
                assert(big_view(&tail) == ti * bv) by (nonlinear_arith)
                    requires
                        big_view(&tail) == bv * ti,
                ;
                assert(bv >= 0 && ti >= 1);
                assert(ti * bv >= 0) by (nonlinear_arith)
                    requires
                        bv >= 0,
                        ti >= 1,
                ;
            }
            let r = sum.widen(&tail);
            proof {
                assert(r.unit() == sum.unit());
                assert(r.contains(v));
            }
            return Some(r);
        }
        proof {
            assert(partial_sum(t, (k + 1) as nat) == partial_sum(t, k as nat) + t(k as nat));
        }
        sum = sum.add(&term);
    }
}

/// The tail bound of each series at a stopping point k: |value − S_k| <= c·|term k| with c the
/// tail factor, given the argument bound (`tail_ok`) and the decrease from term k on.
pub(crate) proof fn lemma_series_tail(s: Series, x: real, k: nat)
    requires
        k >= 1,
        s.wf(s.prec_of()),
        s.tail_ok(x),
        s.decreasing_at(x, k),
    ensures
        abs_r(series_value(s, x) - partial_sum(|j: nat| series_term(s, x, j), k)) <= (if s is Artanh
            || s is Exp {
            2real
        } else {
            1real
        }) * abs_r(series_term(s, x, k)),
{
    let t = |j: nat| series_term(s, x, j);
    lemma_square_bound(x);
    match s {
        Series::SinCos { odd, .. } => {
            assert(abs_r(x * x) == x * x) by (nonlinear_arith);
            axiom_sin_cos_series(x, odd as nat, k);
            lemma_partial_sum_ext(t, |j: nat| sin_cos_term(x, odd as nat, j), k);
        },
        Series::Atan { .. } => {
            assert(abs_r(x * x) == x * x) by (nonlinear_arith);
            axiom_atan_series(x, k);
            lemma_partial_sum_ext(t, |j: nat| atan_term(x, j), k);
        },
        Series::Artanh { .. } => {
            assert(abs_r(x * x) == x * x) by (nonlinear_arith);
            axiom_artanh_series(x, k);
            lemma_partial_sum_ext(t, |j: nat| artanh_term(x, j), k);
            let a = abs_r(artanh_term(x, k));
            assert(a / (1real - x * x) <= 2real * a) by (nonlinear_arith)
                requires
                    x * x <= 1real / 2real,
                    a >= 0real,
            ;
        },
        Series::Exp { .. } => {
            axiom_exp_series(x, k);
            lemma_partial_sum_ext(t, |j: nat| exp_term(x, j), k);
        },
        Series::Bessel { n, .. } => {
            assert(abs_r(x * x) == x * x) by (nonlinear_arith);
            let x2 = 2real * x;
            assert(x2 / 2real == x);
            axiom_bessel_series(n as nat, x2, k);
            lemma_partial_sum_ext(t, |m: nat| bessel_term(n as nat, x2 / 2real, m), k);
        },
    }
}

} // verus!
