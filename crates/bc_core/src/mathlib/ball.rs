// SPDX-License-Identifier: MIT

//! Balls (a midpoint and a radius in ulps that bound a real number), their operations,
//! and the certified truncation with Ziv's retry loop (`certify`).

use super::*;

verus! {

/// Largest working precision. [`certify`] gives up (with `MathArgumentTooLarge`) rather than
/// exceed it; every decimal shift then stays far below `u32::MAX`, as `pow10` requires.
pub(crate) const MAX_WORKING_PREC: usize = 3 * MAX_VERIFIED_SCALE;

/// Series stop once the next term is bounded by this many ulps; its bound is then added to the
/// radius as the tail. Term radii settle below it (`docs/MATH_ERROR_BOUNDS.md` §2).
pub(crate) const TAIL_ULPS: u32 = 16;

/// A real number known to lie in `[mid - rad, mid + rad]`, both in units of `10^-prec`
/// (`rad >= 0`). Every operation returns a ball that contains the exact result of the operation
/// on any values of its operands' balls.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Ball {
    pub(crate) mid: BigInt,
    pub(crate) rad: BigInt,
    pub(crate) prec: usize,
}

/// The value of a `BCNum`, coeff·10^−scale.
pub open spec fn bcnum_real(x: &BCNum) -> real {
    (big_view(&x.coeff) as real) / (spec_num::pow10(x.scale as nat) as real)
}

/// `ceil(a / b)` for `a >= 0` and `b > 0`.
pub(crate) fn ceil_div(a: &BigInt, b: &BigInt) -> (r: BigInt)
    requires
        big_view(a) >= 0,
        big_view(b) > 0,
    ensures
        big_view(&r) == ceil_div_i(big_view(a), big_view(b)),
        big_view(&r) >= 0,
{
    proof {
        lemma_ceil_div(big_view(a), big_view(b));
    }
    big_tdiv(&big_add_i64(big_add(a, b), -1), b)
}

/// `a + 1`.
pub(crate) fn plus_one(a: BigInt) -> (r: BigInt)
    ensures
        big_view(&r) == big_view(&a) + 1,
{
    big_add_i64(a, 1)
}

impl Ball {
    /// The radius is nonnegative and `10^prec` can be computed (`pow10_within`).
    pub(crate) open spec fn wf(&self) -> bool {
        big_view(&self.rad) >= 0 && self.prec <= u32::MAX
    }

    /// One unit of the precision: 10^prec ulps make 1.
    pub(crate) open spec fn unit(&self) -> int {
        spec_num::pow10(self.prec as nat)
    }

    /// The ball contains the real `v`: |v·10^prec − mid| <= rad.
    pub(crate) open spec fn contains(&self, v: real) -> bool {
        in_ball(big_view(&self.mid), big_view(&self.rad), self.unit(), v)
    }

    pub(crate) fn exact(mid: BigInt, prec: usize) -> (r: Self)
        ensures
            r.mid == mid,
            big_view(&r.rad) == 0,
            r.prec == prec,
    {
        Self { mid, rad: big_from_i64(0), prec }
    }

    pub(crate) fn int(value: i64, prec: usize) -> (r: Self)
        requires
            prec <= u32::MAX,
        ensures
            r.wf(),
            r.prec == prec,
            r.contains(value as real),
    {
        let r = Self::exact(big_mul(&big_from_i64(value), &pow10_within(prec)), prec);
        proof {
            lemma_cast_mul(value as int, r.unit());
        }
        r
    }

    /// `x` at precision `prec`: exact when `prec >= x.scale`, which every caller ensures.
    pub(crate) fn from_bcnum(x: &BCNum, prec: usize) -> (r: Self)
        requires
            prec <= u32::MAX,
            x.scale <= u32::MAX,
        ensures
            r.wf(),
            r.prec == prec,
            r.contains(bcnum_real(x)),
    {
        let (shift, multiply) = verified_decimal_scale_shift(x.scale, prec);
        let ghost c = big_view(&x.coeff);
        let ghost us = spec_num::pow10(x.scale as nat);
        let ghost up = spec_num::pow10(prec as nat);
        let ghost uk = spec_num::pow10(shift as nat);
        proof {
            lemma_pow10_pos(x.scale as nat);
            lemma_pow10_pos(prec as nat);
            lemma_pow10_pos(shift as nat);
        }
        if multiply {
            let r = Self::exact(big_mul(&x.coeff, &pow10_within(shift)), prec);
            proof {
                // v·10^prec = c·10^prec / 10^scale = c·10^shift.
                lemma_pow10_add(x.scale as nat, shift as nat);
                lemma_cast_mul(us, uk);
                lemma_cast_mul(c, uk);
                let v = bcnum_real(x);
                assert(v * (up as real) == (c * uk) as real) by (nonlinear_arith)
                    requires
                        v == (c as real) / (us as real),
                        up as real == (us as real) * (uk as real),
                        (c * uk) as real == (c as real) * (uk as real),
                        us as real > 0real,
                ;
            }
            r
        } else {
            let r = Self {
                mid: big_tdiv(&x.coeff, &pow10_within(shift)),
                rad: big_from_i64(1),
                prec,
            };
            proof {
                // In ulps of 10^−scale, x is c exactly; dividing by 10^shift loses < 1 ulp.
                lemma_pow10_add(prec as nat, shift as nat);
                lemma_cast_mul(up, uk);
                let v = bcnum_real(x);
                assert(v * (us as real) == c as real) by (nonlinear_arith)
                    requires
                        v == (c as real) / (us as real),
                        us as real > 0real,
                ;
                assert(v * (uk as real) * (up as real) == v * (us as real)) by (nonlinear_arith)
                    requires
                        us as real == (up as real) * (uk as real),
                ;
                assert(in_ball(c, 0, up, v * (uk as real)));
                lemma_ball_div_int(c, 0, up, v * (uk as real), uk);
                assert(ceil_div_i(0, uk) == 0) by (nonlinear_arith)
                    requires
                        uk > 0,
                ;
                assert(v * (uk as real) / (uk as real) == v) by (nonlinear_arith)
                    requires
                        uk as real > 0real,
                ;
            }
            r
        }
    }

    /// An upper bound on |value|, in ulps.
    pub(crate) fn upper(&self) -> (r: BigInt)
        ensures
            big_view(&r) == abs_i(big_view(&self.mid)) + big_view(&self.rad),
    {
        big_add(&big_abs(&self.mid), &self.rad)
    }

    pub(crate) fn add(&self, other: &Self) -> (r: Self)
        requires
            self.wf(),
            other.wf(),
            self.prec == other.prec,
        ensures
            r.wf(),
            r.prec == self.prec,
            forall|va: real, vb: real|
                #![trigger self.contains(va), other.contains(vb)]
                self.contains(va) && other.contains(vb) ==> r.contains(va + vb),
    {
        let r = Self {
            mid: big_add(&self.mid, &other.mid),
            rad: big_add(&self.rad, &other.rad),
            prec: self.prec,
        };
        proof {
            assert forall|va: real, vb: real|
                #![trigger self.contains(va), other.contains(vb)]
                self.contains(va) && other.contains(vb) implies r.contains(va + vb) by {
                lemma_pow10_pos(self.prec as nat);
                lemma_ball_add(
                    big_view(&self.mid),
                    big_view(&self.rad),
                    big_view(&other.mid),
                    big_view(&other.rad),
                    self.unit(),
                    va,
                    vb,
                );
            }
        }
        r
    }

    pub(crate) fn sub(&self, other: &Self) -> (r: Self)
        requires
            self.wf(),
            other.wf(),
            self.prec == other.prec,
        ensures
            r.wf(),
            r.prec == self.prec,
            forall|va: real, vb: real|
                #![trigger self.contains(va), other.contains(vb)]
                self.contains(va) && other.contains(vb) ==> r.contains(va - vb),
    {
        let r = Self {
            mid: big_sub(&self.mid, &other.mid),
            rad: big_add(&self.rad, &other.rad),
            prec: self.prec,
        };
        proof {
            assert forall|va: real, vb: real|
                #![trigger self.contains(va), other.contains(vb)]
                self.contains(va) && other.contains(vb) implies r.contains(va - vb) by {
                lemma_pow10_pos(self.prec as nat);
                lemma_ball_add(
                    big_view(&self.mid),
                    big_view(&self.rad),
                    big_view(&other.mid),
                    big_view(&other.rad),
                    self.unit(),
                    va,
                    vb,
                );
            }
        }
        r
    }

    pub(crate) fn neg(&self) -> (r: Self)
        requires
            self.wf(),
        ensures
            r.wf(),
            r.prec == self.prec,
            forall|va: real| #[trigger] self.contains(va) ==> r.contains(-va),
    {
        let r = Self { mid: big_neg(&self.mid), rad: big_clone(&self.rad), prec: self.prec };
        proof {
            assert forall|va: real| #[trigger] self.contains(va) implies r.contains(-va) by {
                lemma_ball_neg(big_view(&self.mid), big_view(&self.rad), self.unit(), va);
            }
        }
        r
    }

    /// Adds `extra` ulps of uncertainty (a bound on an omitted series tail).
    pub(crate) fn widen(self, extra: &BigInt) -> (r: Self)
        requires
            self.wf(),
            big_view(extra) >= 0,
        ensures
            r.wf(),
            r.prec == self.prec,
            r.mid == self.mid,
            big_view(&r.rad) == big_view(&self.rad) + big_view(extra),
    {
        let mut r = self;
        r.rad = big_add(&r.rad, extra);
        r
    }

    /// Multiplication by an exact integer.
    pub(crate) fn mul_int(&self, k: &BigInt) -> (r: Self)
        requires
            self.wf(),
        ensures
            r.wf(),
            r.prec == self.prec,
            forall|va: real|
                #[trigger] self.contains(va) ==> r.contains(va * (big_view(k) as real)),
    {
        let r = Self {
            mid: big_mul(&self.mid, k),
            rad: big_mul(&self.rad, &big_abs(k)),
            prec: self.prec,
        };
        proof {
            assert(big_view(&self.rad) * abs_i(big_view(k)) >= 0) by (nonlinear_arith)
                requires
                    big_view(&self.rad) >= 0,
                    abs_i(big_view(k)) >= 0,
            ;
            assert forall|va: real| #[trigger] self.contains(va) implies r.contains(
                va * (big_view(k) as real),
            ) by {
                lemma_ball_mul_int(
                    big_view(&self.mid),
                    big_view(&self.rad),
                    self.unit(),
                    va,
                    big_view(k),
                );
            }
        }
        r
    }

    /// Division by an exact integer `k > 0`: the quotient is truncated (< 1 ulp).
    pub(crate) fn div_int(&self, k: &BigInt) -> (r: Self)
        requires
            self.wf(),
            big_view(k) > 0,
        ensures
            r.wf(),
            r.prec == self.prec,
            forall|va: real|
                #[trigger] self.contains(va) ==> r.contains(va / (big_view(k) as real)),
    {
        let r = Self {
            mid: big_tdiv(&self.mid, k),
            rad: plus_one(ceil_div(&self.rad, k)),
            prec: self.prec,
        };
        proof {
            assert forall|va: real| #[trigger] self.contains(va) implies r.contains(
                va / (big_view(k) as real),
            ) by {
                lemma_pow10_pos(self.prec as nat);
                assert(spec_tdiv(big_view(&self.mid), big_view(k)) == trunc_div(
                    big_view(&self.mid),
                    big_view(k),
                ));
                lemma_ball_div_int(
                    big_view(&self.mid),
                    big_view(&self.rad),
                    self.unit(),
                    va,
                    big_view(k),
                );
            }
        }
        r
    }

    /// Multiplication by 2^n (exact).
    pub(crate) fn shl(&self, n: u64) -> (r: Self)
        requires
            self.wf(),
        ensures
            r.wf(),
            r.prec == self.prec,
            forall|va: real|
                #[trigger] self.contains(va) ==> r.contains(
                    va * (spec_pow_int(2, n as nat) as real),
                ),
    {
        let r = Self { mid: big_shl(&self.mid, n), rad: big_shl(&self.rad, n), prec: self.prec };
        proof {
            let k = spec_pow_int(2, n as nat);
            lemma_pow_positive(2, n as nat);
            assert(abs_i(k) == k);
            assert(big_view(&self.rad) * k >= 0) by (nonlinear_arith)
                requires
                    big_view(&self.rad) >= 0,
                    k > 0,
            ;
            assert forall|va: real| #[trigger] self.contains(va) implies r.contains(
                va * (k as real),
            ) by {
                lemma_ball_mul_int(big_view(&self.mid), big_view(&self.rad), self.unit(), va, k);
            }
        }
        r
    }

    /// Division by 2^n: the shift floors the midpoint (< 1 ulp).
    pub(crate) fn shr(&self, n: u64) -> (r: Self)
        requires
            self.wf(),
        ensures
            r.wf(),
            r.prec == self.prec,
            forall|va: real|
                #[trigger] self.contains(va) ==> r.contains(
                    va / (spec_pow_int(2, n as nat) as real),
                ),
    {
        let divisor = big_shl(&big_from_i64(1), n);
        proof {
            lemma_pow_positive(2, n as nat);
        }
        let r = Self {
            mid: big_shr(&self.mid, n),
            rad: plus_one(ceil_div(&self.rad, &divisor)),
            prec: self.prec,
        };
        proof {
            let k = spec_pow_int(2, n as nat);
            assert forall|va: real| #[trigger] self.contains(va) implies r.contains(
                va / (k as real),
            ) by {
                lemma_pow10_pos(self.prec as nat);
                lemma_ball_div_int_floor(
                    big_view(&self.mid),
                    big_view(&self.rad),
                    self.unit(),
                    va,
                    k,
                );
            }
        }
        r
    }

    /// The same value at a precision `prec <= self.prec`.
    pub(crate) fn reduce_prec(&self, prec: usize) -> (r: Self)
        requires
            self.wf(),
            prec <= self.prec,
        ensures
            r.wf(),
            r.prec == prec,
            forall|va: real| #[trigger] self.contains(va) ==> r.contains(va),
    {
        let divisor = pow10_within(self.prec - prec);
        proof {
            lemma_pow10_pos((self.prec - prec) as nat);
        }
        let r = Self {
            mid: big_tdiv(&self.mid, &divisor),
            rad: plus_one(ceil_div(&self.rad, &divisor)),
            prec,
        };
        proof {
            let k = big_view(&divisor);
            let up = spec_num::pow10(prec as nat);
            lemma_pow10_pos(prec as nat);
            lemma_pow10_add(prec as nat, (self.prec - prec) as nat);
            assert(self.unit() == up * k);
            lemma_cast_mul(up, k);
            assert forall|va: real| #[trigger] self.contains(va) implies r.contains(va) by {
                // In ulps of 10^−prec, the value is va·10^(self.prec − prec) / 10^(self.prec − prec).
                let w = va * (k as real);
                assert(w * (up as real) == va * (self.unit() as real)) by (nonlinear_arith)
                    requires
                        w == va * (k as real),
                        self.unit() as real == (up as real) * (k as real),
                ;
                assert(spec_tdiv(big_view(&self.mid), k) == trunc_div(big_view(&self.mid), k));
                lemma_ball_div_int(big_view(&self.mid), big_view(&self.rad), up, w, k);
                assert(w / (k as real) == va) by (nonlinear_arith)
                    requires
                        w == va * (k as real),
                        k as real > 0real,
                ;
            }
        }
        r
    }

    /// With A = a·10^p and B = b·10^p, |A·B − MA·MB| <= |MA|·RB + |MB|·RA + RA·RB; dividing by
    /// 10^p and truncating adds < 1 ulp.
    pub(crate) fn mul(&self, other: &Self) -> (r: Self)
        requires
            self.wf(),
            other.wf(),
            self.prec == other.prec,
        ensures
            r.wf(),
            r.prec == self.prec,
            forall|va: real, vb: real|
                #![trigger self.contains(va), other.contains(vb)]
                self.contains(va) && other.contains(vb) ==> r.contains(va * vb),
    {
        let scale = pow10_within(self.prec);
        let spread = big_add(
            &big_add(
                &big_mul(&big_abs(&self.mid), &other.rad),
                &big_mul(&big_abs(&other.mid), &self.rad),
            ),
            &big_mul(&self.rad, &other.rad),
        );
        proof {
            lemma_pow10_pos(self.prec as nat);
            assert(big_view(&spread) >= 0) by (nonlinear_arith)
                requires
                    big_view(&spread) == abs_i(big_view(&self.mid)) * big_view(&other.rad)
                        + abs_i(big_view(&other.mid)) * big_view(&self.rad) + big_view(&self.rad)
                        * big_view(&other.rad),
                    big_view(&self.rad) >= 0,
                    big_view(&other.rad) >= 0,
                    abs_i(big_view(&self.mid)) >= 0,
                    abs_i(big_view(&other.mid)) >= 0,
            ;
        }
        let r = Self {
            mid: big_tdiv(&big_mul(&self.mid, &other.mid), &scale),
            rad: plus_one(ceil_div(&spread, &scale)),
            prec: self.prec,
        };
        proof {
            let u = self.unit();
            assert(spec_tdiv(big_view(&self.mid) * big_view(&other.mid), u) == trunc_div(
                big_view(&self.mid) * big_view(&other.mid),
                u,
            ));
            assert forall|va: real, vb: real|
                #![trigger self.contains(va), other.contains(vb)]
                self.contains(va) && other.contains(vb) implies r.contains(va * vb) by {
                lemma_ball_mul(
                    big_view(&self.mid),
                    big_view(&self.rad),
                    big_view(&other.mid),
                    big_view(&other.rad),
                    u,
                    va,
                    vb,
                );
            }
        }
        r
    }

    /// |A/B − MA/MB| = |δA·MB − MA·δB| / (|B|·|MB|) <= (RA·|MB| + |MA|·RB) / ((|MB| − RB)·|MB|),
    /// scaled by 10^p, plus < 1 ulp for truncating. `None` if the divisor's ball contains 0.
    pub(crate) fn div(&self, other: &Self) -> (r: Option<Self>)
        requires
            self.wf(),
            other.wf(),
            self.prec == other.prec,
        ensures
            r is Some ==> r->Some_0.wf() && r->Some_0.prec == self.prec,
            r is Some ==> forall|va: real, vb: real|
                #![trigger self.contains(va), other.contains(vb)]
                self.contains(va) && other.contains(vb) ==> vb != 0real && r->Some_0.contains(
                    va / vb,
                ),
    {
        let mb = big_abs(&other.mid);
        if !matches!(big_cmp(&mb, &other.rad), Ordering::Greater) {
            return None;
        }
        let scale = pow10_within(self.prec);
        let spread = big_mul(
            &big_add(&big_mul(&self.rad, &mb), &big_mul(&big_abs(&self.mid), &other.rad)),
            &scale,
        );
        let den = big_mul(&big_sub(&mb, &other.rad), &mb);
        proof {
            lemma_pow10_pos(self.prec as nat);
            let (ra, rb, ama, amb, u) = (
                big_view(&self.rad),
                big_view(&other.rad),
                abs_i(big_view(&self.mid)),
                big_view(&mb),
                big_view(&scale),
            );
            assert(big_view(&spread) >= 0 && big_view(&den) > 0) by (nonlinear_arith)
                requires
                    big_view(&spread) == (ra * amb + ama * rb) * u,
                    big_view(&den) == (amb - rb) * amb,
                    ra >= 0,
                    rb >= 0,
                    ama >= 0,
                    amb > rb,
                    u > 0,
            ;
        }
        let r = Self {
            mid: big_tdiv(&big_mul(&self.mid, &scale), &other.mid),
            rad: plus_one(ceil_div(&spread, &den)),
            prec: self.prec,
        };
        proof {
            assert forall|va: real, vb: real|
                #![trigger self.contains(va), other.contains(vb)]
                self.contains(va) && other.contains(vb) implies vb != 0real && r.contains(
                    va / vb,
                ) by {
                lemma_ball_div(
                    big_view(&self.mid),
                    big_view(&self.rad),
                    big_view(&other.mid),
                    big_view(&other.rad),
                    self.unit(),
                    va,
                    vb,
                );
            }
        }
        Some(r)
    }

    /// For A >= 0, |√(A·10^p) − √(MA·10^p)| = |δA|·10^p / (√(A·10^p) + √(MA·10^p)), which is at
    /// most RA·10^p / isqrt(MA·10^p); the floor of the integer square root adds < 1 ulp. `None`
    /// if that bound is unavailable (MA·10^p < 1) or the ball reaches below 0.
    pub(crate) fn sqrt(&self) -> (r: Option<Self>)
        requires
            self.wf(),
        ensures
            r is Some ==> r->Some_0.wf() && r->Some_0.prec == self.prec,
            r is Some ==> forall|va: real|
                #[trigger] self.contains(va) ==> va >= 0real && r->Some_0.contains(sqrt_r(va)),
    {
        if matches!(big_cmp(&self.mid, &self.rad), Ordering::Less) {
            return None;
        }
        let scale = pow10_within(self.prec);
        proof {
            lemma_pow10_pos(self.prec as nat);
            assert(big_view(&self.mid) * big_view(&scale) >= 0) by (nonlinear_arith)
                requires
                    big_view(&self.mid) >= big_view(&self.rad),
                    big_view(&self.rad) >= 0,
                    big_view(&scale) > 0,
            ;
        }
        let root = big_isqrt(&big_mul(&self.mid, &scale));
        if big_is_zero(&root) {
            return None;
        }
        proof {
            assert(big_view(&self.rad) * big_view(&scale) >= 0) by (nonlinear_arith)
                requires
                    big_view(&self.rad) >= 0,
                    big_view(&scale) > 0,
            ;
        }
        let r = Self {
            mid: big_clone(&root),
            rad: plus_one(ceil_div(&big_mul(&self.rad, &scale), &root)),
            prec: self.prec,
        };
        proof {
            assert forall|va: real| #[trigger] self.contains(va) implies va >= 0real
                && r.contains(sqrt_r(va)) by {
                lemma_ball_sqrt(
                    big_view(&self.mid),
                    big_view(&self.rad),
                    self.unit(),
                    va,
                    big_view(&root),
                );
            }
        }
        Some(r)
    }

    pub(crate) fn copy(&self) -> (r: Ball)
        ensures
            r.prec == self.prec,
            big_view(&r.mid) == big_view(&self.mid),
            big_view(&r.rad) == big_view(&self.rad),
    {
        Ball { mid: big_clone(&self.mid), rad: big_clone(&self.rad), prec: self.prec }
    }
}

/// The truncation toward zero of every value in `b` at `scale <= b.prec` digits, as the
/// coefficient of a `BCNum` with that scale, or `None` if the values truncate differently.
///
/// With U = 10^(prec − scale) and mid = q·U + r (0 <= r < U), every value lies in
/// [q·U + r − rad, q·U + r + rad]. If rad < r and r + rad < U, that interval is inside the open
/// interval (q·U, (q+1)·U), so every value divided by U truncates toward zero to q when q >= 0
/// and to q + 1 when q < 0. A ball of radius 0 on a multiple of U is exact
/// (`lemma_certified_trunc_real`, `lemma_certified_trunc_real_exact`).
pub(crate) fn certified_trunc(b: &Ball, scale: usize) -> (r: Option<BigInt>)
    requires
        b.wf(),
        scale <= b.prec,
    ensures
        r is Some ==> forall|v: real| #[trigger] b.contains(v) ==> big_view(&r->Some_0) == trunc_r(
            v * (spec_num::pow10(scale as nat) as real),
        ),
{
    let unit = pow10_within(b.prec - scale);
    let ghost s = spec_num::pow10(scale as nat);
    proof {
        lemma_pow10_pos(scale as nat);
        lemma_pow10_pos((b.prec - scale) as nat);
        lemma_pow10_add(scale as nat, (b.prec - scale) as nat);
        assert(b.unit() == s * big_view(&unit));
    }
    let (q, r) = big_div_mod_floor(&b.mid, &unit);
    if big_is_zero(&b.rad) && big_is_zero(&r) {
        proof {
            assert forall|v: real| #[trigger] b.contains(v) implies big_view(&q) == trunc_r(
                v * (s as real),
            ) by {
                lemma_certified_trunc_real_exact(big_view(&b.mid), s, big_view(&unit), v);
            }
        }
        return Some(q);
    }
    if matches!(big_cmp(&b.rad, &r), Ordering::Less) && matches!(
        big_cmp(&big_add(&r, &b.rad), &unit),
        Ordering::Less
    ) {
        let negative = big_is_negative(&q);
        let t = if negative {
            plus_one(q)
        } else {
            q
        };
        proof {
            assert forall|v: real| #[trigger] b.contains(v) implies big_view(&t) == trunc_r(
                v * (s as real),
            ) by {
                lemma_certified_trunc_real(
                    big_view(&b.mid),
                    big_view(&b.rad),
                    s,
                    big_view(&unit),
                    v,
                );
            }
        }
        Some(t)
    } else {
        None
    }
}

/// Every ball that `f` returns contains `v`.
pub(crate) open spec fn all_contain<F: Fn(usize) -> Option<Ball>>(f: F, v: real) -> bool {
    forall|p: usize, b: Ball| #[trigger] f.ensures((p,), Some(b)) ==> b.contains(v)
}

/// Evaluates `f` at increasing working precisions until its ball certifies the truncation to
/// `scale` digits. The first precision comes from `verified_transcendental_guard_prec` (at least
/// `x_scale`, so the argument is exact); each retry doubles the guard digits, until
/// `MAX_WORKING_PREC`.
///
/// If every ball that `f` returns contains `v`, an `Ok` result is `v` truncated toward zero at
/// `scale` digits.
#[allow(clippy::collapsible_if, reason = "Verus does not support `let` chains")]
pub(crate) fn certify(
    x_scale: usize,
    scale: usize,
    extra: usize,
    f: impl Fn(usize) -> Option<Ball>,
) -> (r: Result<BCNum, RuntimeError>)
    requires
        x_scale <= MAX_VERIFIED_SCALE,
        scale <= MAX_VERIFIED_SCALE,
        extra <= MAX_VERIFIED_SCALE,
        forall|p: usize| scale + 15 <= p <= u32::MAX ==> #[trigger] f.requires((p,)),
        forall|p: usize, b: Ball| #[trigger] f.ensures((p,), Some(b)) ==> b.wf() && b.prec == p,
    ensures
        r is Ok ==> r->Ok_0.scale == scale,
        forall|v: real| #[trigger]
            all_contain(f, v) ==> (r is Ok ==> big_view(&r->Ok_0.coeff) == trunc_r(
                v * (spec_num::pow10(scale as nat) as real),
            )),
{
    let mut prec = verified_transcendental_guard_prec(x_scale, scale, extra);
    loop
        invariant
            scale <= MAX_VERIFIED_SCALE,
            scale + 15 <= prec <= 3 * MAX_VERIFIED_SCALE + 15,
            forall|p: usize| scale + 15 <= p <= u32::MAX ==> #[trigger] f.requires((p,)),
            forall|p: usize, b: Ball| #[trigger] f.ensures((p,), Some(b)) ==> b.wf() && b.prec
                == p,
        decreases u32::MAX - prec,
    {
        let fb = f(prec);
        if let Some(b) = fb {
            if let Some(q) = certified_trunc(&b, scale) {
                let r = BCNum::new(q, scale);
                proof {
                    assert forall|v: real| #[trigger] all_contain(f, v) implies big_view(&r.coeff)
                        == trunc_r(v * (spec_num::pow10(scale as nat) as real)) by {
                        assert(f.ensures((prec,), Some(b)));
                    }
                }
                return Ok(r);
            }
        }
        let guard = prec - scale;
        if prec > MAX_WORKING_PREC || guard > MAX_WORKING_PREC - prec {
            return Err(RuntimeError::MathArgumentTooLarge);
        }
        prec += guard;
    }
}

} // verus!
