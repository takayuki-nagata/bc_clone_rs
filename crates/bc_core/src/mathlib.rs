// SPDX-License-Identifier: MIT

//! The `-l` math library — `s`, `c`, `a`, `l`, `e`, `j` — with certified results.
//!
//! Every function returns the exact mathematical value truncated toward zero at the caller's
//! `scale` (`docs/COMPATIBILITY.md` §3.4). Values are computed as [`Ball`]s, a midpoint and a
//! radius that bound the true value, and a result is accepted only when every value in the ball
//! truncates to the same number ([`certified_trunc`]). Otherwise the computation is repeated
//! with twice as many guard digits (Ziv's strategy, [`certify`]).
//!
//! Exact results (`s(0)`, `c(0)`, `a(0)`, `e(0)`, `l(1)`, `j(n,0)`) are returned directly. For
//! every other argument (a rational number) the result is transcendental (Lindemann–Weierstrass;
//! Siegel for the Bessel functions), so it is never exactly a truncation boundary and the loop
//! ends. `docs/MATH_ERROR_BOUNDS.md` derives every radius used here.

use crate::error::RuntimeError;
use crate::math::{BCNum, pow10_within};
#[cfg(verus_keep_ghost)]
use crate::real_arith::*;
#[cfg(verus_keep_ghost)]
use crate::spec_num;
#[cfg(verus_keep_ghost)]
use crate::spec_num::{lemma_pow10_add, lemma_pow10_pos, spec_pow_int, spec_tdiv, trunc_div};
#[cfg(verus_keep_ghost)]
use crate::trusted_bigint::big_view;
use crate::trusted_bigint::{
    big_abs, big_add, big_add_i64, big_bits, big_clone, big_cmp, big_decimal_digits,
    big_div_mod_floor, big_from_i64, big_from_u64, big_from_usize, big_is_negative, big_is_zero,
    big_isqrt, big_mul, big_neg, big_shl, big_shr, big_signum, big_sub, big_tdiv, big_tdiv_u64,
    big_to_i64,
};
#[cfg(verus_keep_ghost)]
use crate::trusted_math::*;
use crate::verified_kernels::{
    MAX_VERIFIED_SCALE, verified_bessel_negative_order_parity, verified_decimal_scale_shift,
    verified_transcendental_guard_prec,
};
#[cfg(verus_keep_ghost)]
use bc_spec::power::lemma_pow_positive;
use core::cmp::Ordering;
use num_bigint::BigInt;
use verus_builtin::{Ghost, real};
#[cfg(not(verus_keep_ghost))]
use verus_builtin_macros::verus;
#[cfg(verus_keep_ghost)]
use vstd::arithmetic::div_mod::lemma_div_denominator;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

verus! {

/// Largest integer part of the argument of `e(x)` and of `x` in `j(n,x)` (`docs/COMPATIBILITY.md`
/// §2). e^x then has at most about 0.4343·x ≈ 8.7·10^8 integer digits, and the extra working
/// precision x/2 stays within `MAX_VERIFIED_SCALE`, the precondition of
/// `verified_transcendental_guard_prec`.
pub const EXP_ARG_MAX: u64 = 2_000_000_000;

/// Largest working precision. [`certify`] gives up (with `MathArgumentTooLarge`) rather than
/// exceed it; every decimal shift then stays far below `u32::MAX`, as `pow10` requires.
const MAX_WORKING_PREC: usize = 3 * MAX_VERIFIED_SCALE;

/// Series stop once the next term is bounded by this many ulps; its bound is then added to the
/// radius as the tail. Term radii settle below it (`docs/MATH_ERROR_BOUNDS.md` §2).
const TAIL_ULPS: u32 = 16;

/// A real number known to lie in `[mid - rad, mid + rad]`, both in units of `10^-prec`
/// (`rad >= 0`). Every operation returns a ball that contains the exact result of the operation
/// on any values of its operands' balls.
#[derive(Clone, Debug, PartialEq, Eq)]
struct Ball {
    mid: BigInt,
    rad: BigInt,
    prec: usize,
}

/// The value of a `BCNum`, coeff·10^−scale.
pub open spec fn bcnum_real(x: &BCNum) -> real {
    (big_view(&x.coeff) as real) / (spec_num::pow10(x.scale as nat) as real)
}

/// `ceil(a / b)` for `a >= 0` and `b > 0`.
fn ceil_div(a: &BigInt, b: &BigInt) -> (r: BigInt)
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
fn plus_one(a: BigInt) -> (r: BigInt)
    ensures
        big_view(&r) == big_view(&a) + 1,
{
    big_add_i64(a, 1)
}

impl Ball {
    /// The radius is nonnegative and `10^prec` can be computed (`pow10_within`).
    spec fn wf(&self) -> bool {
        big_view(&self.rad) >= 0 && self.prec <= u32::MAX
    }

    /// One unit of the precision: 10^prec ulps make 1.
    spec fn unit(&self) -> int {
        spec_num::pow10(self.prec as nat)
    }

    /// The ball contains the real `v`: |v·10^prec − mid| <= rad.
    spec fn contains(&self, v: real) -> bool {
        in_ball(big_view(&self.mid), big_view(&self.rad), self.unit(), v)
    }

    fn exact(mid: BigInt, prec: usize) -> (r: Self)
        ensures
            r.mid == mid,
            big_view(&r.rad) == 0,
            r.prec == prec,
    {
        Self { mid, rad: big_from_i64(0), prec }
    }

    fn int(value: i64, prec: usize) -> (r: Self)
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
    fn from_bcnum(x: &BCNum, prec: usize) -> (r: Self)
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
    fn upper(&self) -> (r: BigInt)
        ensures
            big_view(&r) == abs_i(big_view(&self.mid)) + big_view(&self.rad),
    {
        big_add(&big_abs(&self.mid), &self.rad)
    }

    fn add(&self, other: &Self) -> (r: Self)
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

    fn sub(&self, other: &Self) -> (r: Self)
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

    fn neg(&self) -> (r: Self)
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
    fn widen(self, extra: &BigInt) -> (r: Self)
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
    fn mul_int(&self, k: &BigInt) -> (r: Self)
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
    fn div_int(&self, k: &BigInt) -> (r: Self)
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
    fn shl(&self, n: u64) -> (r: Self)
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
    fn shr(&self, n: u64) -> (r: Self)
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
    fn reduce_prec(&self, prec: usize) -> (r: Self)
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
    fn mul(&self, other: &Self) -> (r: Self)
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
    fn div(&self, other: &Self) -> (r: Option<Self>)
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
    fn sqrt(&self) -> (r: Option<Self>)
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
}

/// The truncation toward zero of every value in `b` at `scale <= b.prec` digits, as the
/// coefficient of a `BCNum` with that scale, or `None` if the values truncate differently.
///
/// With U = 10^(prec − scale) and mid = q·U + r (0 <= r < U), every value lies in
/// [q·U + r − rad, q·U + r + rad]. If rad < r and r + rad < U, that interval is inside the open
/// interval (q·U, (q+1)·U), so every value divided by U truncates toward zero to q when q >= 0
/// and to q + 1 when q < 0. A ball of radius 0 on a multiple of U is exact
/// (`lemma_certified_trunc_real`, `lemma_certified_trunc_real_exact`).
fn certified_trunc(b: &Ball, scale: usize) -> (r: Option<BigInt>)
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
spec fn all_contain<F: Fn(usize) -> Option<Ball>>(f: F, v: real) -> bool {
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
fn certify(
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

verus! {

/// The exact result `value` at `scale` digits.
fn exact_result(value: i64, scale: usize) -> (r: BCNum)
    requires
        scale <= u32::MAX,
    ensures
        r.scale == scale,
        big_view(&r.coeff) == value * spec_num::pow10(scale as nat),
{
    BCNum::new(big_mul(&big_from_i64(value), &pow10_within(scale)), scale)
}

/// The integer part of |x|.
fn abs_int_part(x: &BCNum) -> (r: BigInt)
    requires
        x.scale <= u32::MAX,
    ensures
        big_view(&r) == abs_i(big_view(&x.coeff)) / spec_num::pow10(x.scale as nat),
        big_view(&r) >= 0,
{
    proof {
        lemma_pow10_pos(x.scale as nat);
    }
    big_tdiv(&big_abs(&x.coeff), &pow10_within(x.scale))
}

/// The number of decimal digits of the integer part of |x| (0 when |x| < 1).
fn int_digits(x: &BCNum) -> usize
    requires
        x.scale <= u32::MAX,
{
    let int_part = abs_int_part(x);
    if big_is_zero(&int_part) {
        0
    } else {
        big_decimal_digits(&int_part)
    }
}

} // verus!

verus! {

// --- Constants ---

/// Term k of the series that `arc_inv(n, alternating, _)` sums: atan's (alternating) or
/// artanh's at y = 1/n.
spec fn arc_term(n: int, alternating: bool, k: nat) -> real {
    let y = 1real / (n as real);
    if alternating {
        atan_term(y, k)
    } else {
        artanh_term(y, k)
    }
}

/// The value that `arc_inv(n, alternating, _)` approximates: atan(1/n) or artanh(1/n).
spec fn arc_value(n: int, alternating: bool) -> real {
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
fn arc_inv(n: u32, alternating: bool, prec: usize) -> (r: Ball)
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
fn pi(prec: usize) -> (r: Ball)
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
fn ln2(prec: usize) -> (r: Ball)
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

verus! {

// --- Series ---

/// Series stop after at most this many terms (so that the factors below fit in `u64`); no
/// series of the library comes close.
const MAX_SERIES_TERMS: u64 = 0x100_0000_0000;

/// A series that `sum_series` sums, with the balls its terms are built from. The true
/// argument x of each series is a ghost value: r for sin and cos, y for atan and artanh, r for
/// exp, and h = x/2 for J_n.
enum Series {
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
spec fn series_term(s: Series, x: real, k: nat) -> real {
    match s {
        Series::SinCos { odd, .. } => sin_cos_term(x, odd as nat, k),
        Series::Atan { .. } => atan_term(x, k),
        Series::Artanh { .. } => artanh_term(x, k),
        Series::Exp { .. } => exp_term(x, k),
        Series::Bessel { n, .. } => bessel_term(n as nat, x, k),
    }
}

/// The value of the true series at x.
spec fn series_value(s: Series, x: real) -> real {
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
spec fn power_value(s: Series, x: real, k: nat) -> real {
    match s {
        Series::Atan { .. } => sign_r(k) * pow_r(x, 2 * k + 1),
        _ => pow_r(x, 2 * k + 1),
    }
}

impl Series {
    /// The balls are well formed at precision `p`, and the parameters are in range.
    spec fn wf(&self, p: usize) -> bool {
        match *self {
            Series::SinCos { r_sq, odd } => r_sq.wf() && r_sq.prec == p && odd <= 1,
            Series::Atan { y_sq } => y_sq.wf() && y_sq.prec == p,
            Series::Artanh { y_sq } => y_sq.wf() && y_sq.prec == p,
            Series::Exp { r } => r.wf() && r.prec == p,
            Series::Bessel { half_sq, n } => half_sq.wf() && half_sq.prec == p && n < 0x8000_0000_0000_0000,
        }
    }

    /// The balls contain what they stand for at the argument x.
    spec fn holds(&self, x: real) -> bool {
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
    fn tail_factor(&self) -> (r: u64)
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
    fn tail_applies(&self) -> (r: bool)
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
    spec fn prec_of(&self) -> usize {
        match *self {
            Series::SinCos { r_sq, .. } => r_sq.prec,
            Series::Atan { y_sq } => y_sq.prec,
            Series::Artanh { y_sq } => y_sq.prec,
            Series::Exp { r } => r.prec,
            Series::Bessel { half_sq, .. } => half_sq.prec,
        }
    }

    /// What `tail_applies` establishes about x.
    spec fn tail_ok(&self, x: real) -> bool {
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
    fn decreasing(&self, k: u64) -> (r: bool)
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
    spec fn decreasing_at(&self, x: real, k: nat) -> bool {
        match *self {
            Series::SinCos { odd, .. } => (((2 * k + odd + 1) * (2 * k + odd + 2)) as real) >= abs_r(x * x),
            Series::Bessel { n, .. } => (((k + 1) * (k + n + 1)) as real) >= abs_r(x * x),
            _ => true,
        }
    }

    /// Term k from term k−1 (and `power`, which carries (−1)^k y^(2k+1) or y^(2k+1)).
    fn next(&self, term: &Ball, power: &mut Ball, k: u64, Ghost(x): Ghost<real>) -> (r: Ball)
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

impl Ball {
    fn copy(&self) -> (r: Ball)
        ensures
            r.prec == self.prec,
            big_view(&r.mid) == big_view(&self.mid),
            big_view(&r.rad) == big_view(&self.rad),
    {
        Ball { mid: big_clone(&self.mid), rad: big_clone(&self.rad), prec: self.prec }
    }
}

/// Whether `num·10^p >= den·b.upper()`, so that every value v in `b` has |v| <= num/den. With
/// `num` the factor dividing the next term and `b` the ball of a square, the terms decrease
/// from there on.
fn bounded(b: &Ball, num: &BigInt, den: u64) -> (r: bool)
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
fn sum_series(first: Ball, series: &Series, Ghost(x): Ghost<real>) -> (r: Option<Ball>)
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
            }
            return Some(sum.widen(&tail));
        }
        proof {
            assert(partial_sum(t, (k + 1) as nat) == partial_sum(t, k as nat) + t(k as nat));
        }
        sum = sum.add(&term);
    }
}

/// The tail bound of each series at a stopping point k: |value − S_k| <= c·|term k| with c the
/// tail factor, given the argument bound (`tail_ok`) and the decrease from term k on.
proof fn lemma_series_tail(s: Series, x: real, k: nat)
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

// --- Sine and cosine ---

verus! {

/// x − k·2π.
spec fn shift_2pi(x: real, k: int) -> real {
    x - 2real * (k as real) * pi_r()
}

/// The ball contains x − k·2π for some integer k.
spec fn reduced_by_2pi(b: Ball, x: real) -> bool {
    exists|k: int| #![trigger shift_2pi(x, k)] b.contains(shift_2pi(x, k))
}

/// A witness k for `reduced_by_2pi`.
proof fn lemma_reduced(b: Ball, x: real, k: int)
    requires
        b.contains(shift_2pi(x, k)),
    ensures
        reduced_by_2pi(b, x),
{
}

/// x − k·2π for the integer k nearest x / 2π (any integer k leaves sin and cos unchanged), at
/// precision `prec`. π carries as many extra digits as x has integer digits, so k·rad(2π) stays
/// within a few ulps at `prec`. `None` if that working precision would exceed `u32::MAX`.
fn reduce_angle(x: &BCNum, prec: usize) -> (r: Option<Ball>)
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
    if digits >= u32::MAX as usize - prec {
        return None;
    }
    let work = prec + digits + 1;
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
proof fn lemma_sin_cos_first_terms(r: real)
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
proof fn lemma_sin_cos_zero()
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
proof fn lemma_bcnum_real_zero(x: &BCNum)
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
fn sin_cos_ball(x: &BCNum, prec: usize, cos: bool) -> (r: Option<Ball>)
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

// --- Arctangent ---

verus! {

/// atan 0 = 0 (atan is odd).
proof fn lemma_atan_zero()
    ensures
        atan_r(0real) == 0real,
{
    axiom_atan_odd(0real);
    assert(-0real == 0real);
}

/// Term 0 of the atan series is y.
proof fn lemma_atan_first_term(y: real)
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
proof fn lemma_sign_positive(x: &BCNum, sgn: int)
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
fn atan_ball(x: &BCNum, prec: usize) -> (r: Option<Ball>)
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

// --- Natural logarithm ---

verus! {

/// ln 1 = 0.
proof fn lemma_ln_one()
    ensures
        ln_r(1real) == 0real,
{
    axiom_ln_mul(1real, 1real);
    assert(1real * 1real == 1real);
}

/// 2^n > 0 and ln(2^n) = n·ln 2.
proof fn lemma_ln_pow2(n: nat)
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
spec fn scaled_by_pow2(x: real, k: int) -> real {
    if k >= 0 {
        x / (spec_pow_int(2, k as nat) as real)
    } else {
        x * (spec_pow_int(2, (-k) as nat) as real)
    }
}

/// ln x = ln m + k·ln 2 for m = x·2^−k > 0.
proof fn lemma_ln_scaled(x: real, k: int)
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
proof fn lemma_artanh_of_cayley(m: real, y: real)
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
proof fn lemma_artanh_first_term(y: real)
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
fn shifted(xb: &Ball, k: i64) -> (r: Ball)
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
    reason = "both bit counts are at most i64::MAX, checked just before; Verus checks the casts"
)]
fn ln_ball(x: &BCNum, prec: usize) -> (r: Option<Ball>)
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
    let extra = if k == 0 {
        1
    } else {
        big_decimal_digits(&big_abs(&k_big))
    };
    if extra >= u32::MAX as usize - prec {
        return None;
    }
    let k_ln2 = ln2(prec + extra).mul_int(&k_big).reduce_prec(prec);
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

// --- Exponential ---

verus! {

/// e^0 = 1.
proof fn lemma_exp_zero()
    ensures
        exp_r(0real) == 1real,
{
    lemma_ln_one();
    axiom_exp_ln(1real);
}

/// e^z > 0 and e^z·e^−z = 1.
proof fn lemma_exp_pos(z: real)
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
proof fn lemma_exp_mono(a: real, b: real)
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
proof fn lemma_exp_mul_nat(z: real, k: nat)
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
proof fn lemma_exp_n_ln2(n: int)
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

/// (a as real)^m = (a^m) as real.
proof fn lemma_pow_r_int(a: int, m: nat)
    ensures
        pow_r(a as real, m) == spec_pow_int(a, m) as real,
    decreases m,
{
    if m > 0 {
        lemma_pow_r_int(a, (m - 1) as nat);
        lemma_cast_mul(a, spec_pow_int(a, (m - 1) as nat));
    }
}

/// a^k > b^k for a > b > 0 and k >= 1.
proof fn lemma_pow_r_gt(a: real, b: real, k: nat)
    requires
        a > b,
        b > 0real,
        k >= 1,
    ensures
        pow_r(a, k) > pow_r(b, k),
        pow_r(b, k) > 0real,
    decreases k,
{
    if k == 1 {
        assert(pow_r(a, 1) == a * pow_r(a, 0));
        assert(pow_r(b, 1) == b * pow_r(b, 0));
    } else {
        lemma_pow_r_gt(a, b, (k - 1) as nat);
        let (pa, pb) = (pow_r(a, (k - 1) as nat), pow_r(b, (k - 1) as nat));
        assert(a * pa > b * pb && b * pb > 0real) by (nonlinear_arith)
            requires
                a > b,
                b > 0real,
                pa > pb,
                pb > 0real,
        ;
    }
}

/// e^2.3026 > 10 (2.3026 > ln 10). With z = 2.3026/4, the exponential series' tail bound after
/// nine terms gives e^z >= 1.778284, and 1.778284^4 > 10.
proof fn lemma_exp_23026()
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
proof fn lemma_exp_tiny(x: real, scale: nat)
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

/// 10^n as `pow10` and as `spec_pow_int(10, n)` agree.
proof fn lemma_pow10_is_pow(n: nat)
    ensures
        spec_num::pow10(n) == spec_pow_int(10, n),
    decreases n,
{
    if n > 0 {
        lemma_pow10_is_pow((n - 1) as nat);
    }
}

/// Term 0 of the exponential series is 1.
proof fn lemma_exp_first_term(r: real)
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
fn exp_ball(x: &BCNum, prec: usize) -> (r: Option<Ball>)
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
proof fn lemma_exp_shortcut_bound(x: &BCNum, lhs: int, rhs: int, scale: nat)
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

// --- Bessel functions ---

verus! {

/// 0 <= a <= b implies 0 <= a^k <= b^k.
proof fn lemma_pow_r_mono(a: real, b: real, k: nat)
    requires
        0real <= a,
        a <= b,
    ensures
        0real <= pow_r(a, k),
        pow_r(a, k) <= pow_r(b, k),
    decreases k,
{
    if k > 0 {
        lemma_pow_r_mono(a, b, (k - 1) as nat);
        let (pa, pb) = (pow_r(a, (k - 1) as nat), pow_r(b, (k - 1) as nat));
        assert(0real <= a * pa && a * pa <= b * pb) by (nonlinear_arith)
            requires
                0real <= a,
                a <= b,
                0real <= pa,
                pa <= pb,
        ;
    }
}

/// (a·b)^k = a^k·b^k.
proof fn lemma_pow_r_mul(a: real, b: real, k: nat)
    ensures
        pow_r(a * b, k) == pow_r(a, k) * pow_r(b, k),
    decreases k,
{
    if k > 0 {
        lemma_pow_r_mul(a, b, (k - 1) as nat);
        let (pa, pb) = (pow_r(a, (k - 1) as nat), pow_r(b, (k - 1) as nat));
        assert((a * b) * (pa * pb) == (a * pa) * (b * pb)) by (nonlinear_arith);
    }
}

/// For 0 <= a <= 1, a^k <= a^j when j <= k.
proof fn lemma_pow_r_le_one(a: real, j: nat, k: nat)
    requires
        0real <= a,
        a <= 1real,
        j <= k,
    ensures
        pow_r(a, k) <= pow_r(a, j),
    decreases k - j,
{
    if j < k {
        lemma_pow_r_le_one(a, j, (k - 1) as nat);
        lemma_pow_r_mono(0real, a, (k - 1) as nat);
        let p = pow_r(a, (k - 1) as nat);
        assert(a * p <= p) by (nonlinear_arith)
            requires
                0real <= a,
                a <= 1real,
                0real <= p,
        ;
    }
}

/// e <= 2.75 < 3, from the tail bound of the exponential series after four terms.
proof fn lemma_e_le_3()
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
proof fn lemma_pow_ratio(n: nat)
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
proof fn lemma_fact_lower(n: nat)
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
proof fn lemma_half_pow(k: nat)
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
proof fn lemma_bessel_tiny(n: nat, x: real, scale: nat)
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

/// 1^n = 1.
proof fn lemma_pow_r_one(n: nat)
    ensures
        pow_r(1real, n) == 1real,
    decreases n,
{
    if n > 0 {
        lemma_pow_r_one((n - 1) as nat);
    }
}

/// J_n(0) is 1 for n = 0 and 0 otherwise, from the tail bound of the series after one term.
proof fn lemma_bessel_zero(n: nat)
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
proof fn lemma_bessel_first_step(h: real, i: nat)
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
fn bessel_ball(n: u64, x: &BCNum, prec: usize) -> (r: Option<Ball>)
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
proof fn lemma_bessel_ceil(x: &BCNum, c: int)
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
proof fn lemma_trunc_small(y: real)
    requires
        abs_r(y) < 1real,
    ensures
        trunc_r(y) == 0,
{
}

} // verus!

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::vec::Vec;
    use num_traits::Signed;
    use proptest::prelude::*;

    /// A decimal literal, optionally negative (`BCNum::from_string` takes digits only).
    fn num(s: &str) -> BCNum {
        match s.strip_prefix('-') {
            Some(digits) => {
                let v = BCNum::from_string(digits, 10);
                BCNum::new(-v.coeff, v.scale)
            }
            None => BCNum::from_string(s, 10),
        }
    }

    /// The truncation toward zero of v / 10^k, by integer arithmetic.
    fn trunc_div(v: &BigInt, k: usize) -> BigInt {
        v / pow10_within(k)
    }

    proptest! {
        /// `certified_trunc` never accepts a ball whose values truncate differently, and the
        /// value it returns is their common truncation (checked for every integer in the ball).
        #[test]
        fn certified_trunc_is_sound(mid in -5000i64..5000, rad in 0i64..40, k in 0usize..3) {
            let ball = Ball { mid: BigInt::from(mid), rad: BigInt::from(rad), prec: k };
            let truncs: Vec<BigInt> =
                (mid - rad..=mid + rad).map(|v| trunc_div(&BigInt::from(v), k)).collect();
            let all_same = truncs.iter().all(|t| *t == truncs[0]);
            match certified_trunc(&ball, 0) {
                Some(q) => prop_assert!(all_same && q == truncs[0]),
                // A ball touching a multiple of 10^k is rejected even when the truncations
                // agree, because the true value may be any real in it.
                None => prop_assert!(!all_same || rad > 0 || (mid % 10i64.pow(k as u32) == 0)),
            }
        }

        /// Ball arithmetic contains the exact results: for exact operands a/10^p and b/10^p
        /// with radius 0, the true product, quotient and square root lie in the balls.
        #[test]
        fn ball_operations_contain_exact_results(a in 1i64..10_000_000, b in 1i64..10_000_000) {
            let p = 4;
            let ba = Ball::exact(BigInt::from(a), p);
            let bb = Ball::exact(BigInt::from(b), p);
            let scale = BigInt::from(10_000);
            // a·b / 10^p in ulps is a·b/10^4: check |mid·10^4 − a·b| <= rad·10^4.
            let prod = ba.mul(&bb);
            prop_assert!((&prod.mid * &scale - a * b).abs() <= &prod.rad * &scale);
            // a/b in ulps is a·10^4/b: check |mid·b − a·10^4| <= rad·b.
            let quot = ba.div(&bb).unwrap();
            prop_assert!((&quot.mid * b - BigInt::from(a) * &scale).abs() <= &quot.rad * b);
            // √(a·10^4) in ulps: (mid − rad)² <= a·10^4 <= (mid + rad)².
            let root = ba.sqrt().unwrap();
            let v = BigInt::from(a) * &scale;
            prop_assert!((&root.mid - &root.rad).pow(2) <= v && v <= (&root.mid + &root.rad).pow(2));
        }
    }

    #[test]
    fn constants_contain_their_true_values() {
        // π and ln 2 to 60 digits.
        let pi60 = "3141592653589793238462643383279502884197169399375105820974944";
        let ln2_60 = "0693147180559945309417232121458176568075500134360255254120680";
        for (ball, digits) in [(pi(60), pi60), (ln2(60), ln2_60)] {
            let truth = BigInt::parse_bytes(digits.as_bytes(), 10).unwrap();
            // `truth` is truncated, so the true value is in [truth, truth + 1].
            prop_assert_ok(&ball, &truth);
        }

        fn prop_assert_ok(ball: &Ball, truth: &BigInt) {
            assert!(&ball.mid - &ball.rad <= *truth && *truth < &ball.mid + &ball.rad);
            // About 2 ulps per series term (43 terms for atan(1/5) at 60 digits), times 16.
            assert!(ball.rad < BigInt::from(4000));
        }
    }

    #[test]
    fn exact_results_are_returned_without_series() {
        assert_eq!(bc_sin(&num("0"), 5).unwrap(), exact_result(0, 5));
        assert_eq!(bc_cos(&num("0.000"), 5).unwrap(), exact_result(1, 5));
        assert_eq!(bc_atan(&num("0"), 3).unwrap(), exact_result(0, 3));
        assert_eq!(bc_ln(&num("1.000"), 4).unwrap(), exact_result(0, 4));
        assert_eq!(bc_exp(&num("0"), 2).unwrap(), exact_result(1, 2));
        assert_eq!(
            bc_bessel(&num("0"), &num("0"), 2).unwrap(),
            exact_result(1, 2)
        );
        assert_eq!(
            bc_bessel(&num("3"), &num("0"), 2).unwrap(),
            exact_result(0, 2)
        );
    }

    #[test]
    fn results_are_truncated_toward_zero() {
        // Reference values truncated by hand from 30-digit expansions.
        let cases: [(&str, BCNum); 8] = [
            (".84147098480789650665", bc_sin(&num("1"), 20).unwrap()),
            ("-.84147098480789650665", bc_sin(&num("-1"), 20).unwrap()),
            (".54030230586813971740", bc_cos(&num("1"), 20).unwrap()),
            (".78539816339744830961", bc_atan(&num("1"), 20).unwrap()),
            ("-1.56079666010823138", bc_atan(&num("-100"), 17).unwrap()),
            ("-.69314718055994530941", bc_ln(&num("0.5"), 20).unwrap()),
            ("2.71828182845904523536", bc_exp(&num("1"), 20).unwrap()),
            (
                ".76519768655796655144",
                bc_bessel(&num("0"), &num("1"), 20).unwrap(),
            ),
        ];
        for (expected, actual) in cases {
            assert_eq!(actual.format_obase(10), expected);
        }
    }
}
