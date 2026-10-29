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
use crate::math::{BCNum, pow10, pow10_within};
#[cfg(verus_keep_ghost)]
use crate::real_arith::*;
#[cfg(verus_keep_ghost)]
use crate::spec_num;
#[cfg(verus_keep_ghost)]
use crate::spec_num::{lemma_pow10_add, lemma_pow10_pos, spec_pow_int, spec_tdiv, trunc_div};
#[cfg(verus_keep_ghost)]
use crate::trusted_bigint::big_view;
use crate::trusted_bigint::{
    big_abs, big_add, big_add_i64, big_clone, big_cmp, big_div_mod_floor, big_from_i64,
    big_from_u64, big_is_negative, big_is_zero, big_isqrt, big_mul, big_neg, big_shl, big_shr,
    big_sub, big_tdiv, big_tdiv_u64,
};
#[cfg(verus_keep_ghost)]
use crate::trusted_math::*;
use crate::verified_kernels::{
    MAX_VERIFIED_SCALE, verified_bessel_negative_order_parity, verified_decimal_scale_shift,
    verified_transcendental_guard_prec,
};
use alloc::string::ToString;
#[cfg(verus_keep_ghost)]
use bc_spec::power::lemma_pow_positive;
use core::cmp::Ordering;
use num_bigint::BigInt;
use num_integer::Integer;
use num_traits::{Signed, ToPrimitive, Zero};
use verus_builtin::{Ghost, real};
#[cfg(not(verus_keep_ghost))]
use verus_builtin_macros::verus;
#[cfg(verus_keep_ghost)]
use vstd::arithmetic::div_mod::lemma_div_denominator;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

/// Largest integer part of the argument of `e(x)` and of `x` in `j(n,x)` (`docs/COMPATIBILITY.md`
/// §2). e^x then has at most about 0.4343·x ≈ 8.7·10^8 integer digits, and the extra working
/// precision x/2 stays within `MAX_VERIFIED_SCALE`, the precondition of
/// `verified_transcendental_guard_prec`.
pub const EXP_ARG_MAX: u64 = 2_000_000_000;

verus! {

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
        forall|v: real|
            #![trigger trunc_r(v * (spec_num::pow10(scale as nat) as real))]
            (forall|p: usize, b: Ball| #[trigger] f.ensures((p,), Some(b)) ==> b.contains(v)) ==> (
            r is Ok ==> big_view(&r->Ok_0.coeff) == trunc_r(
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
                    assert forall|v: real|
                        #![trigger trunc_r(v * (spec_num::pow10(scale as nat) as real))]
                        (forall|p: usize, b2: Ball| #[trigger] f.ensures((p,), Some(b2))
                            ==> b2.contains(v)) implies big_view(&r.coeff) == trunc_r(
                        v * (spec_num::pow10(scale as nat) as real),
                    ) by {
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

/// The exact result `value` at `scale` digits.
fn exact_result(value: i64, scale: usize) -> BCNum {
    BCNum::new(BigInt::from(value) * pow10(scale), scale)
}

/// The integer part of |x|.
fn abs_int_part(x: &BCNum) -> BigInt {
    x.coeff.abs() / pow10(x.scale)
}

/// The number of decimal digits of the integer part of |x| (0 when |x| < 1).
fn int_digits(x: &BCNum) -> usize {
    let int_part = abs_int_part(x);
    if int_part.is_zero() {
        0
    } else {
        int_part.to_string().len()
    }
}

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

/// x − k·2π for the integer k nearest x / 2π (any integer k leaves sin and cos unchanged), at
/// precision `prec`. π carries as many extra digits as x has integer digits, so k·rad(2π) stays
/// within a few ulps at `prec`.
fn reduce_angle(x: &BCNum, prec: usize) -> Ball {
    let digits = int_digits(x);
    if digits == 0 {
        return Ball::from_bcnum(x, prec);
    }
    let work = prec + digits + 1;
    let xb = Ball::from_bcnum(x, work);
    let two_pi = pi(work).mul_int(&BigInt::from(2));
    let k: BigInt = Integer::div_floor(&(&xb.mid * 2 + &two_pi.mid), &(&two_pi.mid * 2));
    xb.sub(&two_pi.mul_int(&k)).reduce_prec(prec)
}

/// sin(r) (or cos(r)) by the Taylor series. |r| <= 4 after `reduce_angle`, so the terms
/// r^k/k! decrease once (k+1)(k+2) >= r².
fn sin_cos_ball(x: &BCNum, prec: usize, cos: bool) -> Option<Ball> {
    let r = reduce_angle(x, prec);
    let r_sq = r.mul(&r);
    let (first, odd) = if cos { (Ball::int(1, prec), 0) } else { (r, 1) };
    sum_series(first, &Series::SinCos { r_sq, odd }, Ghost::assume_new())
}

/// Math sine function.
pub fn bc_sin(x: &BCNum, global_scale: usize) -> Result<BCNum, RuntimeError> {
    if x.coeff.is_zero() {
        return Ok(exact_result(0, global_scale));
    }
    certify(x.scale, global_scale, 0, |p| sin_cos_ball(x, p, false))
}

/// Math cosine function.
pub fn bc_cos(x: &BCNum, global_scale: usize) -> Result<BCNum, RuntimeError> {
    if x.coeff.is_zero() {
        return Ok(exact_result(1, global_scale));
    }
    certify(x.scale, global_scale, 0, |p| sin_cos_ball(x, p, true))
}

// --- Arctangent ---

/// atan(x): for |x| > 1 use π/2 − atan(1/|x|); four half-angle steps y → y / (1 + √(1 + y²))
/// bring |y| below tan(π/64) < 0.05; then the alternating series y − y³/3 + …, times 16. atan is
/// odd, so the sign is applied last.
fn atan_ball(x: &BCNum, prec: usize) -> Option<Ball> {
    let ax = Ball::from_bcnum(x, prec).mul_int(&x.coeff.signum());
    let one = Ball::int(1, prec);
    let inverted = ax.mid > one.mid;
    let mut y = if inverted { one.div(&ax)? } else { ax };
    for _ in 0..4 {
        let root = one.add(&y.mul(&y)).sqrt()?;
        y = y.div(&one.add(&root))?;
    }
    let y_sq = y.mul(&y);
    let series = sum_series(y, &Series::Atan { y_sq }, Ghost::assume_new())?;
    let mut value = series.mul_int(&BigInt::from(16));
    if inverted {
        value = pi(prec).div_int(&BigInt::from(2)).sub(&value);
    }
    Some(value.mul_int(&x.coeff.signum()))
}

/// Math arctangent function.
pub fn bc_atan(x: &BCNum, global_scale: usize) -> Result<BCNum, RuntimeError> {
    if x.coeff.is_zero() {
        return Ok(exact_result(0, global_scale));
    }
    certify(x.scale, global_scale, 0, |p| atan_ball(x, p))
}

// --- Natural logarithm ---

/// ln(x) for x > 0: x = m·2^k with m in [0.7, 1.43); ln m = 2·artanh(y) with
/// y = (m − 1)/(m + 1), |y| < 0.18, so the terms y^(2j+1)/(2j+1) decrease and the positive tail
/// is at most 1/(1 − y²) < 2 times the first omitted term. ln x = ln m + k·ln 2, with ln 2
/// carrying as many extra digits as k has.
fn ln_ball(x: &BCNum, prec: usize) -> Option<Ball> {
    let xb = Ball::from_bcnum(x, prec);
    let one = Ball::int(1, prec);
    let low = BigInt::from(7) * pow10(prec) / 10;
    let high = BigInt::from(143) * pow10(prec) / 100;
    let bits = |v: &BigInt| i64::try_from(v.bits()).ok();
    let mut k = bits(&xb.mid)? - bits(&one.mid)?;
    let m = loop {
        let m = if k >= 0 {
            xb.shr(k.unsigned_abs())
        } else {
            xb.shl(k.unsigned_abs())
        };
        if m.mid < low {
            k -= 1;
        } else if m.mid >= high {
            k += 1;
        } else {
            break m;
        }
    };
    let y = m.sub(&one).div(&m.add(&one))?;
    let y_sq = y.mul(&y);
    let artanh = sum_series(y, &Series::Artanh { y_sq }, Ghost::assume_new())?;
    let k_big = BigInt::from(k);
    let extra = k_big.abs().to_string().len();
    let k_ln2 = ln2(prec + extra).mul_int(&k_big).reduce_prec(prec);
    Some(artanh.mul_int(&BigInt::from(2)).add(&k_ln2))
}

/// Math natural logarithm function.
pub fn bc_ln(x: &BCNum, global_scale: usize) -> Result<BCNum, RuntimeError> {
    if !x.coeff.is_positive() {
        // Like GNU's library, l(x) for x <= 0 returns (1 - 10^scale) at the caller's scale.
        let coeff = (BigInt::from(1) - pow10(global_scale)) * pow10(global_scale);
        return Ok(BCNum::new(coeff, global_scale));
    }
    if *x == exact_result(1, x.scale) {
        return Ok(exact_result(0, global_scale));
    }
    certify(x.scale, global_scale, 0, |p| ln_ball(x, p))
}

// --- Exponential ---

/// e^x = e^r·2^n with n = floor(x / ln 2) (any integer n is valid) and r = x − n·ln 2, so
/// |r| < 1. The Taylor terms r^k/k! satisfy |term k+1| <= |term k|/2 for k >= 1, so the tail is
/// at most twice the first omitted term.
fn exp_ball(x: &BCNum, prec: usize) -> Option<Ball> {
    // |x| <= 2.31·10^9, so |n| < 3.4·10^9 has at most 10 digits.
    let work = prec + 11;
    let l2 = ln2(work);
    let xb = Ball::from_bcnum(x, work);
    let n = xb.mid.div_floor(&l2.mid);
    let r = xb.sub(&l2.mul_int(&n)).reduce_prec(prec);
    let series = sum_series(Ball::int(1, prec), &Series::Exp { r }, Ghost::assume_new())?;
    let n = n.to_i64()?;
    Some(if n >= 0 {
        series.shl(n.unsigned_abs())
    } else {
        series.shr(n.unsigned_abs())
    })
}

/// Math exponential function.
///
/// For x <= -2.3026·(scale+1) the result is below 10^-(scale+1), because 2.3026 > ln 10, so
/// its truncation is exactly 0 and nothing is computed. An argument whose integer part exceeds
/// `EXP_ARG_MAX` is a `MathArgumentTooLarge` error.
pub fn bc_exp(x: &BCNum, global_scale: usize) -> Result<BCNum, RuntimeError> {
    if x.coeff.is_zero() {
        return Ok(exact_result(1, global_scale));
    }
    if x.coeff.is_negative() {
        // -x >= 2.3026·(scale+1)  <=>  -coeff·10^4 >= 23026·(scale+1)·10^x.scale
        let lhs = -&x.coeff * BigInt::from(10_000);
        let rhs = BigInt::from(23_026) * (BigInt::from(global_scale) + 1) * pow10(x.scale);
        if lhs >= rhs {
            return Ok(exact_result(0, global_scale));
        }
    }
    let int_part = abs_int_part(x)
        .to_u64()
        .filter(|&v| v <= EXP_ARG_MAX)
        .ok_or(RuntimeError::MathArgumentTooLarge)?;
    // For x >= 0, shifting by 2^n multiplies the radius by e^x, whose 0.4343·x integer digits
    // the guard must cover; x/2 digits do. For x < 0 the shift divides it instead. Both stay
    // within MAX_VERIFIED_SCALE because int_part <= EXP_ARG_MAX.
    let extra = if x.coeff.is_negative() {
        0
    } else {
        usize::try_from(int_part / 2).map_err(|_| RuntimeError::MathArgumentTooLarge)?
    };
    certify(x.scale, global_scale, extra, |p| exp_ball(x, p))
}

// --- Bessel functions ---

/// J_n(x) for n >= 0 by the power series Σ_m (−1)^m (x/2)^(2m+n) / (m!·(m+n)!). The terms
/// decrease once (m+1)(m+n+1) >= (x/2)², after which the tail is at most the first omitted term.
fn bessel_ball(n: u64, x: &BCNum, prec: usize) -> Option<Ball> {
    let half = Ball::from_bcnum(x, prec).div_int(&BigInt::from(2));
    let mut first = Ball::int(1, prec);
    for i in 1..=n {
        first = first.mul(&half).div_int(&BigInt::from(i));
    }
    let half_sq = half.mul(&half);
    sum_series(first, &Series::Bessel { half_sq, n }, Ghost::assume_new())
}

/// Bessel function of the first kind J_n(x), with `n` truncated to an integer.
///
/// For |n| >= 3·ceil(|x|) and |n| >= 4·(scale+1), |J_n(x)| <= (|x|/2)^|n| / |n|!
/// <= (e·|x| / (2·|n|))^|n| <= 2^-|n| < 10^-scale (using |n|! >= (|n|/e)^|n|), so the
/// truncated result is exactly 0. Any other order outside the range of `i64`, or an x whose
/// integer part exceeds `EXP_ARG_MAX`, cannot be computed and is a `MathArgumentTooLarge` error.
pub fn bc_bessel(n_num: &BCNum, x: &BCNum, global_scale: usize) -> Result<BCNum, RuntimeError> {
    let n = &n_num.coeff / pow10(n_num.scale);
    let n_abs_big = n.abs();
    let x_ceil = (x.coeff.abs() + pow10(x.scale) - 1) / pow10(x.scale);
    if n_abs_big >= BigInt::from(3) * &x_ceil
        && n_abs_big >= BigInt::from(4) * (BigInt::from(global_scale) + 1)
    {
        return Ok(exact_result(0, global_scale));
    }
    let n_i64 = n
        .to_i64()
        .filter(|&v| v > i64::MIN)
        .ok_or(RuntimeError::MathArgumentTooLarge)?;
    if x.coeff.is_zero() {
        return Ok(exact_result(i64::from(n_i64 == 0), global_scale));
    }
    let int_part = abs_int_part(x)
        .to_u64()
        .filter(|&v| v <= EXP_ARG_MAX)
        .ok_or(RuntimeError::MathArgumentTooLarge)?;
    let (n_abs, sign) = verified_bessel_negative_order_parity(n_i64);
    let n_abs = n_abs.unsigned_abs();
    // The terms grow to about e^|x| before they decrease, and their radii with them; |x|/2 extra
    // digits cover that (and stay within MAX_VERIFIED_SCALE because int_part <= EXP_ARG_MAX).
    let extra = usize::try_from(int_part / 2).map_err(|_| RuntimeError::MathArgumentTooLarge)?;
    certify(x.scale, global_scale, extra, |p| {
        bessel_ball(n_abs, x, p).map(|b| b.mul_int(&BigInt::from(sign)))
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::vec::Vec;
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
        v / pow10(k)
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
