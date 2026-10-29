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
    big_is_negative, big_is_zero, big_isqrt, big_mul, big_neg, big_shl, big_shr, big_sub, big_tdiv,
};
#[cfg(verus_keep_ghost)]
use crate::trusted_math::sqrt_r;
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
#[cfg(not(verus_keep_ghost))]
use verus_builtin_macros::verus;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

/// Largest integer part of the argument of `e(x)` and of `x` in `j(n,x)` (`docs/COMPATIBILITY.md`
/// §2). e^x then has at most about 0.4343·x ≈ 8.7·10^8 integer digits, and the extra working
/// precision x/2 stays within `MAX_VERIFIED_SCALE`, the precondition of
/// `verified_transcendental_guard_prec`.
pub const EXP_ARG_MAX: u64 = 2_000_000_000;

/// Series stop once the next term is bounded by this many ulps; its bound is then added to the
/// radius as the tail. Term radii settle below it (`docs/MATH_ERROR_BOUNDS.md` §2).
const TAIL_ULPS: u32 = 16;

verus! {

/// Largest working precision. [`certify`] gives up (with `MathArgumentTooLarge`) rather than
/// exceed it; every decimal shift then stays far below `u32::MAX`, as `pow10` requires.
const MAX_WORKING_PREC: usize = 3 * MAX_VERIFIED_SCALE;

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

// --- Constants ---

/// atan(1/n) (`alternating`) or artanh(1/n) for n >= 3, from exact integer terms.
///
/// `power` is floor(10^p / n^(2k+1)) exactly (nested floor divisions compose), so each term
/// floor(power / (2k+1)) is below the true term by less than 2 ulps. When `power` reaches 0 the
/// next true term is below 1 ulp, and the omitted tail is at most 9/8 of it. So the radius is
/// 2 ulps per term plus 2.
fn arc_inv(n: u32, alternating: bool, prec: usize) -> Ball {
    let n_sq = BigInt::from(n) * n;
    let mut power = pow10(prec) / n;
    let mut sum = BigInt::zero();
    let mut k: u64 = 0;
    while !power.is_zero() {
        let term = &power / (2 * k + 1);
        if alternating && k % 2 == 1 {
            sum -= term;
        } else {
            sum += term;
        }
        power /= &n_sq;
        k += 1;
    }
    Ball {
        mid: sum,
        rad: BigInt::from(2 * k + 2),
        prec,
    }
}

/// π by Machin's formula, π = 16·atan(1/5) − 4·atan(1/239).
fn pi(prec: usize) -> Ball {
    arc_inv(5, true, prec)
        .mul_int(&BigInt::from(16))
        .sub(&arc_inv(239, true, prec).mul_int(&BigInt::from(4)))
}

/// ln 2 = 2·artanh(1/3).
fn ln2(prec: usize) -> Ball {
    arc_inv(3, false, prec).mul_int(&BigInt::from(2))
}

// --- Series ---

/// Sums an alternating series whose terms decrease in magnitude from the stopping point on:
/// `first`, then `next(term, k)` for k = 1, 2, …. It stops at the first term bounded by
/// `TAIL_ULPS` for which `decreasing(k)` holds, and adds that term's bound as the tail (the tail
/// of such a series is at most its first omitted term). `tail_factor` multiplies the tail bound
/// for series that are not alternating but have a geometric tail.
fn sum_series(
    first: Ball,
    tail_factor: u32,
    mut next: impl FnMut(&Ball, u64) -> Ball,
    decreasing: impl Fn(u64) -> bool,
) -> Ball {
    let mut sum = first.clone();
    let mut term = first;
    let mut k: u64 = 0;
    loop {
        k += 1;
        term = next(&term, k);
        let bound = term.upper();
        if bound <= BigInt::from(TAIL_ULPS) && decreasing(k) {
            return sum.widen(&(bound * tail_factor));
        }
        sum = sum.add(&term);
    }
}

/// Whether `c·10^p >= sq.upper()`, i.e. the factor `c` dividing the next term exceeds the
/// largest value of the square `sq` (in real units), so the terms decrease from there on.
fn exceeds(c: &BigInt, sq: &Ball) -> bool {
    c * pow10(sq.prec) >= sq.upper()
}

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
fn sin_cos_ball(x: &BCNum, prec: usize, cos: bool) -> Ball {
    let r = reduce_angle(x, prec);
    let r_sq = r.mul(&r);
    let (first, offset) = if cos { (Ball::int(1, prec), 0) } else { (r, 1) };
    // Term k has exponent 2k + offset; term k = term k−1 · (−r²) / ((2k−1+offset)(2k+offset)).
    let factor = |k: u64| BigInt::from(2 * k - 1 + offset) * (2 * k + offset);
    sum_series(
        first,
        1,
        |term, k| term.mul(&r_sq).div_int(&factor(k)).neg(),
        |k| exceeds(&factor(k + 1), &r_sq),
    )
}

/// Math sine function.
pub fn bc_sin(x: &BCNum, global_scale: usize) -> Result<BCNum, RuntimeError> {
    if x.coeff.is_zero() {
        return Ok(exact_result(0, global_scale));
    }
    certify(x.scale, global_scale, 0, |p| {
        Some(sin_cos_ball(x, p, false))
    })
}

/// Math cosine function.
pub fn bc_cos(x: &BCNum, global_scale: usize) -> Result<BCNum, RuntimeError> {
    if x.coeff.is_zero() {
        return Ok(exact_result(1, global_scale));
    }
    certify(x.scale, global_scale, 0, |p| Some(sin_cos_ball(x, p, true)))
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
    // Term k is (−1)^k y^(2k+1) / (2k+1); `power` carries (−1)^k y^(2k+1).
    let mut power = y.clone();
    let series = sum_series(
        y,
        1,
        |_, k| {
            power = power.mul(&y_sq).neg();
            power.div_int(&BigInt::from(2 * k + 1))
        },
        |_| true,
    );
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
    let mut power = y.clone();
    let artanh = sum_series(
        y,
        2,
        |_, j| {
            power = power.mul(&y_sq);
            power.div_int(&BigInt::from(2 * j + 1))
        },
        |_| true,
    );
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
    let series = sum_series(
        Ball::int(1, prec),
        2,
        |term, k| term.mul(&r).div_int(&BigInt::from(k)),
        |k| k >= 1,
    );
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
fn bessel_ball(n: u64, x: &BCNum, prec: usize) -> Ball {
    let half = Ball::from_bcnum(x, prec).div_int(&BigInt::from(2));
    let mut first = Ball::int(1, prec);
    for i in 1..=n {
        first = first.mul(&half).div_int(&BigInt::from(i));
    }
    let half_sq = half.mul(&half);
    let factor = |m: u64| BigInt::from(m) * (BigInt::from(m) + n);
    sum_series(
        first,
        1,
        |term, m| term.mul(&half_sq).div_int(&factor(m)).neg(),
        |m| exceeds(&factor(m + 1), &half_sq),
    )
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
        Some(bessel_ball(n_abs, x, p).mul_int(&BigInt::from(sign)))
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
