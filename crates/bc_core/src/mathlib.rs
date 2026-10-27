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
use crate::math::{BCNum, pow10};
use crate::verified_kernels::{
    MAX_VERIFIED_SCALE, verified_bessel_negative_order_parity, verified_decimal_scale_shift,
    verified_transcendental_guard_prec,
};
use alloc::string::ToString;
use num_bigint::BigInt;
use num_integer::Integer;
use num_traits::{One, Signed, ToPrimitive, Zero};

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

/// `ceil(a / b)` for `a >= 0` and `b > 0`.
fn ceil_div(a: &BigInt, b: &BigInt) -> BigInt {
    (a + b - BigInt::one()) / b
}

impl Ball {
    fn exact(mid: BigInt, prec: usize) -> Self {
        Self {
            mid,
            rad: BigInt::zero(),
            prec,
        }
    }

    fn int(value: i64, prec: usize) -> Self {
        Self::exact(BigInt::from(value) * pow10(prec), prec)
    }

    /// `x` at precision `prec`: exact when `prec >= x.scale`, which every caller ensures.
    fn from_bcnum(x: &BCNum, prec: usize) -> Self {
        let (shift, multiply) = verified_decimal_scale_shift(x.scale, prec);
        if multiply {
            Self::exact(&x.coeff * pow10(shift), prec)
        } else {
            Self {
                mid: &x.coeff / pow10(shift),
                rad: BigInt::one(),
                prec,
            }
        }
    }

    /// An upper bound on |value|, in ulps.
    fn upper(&self) -> BigInt {
        self.mid.abs() + &self.rad
    }

    fn add(&self, other: &Self) -> Self {
        Self {
            mid: &self.mid + &other.mid,
            rad: &self.rad + &other.rad,
            prec: self.prec,
        }
    }

    fn sub(&self, other: &Self) -> Self {
        Self {
            mid: &self.mid - &other.mid,
            rad: &self.rad + &other.rad,
            prec: self.prec,
        }
    }

    fn neg(&self) -> Self {
        Self {
            mid: -&self.mid,
            rad: self.rad.clone(),
            prec: self.prec,
        }
    }

    /// Adds `extra` ulps of uncertainty (a bound on an omitted series tail).
    fn widen(mut self, extra: &BigInt) -> Self {
        self.rad += extra;
        self
    }

    /// Multiplication by an exact integer.
    fn mul_int(&self, k: &BigInt) -> Self {
        Self {
            mid: &self.mid * k,
            rad: &self.rad * k.abs(),
            prec: self.prec,
        }
    }

    /// Division by an exact integer `k > 0`: the quotient is truncated (< 1 ulp).
    fn div_int(&self, k: &BigInt) -> Self {
        Self {
            mid: &self.mid / k,
            rad: ceil_div(&self.rad, k) + 1,
            prec: self.prec,
        }
    }

    /// Multiplication by 2^n (exact).
    fn shl(&self, n: u64) -> Self {
        Self {
            mid: &self.mid << n,
            rad: &self.rad << n,
            prec: self.prec,
        }
    }

    /// Division by 2^n: the shift floors the midpoint (< 1 ulp).
    fn shr(&self, n: u64) -> Self {
        let divisor = BigInt::one() << n;
        Self {
            mid: &self.mid >> n,
            rad: ceil_div(&self.rad, &divisor) + 1,
            prec: self.prec,
        }
    }

    /// The same value at a precision `prec <= self.prec`.
    fn reduce_prec(&self, prec: usize) -> Self {
        let divisor = pow10(self.prec - prec);
        Self {
            mid: &self.mid / &divisor,
            rad: ceil_div(&self.rad, &divisor) + 1,
            prec,
        }
    }

    /// With A = a·10^p and B = b·10^p, |A·B − MA·MB| <= |MA|·RB + |MB|·RA + RA·RB; dividing by
    /// 10^p and truncating adds < 1 ulp.
    fn mul(&self, other: &Self) -> Self {
        let scale = pow10(self.prec);
        let spread =
            self.mid.abs() * &other.rad + other.mid.abs() * &self.rad + &self.rad * &other.rad;
        Self {
            mid: &self.mid * &other.mid / &scale,
            rad: ceil_div(&spread, &scale) + 1,
            prec: self.prec,
        }
    }

    /// |A/B − MA/MB| = |δA·MB − MA·δB| / (|B|·|MB|) <= (RA·|MB| + |MA|·RB) / ((|MB| − RB)·|MB|),
    /// scaled by 10^p, plus < 1 ulp for truncating. `None` if the divisor's ball contains 0.
    fn div(&self, other: &Self) -> Option<Self> {
        let mb = other.mid.abs();
        if mb <= other.rad {
            return None;
        }
        let scale = pow10(self.prec);
        let spread = (&self.rad * &mb + self.mid.abs() * &other.rad) * &scale;
        Some(Self {
            mid: &self.mid * &scale / &other.mid,
            rad: ceil_div(&spread, &((&mb - &other.rad) * &mb)) + 1,
            prec: self.prec,
        })
    }

    /// For A >= 0, |√(A·10^p) − √(MA·10^p)| = |δA|·10^p / (√(A·10^p) + √(MA·10^p)), which is at
    /// most RA·10^p / isqrt(MA·10^p); the floor of the integer square root adds < 1 ulp. `None`
    /// if that bound is unavailable (MA·10^p < 1) or the ball reaches below 0.
    fn sqrt(&self) -> Option<Self> {
        if self.mid < self.rad {
            return None;
        }
        let scale = pow10(self.prec);
        let root = (&self.mid * &scale).sqrt();
        if root.is_zero() {
            return None;
        }
        Some(Self {
            mid: root.clone(),
            rad: ceil_div(&(&self.rad * &scale), &root) + 1,
            prec: self.prec,
        })
    }
}

/// The truncation toward zero of every value in `b` at `scale <= b.prec` digits, as the
/// coefficient of a `BCNum` with that scale, or `None` if the values truncate differently.
///
/// With U = 10^(prec − scale) and mid = q·U + r (0 <= r < U), every value lies in
/// [q·U + r − rad, q·U + r + rad]. If rad < r and r + rad < U, that interval is inside the open
/// interval (q·U, (q+1)·U), so every value divided by U truncates toward zero to q when q >= 0
/// and to q + 1 when q < 0. A ball of radius 0 on a multiple of U is exact. The Verus lemma
/// `lemma_certified_truncation` (`verus_proofs.rs`) proves this decision over the integers.
fn certified_trunc(b: &Ball, scale: usize) -> Option<BigInt> {
    let unit = pow10(b.prec - scale);
    let (q, r) = b.mid.div_mod_floor(&unit);
    if b.rad.is_zero() && r.is_zero() {
        return Some(q);
    }
    if b.rad < r && &r + &b.rad < unit {
        Some(if q.is_negative() { q + 1 } else { q })
    } else {
        None
    }
}

/// Evaluates `f` at increasing working precisions until its ball certifies the truncation to
/// `scale` digits. The first precision comes from `verified_transcendental_guard_prec` (at least
/// `x_scale`, so the argument is exact); each retry doubles the guard digits.
fn certify(
    x_scale: usize,
    scale: usize,
    extra: usize,
    f: impl Fn(usize) -> Option<Ball>,
) -> Result<BCNum, RuntimeError> {
    let mut prec = verified_transcendental_guard_prec(x_scale, scale, extra);
    loop {
        if let Some(q) = f(prec).and_then(|b| certified_trunc(&b, scale)) {
            return Ok(BCNum::new(q, scale));
        }
        prec = prec
            .checked_add(prec - scale)
            .filter(|&p| p <= MAX_WORKING_PREC)
            .ok_or(RuntimeError::MathArgumentTooLarge)?;
    }
}

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
