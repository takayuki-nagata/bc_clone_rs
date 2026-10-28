// SPDX-License-Identifier: MIT

//! Arbitrary-precision decimal math library for bc.
//!
//! Provides the core `BCNum` type representing decimal numbers as integer
//! coefficients paired with a scale factor. Also implements transcendental
//! functions using series expansions.

use crate::error::RuntimeError;
#[cfg(verus_keep_ghost)]
use crate::spec_num;
#[cfg(verus_keep_ghost)]
use crate::spec_num::*;
#[cfg(verus_keep_ghost)]
use crate::trusted_bigint::big_view;
use crate::trusted_bigint::{
    big_abs, big_add, big_clone, big_cmp, big_decimal_digits, big_from_usize, big_is_negative,
    big_is_zero, big_isqrt, big_mul, big_mul_add_small, big_pow_usize, big_pow10, big_sub,
    big_tdiv, big_to_i64, big_zero,
};
use crate::verified_kernels::{BC_SCALE_MAX, MAX_VERIFIED_SCALE};
use crate::verified_kernels::{
    verified_add_sub_scales, verified_alphanumeric_char_val, verified_bcnum_length,
    verified_div_scale_and_shift, verified_mul_scale_and_shift, verified_pow_scale_and_shift,
    verified_relational_scale_shifts, verified_sqrt_scale_and_shift,
};
use alloc::vec::Vec;
#[cfg(verus_keep_ghost)]
use bc_spec::convert::{clamp_digits, lemma_horner_nonneg};
#[cfg(verus_keep_ghost)]
use bc_spec::power::lemma_pow_positive;
use core::cmp::Ordering;
use num_bigint::BigInt;
#[cfg(not(verus_keep_ghost))]
use verus_builtin_macros::verus;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

/// Returns 10^n.
///
/// Every `BCNum` scale is at most `BC_SCALE_MAX` (10^9), so the decimal shifts derived from
/// scales stay below `u32::MAX`. A larger `n` means that invariant was broken, which is a bug.
#[allow(
    clippy::expect_used,
    reason = "a shift above u32::MAX means the BC_SCALE_MAX invariant is broken (a bug), \
              which must not be computed with a truncated exponent"
)]
pub(crate) fn pow10(n: usize) -> BigInt {
    let exp = u32::try_from(n).expect("decimal shift exceeds u32: BCNum scale invariant violated");
    BigInt::from(10).pow(exp)
}

verus! {

/// `10^n` for a decimal shift derived from scales. Every scale is at most `BC_SCALE_MAX`, so the
/// shifts that verified code passes are at most 2·`BC_SCALE_MAX` < `u32::MAX`; Verus checks the
/// precondition at every call.
#[allow(
    clippy::cast_possible_truncation,
    reason = "the precondition n <= u32::MAX makes the cast lossless"
)]
pub(crate) fn pow10_within(n: usize) -> (r: BigInt)
    requires
        n <= u32::MAX,
    ensures
        big_view(&r) == spec_num::pow10(n as nat),
{
    big_pow10(n as u32)
}

/// The value of the digits `ds` in base `ibase` after the `ibase` rule (`clamp_digits`).
fn horner_digits(ds: &[u8], ibase: usize, multi: bool) -> (r: BigInt)
    requires
        2 <= ibase <= 16,
    ensures
        big_view(&r) == spec_horner(0, clamp_digits(ds@, ibase as u8, multi), ibase as int),
{
    let ghost cd = clamp_digits(ds@, ibase as u8, multi);
    proof {
        lemma_clamp_digits(ds@, ibase as u8, multi);
        assert(cd.skip(0) =~= cd);
    }
    let mut acc = big_zero();
    let mut i: usize = 0;
    while i < ds.len()
        invariant
            0 <= i <= ds.len(),
            2 <= ibase <= 16,
            cd == clamp_digits(ds@, ibase as u8, multi),
            cd.len() == ds.len(),
            forall|j: int| 0 <= j < ds.len() ==> #[trigger] cd[j] == (if multi && ds@[j] >= ibase as u8 { (ibase - 1) as u8 } else { ds@[j] }),
            spec_horner(big_view(&acc), cd.skip(i as int), ibase as int) == spec_horner(0, cd, ibase as int),
        decreases ds.len() - i,
    {
        let v = ds[i] as usize;
        let d = if multi && v >= ibase { ibase - 1 } else { v };
        proof {
            let rest = cd.skip(i as int);
            assert(rest[0] == cd[i as int]);
            assert(rest.drop_first() =~= cd.skip(i as int + 1));
            assert(d as u8 == cd[i as int]);
        }
        acc = big_mul_add_small(acc, ibase, d);
        i += 1;
    }
    proof {
        assert(cd.skip(i as int) =~= Seq::<u8>::empty());
    }
    acc
}

/// `clamp_digits` keeps the length and clamps each digit on its own.
proof fn lemma_clamp_digits(ds: Seq<u8>, ib: u8, multi: bool)
    requires
        ib >= 2,
    ensures
        clamp_digits(ds, ib, multi).len() == ds.len(),
        forall|j: int| 0 <= j < ds.len() ==> #[trigger] clamp_digits(ds, ib, multi)[j]
            == (if multi && ds[j] >= ib { (ib - 1) as u8 } else { ds[j] }),
    decreases ds.len(),
{
    if ds.len() > 0 {
        lemma_clamp_digits(ds.drop_first(), ib, multi);
        let d = if multi && ds[0] >= ib && ib >= 1 { (ib - 1) as u8 } else { ds[0] };
        let tail = clamp_digits(ds.drop_first(), ib, multi);
        assert(clamp_digits(ds, ib, multi) == seq![d].add(tail));
        assert forall|j: int| 0 <= j < ds.len() implies #[trigger] clamp_digits(ds, ib, multi)[j]
            == (if multi && ds[j] >= ib { (ib - 1) as u8 } else { ds[j] }) by {
            if j > 0 {
                assert(clamp_digits(ds, ib, multi)[j] == tail[j - 1]);
                assert(ds.drop_first()[j - 1] == ds[j]);
            }
        }
    }
}

/// A nonzero base has a nonzero power.
proof fn lemma_pow_int_nonzero(c: int, n: nat)
    requires
        c != 0,
    ensures
        spec_pow_int(c, n) != 0,
    decreases n,
{
    if n > 0 {
        lemma_pow_int_nonzero(c, (n - 1) as nat);
        assert(c * spec_pow_int(c, (n - 1) as nat) != 0) by (nonlinear_arith)
            requires
                c != 0,
                spec_pow_int(c, (n - 1) as nat) != 0;
    }
}

/// A positive power of zero is zero.
proof fn lemma_pow_int_zero_base(n: nat)
    requires
        n >= 1,
    ensures
        spec_pow_int(0, n) == 0,
{
    assert(spec_pow_int(0, n) == 0 * spec_pow_int(0, (n - 1) as nat));
}

/// Arbitrary-precision decimal number representation for bc.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BCNum {
    pub coeff: BigInt,
    pub scale: usize,
}

impl BCNum {
    /// The value in the L0 model: `coeff × 10^-scale`.
    pub open spec fn val(&self) -> SpecBCNum {
        SpecBCNum { coeff: big_view(&self.coeff), scale: self.scale as nat }
    }

    /// Creates a new BCNum.
    pub fn new(coeff: BigInt, scale: usize) -> (r: Self)
        ensures
            r.coeff == coeff,
            r.scale == scale,
    {
        Self { coeff, scale }
    }

    /// Creates a BCNum representing 0 with scale 0.
    pub fn zero() -> (r: Self)
        ensures
            r.val() == (SpecBCNum { coeff: 0, scale: 0 }),
    {
        Self { coeff: big_zero(), scale: 0 }
    }

    /// The value of a constant from its digit values: integer digits `ds` and fraction digits
    /// `fs`, most significant first, under `ibase`. As in GNU bc, a single-digit number keeps
    /// its face value, while in a multi-digit number a digit >= ibase counts as ibase - 1
    /// (`docs/COMPATIBILITY.md` §3.3). The fraction is converted exactly and truncated to
    /// `len(fs)` decimal digits.
    pub fn from_digit_values(ds: &[u8], fs: &[u8], ibase: usize) -> (r: Self)
        requires
            2 <= ibase <= 16,
            fs.len() <= BC_SCALE_MAX,
        ensures
            ({
                let multi = ds.len() + fs.len() > 1;
                let ib = ibase as u8;
                let iv = spec_horner(0, clamp_digits(ds@, ib, multi), ibase as int);
                let fv = spec_horner(0, clamp_digits(fs@, ib, multi), ibase as int);
                let f = fs.len();
                let den = spec_pow_int(ibase as int, f as nat);
                &&& r.scale == f
                &&& r.val().coeff == if f == 0 { iv } else { (iv * den + fv) * spec_num::pow10(f as nat) / den }
            }),
    {
        let multi = ds.len() > 1 || fs.len() > 1 || (ds.len() == 1 && fs.len() == 1);
        let int_val = horner_digits(ds, ibase, multi);
        if fs.is_empty() {
            return Self::new(int_val, 0);
        }
        let frac_numerator = horner_digits(fs, ibase, multi);
        let frac_denominator = big_pow_usize(ibase, fs.len());
        let num = big_mul(
            &big_add(&big_mul(&int_val, &frac_denominator), &frac_numerator),
            &pow10_within(fs.len()),
        );
        proof {
            lemma_pow_positive(ibase as int, fs.len() as nat);
            lemma_pow10_pos(fs.len() as nat);
            let ib = ibase as u8;
            lemma_horner_nonneg(0, clamp_digits(ds@, ib, multi), ibase as int);
            lemma_horner_nonneg(0, clamp_digits(fs@, ib, multi), ibase as int);
            let (iv, fv, den, p) = (big_view(&int_val), big_view(&frac_numerator), big_view(&frac_denominator),
                spec_num::pow10(fs.len() as nat));
            assert((iv * den + fv) * p >= 0) by (nonlinear_arith)
                requires
                    iv >= 0,
                    fv >= 0,
                    den >= 1,
                    p >= 1;
        }
        Self::new(big_tdiv(&num, &frac_denominator), fs.len())
    }

    /// Returns true if the number is mathematically zero.
    pub fn is_zero(&self) -> (r: bool)
        ensures
            r == (self.val().coeff == 0),
    {
        big_is_zero(&self.coeff)
    }

    /// Adds two BCNum values.
    pub fn add(&self, other: &Self) -> (r: Self)
        requires
            self.scale <= BC_SCALE_MAX,
            other.scale <= BC_SCALE_MAX,
        ensures
            r.val() == self.val().spec_add(other.val()),
            r.scale <= BC_SCALE_MAX,
    {
        let (sr, shift_a, shift_b) = verified_add_sub_scales(self.scale, other.scale);
        let coeff_a = big_mul(&self.coeff, &pow10_within(shift_a));
        let coeff_b = big_mul(&other.coeff, &pow10_within(shift_b));
        Self::new(big_add(&coeff_a, &coeff_b), sr)
    }

    /// Subtracts other from self.
    pub fn sub(&self, other: &Self) -> (r: Self)
        requires
            self.scale <= BC_SCALE_MAX,
            other.scale <= BC_SCALE_MAX,
        ensures
            r.val() == self.val().spec_sub(other.val()),
            r.scale <= BC_SCALE_MAX,
    {
        let (sr, shift_a, shift_b) = verified_add_sub_scales(self.scale, other.scale);
        let coeff_a = big_mul(&self.coeff, &pow10_within(shift_a));
        let coeff_b = big_mul(&other.coeff, &pow10_within(shift_b));
        Self::new(big_sub(&coeff_a, &coeff_b), sr)
    }

    /// Multiplies two BCNum values under scale.
    pub fn mul(&self, other: &Self, global_scale: usize) -> (r: Self)
        requires
            self.scale <= BC_SCALE_MAX,
            other.scale <= BC_SCALE_MAX,
            global_scale <= BC_SCALE_MAX,
        ensures
            r.val() == spec_mul(self.val(), other.val(), global_scale as nat),
            r.scale <= BC_SCALE_MAX,
    {
        let (sr, diff) = verified_mul_scale_and_shift(self.scale, other.scale, global_scale);
        proof {
            lemma_pow10_pos(diff as nat);
        }
        let coeff = big_tdiv(&big_mul(&self.coeff, &other.coeff), &pow10_within(diff));
        Self::new(coeff, sr)
    }

    /// Divides self by other under scale, returning Err on division by zero.
    #[allow(
        clippy::cast_possible_truncation,
        clippy::cast_sign_loss,
        reason = "Verus proves 0 <= |shift| <= 2·BC_SCALE_MAX < 2^31 for both casts"
    )]
    pub fn try_div(&self, other: &Self, global_scale: usize) -> (r: Result<Self, RuntimeError>)
        requires
            self.scale <= BC_SCALE_MAX,
            other.scale <= BC_SCALE_MAX,
            global_scale <= BC_SCALE_MAX,
        ensures
            match r {
                Ok(q) => other.val().coeff != 0 && q.val() == spec_div(self.val(), other.val(), global_scale as nat)
                    && q.scale == global_scale,
                Err(e) => other.val().coeff == 0 && e == RuntimeError::DivideByZero,
            },
    {
        if big_is_zero(&other.coeff) {
            return Err(RuntimeError::DivideByZero);
        }
        let (sr, shift) = verified_div_scale_and_shift(self.scale, other.scale, global_scale);
        let coeff = if shift >= 0 {
            proof {
                lemma_pow10_pos(shift as nat);
            }
            let num = big_mul(&self.coeff, &pow10_within(shift as usize));
            big_tdiv(&num, &other.coeff)
        } else {
            proof {
                lemma_pow10_pos((-shift) as nat);
                assert(big_view(&other.coeff) * spec_num::pow10((-shift) as nat) != 0) by (nonlinear_arith)
                    requires
                        big_view(&other.coeff) != 0,
                        spec_num::pow10((-shift) as nat) >= 1;
            }
            let den = big_mul(&other.coeff, &pow10_within((-shift) as usize));
            big_tdiv(&self.coeff, &den)
        };
        Ok(Self::new(coeff, sr))
    }

    /// Computes self % other under scale, returning Err on division by zero.
    pub fn try_mod_op(&self, other: &Self, global_scale: usize) -> (r: Result<Self, RuntimeError>)
        requires
            self.scale <= BC_SCALE_MAX,
            other.scale <= BC_SCALE_MAX,
            global_scale <= BC_SCALE_MAX,
        ensures
            match r {
                Ok(m) => other.val().coeff != 0 && global_scale + other.scale <= BC_SCALE_MAX
                    && m.val() == spec_mod(self.val(), other.val(), global_scale as nat)
                    && m.scale <= BC_SCALE_MAX,
                Err(e) => (other.val().coeff == 0 && e == RuntimeError::ModuloByZero)
                    || (other.val().coeff != 0 && global_scale + other.scale > BC_SCALE_MAX
                        && e == RuntimeError::ScaleTooLarge),
            },
    {
        if big_is_zero(&other.coeff) {
            return Err(RuntimeError::ModuloByZero);
        }
        // The result scale is max(scale + scale(b), scale(a)).
        if global_scale + other.scale > BC_SCALE_MAX {
            return Err(RuntimeError::ScaleTooLarge);
        }
        let q = self.try_div(other, global_scale)?;
        let prod_coeff = big_mul(&q.coeff, &other.coeff);
        let prod_scale = q.scale + other.scale;
        let prod = Self::new(prod_coeff, prod_scale);
        Ok(self.sub(&prod))
    }
    /// Computes the square root of self under scale, returning Err on negative input.
    pub fn try_sqrt(&self, global_scale: usize) -> (r: Result<Self, RuntimeError>)
        requires
            self.scale <= BC_SCALE_MAX,
            global_scale <= BC_SCALE_MAX,
        ensures
            match r {
                Ok(q) => self.val().coeff >= 0
                    && q.scale == (if self.scale >= global_scale { self.scale } else { global_scale })
                    && is_isqrt(self.val().coeff * spec_num::pow10((2 * q.scale - self.scale) as nat), q.val().coeff),
                Err(e) => self.val().coeff < 0 && e == RuntimeError::NegativeSqrt,
            },
    {
        if big_is_negative(&self.coeff) {
            return Err(RuntimeError::NegativeSqrt);
        }
        let (sr, shift) = verified_sqrt_scale_and_shift(self.scale, global_scale);
        let num = big_mul(&self.coeff, &pow10_within(shift));
        proof {
            lemma_pow10_pos(shift as nat);
            assert(big_view(&num) >= 0) by (nonlinear_arith)
                requires
                    big_view(&num) == big_view(&self.coeff) * spec_num::pow10(shift as nat),
                    big_view(&self.coeff) >= 0,
                    spec_num::pow10(shift as nat) >= 1;
        }
        Ok(Self::new(big_isqrt(&num), sr))
    }

    /// Computes the total number of significant decimal digits.
    pub fn length(&self) -> (r: Self)
        requires
            self.scale <= BC_SCALE_MAX,
        ensures
            r.scale == 0,
            ({
                let c = self.val().coeff;
                let ip = (if c >= 0 { c } else { -c }) / spec_num::pow10(self.scale as nat);
                &&& ip == 0 ==> r.val().coeff == (if self.scale >= 1 { self.scale as int } else { 1 })
                &&& ip > 0 ==> r.val().coeff > self.scale
                    && is_digit_count(ip, (r.val().coeff - self.scale) as nat)
            }),
    {
        proof {
            lemma_pow10_pos(self.scale as nat);
        }
        let int_part = big_tdiv(&big_abs(&self.coeff), &pow10_within(self.scale));
        if big_is_zero(&int_part) {
            let val = verified_bcnum_length(true, 0, self.scale);
            Self::new(big_from_usize(val), 0)
        } else {
            let digits = big_decimal_digits(&int_part);
            if digits <= MAX_VERIFIED_SCALE {
                let val = verified_bcnum_length(false, digits, self.scale);
                Self::new(big_from_usize(val), 0)
            } else {
                // More integer digits than the kernel's bound: add them as integers.
                Self::new(big_add(&big_from_usize(digits), &big_from_usize(self.scale)), 0)
            }
        }
    }

    /// Raises self to the power of the integer part of other under scale.
    ///
    /// Returns Err when a negative power of zero divides by zero, when the exponent does not
    /// fit in an `i64`, or when the exact intermediate scale `scale(self) * |exponent|` would
    /// exceed `BC_SCALE_MAX` (`docs/COMPATIBILITY.md` §2).
    #[allow(
        clippy::cast_sign_loss,
        clippy::cast_possible_truncation,
        reason = "Verus proves each cast lossless: a non-negative i64 to u64, and an exact scale \
                  of at most BC_SCALE_MAX to usize"
    )]
    pub fn try_pow(&self, other: &Self, global_scale: usize) -> (r: Result<Self, RuntimeError>)
        requires
            self.scale <= BC_SCALE_MAX,
            other.scale <= BC_SCALE_MAX,
            global_scale <= BC_SCALE_MAX,
        ensures
            ({
                let e = spec_int_part(other.val());
                let n = if e >= 0 { e } else { -e };
                let in_i64 = i64::MIN <= e <= i64::MAX;
                match r {
                    Err(RuntimeError::ExponentTooLarge) => !in_i64,
                    Err(RuntimeError::ScaleTooLarge) => in_i64 && self.scale * n > BC_SCALE_MAX,
                    Err(RuntimeError::NegativePowerOfZero) => in_i64 && self.scale * n <= BC_SCALE_MAX
                        && e < 0 && self.val().coeff == 0,
                    Ok(q) => in_i64 && self.scale * n <= BC_SCALE_MAX && !(e < 0 && self.val().coeff == 0)
                        && q.val() == spec_pow(self.val(), other.val(), global_scale as nat),
                    _ => false,
                }
            }),
    {
        proof {
            lemma_pow10_pos(other.scale as nat);
        }
        let b_val = big_tdiv(&other.coeff, &pow10_within(other.scale));
        let b_i64 = match big_to_i64(&b_val) {
            Some(x) => x,
            None => return Err(RuntimeError::ExponentTooLarge),
        };
        // |b|, without overflow for i64::MIN.
        let b_abs: u64 = if b_i64 >= 0 { b_i64 as u64 } else { (-(b_i64 + 1)) as u64 + 1 };
        // The exact scale of the power, computed in u64 so that it does not depend on the width
        // of usize: a scale of 0 gives 0 for any exponent.
        let exact_scale: usize = if self.scale == 0 {
            0
        } else if b_abs > BC_SCALE_MAX as u64 {
            proof {
                assert(self.scale * b_abs > BC_SCALE_MAX) by (nonlinear_arith)
                    requires
                        self.scale >= 1,
                        b_abs > BC_SCALE_MAX;
            }
            return Err(RuntimeError::ScaleTooLarge);
        } else {
            proof {
                assert(self.scale * b_abs <= BC_SCALE_MAX * BC_SCALE_MAX) by (nonlinear_arith)
                    requires
                        self.scale <= BC_SCALE_MAX,
                        b_abs <= BC_SCALE_MAX;
            }
            let s = (self.scale as u64) * b_abs;
            if s > BC_SCALE_MAX as u64 {
                return Err(RuntimeError::ScaleTooLarge);
            }
            s as usize
        };
        proof {
            if self.scale == 0 {
                assert(self.scale * b_abs == 0) by (nonlinear_arith)
                    requires
                        self.scale == 0;
            }
        }

        // Exponentiation by squaring on the coefficient; the scale of the exact power is
        // `exact_scale`. The base is only squared while bits remain, so it never exceeds
        // the size of the result.
        let ghost c = big_view(&self.coeff);
        let mut res_coeff = big_from_usize(1);
        let mut base_coeff = big_clone(&self.coeff);
        let mut remaining = b_abs;
        while remaining > 0
            invariant
                big_view(&res_coeff) * spec_pow_int(big_view(&base_coeff), remaining as nat)
                    == spec_pow_int(c, b_abs as nat),
            decreases remaining,
        {
            let ghost (r0, b0, k0) = (big_view(&res_coeff), big_view(&base_coeff), remaining as nat);
            proof {
                lemma_pow_int_squaring(b0, k0);
            }
            if remaining % 2 == 1 {
                res_coeff = big_mul(&res_coeff, &base_coeff);
                proof {
                    assert(r0 * (b0 * spec_pow_int(b0 * b0, k0 / 2)) == (r0 * b0) * spec_pow_int(b0 * b0, k0 / 2))
                        by (nonlinear_arith);
                }
            }
            remaining /= 2;
            if remaining > 0 {
                base_coeff = big_mul(&base_coeff, &base_coeff);
            } else {
                proof {
                    assert(spec_pow_int(b0 * b0, 0) == 1 && spec_pow_int(b0, 0) == 1);
                }
            }
        }
        proof {
            assert(spec_pow_int(big_view(&base_coeff), 0) == 1);
        }

        if !big_is_negative(&b_val) {
            let (sr, diff) = verified_pow_scale_and_shift(exact_scale, self.scale, global_scale);
            proof {
                lemma_pow10_pos(diff as nat);
            }
            Ok(Self::new(big_tdiv(&res_coeff, &pow10_within(diff)), sr))
        } else if big_is_zero(&res_coeff) {
            proof {
                if c != 0 {
                    lemma_pow_int_nonzero(c, b_abs as nat);
                }
            }
            Err(RuntimeError::NegativePowerOfZero)
        } else {
            proof {
                if c == 0 {
                    lemma_pow_int_zero_base(b_abs as nat);
                }
            }
            Self::new(big_from_usize(1), 0).try_div(&Self::new(res_coeff, exact_scale), global_scale)
        }
    }

    /// Compares the values of self and other (as `==`, `<`, … do).
    pub fn cmp_val(&self, other: &Self) -> (r: Ordering)
        requires
            self.scale <= BC_SCALE_MAX,
            other.scale <= BC_SCALE_MAX,
        ensures
            (r == Ordering::Less) == spec_bcnum_lt(self.val(), other.val()),
            (r == Ordering::Equal) == spec_bcnum_eq(self.val(), other.val()),
            (r == Ordering::Greater) == spec_bcnum_gt(self.val(), other.val()),
    {
        let (shift_l, shift_r) = verified_relational_scale_shifts(self.scale, other.scale);
        proof {
            assert(spec_num::pow10(0) == 1);
        }
        let coeff_l = big_mul(&self.coeff, &pow10_within(shift_l));
        let coeff_r = big_mul(&other.coeff, &pow10_within(shift_r));
        proof {
            let (a, b) = (self.val(), other.val());
            if self.scale >= other.scale {
                assert(shift_l == 0);
                assert(big_view(&coeff_l) == a.coeff);
                assert(spec_rel_norm_lhs(a, b) == a.coeff);
                if self.scale == other.scale {
                    assert(big_view(&coeff_r) == b.coeff);
                    assert(spec_rel_norm_rhs(a, b) == b.coeff);
                } else {
                    assert(spec_rel_norm_rhs(a, b) == big_view(&coeff_r));
                }
            } else {
                assert(shift_r == 0);
                assert(big_view(&coeff_r) == b.coeff);
                assert(spec_rel_norm_rhs(a, b) == b.coeff);
                assert(spec_rel_norm_lhs(a, b) == big_view(&coeff_l));
            }
        }
        big_cmp(&coeff_l, &coeff_r)
    }

    /// Returns the scale of self.
    pub fn scale_func(&self) -> (r: Self)
        ensures
            r.val() == (SpecBCNum { coeff: self.scale as int, scale: 0 }),
    {
        Self::new(big_from_usize(self.scale), 0)
    }
}

} // verus!

impl BCNum {
    /// The digit values of a numeric constant: its integer digits and its fraction digits, most
    /// significant first, without backslash-newlines and the radix point. Not verified yet: the
    /// refinement proof relates it to the specification's literal digits.
    #[allow(
        clippy::cast_possible_truncation,
        reason = "verified_alphanumeric_char_val returns at most 35"
    )]
    fn digit_values(num_str: &str) -> (Vec<u8>, Vec<u8>) {
        let num_str = num_str.replace("\\\n", "");
        let (int_part, frac_part) = match num_str.find('.') {
            Some(pos) => (&num_str[..pos], &num_str[pos + 1..]),
            None => (num_str.as_str(), ""),
        };
        let value = |b: u8| verified_alphanumeric_char_val(b) as u8;
        (
            int_part.bytes().map(value).collect(),
            frac_part.bytes().map(value).collect(),
        )
    }

    /// Parses a numeric constant string under `ibase` (2 to 16) into a BCNum. A constant with
    /// more than `BC_SCALE_MAX` fraction digits is `ScaleTooLarge`, rejected before any
    /// arithmetic, which keeps the scale invariant.
    pub fn try_from_string(num_str: &str, ibase: usize) -> Result<Self, RuntimeError> {
        let (ds, fs) = Self::digit_values(num_str);
        if fs.len() > BC_SCALE_MAX {
            return Err(RuntimeError::ScaleTooLarge);
        }
        Ok(Self::from_digit_values(&ds, &fs, ibase))
    }

    /// Parses a numeric constant string under `ibase` into a BCNum.
    #[cfg(test)]
    pub fn from_string(num_str: &str, ibase: usize) -> Self {
        Self::try_from_string(num_str, ibase).unwrap_or_else(|msg| panic!("{}", msg))
    }

    /// Divides self by other under scale.
    #[cfg(test)]
    pub fn div(&self, other: &Self, global_scale: usize) -> Self {
        self.try_div(other, global_scale)
            .unwrap_or_else(|msg| panic!("{}", msg))
    }

    /// Computes self % other under scale.
    #[cfg(test)]
    pub fn mod_op(&self, other: &Self, global_scale: usize) -> Self {
        self.try_mod_op(other, global_scale)
            .unwrap_or_else(|msg| panic!("{}", msg))
    }

    /// Raises self to the power of other under scale.
    #[cfg(test)]
    pub fn pow(&self, other: &Self, global_scale: usize) -> Self {
        self.try_pow(other, global_scale)
            .unwrap_or_else(|msg| panic!("{}", msg))
    }

    /// Computes the square root of self under scale.
    #[cfg(test)]
    pub fn sqrt(&self, global_scale: usize) -> Self {
        self.try_sqrt(global_scale)
            .unwrap_or_else(|msg| panic!("{}", msg))
    }
}

// The `-l` math library lives in `mathlib.rs`.
#[cfg(not(verus_keep_ghost))]
pub use crate::mathlib::{EXP_ARG_MAX, bc_atan, bc_bessel, bc_cos, bc_exp, bc_ln, bc_sin};

#[cfg(test)]
mod tests {
    use super::*;
    use num_traits::Zero;

    // The fallible math functions, unwrapped for tests whose arguments are in range.
    fn bc_sin(x: &BCNum, scale: usize) -> BCNum {
        super::bc_sin(x, scale).unwrap()
    }

    fn bc_cos(x: &BCNum, scale: usize) -> BCNum {
        super::bc_cos(x, scale).unwrap()
    }

    fn bc_atan(x: &BCNum, scale: usize) -> BCNum {
        super::bc_atan(x, scale).unwrap()
    }

    fn bc_ln(x: &BCNum, scale: usize) -> BCNum {
        super::bc_ln(x, scale).unwrap()
    }

    fn bc_exp(x: &BCNum, scale: usize) -> BCNum {
        super::bc_exp(x, scale).unwrap()
    }

    fn bc_bessel(n: &BCNum, x: &BCNum, scale: usize) -> BCNum {
        super::bc_bessel(n, x, scale).unwrap()
    }

    #[test]
    fn test_from_string_basic() {
        let num1 = BCNum::from_string("12.34", 10);
        assert_eq!(num1.coeff, BigInt::from(1234));
        assert_eq!(num1.scale, 2);

        let num2 = BCNum::from_string("10", 8);
        assert_eq!(num2.coeff, BigInt::from(8));
        assert_eq!(num2.scale, 0);

        let num3 = BCNum::from_string("FF", 16);
        assert_eq!(num3.coeff, BigInt::from(255));
        assert_eq!(num3.scale, 0);
    }

    #[test]
    fn test_basic_arithmetic() {
        let a = BCNum::from_string("1.25", 10);
        let b = BCNum::from_string("2.5", 10);

        let sum = a.add(&b);
        assert_eq!(sum.coeff, BigInt::from(375));
        assert_eq!(sum.scale, 2);

        let diff = a.sub(&b);
        assert_eq!(diff.coeff, BigInt::from(-125));
        assert_eq!(diff.scale, 2);

        let diff_rev = b.sub(&a);
        assert_eq!(diff_rev.coeff, BigInt::from(125));
        assert_eq!(diff_rev.scale, 2);

        assert_eq!(
            BCNum::from_string("123.45", 10).length().coeff,
            BigInt::from(5)
        );
        assert_eq!(
            BCNum::from_string("0.05", 10).length().coeff,
            BigInt::from(2)
        );

        let prod = a.mul(&b, 4);
        assert_eq!(prod.coeff, BigInt::from(3125));
        assert_eq!(prod.scale, 3); // min(2+1, max(4, 2, 1)) -> min(3, 4) = 3

        let quotient = b.div(&a, 2);
        assert_eq!(quotient.coeff, BigInt::from(200));
        assert_eq!(quotient.scale, 2);
    }

    #[test]
    fn test_power_and_sqrt() {
        let a = BCNum::from_string("2.5", 10);
        let exp = BCNum::from_string("2", 10);
        let p = a.pow(&exp, 5);
        assert_eq!(p.coeff, BigInt::from(625));
        assert_eq!(p.scale, 2);

        let p_zero = a.pow(&BCNum::zero(), 5);
        assert_eq!(p_zero.coeff, BigInt::from(1));
        assert_eq!(p_zero.scale, 0);

        let p_trunc = BCNum::from_string("1.25", 10).pow(&exp, 1);
        assert_eq!(p_trunc.coeff, BigInt::from(156));
        assert_eq!(p_trunc.scale, 2);

        let neg_exp = BCNum::new(BigInt::from(-2), 0);
        let p_neg = a.pow(&neg_exp, 4);
        assert_eq!(p_neg.coeff, BigInt::from(1600));
        assert_eq!(p_neg.scale, 4); // 1 / 6.25 = 0.1600

        // Exponents beyond u32 with a scale-0 base (the exact scale is computed in u64).
        let huge = BCNum::new(BigInt::from(5_000_000_000u64), 0);
        assert_eq!(
            BCNum::new(BigInt::from(1), 0).pow(&huge, 0).coeff,
            BigInt::from(1)
        );
        assert_eq!(BCNum::zero().pow(&huge, 0).coeff, BigInt::from(0));
        assert_eq!(
            BCNum::from_string("0.5", 10).try_pow(&huge, 0),
            Err(RuntimeError::ScaleTooLarge)
        );

        let val_4 = BCNum::from_string("4", 10);
        let root = val_4.sqrt(2);
        assert_eq!(root.coeff, BigInt::from(200));
        assert_eq!(root.scale, 2);
    }

    #[test]
    fn test_format_obase() {
        let a = BCNum::from_string("255", 10);
        assert_eq!(a.format_obase(16), "FF");
        assert_eq!(a.format_obase(10), "255");
        assert_eq!(a.format_obase(256), " 255");

        let b = BCNum::from_string("0.25", 10);
        assert_eq!(b.format_obase(16), ".40");
    }

    #[test]
    fn test_transcendentals() {
        let zero = BCNum::from_string("0", 10);
        let sin_zero = bc_sin(&zero, 5);
        assert_eq!(sin_zero.coeff, BigInt::zero());

        let cos_zero = bc_cos(&zero, 5);
        assert_eq!(cos_zero.coeff, BigInt::from(100000));

        let one = BCNum::from_string("1", 10);
        let ln_one = bc_ln(&one, 5);
        assert_eq!(ln_one.coeff, BigInt::zero());

        let exp_zero = bc_exp(&zero, 5);
        assert_eq!(exp_zero.coeff, BigInt::from(100000));
    }

    #[test]
    fn test_math_uncovered_lines() {
        // 1. Invalid char in unsigned parsing (line 48)
        let num1 = BCNum::from_string("_", 10);
        assert_eq!(num1.coeff, BigInt::zero());

        // 2. Power with fractional exponent (line 145)
        let num_2 = BCNum::from_string("2", 10);
        let num_1_5 = BCNum::from_string("1.5", 10);
        let pow_res = num_2.pow(&num_1_5, 2);
        assert_eq!(pow_res.coeff, BigInt::from(2)); // 2^1.5 truncated to 2^1 = 2 under scale 0

        // 5. atan_tiny precision break (line 484)
        let _ = bc_atan(&BCNum::new(BigInt::from(5), 1), 2);

        // 6. decimal_sin / decimal_cos / atan_machin / compute_ln2 precision breaks (lines 539, 591, 652, 689)
        let _ = bc_sin(&BCNum::new(BigInt::from(10), 0), 2);
        let _ = bc_cos(&BCNum::new(BigInt::from(10), 0), 2);
        let _ = bc_atan(&BCNum::new(BigInt::from(1), 0), 2);
        let _ = bc_ln(&BCNum::new(BigInt::from(2), 0), 2);

        // 7. decimal_ln scale down / scale up / k < 0 (lines 713-716, 724-726, 727-730, 747)
        let _ = bc_ln(&BCNum::new(BigInt::from(15), 1), 5); // x = 1.5
        let _ = bc_ln(&BCNum::new(BigInt::from(5), 1), 5); // x = 0.5
        let _ = bc_ln(&BCNum::new(BigInt::from(1), 2), 5); // x = 0.01 (k < 0)

        // 8. decimal_exp precision break and overflow (line 796, 811)
        let _ = bc_exp(&BCNum::new(BigInt::from(2), 0), 2);
        let _ = bc_exp(&BCNum::new(BigInt::from(100i64), 0), 2);

        // 9. bc_bessel fractional order (lines 875-876)
        let _ = bc_bessel(
            &BCNum::new(BigInt::from(15), 1),
            &BCNum::new(BigInt::from(2), 0),
            2,
        );

        // 10. bc_bessel zero x, non-zero order (line 888)
        let j_res = bc_bessel(
            &BCNum::new(BigInt::from(2), 0),
            &BCNum::new(BigInt::from(0), 0),
            2,
        );
        assert_eq!(j_res.coeff, BigInt::zero());

        // 11. bc_bessel precision break
        let _ = bc_bessel(
            &BCNum::new(BigInt::from(1), 0),
            &BCNum::new(BigInt::from(10), 0),
            2,
        );

        // 12. Trigger term.is_zero() loops for Sin/Cos/Atan/Ln/Exp/Bessel
        let _ = bc_sin(&BCNum::new(BigInt::from(1), 2), 50); // sin(0.01)
        let _ = bc_cos(&BCNum::new(BigInt::from(1), 2), 50); // cos(0.01)
        let _ = bc_atan(&BCNum::new(BigInt::from(1), 2), 50); // atan(0.01)
        let _ = bc_ln(&BCNum::new(BigInt::from(101), 2), 50); // ln(1.01)
        let _ = bc_exp(&BCNum::new(BigInt::from(1), 2), 50); // exp(0.01)
        let _ = bc_bessel(
            &BCNum::new(BigInt::from(1), 0),
            &BCNum::new(BigInt::from(1), 2),
            50,
        ); // J_1(0.01)

        // 13. Trigger decimal_ln scaling loops (large and intermediate inputs)
        let _ = bc_ln(&BCNum::new(BigInt::from(1000000000000i64), 0), 20);
        for val in &["1.5", "1.8", "2.5", "3.0", "5.0", "10.0", "100.0"] {
            let _ = bc_ln(&BCNum::from_string(val, 10), 20);
        }

        // 14. bc_bessel with negative even order (e.g. n = -2)
        let _ = bc_bessel(
            &BCNum::new(BigInt::from(-2), 0),
            &BCNum::new(BigInt::from(5), 0),
            5,
        );
    }

    #[test]
    fn test_math_mutant_boundary_cases() {
        // Bessel function negative odd and even orders: J_{-n}(x) = (-1)^n J_n(x)
        let j1 = bc_bessel(
            &BCNum::new(BigInt::from(1), 0),
            &BCNum::new(BigInt::from(2), 0),
            5,
        );
        let j_neg1 = bc_bessel(
            &BCNum::new(BigInt::from(-1), 0),
            &BCNum::new(BigInt::from(2), 0),
            5,
        );
        assert_eq!(j_neg1.coeff, -j1.coeff);

        let j2 = bc_bessel(
            &BCNum::new(BigInt::from(2), 0),
            &BCNum::new(BigInt::from(2), 0),
            5,
        );
        let j_neg2 = bc_bessel(
            &BCNum::new(BigInt::from(-2), 0),
            &BCNum::new(BigInt::from(2), 0),
            5,
        );
        assert_eq!(j_neg2.coeff, j2.coeff);

        // Power boundary operations
        let x = BCNum::from_string("5", 10);
        let zero = BCNum::from_string("0", 10);
        let pow_zero = x.pow(&zero, 4);
        assert_eq!(pow_zero.coeff, BigInt::from(1));

        let zero_pow_x = zero.pow(&x, 4);
        assert_eq!(zero_pow_x.coeff, BigInt::zero());

        // Hex base parsing
        let hex_val = BCNum::from_string("1A", 16);
        assert_eq!(hex_val.coeff, BigInt::from(26));
        let hex_val_lower = BCNum::from_string("1a", 16);
        assert_eq!(hex_val_lower.coeff, BigInt::from(26));

        // Arctangent boundary: atan(1) and atan(-1)
        let one = BCNum::from_string("1", 10);
        let neg_one = BCNum::new(BigInt::from(-1), 0);
        let atan_pos = bc_atan(&one, 5);
        let atan_neg = bc_atan(&neg_one, 5);
        assert_eq!(atan_neg.coeff, -atan_pos.coeff);
    }

    #[test]
    fn test_bessel_fractional_orders_and_edge_cases() {
        let zero = BCNum::from_string("0", 10);
        let x = BCNum::from_string("3.5", 10);

        // J_0(0) = 1
        let j0_zero = bc_bessel(&zero, &zero, 5);
        assert_eq!(j0_zero.coeff, BigInt::from(100000));

        // J_1(0) = 0
        let one = BCNum::from_string("1", 10);
        let j1_zero = bc_bessel(&one, &zero, 5);
        assert_eq!(j1_zero.coeff, BigInt::zero());

        // Fractional order truncates n: j(2.8, x) == j(2, x)
        let order_frac = BCNum::from_string("2.8", 10);
        let order_int = BCNum::from_string("2", 10);
        let j_frac = bc_bessel(&order_frac, &x, 5);
        let j_int = bc_bessel(&order_int, &x, 5);
        assert_eq!(j_frac.coeff, j_int.coeff);
    }

    #[test]
    fn test_math_invariants_and_decimal_precision() {
        let scale = 10;
        let half = BCNum::from_string("0.5", 10);

        // 1. sin^2(x) + cos^2(x) = 1
        let s = bc_sin(&half, scale);
        let c = bc_cos(&half, scale);
        let s_sq = s.mul(&s, scale);
        let c_sq = c.mul(&c, scale);
        let pythagoras = s_sq.add(&c_sq);
        assert_eq!(pythagoras.coeff, BigInt::from(9_999_999_997i64)); // 0.9999999997 (scale 10 truncation)

        // 2. ln(exp(2)) == 2
        let two = BCNum::from_string("2", 10);
        let exp_2 = bc_exp(&two, scale);
        let ln_exp_2 = bc_ln(&exp_2, scale);
        assert_eq!(ln_exp_2.coeff, BigInt::from(19_999_999_999i64)); // 1.9999999999 (scale 10 truncation)

        // 3. 4 * atan(1) == pi (3.1415926535)
        let one = BCNum::from_string("1", 10);
        let four = BCNum::from_string("4", 10);
        let atan_1 = bc_atan(&one, scale);
        let pi = four.mul(&atan_1, scale);
        assert_eq!(pi.coeff, BigInt::from(31_415_926_532i64));
    }

    #[test]
    fn test_large_angle_trig_reduction_and_obase_formatting() {
        let scale = 6;
        let x_large = BCNum::from_string("100", 10);
        let x_neg_large = BCNum::new(BigInt::from(-15), 0);

        // 1. Large angle reduction sin(100) and cos(100)
        let s100 = bc_sin(&x_large, scale);
        let c100 = bc_cos(&x_large, scale);
        let s100_sq = s100.mul(&s100, scale);
        let c100_sq = c100.mul(&c100, scale);
        let pyth100 = s100_sq.add(&c100_sq);
        assert_eq!(pyth100.coeff, BigInt::from(999_997)); // ~0.999997 (scale 6 truncation)

        // Negative angle reduction sin(-15) == -sin(15)
        let x15 = BCNum::from_string("15", 10);
        let s_pos15 = bc_sin(&x15, scale);
        let s_neg15 = bc_sin(&x_neg_large, scale);
        assert_eq!(s_neg15.coeff, -s_pos15.coeff);

        // 2. Format obase variations (base 2, 8, 16, 100)
        let ten = BCNum::from_string("10", 10);
        assert_eq!(ten.format_obase(2), "1010");

        let sixty_four = BCNum::from_string("64", 10);
        assert_eq!(sixty_four.format_obase(8), "100");

        let ff = BCNum::from_string("255", 10);
        assert_eq!(ff.format_obase(16), "FF");

        let hundred = BCNum::from_string("250", 10);
        assert_eq!(hundred.format_obase(100), " 02 50");

        // 3. String parsing edge cases (.5, 007)
        let dot_five = BCNum::from_string(".5", 10);
        assert_eq!(dot_five.coeff, BigInt::from(5));
        assert_eq!(dot_five.scale, 1);

        let leading_zeros = BCNum::from_string("007", 10);
        assert_eq!(leading_zeros.coeff, BigInt::from(7));
    }

    #[test]
    fn test_trig_modulo_ranges_atan_inversion_and_fractional_ln() {
        let scale = 6;

        // 1. Trig in range (pi, 2pi): x = 4.5 and x = -4.5
        let x_pi_2pi = BCNum::from_string("4.5", 10);
        let x_neg_pi_2pi = BCNum::new(BigInt::from(-45), 1);
        let s_45 = bc_sin(&x_pi_2pi, scale);
        let c_45 = bc_cos(&x_pi_2pi, scale);
        let s_neg45 = bc_sin(&x_neg_pi_2pi, scale);
        let c_neg45 = bc_cos(&x_neg_pi_2pi, scale);
        assert_eq!(s_neg45.coeff, -s_45.coeff);
        assert_eq!(c_neg45.coeff, c_45.coeff);

        // 2. atan(x) for x > 1 (3.5), x = 0, and x < -1 (-3.5)
        let zero = BCNum::from_string("0", 10);
        let atan_zero = bc_atan(&zero, scale);
        assert_eq!(atan_zero.coeff, BigInt::from(0));

        let x_gt1 = BCNum::from_string("3.5", 10);
        let x_lt_neg1 = BCNum::new(BigInt::from(-35), 1);

        let atan_gt1 = bc_atan(&x_gt1, scale);
        let atan_lt_neg1 = bc_atan(&x_lt_neg1, scale);
        assert_eq!(atan_lt_neg1.coeff, -atan_gt1.coeff);

        // 3. ln(x) for fractional x < 1 (0.5, 0.1, 0.01)
        let p5 = BCNum::from_string("0.5", 10);
        let p1 = BCNum::from_string("0.1", 10);
        let ln_p5 = bc_ln(&p5, scale);
        let ln_p1 = bc_ln(&p1, scale);
        assert_eq!(ln_p5.coeff, BigInt::from(-693_147)); // ln(0.5) = -0.693147
        assert_eq!(ln_p1.coeff, BigInt::from(-2_302_585)); // ln(0.1) = -2.302585

        // exp(ln(0.5)) == 0.5
        let exp_ln_p5 = bc_exp(&ln_p5, scale);
        assert_eq!(exp_ln_p5.coeff, BigInt::from(500_000));
    }

    #[test]
    fn test_small_argument_bessel_and_exponential_series_boundaries() {
        let scale = 6;
        let zero = BCNum::from_string("0", 10);
        let p1 = BCNum::from_string("0.1", 10);

        // 1. Bessel J_0(0.1) and J_1(0.1)
        let j0 = bc_bessel(&zero, &p1, scale);
        let one = BCNum::from_string("1", 10);
        let j1 = bc_bessel(&one, &p1, scale);
        assert_eq!(j0.coeff, BigInt::from(997_501)); // J_0(0.1) = 0.997501

        assert_eq!(j1.coeff, BigInt::from(49_937)); // J_1(0.1) = 0.049937

        // 2. Exponential near zero e(0.001)
        let tiny = BCNum::from_string("0.001", 10);
        let exp_tiny = bc_exp(&tiny, scale);
        assert_eq!(exp_tiny.coeff, BigInt::from(1_001_000)); // e(0.001) = 1.001000

        // 3. Natural log near 1 l(1.001)
        let one_tiny = BCNum::from_string("1.001", 10);
        let ln_one_tiny = bc_ln(&one_tiny, scale);
        assert_eq!(ln_one_tiny.coeff, BigInt::from(999)); // ln(1.001) = 0.000999
    }

    #[test]
    fn test_transcendental_zero_scale_guard_precision() {
        let zero = BCNum::from_string("0", 10);
        let one = BCNum::from_string("1", 10);
        let two = BCNum::from_string("2", 10);
        let three = BCNum::from_string("3", 10);

        let ten = BCNum::from_string("10", 10);
        let hundred = BCNum::from_string("100", 10);

        // Under global_scale = 0 and x.scale = 0, guard precision (+15) ensures accurate scale 0 integer results
        assert_eq!(bc_sin(&one, 0).coeff, BigInt::from(0)); // sin(1) ~ 0.8414 -> 0
        assert_eq!(bc_cos(&one, 0).coeff, BigInt::from(0)); // cos(1) ~ 0.5403 -> 0
        assert_eq!(bc_atan(&two, 0).coeff, BigInt::from(1)); // atan(2) ~ 1.1071 -> 1
        assert_eq!(bc_ln(&three, 0).coeff, BigInt::from(1)); // ln(3) ~ 1.0986 -> 1
        assert_eq!(bc_exp(&one, 0).coeff, BigInt::from(2)); // exp(1) ~ 2.7182 -> 2
        assert_eq!(bc_exp(&two, 0).coeff, BigInt::from(7)); // exp(2) ~ 7.3891 -> 7 (kills +15 vs *15 in bc_exp)
        assert_eq!(
            bc_exp(&hundred, 0).coeff,
            BigInt::parse_bytes(b"26881171418161354484126255515800135873611118", 10).unwrap()
        ); // exp(100) ~ 2.688e43 (kills int_approx * 44 / 100 mutants)

        assert_eq!(bc_ln(&ten, 0).coeff, BigInt::from(2)); // ln(10) ~ 2.3025 -> 2 (kills +15 vs *15 in bc_ln)
        assert_eq!(bc_bessel(&zero, &one, 0).coeff, BigInt::from(0)); // J_0(1) ~ 0.7651 -> 0
    }

    #[test]
    fn test_obase_power_of_ten_digit_padding_width() {
        let num = BCNum::from_string("0.05", 10);
        let str_100 = num.format_obase(100);
        assert_eq!(str_100, ".05");
    }

    #[test]
    fn test_verified_kernels_boundary_contracts() {
        use crate::verified_kernels::*;
        assert_eq!(verified_pow_scale_and_shift(6, 2, 4), (4, 2));
        assert_eq!(verified_pow_scale_and_shift(3, 5, 2), (3, 0));
        assert_eq!(verified_multi_digit_obase_pad_zeros(3, 1), 2);
        assert_eq!(verified_multi_digit_obase_pad_zeros(2, 2), 0);
        assert_eq!(verified_multi_digit_obase_pad_zeros(2, 3), 0);
        assert_eq!(verified_transcendental_guard_prec(2, 4, 3), 22);
        assert_eq!(verified_transcendental_guard_prec(5, 2, 0), 20);
        assert_eq!(verified_transcendental_guard_prec(3, 3, 1), 19);
        assert!(!verified_c_ffi_check_buf_capacity(0, 0));
        assert!(verified_c_ffi_check_buf_capacity(0, 1));
        assert!(!verified_c_ffi_check_buf_capacity(1, 1));
        assert!(verified_c_ffi_check_buf_capacity(4, 5));
        assert!(!verified_c_ffi_check_buf_capacity(5, 5));
        assert_eq!(verified_zephyr_classify_char(b'\r'), 1);
        assert_eq!(verified_zephyr_classify_char(b'\n'), 1);
        assert_eq!(verified_zephyr_classify_char(0x08), 2);
        assert_eq!(verified_zephyr_classify_char(0x7F), 2);
        assert_eq!(verified_zephyr_classify_char(0x03), 3);
        assert_eq!(verified_zephyr_classify_char(b' '), 4);
        assert_eq!(verified_zephyr_classify_char(b'~'), 4);
        assert_eq!(verified_zephyr_classify_char(0x1F), 0);
        assert_eq!(verified_zephyr_classify_char(0x80), 0);
        assert_eq!(verified_lexer_advance_step(5, 10, false), (6, 10));
        assert_eq!(verified_lexer_advance_step(5, 10, true), (6, 11));
        assert_eq!(verified_decimal_scale_shift(2, 5), (3, true));
        assert_eq!(verified_decimal_scale_shift(3, 3), (0, true));
        assert_eq!(verified_decimal_scale_shift(5, 2), (3, false));
        assert_eq!(verified_clamp_register(5, true, 2, 16), (2, -2));
        assert_eq!(verified_clamp_register(0, true, 0, BC_SCALE_MAX), (0, -2));
        assert_eq!(verified_clamp_register(1, false, 2, 16), (2, -1));
        assert_eq!(verified_clamp_register(2, false, 2, 16), (2, 0));
        assert_eq!(verified_clamp_register(16, false, 2, 16), (16, 0));
        assert_eq!(verified_clamp_register(17, false, 2, 16), (16, 1));
        assert_eq!(verified_clamp_register(0, false, 0, BC_SCALE_MAX), (0, 0));
        assert_eq!(
            verified_clamp_register(usize::MAX, false, 0, BC_SCALE_MAX),
            (BC_SCALE_MAX, 1)
        );
        assert_eq!(verified_pratt_infix_info(0), (-1, false, 0));
        assert_eq!(verified_pratt_infix_info(TOK_ASSIGN_OP), (1, true, 1));
        assert_eq!(verified_pratt_infix_info(TOK_PLUS_MINUS), (2, false, 3));
        assert_eq!(verified_pratt_infix_info(TOK_MUL_OP), (3, false, 4));
        assert_eq!(verified_pratt_infix_info(TOK_EXP_OP), (4, true, 4));
        assert_eq!(verified_pratt_infix_info(5), (-1, false, 0));
        assert_eq!(verified_lexer_peek_char_index(5, 2, 2), (true, 4));
        assert_eq!(verified_lexer_peek_char_index(5, 2, 3), (false, 0));
        assert_eq!(verified_lexer_peek_char_index(5, 2, 4), (false, 0));
        assert!(!verified_is_ident_continue(96)); // '`'
        assert!(verified_is_ident_continue(97)); // 'a'
        assert!(verified_is_ident_continue(122)); // 'z'
        assert!(!verified_is_ident_continue(123)); // '{'
        assert!(!verified_is_ident_continue(47)); // '/'
        assert!(verified_is_ident_continue(48)); // '0'
        assert!(verified_is_ident_continue(57)); // '9'
        assert!(!verified_is_ident_continue(58)); // ':'
        assert!(!verified_is_ident_continue(94)); // '^'
        assert!(verified_is_ident_continue(95)); // '_'
        assert_eq!(verified_cli_classify_arg(b"-l", false), CLI_ARG_OPT_CLUSTER);
        assert_eq!(
            verified_cli_classify_arg(b"-ls", false),
            CLI_ARG_OPT_CLUSTER
        );
        assert_eq!(verified_cli_classify_arg(b"-l", true), CLI_ARG_FILE);
        assert_eq!(verified_cli_classify_arg(b"-", false), CLI_ARG_FILE);
        assert_eq!(
            verified_cli_classify_arg(b"--", false),
            CLI_ARG_END_OF_OPTIONS
        );
        assert_eq!(verified_cli_classify_arg(b"--", true), CLI_ARG_FILE);
        assert_eq!(
            verified_cli_classify_arg(b"--x", false),
            CLI_ARG_OPT_INVALID
        );
        assert_eq!(verified_cli_classify_arg(b"", false), CLI_ARG_FILE);
        assert_eq!(verified_cli_classify_arg(b"test.bc", false), CLI_ARG_FILE);
        assert_eq!(
            verified_cli_classify_option_char(u32::from('l')),
            CLI_ARG_OPT_L
        );
        assert_eq!(
            verified_cli_classify_option_char(u32::from('s')),
            CLI_ARG_OPT_S
        );
        assert_eq!(
            verified_cli_classify_option_char(u32::from('w')),
            CLI_ARG_OPT_W
        );
        assert_eq!(
            verified_cli_classify_option_char(u32::from('q')),
            CLI_ARG_OPT_INVALID
        );
        assert_eq!(
            verified_cli_classify_option_char(u32::from('-')),
            CLI_ARG_OPT_INVALID
        );
        assert_eq!(verified_cli_initial_scale(true), 20);
        assert_eq!(verified_cli_initial_scale(false), 0);
    }

    #[test]
    #[should_panic(expected = "Modulo by zero")]
    fn test_mod_op_panics_on_zero_divisor() {
        let _ = BCNum::from_string("1", 10).mod_op(&BCNum::zero(), 0);
    }

    #[test]
    fn test_fallible_math_operations() {
        let zero = BCNum::zero();
        let ten = BCNum::from_string("10", 10);
        let neg = BCNum::new(BigInt::from(-4), 0);

        assert_eq!(ten.try_div(&zero, 0), Err(RuntimeError::DivideByZero));
        assert_eq!(ten.try_mod_op(&zero, 0), Err(RuntimeError::ModuloByZero));
        assert_eq!(
            zero.try_pow(&neg, 0),
            Err(RuntimeError::NegativePowerOfZero)
        );
        assert_eq!(neg.try_sqrt(0), Err(RuntimeError::NegativeSqrt));

        assert_eq!(
            ten.try_div(&BCNum::from_string("2", 10), 0),
            Ok(BCNum::from_string("5", 10))
        );
        assert_eq!(
            ten.try_mod_op(&BCNum::from_string("3", 10), 0),
            Ok(BCNum::from_string("1", 10))
        );
        assert_eq!(
            BCNum::from_string("9", 10).try_sqrt(0),
            Ok(BCNum::from_string("3", 10))
        );
        assert_eq!(zero.try_sqrt(0), Ok(BCNum::zero()));
    }
}
