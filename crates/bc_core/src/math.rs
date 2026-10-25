// SPDX-License-Identifier: MIT

//! Arbitrary-precision decimal math library for bc.
//!
//! Provides the core `BCNum` type representing decimal numbers as integer
//! coefficients paired with a scale factor. Also implements transcendental
//! functions using series expansions.

use crate::verified_kernels::{
    verified_add_sub_scales, verified_alphanumeric_char_val, verified_bcnum_length,
    verified_bessel_negative_order_parity, verified_decimal_scale_shift,
    verified_div_scale_and_shift, verified_mul_scale_and_shift,
    verified_multi_digit_obase_pad_zeros, verified_pow_scale_and_shift,
    verified_sqrt_scale_and_shift, verified_transcendental_guard_prec,
};
use alloc::format;
use alloc::string::{String, ToString};
use alloc::vec::Vec;
use num_bigint::BigInt;
use num_traits::{Signed, ToPrimitive, Zero};

/// Arbitrary-precision decimal number representation for bc.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BCNum {
    pub coeff: BigInt,
    pub scale: usize,
}

impl BCNum {
    /// Creates a new BCNum.
    pub fn new(coeff: BigInt, scale: usize) -> Self {
        Self { coeff, scale }
    }

    /// Creates a BCNum representing 0 with scale 0.
    pub fn zero() -> Self {
        Self {
            coeff: BigInt::zero(),
            scale: 0,
        }
    }

    /// Parses a numeric constant string under `ibase` into a BCNum.
    pub fn from_string(num_str: &str, ibase: usize) -> Self {
        let num_str = num_str.replace("\\\n", "");
        let (int_part, frac_part) = if let Some(pos) = num_str.find('.') {
            (&num_str[..pos], &num_str[pos + 1..])
        } else {
            (num_str.as_str(), "")
        };

        let mut int_val = BigInt::zero();
        for b in int_part.bytes() {
            int_val = int_val * ibase + verified_alphanumeric_char_val(b);
        }

        let scale_val = frac_part.len();
        let coeff = if scale_val > 0 {
            let mut frac_numerator = BigInt::zero();
            for b in frac_part.bytes() {
                frac_numerator = frac_numerator * ibase + verified_alphanumeric_char_val(b);
            }
            let frac_denominator = BigInt::from(ibase).pow(scale_val as u32);
            let num = (int_val * &frac_denominator + frac_numerator)
                * BigInt::from(10).pow(scale_val as u32);
            num / frac_denominator
        } else {
            int_val
        };

        Self {
            coeff,
            scale: scale_val,
        }
    }

    /// Returns true if the number is mathematically zero.
    pub fn is_zero(&self) -> bool {
        self.coeff.is_zero()
    }

    /// Adds two BCNum values.
    pub fn add(&self, other: &Self) -> Self {
        let (sr, shift_a, shift_b) = verified_add_sub_scales(self.scale, other.scale);
        let coeff_a = &self.coeff * BigInt::from(10).pow(shift_a as u32);
        let coeff_b = &other.coeff * BigInt::from(10).pow(shift_b as u32);
        Self::new(coeff_a + coeff_b, sr)
    }

    /// Subtracts other from self.
    pub fn sub(&self, other: &Self) -> Self {
        let (sr, shift_a, shift_b) = verified_add_sub_scales(self.scale, other.scale);
        let coeff_a = &self.coeff * BigInt::from(10).pow(shift_a as u32);
        let coeff_b = &other.coeff * BigInt::from(10).pow(shift_b as u32);
        Self::new(coeff_a - coeff_b, sr)
    }

    /// Multiplies two BCNum values under scale.
    pub fn mul(&self, other: &Self, global_scale: usize) -> Self {
        let (sr, diff) = verified_mul_scale_and_shift(self.scale, other.scale, global_scale);
        let coeff = (&self.coeff * &other.coeff) / BigInt::from(10).pow(diff as u32);
        Self::new(coeff, sr)
    }

    /// Divides self by other under scale, returning Err on division by zero.
    pub fn try_div(&self, other: &Self, global_scale: usize) -> Result<Self, &'static str> {
        if other.coeff.is_zero() {
            return Err("division by zero");
        }
        let (sr, shift) = verified_div_scale_and_shift(self.scale, other.scale, global_scale);
        let coeff = if shift >= 0 {
            let num = &self.coeff * BigInt::from(10).pow(shift as u32);
            num / &other.coeff
        } else {
            let den = &other.coeff * BigInt::from(10).pow((-shift) as u32);
            &self.coeff / den
        };
        Ok(Self::new(coeff, sr))
    }

    /// Divides self by other under scale.
    pub fn div(&self, other: &Self, global_scale: usize) -> Self {
        self.try_div(other, global_scale)
            .unwrap_or_else(|msg| panic!("{}", msg))
    }

    /// Computes self % other under scale, returning Err on division by zero.
    pub fn try_mod_op(&self, other: &Self, global_scale: usize) -> Result<Self, &'static str> {
        let q = self.try_div(other, global_scale)?;
        let prod_coeff = &q.coeff * &other.coeff;
        let prod_scale = q.scale + other.scale;
        let prod = Self::new(prod_coeff, prod_scale);
        Ok(self.sub(&prod))
    }

    /// Computes self % other under scale.
    pub fn mod_op(&self, other: &Self, global_scale: usize) -> Self {
        self.try_mod_op(other, global_scale)
            .unwrap_or_else(|msg| panic!("{}", msg))
    }

    /// Raises self to the power of other under scale, returning Err on division by zero.
    pub fn try_pow(&self, other: &Self, global_scale: usize) -> Result<Self, &'static str> {
        let b_val = if other.scale > 0 {
            &other.coeff / BigInt::from(10).pow(other.scale as u32)
        } else {
            other.coeff.clone()
        };

        if b_val >= BigInt::zero() {
            let mut res_coeff = BigInt::from(1);
            let mut res_scale = 0usize;
            let mut base_coeff = self.coeff.clone();
            let mut base_scale = self.scale;
            let mut temp_b = b_val;
            while temp_b > BigInt::zero() {
                if &temp_b % 2 == BigInt::from(1) {
                    res_coeff *= &base_coeff;
                    res_scale += base_scale;
                }
                base_coeff = &base_coeff * &base_coeff;
                base_scale += base_scale;
                temp_b /= 2;
            }
            let (sr, diff) = verified_pow_scale_and_shift(res_scale, self.scale, global_scale);
            let coeff = res_coeff / BigInt::from(10).pow(diff as u32);
            Ok(Self::new(coeff, sr))
        } else {
            let b_abs = -b_val;
            let mut res_coeff = BigInt::from(1);
            let mut res_scale = 0usize;
            let mut base_coeff = self.coeff.clone();
            let mut base_scale = self.scale;
            let mut temp_b = b_abs;
            while temp_b > BigInt::zero() {
                if &temp_b % 2 == BigInt::from(1) {
                    res_coeff *= &base_coeff;
                    res_scale += base_scale;
                }
                base_coeff = &base_coeff * &base_coeff;
                base_scale += base_scale;
                temp_b /= 2;
            }
            let exact_pow = Self::new(res_coeff, res_scale);
            Self::new(BigInt::from(1), 0).try_div(&exact_pow, global_scale)
        }
    }

    /// Raises self to the power of other under scale.
    pub fn pow(&self, other: &Self, global_scale: usize) -> Self {
        self.try_pow(other, global_scale)
            .unwrap_or_else(|msg| panic!("{}", msg))
    }

    /// Computes the square root of self under scale, returning Err on negative input.
    pub fn try_sqrt(&self, global_scale: usize) -> Result<Self, &'static str> {
        if self.coeff < BigInt::zero() {
            return Err("square root of negative number");
        }
        let (sr, shift) = verified_sqrt_scale_and_shift(self.scale, global_scale);
        let num = &self.coeff * BigInt::from(10).pow(shift as u32);
        let coeff = num.sqrt();
        Ok(Self::new(coeff, sr))
    }

    /// Computes the square root of self under scale.
    pub fn sqrt(&self, global_scale: usize) -> Self {
        self.try_sqrt(global_scale)
            .unwrap_or_else(|msg| panic!("{}", msg))
    }

    /// Computes the total number of significant decimal digits.
    pub fn length(&self) -> Self {
        let divisor = BigInt::from(10).pow(self.scale as u32);
        let int_part = self.coeff.abs() / divisor;
        let is_zero = int_part.is_zero();
        let digits = if is_zero {
            0
        } else {
            int_part.to_string().len()
        };
        let val = verified_bcnum_length(is_zero, digits, self.scale);
        Self::new(BigInt::from(val), 0)
    }

    /// Returns the scale of self.
    pub fn scale_func(&self) -> Self {
        Self::new(BigInt::from(self.scale), 0)
    }

    /// Formats the BCNum value as a string in `obase`.
    pub fn format_obase(&self, obase: usize) -> String {
        if self.coeff.is_zero() {
            return "0".to_string();
        }

        let is_negative = self.coeff < BigInt::zero();
        let coeff_abs = self.coeff.abs();

        let divisor = BigInt::from(10).pow(self.scale as u32);
        let int_part = &coeff_abs / &divisor;
        let frac_coeff = &coeff_abs % &divisor;

        let mut int_str = String::new();
        if !int_part.is_zero() {
            if obase <= 16 {
                let mut digits = Vec::new();
                let mut temp = int_part;
                let ob = BigInt::from(obase);
                while !temp.is_zero() {
                    let rem = (&temp % &ob).to_usize().unwrap();
                    digits.push(b"0123456789ABCDEF"[rem] as char);
                    temp /= &ob;
                }
                int_str = digits.into_iter().rev().collect();
            } else {
                let digit_width = (obase - 1).to_string().len();
                let mut digits = Vec::new();
                let mut temp = int_part;
                let ob = BigInt::from(obase);
                while !temp.is_zero() {
                    let rem = (&temp % &ob).to_string();
                    let mut padded = String::new();
                    let pad_zeros = verified_multi_digit_obase_pad_zeros(digit_width, rem.len());
                    for _ in 0..pad_zeros {
                        padded.push('0');
                    }
                    padded.push_str(&rem);
                    digits.push(padded);
                    temp /= &ob;
                }
                let mut parts = Vec::new();
                for d in digits.into_iter().rev() {
                    parts.push(format!(" {}", d));
                }
                int_str = parts.concat();
            }
        }

        let mut frac_str = String::new();
        if self.scale > 0 {
            let num_digits = if obase != 10 {
                let target = BigInt::from(10).pow(self.scale as u32);
                let mut k = 0usize;
                let mut current = BigInt::from(1);
                let ob = BigInt::from(obase);
                while current < target {
                    current *= &ob;
                    k += 1;
                    if current.is_zero() {
                        break;
                    }
                }
                k
            } else {
                self.scale
            };

            let mut num = frac_coeff;
            let den = divisor;
            let ob = BigInt::from(obase);
            let mut frac_digits = Vec::new();
            for _ in 0..num_digits {
                num *= &ob;
                let d = &num / &den;
                frac_digits.push(d.to_usize().unwrap());
                num %= &den;
            }

            if obase <= 16 {
                let chars: String = frac_digits
                    .iter()
                    .map(|&d| b"0123456789ABCDEF"[d] as char)
                    .collect();
                frac_str = format!(".{}", chars);
            } else {
                let digit_width = (obase - 1).to_string().len();
                let mut parts = Vec::new();
                for (i, &d) in frac_digits.iter().enumerate() {
                    let s = d.to_string();
                    let mut padded = String::new();
                    let pad_zeros = verified_multi_digit_obase_pad_zeros(digit_width, s.len());
                    for _ in 0..pad_zeros {
                        padded.push('0');
                    }
                    padded.push_str(&s);
                    if i == 0 {
                        parts.push(format!(".{}", padded));
                    } else {
                        parts.push(format!(" {}", padded));
                    }
                }
                frac_str = parts.concat();
            }
        }

        let mut result = format!("{}{}", int_str, frac_str);
        if is_negative {
            result = format!("-{}", result);
        }
        result
    }
}

// --- Transcendental Math Helper: Decimal ---

#[derive(Clone)]
struct Decimal {
    value: BigInt,
    prec: usize,
}

impl Decimal {
    fn zero(prec: usize) -> Self {
        Self {
            value: BigInt::zero(),
            prec,
        }
    }

    fn one(prec: usize) -> Self {
        Self {
            value: BigInt::from(10).pow(prec as u32),
            prec,
        }
    }

    fn from_fraction(num: i64, den: i64, prec: usize) -> Self {
        Self {
            value: BigInt::from(num) * BigInt::from(10).pow(prec as u32) / BigInt::from(den),
            prec,
        }
    }

    fn from_int(val: i64, prec: usize) -> Self {
        Self {
            value: BigInt::from(val) * BigInt::from(10).pow(prec as u32),
            prec,
        }
    }

    fn from_bc_num(num: &BCNum, prec: usize) -> Self {
        let (shift, should_mul) = verified_decimal_scale_shift(num.scale, prec);
        let value = if should_mul {
            &num.coeff * BigInt::from(10).pow(shift as u32)
        } else {
            &num.coeff / BigInt::from(10).pow(shift as u32)
        };
        Self { value, prec }
    }

    fn to_bc_num(&self, target_scale: usize) -> BCNum {
        let (shift, should_mul) = verified_decimal_scale_shift(self.prec, target_scale);
        let coeff = if should_mul {
            &self.value * BigInt::from(10).pow(shift as u32)
        } else {
            &self.value / BigInt::from(10).pow(shift as u32)
        };
        BCNum::new(coeff, target_scale)
    }

    fn add(&self, other: &Self) -> Self {
        Self {
            value: &self.value + &other.value,
            prec: self.prec,
        }
    }

    fn sub(&self, other: &Self) -> Self {
        Self {
            value: &self.value - &other.value,
            prec: self.prec,
        }
    }

    fn mul(&self, other: &Self) -> Self {
        Self {
            value: (&self.value * &other.value) / BigInt::from(10).pow(self.prec as u32),
            prec: self.prec,
        }
    }

    fn mul_int(&self, factor: i64) -> Self {
        Self {
            value: &self.value * factor,
            prec: self.prec,
        }
    }

    fn mul_bigint(&self, factor: &BigInt) -> Self {
        Self {
            value: &self.value * factor,
            prec: self.prec,
        }
    }

    fn div(&self, other: &Self) -> Self {
        Self {
            value: (&self.value * BigInt::from(10).pow(self.prec as u32)) / &other.value,
            prec: self.prec,
        }
    }

    fn div_int(&self, divisor: i64) -> Self {
        Self {
            value: &self.value / divisor,
            prec: self.prec,
        }
    }

    fn rem(&self, other: &Self) -> Self {
        let q = &self.value / &other.value;
        Self {
            value: &self.value - &q * &other.value,
            prec: self.prec,
        }
    }

    fn is_zero(&self) -> bool {
        self.value.is_zero()
    }

    fn sqrt(&self) -> Self {
        let num = &self.value * BigInt::from(10).pow(self.prec as u32);
        Self {
            value: num.sqrt(),
            prec: self.prec,
        }
    }
}

// --- Math Library Transcendental Calculations ---

fn atan_tiny(x: &Decimal) -> Decimal {
    let mut total = Decimal::zero(x.prec);
    let mut num = x.clone();
    let x_sq = x.mul(x);
    let mut k = 1;
    let mut sign = 1;
    loop {
        let term = num.div_int(k);
        if term.is_zero() {
            break;
        }
        total = if sign > 0 {
            total.add(&term)
        } else {
            total.sub(&term)
        };
        num = num.mul(&x_sq);
        k += 2;
        sign = -sign;
    }
    total
}

fn get_pi(prec: usize) -> Decimal {
    let dec_0_2 = Decimal::from_fraction(2, 10, prec);
    let dec_1_239 = Decimal::from_fraction(1, 239, prec);
    let atan_0_2 = atan_tiny(&dec_0_2);
    let atan_1_239 = atan_tiny(&dec_1_239);
    atan_0_2.mul_int(4).sub(&atan_1_239).mul_int(4)
}

fn decimal_sin(x: &Decimal, prec: usize) -> Decimal {
    let pi = get_pi(prec + 10);
    let two_pi = pi.mul_int(2);

    let mut x_p = Decimal {
        value: &x.value * BigInt::from(10).pow(10),
        prec: prec + 10,
    };

    x_p = x_p.rem(&two_pi);

    if x_p.value > pi.value {
        x_p = x_p.sub(&two_pi);
    } else if x_p.value < -pi.value {
        x_p = x_p.add(&two_pi);
    }

    let mut total = Decimal::zero(prec + 10);
    let mut num = x_p.clone();
    let x_sq = x_p.mul(&x_p);
    let mut fact = BigInt::from(1);
    let mut k = 1;
    let mut sign = 1;
    loop {
        let term = Decimal {
            value: &num.value / &fact,
            prec: prec + 10,
        };
        if term.is_zero() {
            break;
        }
        total = if sign > 0 {
            total.add(&term)
        } else {
            total.sub(&term)
        };
        num = num.mul(&x_sq);
        fact = fact * (k + 1) * (k + 2);
        k += 2;
        sign = -sign;
    }

    Decimal {
        value: total.value / BigInt::from(10).pow(10),
        prec,
    }
}

fn decimal_cos(x: &Decimal, prec: usize) -> Decimal {
    let pi = get_pi(prec + 10);
    let two_pi = pi.mul_int(2);

    let mut x_p = Decimal {
        value: &x.value * BigInt::from(10).pow(10),
        prec: prec + 10,
    };

    x_p = x_p.rem(&two_pi);

    if x_p.value > pi.value {
        x_p = x_p.sub(&two_pi);
    } else if x_p.value < -pi.value {
        x_p = x_p.add(&two_pi);
    }

    let mut total = Decimal::zero(prec + 10);
    let mut num = Decimal::one(prec + 10);
    let x_sq = x_p.mul(&x_p);
    let mut fact = BigInt::from(1);
    let mut k = 0;
    let mut sign = 1;
    loop {
        let term = Decimal {
            value: &num.value / &fact,
            prec: prec + 10,
        };
        if term.is_zero() {
            break;
        }
        total = if sign > 0 {
            total.add(&term)
        } else {
            total.sub(&term)
        };
        num = num.mul(&x_sq);
        fact = fact * (k + 1) * (k + 2);
        k += 2;
        sign = -sign;
    }

    Decimal {
        value: total.value / BigInt::from(10).pow(10),
        prec,
    }
}

fn decimal_atan(x: &Decimal, prec: usize) -> Decimal {
    let mut x_p = Decimal {
        value: &x.value * BigInt::from(10).pow(10),
        prec: prec + 10,
    };

    if x_p.is_zero() {
        return x.clone();
    }

    let mut neg = false;
    if x_p.value < BigInt::zero() {
        x_p.value = -x_p.value;
        neg = true;
    }

    let mut inv = false;
    let one_p = Decimal::one(prec + 10);
    if x_p.value > one_p.value {
        x_p = one_p.div(&x_p);
        inv = true;
    }

    for _ in 0..4 {
        let one = Decimal::one(prec + 10);
        let x_sq = x_p.mul(&x_p);
        let sqrt_term = one.add(&x_sq).sqrt();
        x_p = x_p.div(&one.add(&sqrt_term));
    }

    let mut total = Decimal::zero(prec + 10);
    let mut num = x_p.clone();
    let x_sq = x_p.mul(&x_p);
    let mut k = 1;
    let mut sign = 1;
    loop {
        let term = num.div_int(k);
        if term.is_zero() {
            break;
        }
        total = if sign > 0 {
            total.add(&term)
        } else {
            total.sub(&term)
        };
        num = num.mul(&x_sq);
        k += 2;
        sign = -sign;
    }

    let mut val = total.mul_int(16);
    if inv {
        let pi = get_pi(prec + 10);
        let pi_over_2 = pi.div_int(2);
        val = pi_over_2.sub(&val);
    }
    if neg {
        val.value = -val.value;
    }

    Decimal {
        value: val.value / BigInt::from(10).pow(10),
        prec,
    }
}

fn compute_ln2(prec: usize) -> Decimal {
    let y = Decimal::from_fraction(1, 3, prec);
    let mut total = Decimal::zero(prec);
    let mut term_num = y.clone();
    let y_sq = y.mul(&y);
    let mut idx = 1;
    loop {
        let term = term_num.div_int(idx);
        if term.is_zero() {
            break;
        }
        total = total.add(&term);
        term_num = term_num.mul(&y_sq);
        idx += 2;
    }
    total.mul_int(2)
}

fn decimal_ln(x: &Decimal, prec: usize) -> Decimal {
    let p = prec + 15;
    let x_p = Decimal {
        value: &x.value * BigInt::from(10).pow(15),
        prec: p,
    };

    let bits = x_p.value.bits() as i64;
    let mut k = bits - (p as i64 * 3321928 / 1000000);
    let mut m = if k >= 0 {
        Decimal {
            value: &x_p.value >> k,
            prec: p,
        }
    } else {
        Decimal {
            value: &x_p.value << -k,
            prec: p,
        }
    };

    let threshold_lower = Decimal::from_fraction(707, 1000, p);
    let two = Decimal::from_int(2, p);

    while m.value < threshold_lower.value && m.value > BigInt::zero() {
        m = m.mul(&two);
        k -= 1;
    }

    let one = Decimal::from_int(1, p);
    let num_y = m.sub(&one);
    let den_y = m.add(&one);
    let y = num_y.div(&den_y);

    let mut total = Decimal::zero(p);
    let mut term_num = y.clone();
    let y_sq = y.mul(&y);
    let mut idx = 1;
    loop {
        let term = term_num.div_int(idx);
        if term.is_zero() {
            break;
        }
        total = total.add(&term);
        term_num = term_num.mul(&y_sq);
        idx += 2;
    }
    let ln_m = total.mul_int(2);

    let ln_2 = compute_ln2(p);
    let ln_x = ln_m.add(&ln_2.mul_bigint(&BigInt::from(k)));

    Decimal {
        value: ln_x.value / BigInt::from(10).pow(15),
        prec,
    }
}

fn decimal_exp(x: &Decimal, prec: usize) -> Decimal {
    let p = prec + 15;
    let mut x_p = Decimal {
        value: &x.value * BigInt::from(10).pow(15),
        prec: p,
    };

    let mut is_neg = false;
    if x_p.value < BigInt::zero() {
        x_p.value = -x_p.value;
        is_neg = true;
    }

    let ln_2 = compute_ln2(p);
    let n = &x_p.value / &ln_2.value;
    let r = x_p.sub(&ln_2.mul_bigint(&n));

    let mut total = Decimal::zero(p);
    let mut num = Decimal::one(p);
    let mut fact = BigInt::from(1);
    let mut k = 0i64;
    loop {
        let term = Decimal {
            value: &num.value / &fact,
            prec: p,
        };
        if term.is_zero() {
            break;
        }
        total = total.add(&term);
        num = num.mul(&r);
        k += 1;
        fact *= k;
    }

    let n_u32 = n.to_u32().unwrap_or(u32::MAX);
    let mut val = if n_u32 != u32::MAX {
        Decimal {
            value: total.value << n_u32,
            prec: p,
        }
    } else {
        Decimal::zero(p)
    };

    if is_neg {
        let one = Decimal::one(p);
        val = one.div(&val);
    }

    Decimal {
        value: val.value / BigInt::from(10).pow(15),
        prec,
    }
}

// --- Public Transcendental Functions (Math Library) ---

/// Math sine function.
pub fn bc_sin(x: &BCNum, global_scale: usize) -> BCNum {
    let prec = verified_transcendental_guard_prec(x.scale, global_scale, 0);
    let dec_x = Decimal::from_bc_num(x, prec);
    let dec_res = decimal_sin(&dec_x, prec);
    dec_res.to_bc_num(global_scale)
}

/// Math cosine function.
pub fn bc_cos(x: &BCNum, global_scale: usize) -> BCNum {
    let prec = verified_transcendental_guard_prec(x.scale, global_scale, 0);
    let dec_x = Decimal::from_bc_num(x, prec);
    let dec_res = decimal_cos(&dec_x, prec);
    dec_res.to_bc_num(global_scale)
}

/// Math arctangent function.
pub fn bc_atan(x: &BCNum, global_scale: usize) -> BCNum {
    let prec = verified_transcendental_guard_prec(x.scale, global_scale, 0);
    let dec_x = Decimal::from_bc_num(x, prec);
    let dec_res = decimal_atan(&dec_x, prec);
    dec_res.to_bc_num(global_scale)
}

/// Math natural logarithm function.
pub fn bc_ln(x: &BCNum, global_scale: usize) -> BCNum {
    let prec = verified_transcendental_guard_prec(x.scale, global_scale, 0);
    let dec_x = Decimal::from_bc_num(x, prec);
    if dec_x.value <= BigInt::zero() {
        let coeff = BigInt::parse_bytes(b"-99999999999999999999", 10).unwrap()
            * BigInt::from(10).pow(global_scale as u32);
        return BCNum::new(coeff, global_scale);
    }
    let dec_res = decimal_ln(&dec_x, prec);
    dec_res.to_bc_num(global_scale)
}

/// Math exponential function.
pub fn bc_exp(x: &BCNum, global_scale: usize) -> BCNum {
    let int_approx = if x.scale > 0 {
        let divisor = BigInt::from(10).pow(x.scale as u32);
        (&x.coeff / divisor).abs().to_u64().unwrap_or(0) as usize
    } else {
        x.coeff.abs().to_u64().unwrap_or(0) as usize
    };
    // e^x has approx (0.4343 * x) integer digits. Add int_approx / 2 extra guard precision
    // so large exponents retain all integer digits and fractional precision.
    let extra_prec = int_approx / 2;
    let prec = verified_transcendental_guard_prec(x.scale, global_scale, extra_prec);

    let dec_x = Decimal::from_bc_num(x, prec);
    let dec_res = decimal_exp(&dec_x, prec);
    dec_res.to_bc_num(global_scale)
}

/// Bessel function of the first kind J_n(x).
pub fn bc_bessel(n_num: &BCNum, x: &BCNum, global_scale: usize) -> BCNum {
    let n = if n_num.scale > 0 {
        let divisor = BigInt::from(10).pow(n_num.scale as u32);
        &n_num.coeff / divisor
    } else {
        n_num.coeff.clone()
    };
    let n_i64 = n.to_i64().unwrap_or(0);
    let prec = verified_transcendental_guard_prec(x.scale, global_scale, 0);
    let dec_x = Decimal::from_bc_num(x, prec);

    if dec_x.is_zero() {
        let res_val = if n_i64 == 0 {
            Decimal::from_int(1, prec)
        } else {
            Decimal::zero(prec)
        };
        return res_val.to_bc_num(global_scale);
    }

    let (n_abs, sign) = verified_bessel_negative_order_parity(n_i64);

    let x_half = dec_x.div_int(2);
    let mut term_factor = Decimal::one(prec);
    for _ in 0..n_abs {
        term_factor = term_factor.mul(&x_half);
    }

    let mut total = Decimal::zero(prec);
    let mut m = 0;
    let mut fact_m = BigInt::from(1);
    let mut fact_n_m = BigInt::from(1);
    for i in 1..=n_abs {
        fact_n_m *= i;
    }
    let x_half_sq = x_half.mul(&x_half);
    let mut num = term_factor;

    loop {
        let den = &fact_m * &fact_n_m;
        let term = Decimal {
            value: &num.value / &den,
            prec,
        };
        if term.is_zero() {
            break;
        }
        total = if m % 2 == 1 {
            total.sub(&term)
        } else {
            total.add(&term)
        };

        m += 1;
        num = num.mul(&x_half_sq);
        fact_m *= m;
        fact_n_m *= n_abs + m;
    }

    let dec_res = total.mul_int(sign);
    dec_res.to_bc_num(global_scale)
}

#[cfg(test)]
mod tests {
    use super::*;

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

        // 3. Decimal::from_bc_num with prec < scale (line 380)
        let num_large_scale = BCNum::new(BigInt::from(12345), 4);
        let dec_from = Decimal::from_bc_num(&num_large_scale, 2);
        assert_eq!(dec_from.value, BigInt::from(123));

        // 4. Decimal::to_bc_num with target_scale >= prec (line 388)
        let dec_val = Decimal {
            value: BigInt::from(123),
            prec: 2,
        };
        let bc_to = dec_val.to_bc_num(4);
        assert_eq!(bc_to.coeff, BigInt::from(12300));

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

        // 4. Decimal helper precision
        let dec_frac = Decimal::from_fraction(1, 3, 10);
        assert_eq!(dec_frac.value, BigInt::from(3_333_333_333i64));
        assert_eq!(dec_frac.prec, 10);

        let d1 = Decimal::from_int(10, 5);
        let d2 = Decimal::from_int(3, 5);
        let d_rem = d1.rem(&d2);
        assert_eq!(d_rem.value, BigInt::from(100_000)); // 1.00000
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
        assert_eq!(verified_ibase_warning_and_clamp(0), (2, -1));
        assert_eq!(verified_ibase_warning_and_clamp(1), (2, -1));
        assert_eq!(verified_ibase_warning_and_clamp(2), (2, 0));
        assert_eq!(verified_ibase_warning_and_clamp(10), (10, 0));
        assert_eq!(verified_ibase_warning_and_clamp(16), (16, 0));
        assert_eq!(verified_ibase_warning_and_clamp(17), (16, 1));
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
        assert_eq!(verified_cli_classify_arg(b"-l"), CLI_ARG_OPT_L);
        assert_eq!(verified_cli_classify_arg(b"-"), CLI_ARG_OPT_INVALID);
        assert_eq!(verified_cli_classify_arg(b"-q"), CLI_ARG_OPT_INVALID);
        assert_eq!(verified_cli_classify_arg(b"-ll"), CLI_ARG_OPT_INVALID);
        assert_eq!(verified_cli_classify_arg(b""), CLI_ARG_FILE);
        assert_eq!(verified_cli_classify_arg(b"test.bc"), CLI_ARG_FILE);
        assert_eq!(verified_cli_initial_scale(true), 20);
        assert_eq!(verified_cli_initial_scale(false), 0);
    }

    #[test]
    fn test_fallible_math_operations() {
        let zero = BCNum::zero();
        let ten = BCNum::from_string("10", 10);
        let neg = BCNum::new(BigInt::from(-4), 0);

        assert_eq!(ten.try_div(&zero, 0), Err("division by zero"));
        assert_eq!(ten.try_mod_op(&zero, 0), Err("division by zero"));
        assert_eq!(zero.try_pow(&neg, 0), Err("division by zero"));
        assert_eq!(neg.try_sqrt(0), Err("square root of negative number"));

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
