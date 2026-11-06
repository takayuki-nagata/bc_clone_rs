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

#[cfg(verus_keep_ghost)]
use crate::bigint::big_view;
use crate::bigint::{
    big_abs, big_add, big_add_i64, big_bits, big_clone, big_cmp, big_decimal_digits,
    big_div_mod_floor, big_from_i64, big_from_u64, big_from_usize, big_is_negative, big_is_zero,
    big_isqrt, big_mul, big_neg, big_shl, big_shr, big_signum, big_sub, big_tdiv, big_tdiv_u64,
    big_to_i64,
};
use crate::error::RuntimeError;
use crate::math::{BCNum, pow10_within};
#[cfg(verus_keep_ghost)]
use crate::real_arith::*;
#[cfg(verus_keep_ghost)]
use crate::spec_num;
#[cfg(verus_keep_ghost)]
use crate::spec_num::{lemma_pow10_add, lemma_pow10_pos, spec_pow_int, spec_tdiv, trunc_div};
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

mod atan;
mod ball;
mod bessel;
mod constants;
mod exp;
mod ln;
mod series;
mod sincos;
#[cfg(test)]
mod tests;

pub use atan::bc_atan;
pub use bessel::bc_bessel;
pub use exp::{EXP_ARG_MAX, bc_exp};
pub use ln::bc_ln;
pub use sincos::{bc_cos, bc_sin};

// The submodules share their items through `use super::*`. Outside Verus some of these globs
// bring in nothing that is not also `pub use`d above.
#[allow(
    unused_imports,
    reason = "used by the proofs, which normal builds erase"
)]
use {atan::*, ball::*, bessel::*, constants::*, exp::*, ln::*, series::*, sincos::*};

verus! {

/// The exact result `value` at `scale` digits.
pub(crate) fn exact_result(value: i64, scale: usize) -> (r: BCNum)
    requires
        scale <= u32::MAX,
    ensures
        r.scale == scale,
        big_view(&r.coeff) == value * spec_num::pow10(scale as nat),
{
    BCNum::new(big_mul(&big_from_i64(value), &pow10_within(scale)), scale)
}

/// The integer part of |x|.
pub(crate) fn abs_int_part(x: &BCNum) -> (r: BigInt)
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
pub(crate) fn int_digits(x: &BCNum) -> u64
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

/// The result `r` of `-l`'s function `name` (its bytes) is correct for the arguments `a` (and
/// `b` for `j`): the exact value truncated toward zero at `r.scale` digits (for `l` with
/// a <= 0, GNU's 1 − 10^scale). This is what `bc_sin`, …, `bc_bessel` ensure.
pub open spec fn math_result(name: Seq<u8>, a: BCNum, b: BCNum, r: BCNum) -> bool {
    let p = spec_num::pow10(r.scale as nat);
    let pr = p as real;
    let c = big_view(&r.coeff);
    if name == seq![115u8] {
        c == trunc_r(sin_r(bcnum_real(&a)) * pr)
    } else if name == seq![99u8] {
        c == trunc_r(cos_r(bcnum_real(&a)) * pr)
    } else if name == seq![97u8] {
        c == trunc_r(atan_r(bcnum_real(&a)) * pr)
    } else if name == seq![108u8] {
        if big_view(&a.coeff) > 0 {
            c == trunc_r(ln_r(bcnum_real(&a)) * pr)
        } else {
            c == (1 - p) * p
        }
    } else if name == seq![101u8] {
        c == trunc_r(exp_r(bcnum_real(&a)) * pr)
    } else if name == seq![106u8] {
        c == trunc_r(bessel_int_r(bessel_order(&a), bcnum_real(&b)) * pr)
    } else {
        false
    }
}

/// `r` is a correct result of `-l`'s function `name` for some argument values.
pub open spec fn math_ok(name: Seq<u8>, r: BCNum) -> bool {
    exists|a: BCNum, b: BCNum| #[trigger] math_result(name, a, b, r)
}

/// A witness for `math_ok`.
pub proof fn lemma_math_ok(name: Seq<u8>, a: BCNum, b: BCNum, r: BCNum)
    requires
        math_result(name, a, b, r),
    ensures
        math_ok(name, r),
{
}

} // verus!
