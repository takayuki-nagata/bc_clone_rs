// SPDX-License-Identifier: MIT

//! The evaluator uses numbers only through their L0 values.
//!
//! A `Num` is not normalized (its magnitude may have leading zero digits), so numbers with the
//! same value can differ as sequences. The refinement proofs of `bc_core` relate
//! an implementation number to a specification number by value alone (`to_l0`), so every use of
//! a number must depend only on its value:
//! - arithmetic, comparison, `length`, `scale` and `sqrt` produce results described by value
//!   (`lemma_num_add`, …, `lemma_num_cmp`, `lemma_num_length`, `lemma_num_sqrt`, `lemma_num_pow`),
//!   and conditions test `is_zero_mag` (`lemma_is_zero_mag`);
//! - this module states the remaining uses by value: array subscripts (`array_index`) and register
//!   stores (`store_register`);
//! - `format_num` is characterized by value in `format.rs` (`lemma_format_num`).

// Explicit, because `vstd::prelude` also exports an `array_index`; erased in normal builds.
#[cfg(verus_keep_ghost)]
use crate::eval::array_index;
use crate::eval::*;
use crate::num::*;
use crate::power::*;
use crate::spec_num::*;
use vstd::prelude::*;

verus! {

/// `mag_to_u64` as a function of the value: exact up to `18446744073709551609`, `u64::MAX` above.
/// (The six values just below `u64::MAX` also saturate.)
pub open spec fn sat_u64(x: int) -> u64 {
    if 0 <= x <= 18446744073709551609 { x as u64 } else { u64::MAX }
}

pub proof fn lemma_mag_to_u64_sat(m: Seq<u8>)
    requires
        wf_mag(m),
    ensures
        mag_to_u64(m) == sat_u64(mag_val(m)),
    decreases m.len(),
{
    lemma_split(m);
    if m.len() > 0 {
        let rest = m.drop_first();
        lemma_mag_to_u64_sat(rest);
        lemma_mag_bounds(rest);
        let vr = mag_val(rest);
        if mag_val(m) <= 18446744073709551609 {
            assert(vr <= 1844674407370955160);
        } else {
            assert(vr >= 1844674407370955161);
        }
    }
}

/// The integer part of `|v|`.
pub open spec fn int_mag(v: Num) -> int {
    mag_val(v.mag) / pow10(v.scale as nat)
}

/// `array_index` by value: a subscript is valid when the value is not negative and its integer
/// part is below `BC_DIM_MAX`, and then the index is that integer part.
pub proof fn lemma_array_index_value(v: Num)
    requires
        wf_num(v),
    ensures
        array_index(v).0 <==> (num_coeff(v) >= 0 && int_mag(v) < 16777216),
        array_index(v).0 ==> array_index(v).1 == int_mag(v),
{
    let ip = drop_mag(v.mag, v.scale);
    lemma_drop_mag(v.mag, v.scale);
    lemma_is_zero_mag(v.mag);
    lemma_mag_bounds(v.mag);
    lemma_u64_mag(16777216u64);
    lemma_cmp_mag(ip, u64_mag(16777216u64));
    lemma_mag_to_u64_sat(ip);
    if array_index(v).0 {
        lemma_pow10_pos(v.scale as nat);
        assert(mag_val(ip) == int_mag(v));
        assert(mag_val(u64_mag(16777216u64)) == 16777216);
        assert(cmp_mag(ip, u64_mag(16777216u64)) < 0);
        assert(int_mag(v) < 16777216);
        assert(0 <= int_mag(v)) by (nonlinear_arith)
            requires
                int_mag(v) == mag_val(v.mag) / pow10(v.scale as nat),
                mag_val(v.mag) >= 0,
                pow10(v.scale as nat) >= 1;
        assert(mag_to_u64(ip) == int_mag(v));
        assert((mag_to_u64(ip) as u32) as int == int_mag(v));
    }
}

/// The inputs of `store_register`, by value: whether the value is negative, and its integer part
/// saturated to `u64`.
pub proof fn lemma_register_input(v: Num)
    requires
        wf_num(v),
    ensures
        mag_to_u64(drop_mag(v.mag, v.scale)) == sat_u64(int_mag(v)),
        (v.neg && !is_zero_mag(v.mag)) <==> num_coeff(v) < 0,
{
    lemma_drop_mag(v.mag, v.scale);
    lemma_mag_to_u64_sat(drop_mag(v.mag, v.scale));
    lemma_is_zero_mag(v.mag);
    lemma_mag_bounds(v.mag);
}

/// Numbers with the same value have the same magnitude value and the same integer part.
pub proof fn lemma_same_value(v: Num, w: Num)
    requires
        to_l0(v) == to_l0(w),
    ensures
        mag_val(v.mag) == mag_val(w.mag),
        int_mag(v) == int_mag(w),
        v.scale == w.scale,
{
    lemma_nonneg_mag(v.mag);
    lemma_nonneg_mag(w.mag);
}

/// `mag_val` is never negative (for any digit sequence).
pub proof fn lemma_nonneg_mag(m: Seq<u8>)
    ensures
        mag_val(m) >= 0,
    decreases m.len(),
{
    if m.len() > 0 {
        lemma_nonneg_mag(m.drop_first());
    }
}

/// `store_register` gives the same result for numbers with the same value.
pub proof fn lemma_store_register_value(st: EState, r: u8, v: Num, w: Num)
    requires
        wf_num(v),
        wf_num(w),
        to_l0(v) == to_l0(w),
    ensures
        store_register(st, r, v) == store_register(st, r, w),
{
    lemma_same_value(v, w);
    lemma_register_input(v);
    lemma_register_input(w);
}

/// `array_index` gives the same result for numbers with the same value.
pub proof fn lemma_array_index_congruent(v: Num, w: Num)
    requires
        wf_num(v),
        wf_num(w),
        to_l0(v) == to_l0(w),
    ensures
        array_index(v) == array_index(w),
{
    lemma_same_value(v, w);
    lemma_array_index_value(v);
    lemma_array_index_value(w);
}

} // verus!
