// SPDX-License-Identifier: MIT

//! Trusted facts of real analysis about the functions of the `-l` math library.
//!
//! Verus has a `real` type but no theory of limits or series, so the exact values that `-l`
//! approximates are uninterpreted `spec fn`s on `real` (`sin_r`, `exp_r`, …), and the facts
//! the error bounds need are `axiom fn`s: Verus assumes them without proof. They are textbook
//! facts; each names the DLMF section that states it (<https://dlmf.nist.gov>) and, where it
//! is a bound on a series tail, the derivation in one line. Together with `trusted_bigint.rs`
//! and `trusted_std.rs`, this file is the trusted base of the math-library proofs beyond
//! Verus, `vstd`, rustc and Z3. Compiled only under Verus.
//!
//! The series terms and partial sums are ordinary (proved-about, not trusted) definitions. A
//! partial sum `partial_sum(t, k)` is `t(0) + … + t(k − 1)`.
//!
//! Keep every axiom a single, recognizable statement. Where an axiom's precondition is a bound
//! on the argument (`|y| <= 1`, `|r| <= 1`, …), production code checks the bound at run time on
//! the ball rather than relying on an informal argument.

use vstd::prelude::*;

verus! {

// --- Definitions (not trusted) ---

/// |x|.
pub open spec fn abs_r(x: real) -> real {
    if x < 0real {
        -x
    } else {
        x
    }
}

/// x^k.
pub open spec fn pow_r(x: real, k: nat) -> real
    decreases k,
{
    if k == 0 {
        1real
    } else {
        x * pow_r(x, (k - 1) as nat)
    }
}

/// (−1)^k.
pub open spec fn sign_r(k: nat) -> real {
    if k % 2 == 0 {
        1real
    } else {
        -1real
    }
}

/// k!.
pub open spec fn fact(k: nat) -> nat
    decreases k,
{
    if k == 0 {
        1
    } else {
        k * fact((k - 1) as nat)
    }
}

/// t(0) + … + t(k − 1).
pub open spec fn partial_sum(t: spec_fn(nat) -> real, k: nat) -> real
    decreases k,
{
    if k == 0 {
        0real
    } else {
        partial_sum(t, (k - 1) as nat) + t((k - 1) as nat)
    }
}

/// Term k of the Taylor series of sin (`odd == 1`) or cos (`odd == 0`):
/// (−1)^k r^(2k+odd) / (2k+odd)! (DLMF §4.19).
pub open spec fn sin_cos_term(r: real, odd: nat, k: nat) -> real {
    sign_r(k) * pow_r(r, 2 * k + odd) / (fact(2 * k + odd) as real)
}

/// Term k of the series of atan: (−1)^k y^(2k+1) / (2k+1) (DLMF §4.24).
pub open spec fn atan_term(y: real, k: nat) -> real {
    sign_r(k) * pow_r(y, 2 * k + 1) / ((2 * k + 1) as real)
}

/// Term k of the series of artanh: y^(2k+1) / (2k+1) (DLMF §4.38 with §4.37).
pub open spec fn artanh_term(y: real, k: nat) -> real {
    pow_r(y, 2 * k + 1) / ((2 * k + 1) as real)
}

/// Term k of the series of exp: r^k / k! (DLMF §4.2).
pub open spec fn exp_term(r: real, k: nat) -> real {
    pow_r(r, k) / (fact(k) as real)
}

/// Term m of the series of J_n(x), with h = x/2: (−1)^m h^(2m+n) / (m!·(m+n)!) (DLMF §10.2).
pub open spec fn bessel_term(n: nat, h: real, m: nat) -> real {
    sign_r(m) * pow_r(h, 2 * m + n) / ((fact(m) * fact(m + n)) as real)
}

/// artanh y = ln((1 + y)/(1 − y)) / 2 for |y| < 1 (DLMF §4.37).
pub open spec fn artanh_r(y: real) -> real {
    ln_r((1real + y) / (1real - y)) / 2real
}

/// ln 2.
pub open spec fn ln2_r() -> real {
    ln_r(2real)
}

/// `-l`'s `j(n, x)` for an integer order: J_n(x), with J_−n(x) = (−1)^n J_n(x) (DLMF §10.4).
pub open spec fn bessel_int_r(n: int, x: real) -> real {
    if n >= 0 {
        bessel_r(n as nat, x)
    } else {
        sign_r((-n) as nat) * bessel_r((-n) as nat, x)
    }
}

// --- The functions (uninterpreted) ---

/// The nonnegative square root (of a nonnegative argument).
pub uninterp spec fn sqrt_r(x: real) -> real;

/// π.
pub uninterp spec fn pi_r() -> real;

/// sin x.
pub uninterp spec fn sin_r(x: real) -> real;

/// cos x.
pub uninterp spec fn cos_r(x: real) -> real;

/// atan x, the principal value in (−π/2, π/2).
pub uninterp spec fn atan_r(x: real) -> real;

/// e^x.
pub uninterp spec fn exp_r(x: real) -> real;

/// ln x (of a positive argument).
pub uninterp spec fn ln_r(x: real) -> real;

/// The Bessel function of the first kind J_n(x), for an order n >= 0.
pub uninterp spec fn bessel_r(n: nat, x: real) -> real;

// --- Axioms ---

/// The square root of x >= 0 is the nonnegative number whose square is x.
pub axiom fn axiom_sqrt(x: real)
    requires
        x >= 0real,
    ensures
        sqrt_r(x) >= 0real,
        sqrt_r(x) * sqrt_r(x) == x,
;

/// sin and cos have period 2π (DLMF §4.14).
pub axiom fn axiom_sin_cos_periodic(x: real, k: int)
    ensures
        sin_r(x + 2real * (k as real) * pi_r()) == sin_r(x),
        cos_r(x + 2real * (k as real) * pi_r()) == cos_r(x),
;

/// The alternating-series bound for the Taylor series of sin (`odd == 1`) and cos (`odd == 0`):
/// if (2K+odd+1)(2K+odd+2) >= r², the term magnitudes decrease from term K on (the ratio of
/// term j+1 to term j is −r²/((2j+odd+1)(2j+odd+2))), so the tail from term K is at most
/// |term K|.
pub axiom fn axiom_sin_cos_series(r: real, odd: nat, k: nat)
    requires
        odd <= 1,
        ((2 * k + odd + 1) * (2 * k + odd + 2)) as real >= r * r,
    ensures
        abs_r((if odd == 1 { sin_r(r) } else { cos_r(r) }) - partial_sum(
            |j: nat| sin_cos_term(r, odd, j),
            k,
        )) <= abs_r(sin_cos_term(r, odd, k)),
;

/// atan is odd (DLMF §4.24).
pub axiom fn axiom_atan_odd(x: real)
    ensures
        atan_r(-x) == -atan_r(x),
;

/// atan x + atan(1/x) = π/2 for x > 0 (DLMF §4.24).
pub axiom fn axiom_atan_inverse(x: real)
    requires
        x > 0real,
    ensures
        atan_r(x) + atan_r(1real / x) == pi_r() / 2real,
;

/// The half-angle formula: atan y = 2·atan(y / (1 + √(1 + y²))), from
/// tan(θ/2) = tan θ / (1 + sec θ) with sec θ = √(1 + tan² θ) for |θ| < π/2 (DLMF §4.21).
pub axiom fn axiom_atan_half(y: real)
    ensures
        atan_r(y) == 2real * atan_r(y / (1real + sqrt_r(1real + y * y))),
;

/// The alternating-series bound for atan: for |y| <= 1 the terms y^(2k+1)/(2k+1) decrease in
/// magnitude, so the tail from term K is at most |term K| (DLMF §4.24).
pub axiom fn axiom_atan_series(y: real, k: nat)
    requires
        abs_r(y) <= 1real,
    ensures
        abs_r(atan_r(y) - partial_sum(|j: nat| atan_term(y, j), k)) <= abs_r(atan_term(y, k)),
;

/// Machin's formula, π = 16·atan(1/5) − 4·atan(1/239) (Machin, 1706); it follows from the addition formula for
/// atan (DLMF §4.24).
pub axiom fn axiom_machin()
    ensures
        pi_r() == 16real * atan_r(1real / 5real) - 4real * atan_r(1real / 239real),
;

/// ln(a·b) = ln a + ln b for a, b > 0 (DLMF §4.8).
pub axiom fn axiom_ln_mul(a: real, b: real)
    requires
        a > 0real,
        b > 0real,
    ensures
        ln_r(a * b) == ln_r(a) + ln_r(b),
;

/// The bound on the tail of the artanh series for |y| < 1: every term from K on has the sign
/// of y and |term k| <= |term K|·y^(2(k−K)), so the tail is at most |term K| / (1 − y²)
/// (DLMF §4.38 with §4.37).
pub axiom fn axiom_artanh_series(y: real, k: nat)
    requires
        abs_r(y) < 1real,
    ensures
        abs_r(artanh_r(y) - partial_sum(|j: nat| artanh_term(y, j), k)) <= abs_r(
            artanh_term(y, k),
        ) / (1real - y * y),
;

/// e^(ln x) = x for x > 0 (DLMF §4.2).
pub axiom fn axiom_exp_ln(x: real)
    requires
        x > 0real,
    ensures
        exp_r(ln_r(x)) == x,
;

/// e^(a+b) = e^a·e^b (DLMF §4.8).
pub axiom fn axiom_exp_add(a: real, b: real)
    ensures
        exp_r(a + b) == exp_r(a) * exp_r(b),
;

/// e^z >= 1 + z (DLMF §4.5).
pub axiom fn axiom_exp_ge(z: real)
    ensures
        exp_r(z) >= 1real + z,
;

/// The bound on the tail of the exponential series for |r| <= 1 and K >= 1: the ratio of term
/// k+1 to term k is r/(k+1), at most 1/2 in magnitude, so the tail from term K is at most
/// 2·|term K| (DLMF §4.2).
pub axiom fn axiom_exp_series(r: real, k: nat)
    requires
        abs_r(r) <= 1real,
        k >= 1,
    ensures
        abs_r(exp_r(r) - partial_sum(|j: nat| exp_term(r, j), k)) <= 2real * abs_r(
            exp_term(r, k),
        ),
;

/// The alternating-series bound for the Bessel series with h = x/2: if (K+1)(K+n+1) >= h², the
/// term magnitudes decrease from term K on (the ratio of term m+1 to term m is
/// −h²/((m+1)(m+n+1))), so the tail from term K is at most |term K| (DLMF §10.2).
pub axiom fn axiom_bessel_series(n: nat, x: real, k: nat)
    requires
        ((k + 1) * (k + n + 1)) as real >= (x / 2real) * (x / 2real),
    ensures
        abs_r(bessel_r(n, x) - partial_sum(|m: nat| bessel_term(n, x / 2real, m), k)) <= abs_r(
            bessel_term(n, x / 2real, k),
        ),
;

/// |J_n(x)| <= |x/2|^n / n! for an integer order n >= 0 and real x (DLMF §10.14).
pub axiom fn axiom_bessel_bound(n: nat, x: real)
    ensures
        abs_r(bessel_r(n, x)) <= pow_r(abs_r(x / 2real), n) / (fact(n) as real),
;

} // verus!
