# Error bounds of the math library

`bc_clone -l` returns, for `s(x)`, `c(x)`, `a(x)`, `l(x)`, `e(x)` and `j(n,x)`, the exact
mathematical value truncated toward zero to the current `scale` (`COMPATIBILITY.md` §3.4). This
document gives the argument behind that claim for the implementation in
`crates/bc_core/src/mathlib/`. Section numbers are referenced from the code.

## 1. Structure of the argument

1. Every intermediate value is a **ball** `[mid − rad, mid + rad]` in units (ulps) of 10^−p at a
   working precision p. Each operation returns a ball that contains the exact result of the
   operation applied to *any* values of its operands' balls (§2).
2. Infinite series are summed until the next term is small, and a bound on the omitted tail is
   added to the radius (§3). So the final ball contains the exact function value.
3. `certified_trunc` accepts the ball only if every value in it truncates to the same result
   at `scale` digits. Its soundness is proved in Verus over the reals (in place, with
   `lemma_certified_trunc_real` and `lemma_certified_trunc_real_exact` in `real_arith.rs`) and
   property-tested (`mathlib::tests::certified_trunc_is_sound`).
4. If the ball is rejected, `certify` doubles the guard digits p − scale and recomputes (Ziv's
   strategy). The radii shrink in proportion to 10^−p, so the loop ends unless the exact value is
   itself a truncation boundary k·10^−scale. That happens only for the exact cases handled before
   any computation: `s(0)`, `c(0)`, `a(0)`, `e(0)`, `l(1)`, `j(n,0)`. For every other rational
   argument the value is transcendental (Lindemann–Weierstrass for `e^x`, `ln x`, `sin x`,
   `cos x`, `atan x`; Siegel for `J_n(x)`), so it is not a boundary.

The working precision is capped at 3·10^9 digits (`MAX_WORKING_PREC`); reaching it is reported
as `argument too large`. With the argument limits of `COMPATIBILITY.md` §2 the cap is not reached
in practice.

## 2. Ball operations

Let A = a·10^p denote a value in ulps, with ball (MA, RA), so |A − MA| <= RA.

| Operation | Midpoint | Radius | Reason |
|---|---|---|---|
| A ± B | MA ± MB | RA + RB | triangle inequality |
| k·A (integer k) | k·MA | \|k\|·RA | exact scaling |
| A / k (integer k > 0) | trunc(MA / k) | ⌈RA / k⌉ + 1 | truncation error < 1 |
| A·2^n | MA·2^n | RA·2^n | exact |
| A / 2^n | floor(MA / 2^n) | ⌈RA / 2^n⌉ + 1 | floor error < 1 |
| precision p → p − d | trunc(MA / 10^d) | ⌈RA / 10^d⌉ + 1 | truncation error < 1 |
| A·B | trunc(MA·MB / 10^p) | ⌈(\|MA\|·RB + \|MB\|·RA + RA·RB) / 10^p⌉ + 1 | \|AB − MA·MB\| = \|MA·δB + MB·δA + δA·δB\| |
| A / B (requires \|MB\| > RB) | trunc(MA·10^p / MB) | ⌈10^p·(RA·\|MB\| + \|MA\|·RB) / ((\|MB\| − RB)·\|MB\|)⌉ + 1 | A/B − MA/MB = (δA·MB − MA·δB) / (B·MB) and \|B\| >= \|MB\| − RB |
| √A (requires MA >= RA, MA·10^p >= 1) | isqrt(MA·10^p) | ⌈RA·10^p / isqrt(MA·10^p)⌉ + 1 | \|√(A·10^p) − √(MA·10^p)\| = \|δA\|·10^p / (√(A·10^p) + √(MA·10^p)) |

Verus proves each row in place (`Ball` in `mathlib/ball.rs`, lemmas `lemma_ball_*` in
`real_arith.rs`): for all reals in the operands' balls, the result's ball contains the exact
result. `mathlib::tests::ball_operations_contain_exact_results` also checks containment for
random operands.

Series stop when the next term's bound `|mid| + rad` is at most 16 ulps (`TAIL_ULPS`). The radius
of a term settles below that: each step multiplies the previous radius by a factor below 1/2
(once the terms decrease) and adds at most 3 ulps. (This is why the loop ends; the proofs do not
depend on it, see §4.)

## 3. Functions

### Constants

`arc_inv(n)` sums atan(1/n) (alternating) or artanh(1/n) with exact integers:
`power_k = floor(10^p / n^(2k+1))` exactly (nested floor divisions compose), and the term
`floor(power_k / (2k+1))` is below the true term by less than 2 ulps. When `power_k` reaches 0
the next true term is below 1 ulp, and the omitted tail is at most 9/8 of it (n >= 3). The
radius is therefore 2 ulps per term plus 2.

- π = 16·atan(1/5) − 4·atan(1/239) (Machin).
- ln 2 = 2·artanh(1/3).

Verus proves this in place (`arc_inv`, `pi`, `ln2`): the loop invariant is `power_k =
⌊10^p / n^(2k+1)⌋` and |10^p·S_k − sum| <= 2k for the true partial sum S_k; each term is within
2 ulps (`lemma_arc_term`); the loop ends because `power` decreases, and k <= 4p because
n^(2k+1) <= 10^p <= 2^(4p). The tail is bounded by `axiom_atan_series` and
`axiom_artanh_series` (with 1 − 1/n² >= 8/9).

### Series

For an alternating series whose term magnitudes decrease from term K on, the tail from term K is
at most |term K|. `sum_series` stops only where `Series::decreasing` guarantees this, and adds
|term K|'s bound times the tail factor: 1 for the alternating series (sin, cos, atan, J_n), 2 for
the geometric tails of artanh (y² <= 1/2) and exp (|r| <= 1).

Verus proves `sum_series` in place: each step (`Series::next`) builds a ball that contains the
next true term, from the identities between consecutive terms (`lemma_sin_cos_term_step`,
`lemma_exp_term_step`, `lemma_bessel_term_step`, `lemma_atan_power_step`); the partial sum's ball
contains the true partial sum; and at the stopping point the tail axiom of the series
(`lemma_series_tail`) widens it to contain the series' value. The tail axioms of atan, artanh and
exp need a bound on the argument; `Series::tail_applies` checks it on the ball before summing
(and returns `None`, so that `certify` retries, if it fails; the library's arguments are far
inside the bounds). The decrease condition is checked on the ball of r² or h²
(`Series::decreasing`, through `bounded`).

### `s(x)`, `c(x)`

The argument is reduced to r = x − k·2π, k = round(x / 2π) (any integer k is valid). π is
computed with as many extra digits as x has integer digits, so |k|·rad(2π) stays within a few
ulps. Then |r| <= π + ε < 4 and the Taylor terms r^k/k! decrease once (k+1)(k+2) >= r².

Verus proves `bc_sin` and `bc_cos` in place: `reduce_angle` returns a ball that contains
x − k·2π for some integer k (it takes k = 0 if the midpoint of 2π were not positive, and returns
`None` if the working precision would exceed `u32::MAX`), `axiom_sin_cos_periodic` carries the
series' value back to x, and sin 0 = 0, cos 0 = 1 follow from the series' tail bound.

### `a(x)`

atan is odd; for |x| > 1, atan|x| = π/2 − atan(1/|x|). Four half-angle steps
y → y / (1 + √(1 + y²)) (each halves the angle) give |y| <= tan(π/64) < 0.05, then
atan y = y − y³/3 + … (alternating, decreasing), and the result is 16·atan y.

Verus proves `bc_atan` in place: the loop invariant is atan y₀ = 2^i·atan yᵢ
(`axiom_atan_half`), the inversion uses `axiom_atan_inverse`, the sign `axiom_atan_odd`, and
atan 0 = 0 follows from oddness.

### `l(x)`

x = m·2^k with m in [0.7, 1.43) (k chosen from bit lengths; any k is valid since the shift is
part of the ball). ln m = 2·artanh(y), y = (m − 1)/(m + 1), |y| < 0.18. The series terms all have
the sign of y, and the tail after the first omitted term t is at most t / (1 − y²) < 2t.
ln x = ln m + k·ln 2, with ln 2 carrying as many extra digits as k.

Verus proves `bc_ln` in place: the search for k keeps a ball of x·2^−k (any k is valid,
`lemma_ln_scaled`, from `axiom_ln_mul`); 2·artanh((m − 1)/(m + 1)) = ln m follows from the
definition of artanh (`lemma_artanh_of_cayley`); and ln 1 = 0 from `axiom_ln_mul`. For x <= 0
the result is the documented 1 − 10^scale. The search returns `None` if k would leave the range
of `i64`, and so does `ln_ball` if the working precision of ln 2 would exceed `u32::MAX`.

### `e(x)`

e^x = e^r·2^n with n = floor(x / ln 2) and r = x − n·ln 2, so |r| < 1 (any integer n is
valid). For k >= 1 the terms r^k/k! satisfy |term k+1| <= |term k| / 2, so the tail is at most
twice the first omitted term. Multiplying by 2^n scales the radius by 2^n, so the guard digits
start at x/2 > 0.4343·x for x > 0 (`bc_exp`).

Arguments with x <= −2.3026·(scale + 1) give e^x < 10^−(scale+1) (2.3026 > ln 10) and return 0
without computation. Arguments whose integer part exceeds 2·10^9 are an error.

Verus proves `bc_exp` in place: e^(n·ln 2) = 2^n (`lemma_exp_n_ln2`, from `axiom_exp_ln` and
`axiom_exp_add`), and any integer n is valid (n = 0 if the midpoint of ln 2 were not positive).
For the shortcut, `lemma_exp_23026` shows e^2.3026 > 10: with z = 2.3026/4, the tail bound of
the series after nine terms gives e^z >= 1.778284 (exact rational arithmetic), and
1.778284^4 > 10; monotonicity and positivity of e^x follow from `axiom_exp_ge` and
`axiom_exp_add`. `exp_ball` returns `None` if the working precision would exceed `u32::MAX`.

### `j(n, x)`

J_n(x) = Σ_m (−1)^m (x/2)^(2m+n) / (m!·(m+n)!) for n >= 0; J_−n = (−1)^n J_n. The terms
decrease once (m+1)(m+n+1) >= (x/2)², and from there the tail is at most the first omitted term.
The terms first grow to about e^|x|, and their radii with them, so the guard digits start at
|x|/2.

For |n| >= 3·⌈|x|⌉ and |n| >= 4·(scale + 1), |J_n(x)| <= (|x|/2)^|n| / |n|! <=
(3·|x| / |n|)^|n|·2^−|n| <= 2^−|n| < 10^−(scale+1) (using |n|! >= (|n|/3)^|n|), so the result is 0
without computation. Orders outside the 64-bit range that are not provably 0, and arguments whose
integer part exceeds 2·10^9, are errors.

Verus proves `bc_bessel` in place. The shortcut uses `axiom_bessel_bound` and
`lemma_fact_lower` (n^n <= 3^n·n!, by induction: (1 + 1/n)^n <= (e^(1/n))^n = e <= 2.75, from
`axiom_exp_ge` and the tail bound of the exponential series), and 2^−4K·10^K <= 5/8
(`lemma_half_pow`). J_n(0) (1 for n = 0, else 0) follows from the series' tail bound. Negative
orders use the definition J_−n = (−1)^n J_n (`bessel_int_r`), and the first term
(x/2)^n / n! is built by a loop with that invariant.

## 4. What is and is not machine-checked

- Verus proves, in place and over the reals, the end-to-end theorem for each of `s`, `c`, `a`,
  `l`, `e` and `j`: an `Ok` result has the caller's scale and is the exact value truncated toward
  zero at that scale (`l(x)` for x <= 0 is the documented 1 − 10^scale). This covers §1 (the
  truncation decision and the retry loop of `certify`, which ends at `MAX_WORKING_PREC` at the
  latest), §2 (every ball operation), and §3 (the constants, every series with its tail bound,
  and every argument reduction).
- The proofs assume the facts of real analysis stated as axioms in
  `crates/bc_core/src/trusted_math.rs` (each with its DLMF section), the `num-bigint` wrappers in
  `trusted_bigint.rs`, and Verus, Z3 and rustc.
- They are partial correctness: that a series loop (and the search for k in `l(x)`) ends is argued
  in §2, not proved. The evaluator calls the functions from `Evaluator::eval_math`, which is
  verified: it establishes their preconditions and ensures that an `Ok` result is the function's
  exact value at some argument values (`mathlib::math_ok`). The math library is not part of the
  refinement theorem of the evaluator (`r_state` excludes `-l`), so which argument values is not
  stated.
- The tests remain (`mathlib::tests`, the property tests, and
  `test_math_library_against_high_precision_oracle`, which compares with GNU `bc` at
  `scale + 100`).
