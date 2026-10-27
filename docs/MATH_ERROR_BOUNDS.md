# Error bounds of the math library

`bc_clone -l` returns, for `s(x)`, `c(x)`, `a(x)`, `l(x)`, `e(x)` and `j(n,x)`, the exact
mathematical value truncated toward zero to the current `scale` (`COMPATIBILITY.md` §3.4). This
document gives the argument behind that claim for the implementation in
`crates/bc_core/src/mathlib.rs`. Section numbers are referenced from the code.

## 1. Structure of the argument

1. Every intermediate value is a **ball** `[mid − rad, mid + rad]` in units (ulps) of 10^−p at a
   working precision p. Each operation returns a ball that contains the exact result of the
   operation applied to *any* values of its operands' balls (§2).
2. Infinite series are summed until the next term is small, and a bound on the omitted tail is
   added to the radius (§3). So the final ball contains the exact function value.
3. `certified_trunc` accepts the ball only if every value in it truncates to the same result
   at `scale` digits. Its soundness is proved in Verus (`lemma_certified_truncation`,
   `lemma_certified_truncation_exact` in `verus_proofs.rs`) and property-tested
   (`mathlib::tests::certified_trunc_is_sound`).
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

`mathlib::tests::ball_operations_contain_exact_results` checks containment for random operands.

Series stop when the next term's bound `|mid| + rad` is at most 16 ulps (`TAIL_ULPS`). The radius
of a term settles below that: each step multiplies the previous radius by a factor below 1/2
(once the terms decrease) and adds at most 3 ulps.

## 3. Functions

### Constants

`arc_inv(n)` sums atan(1/n) (alternating) or artanh(1/n) with exact integers:
`power_k = floor(10^p / n^(2k+1))` exactly (nested floor divisions compose), and the term
`floor(power_k / (2k+1))` is below the true term by less than 2 ulps. When `power_k` reaches 0
the next true term is below 1 ulp, and the omitted tail is at most 9/8 of it (n >= 3). The
radius is therefore 2 ulps per term plus 2.

- π = 16·atan(1/5) − 4·atan(1/239) (Machin).
- ln 2 = 2·artanh(1/3).

### Alternating series

For an alternating series whose term magnitudes decrease from term K on, the tail from term K is
at most |term K|. `sum_series` stops only where the caller's `decreasing` condition guarantees
this, and adds |term K|'s bound.

### `s(x)`, `c(x)`

The argument is reduced to r = x − k·2π, k = round(x / 2π) (any integer k is valid). π is
computed with as many extra digits as x has integer digits, so |k|·rad(2π) stays within a few
ulps. Then |r| <= π + ε < 4 and the Taylor terms r^k/k! decrease once (k+1)(k+2) >= r².

### `a(x)`

atan is odd; for |x| > 1, atan|x| = π/2 − atan(1/|x|). Four half-angle steps
y → y / (1 + √(1 + y²)) (each halves the angle) give |y| <= tan(π/64) < 0.05, then
atan y = y − y³/3 + … (alternating, decreasing), and the result is 16·atan y.

### `l(x)`

x = m·2^k with m in [0.7, 1.43) (k chosen from bit lengths; any k is valid since the shift is
part of the ball). ln m = 2·artanh(y), y = (m − 1)/(m + 1), |y| < 0.18. The series terms all have
the sign of y, and the tail after the first omitted term t is at most t / (1 − y²) < 2t.
ln x = ln m + k·ln 2, with ln 2 carrying as many extra digits as k.

### `e(x)`

e^x = e^r·2^n with n = floor(x / ln 2) and r = x − n·ln 2, so |r| < 1 (any integer n is
valid). For k >= 1 the terms r^k/k! satisfy |term k+1| <= |term k| / 2, so the tail is at most
twice the first omitted term. Multiplying by 2^n scales the radius by 2^n, so the guard digits
start at x/2 > 0.4343·x for x > 0 (`bc_exp`).

Arguments with x <= −2.3026·(scale + 1) give e^x < 10^−(scale+1) (2.3026 > ln 10) and return 0
without computation. Arguments whose integer part exceeds 2·10^9 are an error.

### `j(n, x)`

J_n(x) = Σ_m (−1)^m (x/2)^(2m+n) / (m!·(m+n)!) for n >= 0; J_−n = (−1)^n J_n. The terms
decrease once (m+1)(m+n+1) >= (x/2)², and from there the tail is at most the first omitted term.
The terms first grow to about e^|x|, and their radii with them, so the guard digits start at
|x|/2.

For |n| >= 3·⌈|x|⌉ and |n| >= 4·(scale + 1), |J_n(x)| <= (|x|/2)^|n| / |n|! <=
(e·|x| / (2|n|))^|n| <= 2^−|n| < 10^−scale (using |n|! >= (|n|/e)^|n|), so the result is 0
without computation. Orders outside the 64-bit range that are not provably 0, and arguments whose
integer part exceeds 2·10^9, are errors.

## 4. What is and is not machine-checked

- Verus proves the truncation decision (§1.3) over the integers.
- The ball operations (§2) and the series bounds (§3) are argued here and tested
  (`mathlib::tests`, the property tests, `test_math_library_against_high_precision_oracle`, which
  compares with GNU `bc` at `scale + 100`). Machine-checking them is future work.
