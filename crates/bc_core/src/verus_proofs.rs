// SPDX-License-Identifier: MIT

//! Formal verification specifications, lemmas, and verified core algorithms for `bc_core` using Verus.
//!
//! This module is verified by the Verus SMT prover (`scripts/run_verus_verification.sh`)
//! and compiled only under `#[cfg(verus_keep_ghost)]`, ensuring zero overhead or coverage impact
//! on standard `#![no_std]` and embedded target builds.

use vstd::prelude::*;

verus! {

// ============================================================================
// Target 1: POSIX `bc` Scale Rules, Shift Calculations & Fixed-Point Arithmetic
// ============================================================================

/// Maximum verified scale bound to prevent `usize` / `i64` arithmetic overflow
/// during scale and exponent shift calculations.
pub const MAX_VERIFIED_SCALE: usize = 1_000_000_000;

/// Mathematical specification of $10^n$ over arbitrary-precision natural numbers.
pub open spec fn pow10(n: nat) -> int
    decreases n,
{
    if n == 0 {
        1
    } else {
        10 * pow10((n - 1) as nat)
    }
}

/// Lemma: $10^n \ge 1$ for all $n \ge 0$.
pub proof fn lemma_pow10_pos(n: nat)
    ensures
        pow10(n) >= 1,
    decreases n,
{
    if n > 0 {
        lemma_pow10_pos((n - 1) as nat);
    }
}

/// Lemma: $10^{a + b} == 10^a \cdot 10^b$ for all $a, b \ge 0$.
pub proof fn lemma_pow10_add(a: nat, b: nat)
    ensures
        pow10(a + b) == pow10(a) * pow10(b),
    decreases a,
{
    if a == 0 {
        assert(0 + b == b);
        assert(pow10(0) == 1);
    } else {
        lemma_pow10_add((a - 1) as nat, b);
        assert((a - 1) as nat + b == (a + b - 1) as nat);
        assert(pow10(a) * pow10(b) == (10 * pow10((a - 1) as nat)) * pow10(b));
        assert((10 * pow10((a - 1) as nat)) * pow10(b) == 10 * (pow10((a - 1) as nat) * pow10(b)))
            by (nonlinear_arith);
    }
}

/// Abstract specification model of `BCNum` representing $\text{coeff} \times 10^{-\text{scale}}$.
pub ghost struct SpecBCNum {
    pub coeff: int,
    pub scale: nat,
}

impl SpecBCNum {
    /// Returns the numerator when normalized to `target_scale` ($\ge \text{self.scale}$).
    pub open spec fn scaled_coeff(self, target_scale: nat) -> int
        recommends
            target_scale >= self.scale,
    {
        self.coeff * pow10((target_scale - self.scale) as nat)
    }

    /// Mathematical specification of `BCNum::add`.
    pub open spec fn spec_add(self, other: SpecBCNum) -> SpecBCNum {
        let sr = if self.scale >= other.scale { self.scale } else { other.scale };
        SpecBCNum {
            coeff: self.scaled_coeff(sr) + other.scaled_coeff(sr),
            scale: sr,
        }
    }

    /// Mathematical specification of `BCNum::sub`.
    pub open spec fn spec_sub(self, other: SpecBCNum) -> SpecBCNum {
        let sr = if self.scale >= other.scale { self.scale } else { other.scale };
        SpecBCNum {
            coeff: self.scaled_coeff(sr) - other.scaled_coeff(sr),
            scale: sr,
        }
    }
}

/// Proof that `BCNum` addition is commutative and subtraction is the exact inverse of addition
/// when scales match or are bounded by `other.scale <= self.scale`.
pub proof fn lemma_bcnum_add_sub_properties(a: SpecBCNum, b: SpecBCNum)
    ensures
        a.spec_add(b) == b.spec_add(a),
        a.scale >= b.scale ==> a.spec_add(b).spec_sub(b) == a,
{
    let sr = if a.scale >= b.scale { a.scale } else { b.scale };
    if a.scale >= b.scale {
        assert(sr == a.scale);
        assert((sr - a.scale) as nat == 0);
        assert(pow10(0) == 1);
        assert(a.scaled_coeff(sr) == a.coeff);
        let sum = a.spec_add(b);
        assert(sum.scale == a.scale);
        assert(sum.scaled_coeff(sr) == sum.coeff);
    }
}

/// Verified POSIX scale and shift calculation for `BCNum::add` and `BCNum::sub`.
///
/// Mirrors `crates/bc_core/src/math.rs` (`BCNum::add` / `BCNum::sub`).
pub fn verified_add_sub_scales(self_scale: usize, other_scale: usize) -> (res: (usize, usize, usize))
    ensures
        res.0 == if self_scale >= other_scale { self_scale } else { other_scale },
        res.1 == res.0 - self_scale,
        res.2 == res.0 - other_scale,
        res.0 >= self_scale && res.0 >= other_scale,
        (res.1 == 0 || res.2 == 0),
{
    let sr = if self_scale >= other_scale { self_scale } else { other_scale };
    let shift_a = sr - self_scale;
    let shift_b = sr - other_scale;
    (sr, shift_a, shift_b)
}

/// POSIX specification for multiplication scale:
/// $\min(a + b, \max(\text{global\_scale}, \max(a, b)))$.
pub open spec fn spec_posix_mul_scale(a: nat, b: nat, global_scale: nat) -> nat {
    let max_ab = if a >= b { a } else { b };
    let max_all = if global_scale >= max_ab { global_scale } else { max_ab };
    if a + b <= max_all {
        a + b
    } else {
        max_all
    }
}

/// Verified POSIX scale and truncation shift calculation for `BCNum::mul`.
///
/// POSIX IEEE Std 1003.1 mandates:
/// `scale(a * b) = min(scale(a) + scale(b), max(scale, scale(a), scale(b)))`.
/// Furthermore, proves that `exact_scale >= sr` always holds (i.e., `diff >= 0`),
/// guaranteeing that multiplication never requires negative truncation shifts.
pub fn verified_mul_scale_and_shift(
    self_scale: usize,
    other_scale: usize,
    global_scale: usize,
) -> (res: (usize, usize, usize))
    requires
        self_scale <= MAX_VERIFIED_SCALE,
        other_scale <= MAX_VERIFIED_SCALE,
        global_scale <= MAX_VERIFIED_SCALE,
    ensures
        // res = (sr, exact_scale, truncation_diff)
        res.1 == self_scale + other_scale,
        res.0 <= res.1,
        res.0 >= self_scale || res.0 >= other_scale,
        res.2 == res.1 - res.0,
        // Exact match with POSIX specification:
        res.0 as nat == spec_posix_mul_scale(
            self_scale as nat,
            other_scale as nat,
            global_scale as nat,
        ),
{
    let max_ab = if self_scale >= other_scale { self_scale } else { other_scale };
    let max_all = if global_scale >= max_ab { global_scale } else { max_ab };
    let exact_scale = self_scale + other_scale;
    let sr = if exact_scale <= max_all { exact_scale } else { max_all };
    let diff = exact_scale - sr;
    (sr, exact_scale, diff)
}

/// Verified POSIX scale and signed decimal shift calculation for `BCNum::div`.
///
/// Mirrors `crates/bc_core/src/math.rs` (`BCNum::div`):
/// `sr = global_scale`, `shift = other.scale - self.scale + sr`.
pub fn verified_div_scale_and_shift(
    self_scale: usize,
    other_scale: usize,
    global_scale: usize,
) -> (res: (usize, i64))
    requires
        self_scale <= MAX_VERIFIED_SCALE,
        other_scale <= MAX_VERIFIED_SCALE,
        global_scale <= MAX_VERIFIED_SCALE,
    ensures
        res.0 == global_scale,
        res.1 == (other_scale as int) - (self_scale as int) + (global_scale as int),
{
    let sr = global_scale;
    let shift: i64 = (other_scale as i64) - (self_scale as i64) + (sr as i64);
    (sr, shift)
}

/// Verified POSIX scale and radicand shift calculation for `BCNum::sqrt`.
///
/// Mirrors `crates/bc_core/src/math.rs` (`BCNum::sqrt`):
/// `sr = max(self.scale, global_scale)`, `shift = 2 * sr - self.scale`.
/// Proves that `2 * sr >= self.scale` always holds without underflow, and that
/// shifting the radicand by `shift` yields an exact square scale `self.scale + shift == 2 * sr`.
pub fn verified_sqrt_scale_and_shift(
    self_scale: usize,
    global_scale: usize,
) -> (res: (usize, usize))
    requires
        self_scale <= MAX_VERIFIED_SCALE,
        global_scale <= MAX_VERIFIED_SCALE,
    ensures
        res.0 == if self_scale >= global_scale { self_scale } else { global_scale },
        res.0 >= self_scale,
        res.0 >= global_scale,
        res.1 == 2 * res.0 - self_scale,
        self_scale + res.1 == 2 * res.0,
{
    let sr = if self_scale >= global_scale { self_scale } else { global_scale };
    let shift = 2 * sr - self_scale;
    (sr, shift)
}

/// Proof of POSIX `bc` modulo identity and truncation error bound:
/// When `q = (a * 10^shift) / b` (integer truncating division for `a >= 0, b > 0`),
/// the remainder `r = a * 10^shift - q * b` satisfies `0 <= r < b`.
pub proof fn lemma_truncating_div_mod_bounds(num: int, den: int)
    requires
        num >= 0,
        den > 0,
    ensures
        0 <= num - (num / den) * den,
        num - (num / den) * den < den,
        (num / den) * den + (num % den) == num,
{
    assert((num / den) * den + (num % den) == num) by (nonlinear_arith)
        requires
            num >= 0,
            den > 0,
    ;
    assert(0 <= num % den && num % den < den) by (nonlinear_arith)
        requires
            num >= 0,
            den > 0,
    ;
}

// ============================================================================
// Target 2: Non-Decimal `obase` Fractional Digit Count Termination & Minimality
// ============================================================================

/// Mathematical specification of $\text{base}^{\text{exp}}$ over natural numbers.
pub open spec fn pow_base(base: nat, exp: nat) -> nat
    decreases exp,
{
    if exp == 0 {
        1
    } else {
        base * pow_base(base, (exp - 1) as nat)
    }
}

/// Lemma: For $\text{base} \ge 1$, $\text{base}^{\text{exp}} \ge 1$.
pub proof fn lemma_pow_base_pos(base: nat, exp: nat)
    requires
        base >= 1,
    ensures
        pow_base(base, exp) >= 1,
    decreases exp,
{
    if exp > 0 {
        lemma_pow_base_pos(base, (exp - 1) as nat);
        assert(base * pow_base(base, (exp - 1) as nat) >= 1 * 1) by (nonlinear_arith)
            requires
                base >= 1,
                pow_base(base, (exp - 1) as nat) >= 1,
        ;
    }
}

/// Lemma: For $\text{base} \ge 2$, $\text{base}^{\text{exp} + 1} > \text{base}^{\text{exp}}$.
pub proof fn lemma_pow_base_strictly_increasing(base: nat, exp: nat)
    requires
        base >= 2,
    ensures
        pow_base(base, exp + 1) == base * pow_base(base, exp),
        pow_base(base, exp + 1) > pow_base(base, exp),
{
    lemma_pow_base_pos(base, exp);
    let p = pow_base(base, exp);
    assert(pow_base(base, exp + 1) == base * p);
    assert(base * p >= 2 * p) by (nonlinear_arith)
        requires
            base >= 2,
            p >= 1,
    ;
}

/// Verified calculation of the minimum fractional digit count $k$ in base `obase`
/// such that $\text{obase}^k \ge \text{target}$ (where $\text{target} = 10^{\text{scale}}$).
///
/// Mirrors the `#![no_std]` floating-point-free loop in `crates/bc_core/src/math.rs` (`format_obase`):
/// proves both loop termination (`decreases target - current`) and exact minimality of $k$:
/// $\text{obase}^k \ge \text{target}$ and ($k > 0 \implies \text{obase}^{k-1} < \text{target}$).
pub fn verified_obase_frac_digits(obase: u64, target: u64, max_bound: u64) -> (res: (usize, u64))
    requires
        obase >= 2,
        target >= 1,
        // Ensure `current * obase` will not overflow u64 before reaching `target`
        target <= max_bound,
        max_bound <= usize::MAX as u64,
        max_bound * (obase as int) <= u64::MAX as int,
    ensures
        res.1 as nat == pow_base(obase as nat, res.0 as nat),
        res.1 >= target,
        pow_base(obase as nat, res.0 as nat) >= target as nat,
        res.0 > 0 ==> pow_base(obase as nat, (res.0 - 1) as nat) < target as nat,
        res.0 == 0 <==> target == 1,
{
    let mut k: usize = 0;
    let mut current: u64 = 1;

    while current < target
        invariant
            obase >= 2,
            target >= 1,
            target <= max_bound,
            max_bound <= usize::MAX as u64,
            max_bound * (obase as int) <= u64::MAX as int,
            current >= 1,
            current as nat == pow_base(obase as nat, k as nat),
            (k as int) < (current as int),
            k > 0 ==> pow_base(obase as nat, (k - 1) as nat) < target as nat,
            k == 0 <==> current == 1,
        decreases
            if current < target {
                target - current
            } else {
                0
            },
    {
        let prev_current = current;
        let prev_k = k;

        proof {
            lemma_pow_base_strictly_increasing(obase as nat, prev_k as nat);
            assert((prev_current as int) * (obase as int) <= (max_bound as int) * (obase as int))
                by (nonlinear_arith)
                requires
                    prev_current < target,
                    target <= max_bound,
                    obase >= 2,
            ;
            assert((prev_current as int) * (obase as int) >= (prev_current as int) * 2)
                by (nonlinear_arith)
                requires
                    prev_current >= 1,
                    obase >= 2,
            ;
            assert((prev_k as int) + 1 < (prev_current as int) * (obase as int))
                by (nonlinear_arith)
                requires
                    (prev_k as int) < (prev_current as int),
                    prev_current >= 1,
                    (prev_current as int) * (obase as int) >= (prev_current as int) * 2,
            ;
        }

        current = current * obase;
        k = k + 1;
    }

    proof {
        if k > 0 {
            lemma_pow_base_pos(obase as nat, (k - 1) as nat);
        }
    }

    (k, current)
}

// ============================================================================
// Target 3: POSIX 70-Char Line Wrapping (`WrappedStdout`) & `Lexer` Safety
// ============================================================================

/// Maximum column index before POSIX `bc` emits a `\\\n` continuation (68 chars + `\` + `\n` = 70 chars).
pub const POSIX_WRAP_COL_LIMIT: usize = 68;

/// Verified single-character state transition for `WrappedStdout` (`crates/bc_core/src/eval.rs`).
///
/// Returns `(next_col, emitted_backslash_newline)`.
/// Proves that if `col <= 68`, then `next_col <= 68` holds unconditionally, and whenever
/// a line wrap (`\\\n`, 2 characters) is emitted, the line length including `\\\n` is at most 70.
pub fn verified_wrapped_stdout_step(col: usize, is_newline: bool) -> (res: (usize, bool))
    requires
        col <= POSIX_WRAP_COL_LIMIT,
    ensures
        res.0 <= POSIX_WRAP_COL_LIMIT,
        is_newline ==> (res.0 == 0 && !res.1),
        (!is_newline && col < POSIX_WRAP_COL_LIMIT) ==> (res.0 == col + 1 && !res.1),
        (!is_newline && col == POSIX_WRAP_COL_LIMIT) ==> (res.0 == 1 && res.1 && col + 2 <= 70),
{
    if is_newline {
        (0, false)
    } else if col >= POSIX_WRAP_COL_LIMIT {
        // Emits "\\\n" (resets column to 0), then emits the character (col becomes 1)
        (1, true)
    } else {
        (col + 1, false)
    }
}

/// Verified multi-character stream processing loop for `WrappedStdout::write_str`.
///
/// Proves that across an arbitrary input slice `bytes`, the column counter invariant
/// `col <= 68` is preserved at every iteration and upon return, and the total number
/// of line-wrap continuations emitted is bounded by the input length.
pub fn verified_wrapped_stdout_write_bytes(initial_col: usize, bytes: &[u8]) -> (res: (usize, usize))
    requires
        initial_col <= POSIX_WRAP_COL_LIMIT,
    ensures
        res.0 <= POSIX_WRAP_COL_LIMIT,
        res.1 <= bytes@.len(),
{
    let mut col: usize = initial_col;
    let mut wrap_count: usize = 0;
    let mut i: usize = 0;
    let len: usize = bytes.len();

    while i < len
        invariant
            0 <= i <= len,
            len == bytes@.len(),
            col <= POSIX_WRAP_COL_LIMIT,
            wrap_count <= i,
        decreases len - i,
    {
        let b = bytes[i];
        let (next_col, wrapped) = verified_wrapped_stdout_step(col, b == b'\n');
        col = next_col;
        if wrapped {
            wrap_count = wrap_count + 1;
        }
        i = i + 1;
    }

    (col, wrap_count)
}

/// Verified bounds-safe lookahead `Lexer::peek_char` (`crates/bc_core/src/parser.rs`).
///
/// Proves absence of out-of-bounds slice indexing and arithmetic overflow when peeking ahead.
pub fn verified_lexer_peek_byte(text: &[u8], pos: usize, offset: usize) -> (res: u8)
    requires
        pos <= text@.len(),
        offset <= usize::MAX - pos,
    ensures
        pos + offset >= text@.len() ==> res == 0u8,
        pos + offset < text@.len() ==> res == text@[pos + offset],
{
    let idx = pos + offset;
    if idx >= text.len() {
        0u8
    } else {
        text[idx]
    }
}

/// Verified cursor and line advancement `Lexer::advance_char` (`crates/bc_core/src/parser.rs`).
///
/// Proves that:
/// 1. Slice indexing `text[pos]` never panics (out-of-bounds is impossible).
/// 2. `pos` advances monotonically to `min(initial_pos + steps, text.len())`.
/// 3. `line` increases monotonically and never overflows `usize`.
pub fn verified_lexer_advance_bytes(
    text: &[u8],
    initial_pos: usize,
    initial_line: usize,
    steps: usize,
) -> (res: (usize, usize))
    requires
        initial_pos <= text@.len(),
        initial_line >= 1,
        initial_line <= usize::MAX - text@.len(),
    ensures
        res.0 <= text@.len(),
        res.0 >= initial_pos,
        res.0 == if initial_pos + steps <= text@.len() {
            (initial_pos + steps) as usize
        } else {
            text@.len() as usize
        },
        res.1 >= initial_line,
        res.1 <= initial_line + (res.0 - initial_pos),
{
    let mut pos: usize = initial_pos;
    let mut line: usize = initial_line;
    let mut s: usize = 0;
    let len: usize = text.len();

    while s < steps
        invariant
            0 <= s <= steps,
            len == text@.len(),
            initial_pos <= pos <= len,
            initial_line <= usize::MAX - len,
            pos == if initial_pos + s <= len {
                (initial_pos + s) as usize
            } else {
                len
            },
            line >= initial_line,
            line <= initial_line + (pos - initial_pos),
        decreases steps - s,
    {
        if pos < len {
            if text[pos] == b'\n' {
                line = line + 1;
            }
            pos = pos + 1;
        }
        s = s + 1;
    }

    (pos, line)
}

// ============================================================================
// Target 4: Binary Exponentiation (`BCNum::pow`) Loop & POSIX Scale Invariants
// ============================================================================

/// Mathematical specification of integer exponentiation $\text{base}^{\text{exp}}$.
pub open spec fn spec_pow_int(base: int, exp: nat) -> int
    decreases exp,
{
    if exp == 0 {
        1
    } else {
        base * spec_pow_int(base, (exp - 1) as nat)
    }
}

/// Lemma: Inductive step for binary exponentiation (exponentiation by squaring):
/// - If `exp` is even ($\text{exp} > 0$), $\text{base}^{\text{exp}} == (\text{base} \cdot \text{base})^{\text{exp} / 2}$.
/// - If `exp` is odd, $\text{base}^{\text{exp}} == \text{base} \cdot (\text{base} \cdot \text{base})^{\text{exp} / 2}$.
pub proof fn lemma_pow_int_squaring(base: int, exp: nat)
    requires
        exp > 0,
    ensures
        exp % 2 == 0 ==> spec_pow_int(base, exp) == spec_pow_int(base * base, exp / 2),
        exp % 2 == 1 ==> spec_pow_int(base, exp) == base * spec_pow_int(base * base, exp / 2),
    decreases exp,
{
    reveal_with_fuel(spec_pow_int, 2);
    if exp == 1 {
        assert(1nat % 2 == 1);
        assert(1nat / 2 == 0);
        assert(spec_pow_int(base * base, 0) == 1);
    } else if exp % 2 == 1 {
        let prev = (exp - 1) as nat;
        assert(prev > 0);
        assert(prev % 2 == 0);
        assert(prev / 2 == exp / 2);
        lemma_pow_int_squaring(base, prev);
        assert(spec_pow_int(base, exp) == base * spec_pow_int(base, prev));
    } else {
        let prev = (exp - 1) as nat;
        assert(prev % 2 == 1);
        assert(prev / 2 == (exp / 2 - 1) as nat);
        lemma_pow_int_squaring(base, prev);
        assert(spec_pow_int(base, exp) == base * spec_pow_int(base, prev));
        assert(spec_pow_int(base, prev) == base * spec_pow_int(base * base, prev / 2));
        let sub_pow = spec_pow_int(base * base, prev / 2);
        assert(base * (base * sub_pow) == (base * base) * sub_pow) by (nonlinear_arith);
        assert(spec_pow_int(base * base, exp / 2) == (base * base) * sub_pow);
    }
}

/// POSIX specification for positive-exponent power scale:
/// $\min(a \cdot b, \max(\text{global\_scale}, a))$.
pub open spec fn spec_posix_pow_scale(a: nat, b: nat, global_scale: nat) -> nat {
    let max_gs = if global_scale >= a { global_scale } else { a };
    if a * b <= max_gs {
        a * b
    } else {
        max_gs
    }
}

/// Verified POSIX scale and truncation shift calculation for `BCNum::pow` (positive exponent $b > 0$).
///
/// Mirrors `crates/bc_core/src/math.rs` (`BCNum::pow`):
/// `sr = min(self.scale * b, max(global_scale, self.scale))`, `diff = self.scale * b - sr`.
/// Proves that `self.scale * b >= sr` always holds (so `diff >= 0`).
pub fn verified_pow_scale_and_shift(
    self_scale: usize,
    b_val: usize,
    global_scale: usize,
) -> (res: (usize, usize, usize))
    requires
        b_val >= 1,
        self_scale <= 30_000,
        b_val <= 30_000,
        global_scale <= MAX_VERIFIED_SCALE,
    ensures
        res.1 == self_scale * b_val,
        res.0 <= res.1,
        res.2 == res.1 - res.0,
        res.0 as nat == spec_posix_pow_scale(
            self_scale as nat,
            b_val as nat,
            global_scale as nat,
        ),
{
    proof {
        assert(self_scale * b_val <= 900_000_000) by (nonlinear_arith)
            requires
                self_scale <= 30_000,
                b_val <= 30_000,
        ;
    }
    let self_scale_b = self_scale * b_val;
    let max_gs = if global_scale >= self_scale { global_scale } else { self_scale };
    let sr = if self_scale_b <= max_gs { self_scale_b } else { max_gs };
    let diff = self_scale_b - sr;
    (sr, self_scale_b, diff)
}

/// Verified binary exponentiation loop for `BCNum::pow` (`crates/bc_core/src/math.rs:164-177`).
///
/// Tracks both the executable `res_scale` / `base_scale` and the ghost `res_coeff` / `base_coeff`
/// across the `while temp_b > 0` squaring loop, proving:
/// 1. Loop termination in $\mathcal{O}(\log b)$ iterations (`decreases temp_b`).
/// 2. Exact final scale: `res_scale == self_scale * b_val`.
/// 3. Exact final coefficient: `res_coeff@ == spec_pow_int(initial_coeff, b_val as nat)`.
pub fn verified_pow_binary_loop(
    Ghost(initial_coeff): Ghost<int>,
    self_scale: usize,
    b_val: usize,
) -> (res: (usize, Ghost<int>))
    requires
        self_scale <= 30_000,
        b_val <= 30_000,
    ensures
        res.0 == self_scale * b_val,
        res.1@ == spec_pow_int(initial_coeff, b_val as nat),
{
    let mut res_scale: usize = 0;
    let mut base_scale: usize = self_scale;
    let mut temp_b: usize = b_val;

    let ghost mut res_coeff: int = 1;
    let ghost mut base_coeff: int = initial_coeff;

    proof {
        assert(self_scale * b_val <= 900_000_000) by (nonlinear_arith)
            requires
                self_scale <= 30_000,
                b_val <= 30_000,
        ;
    }

    while temp_b > 0
        invariant
            temp_b <= b_val,
            self_scale <= 30_000,
            b_val <= 30_000,
            self_scale * b_val <= 900_000_000,
            res_scale <= self_scale * b_val,
            base_scale * temp_b <= self_scale * b_val,
            res_scale + base_scale * temp_b == self_scale * b_val,
            res_coeff * spec_pow_int(base_coeff, temp_b as nat)
                == spec_pow_int(initial_coeff, b_val as nat),
        decreases temp_b,
    {
        let prev_temp_b = temp_b;
        let prev_base_scale = base_scale;
        let prev_res_scale = res_scale;
        let ghost prev_base_coeff = base_coeff;
        let ghost prev_res_coeff = res_coeff;

        proof {
            lemma_pow_int_squaring(prev_base_coeff, prev_temp_b as nat);
            assert(prev_base_scale <= prev_base_scale * prev_temp_b) by (nonlinear_arith)
                requires
                    prev_temp_b >= 1,
                    prev_base_scale >= 0,
            ;
        }

        if temp_b % 2 == 1 {
            proof {
                assert(prev_temp_b == 2 * (prev_temp_b / 2) + 1);
                assert(prev_res_scale + prev_base_scale + (prev_base_scale + prev_base_scale) * (prev_temp_b / 2)
                    == prev_res_scale + prev_base_scale * prev_temp_b) by (nonlinear_arith)
                    requires
                        prev_temp_b == 2 * (prev_temp_b / 2) + 1,
                ;
                let sq_pow = spec_pow_int(prev_base_coeff * prev_base_coeff, (prev_temp_b / 2) as nat);
                assert((prev_res_coeff * prev_base_coeff) * sq_pow
                    == prev_res_coeff * (prev_base_coeff * sq_pow)) by (nonlinear_arith);
            }
            res_scale = res_scale + base_scale;
            proof {
                res_coeff = res_coeff * base_coeff;
            }
        } else {
            proof {
                assert(prev_temp_b == 2 * (prev_temp_b / 2));
                assert(prev_res_scale + (prev_base_scale + prev_base_scale) * (prev_temp_b / 2)
                    == prev_res_scale + prev_base_scale * prev_temp_b) by (nonlinear_arith)
                    requires
                        prev_temp_b == 2 * (prev_temp_b / 2),
                ;
            }
        }

        temp_b = temp_b / 2;
        if temp_b > 0 {
            proof {
                assert(prev_base_scale + prev_base_scale <= prev_base_scale * prev_temp_b)
                    by (nonlinear_arith)
                    requires
                        prev_temp_b >= 2,
                        prev_base_scale >= 0,
                ;
            }
            base_scale = base_scale + base_scale;
        } else {
            proof {
                assert(temp_b == 0);
                assert(base_scale * temp_b == 0) by (nonlinear_arith)
                    requires
                        temp_b == 0,
                ;
                assert(prev_temp_b == 1);
                assert(prev_base_scale * prev_temp_b == prev_base_scale) by (nonlinear_arith)
                    requires
                        prev_temp_b == 1,
                ;
            }
        }
        proof {
            base_coeff = base_coeff * base_coeff;
        }
    }

    proof {
        assert(temp_b == 0);
        assert(spec_pow_int(base_coeff, 0) == 1);
        assert(res_scale + base_scale * 0 == self_scale * b_val) by (nonlinear_arith)
            requires
                res_scale + base_scale * temp_b == self_scale * b_val,
                temp_b == 0,
        ;
    }

    (res_scale, Ghost(res_coeff))
}

// ============================================================================
// Target 5: Base Conversion (`ibase`/`obase`) Digit Bounds, LUT Safety & Padding
// ============================================================================

/// Verified hexadecimal digit parser (`crates/bc_core/src/math.rs:45-56` & `eval.rs:245-254`).
///
/// Proves that any ASCII byte maps to a bounded value in $0..=15$, with exact mappings
/// for `'0'..='9'`, `'A'..='F'`, and `'a'..='f'`.
pub fn verified_hex_char_val(c: u8) -> (res: usize)
    ensures
        res <= 15,
        (b'0' <= c && c <= b'9') ==> res == (c - b'0') as usize,
        (b'A' <= c && c <= b'F') ==> res == (c - b'A') as usize + 10,
        (b'a' <= c && c <= b'f') ==> res == (c - b'a') as usize + 10,
        !((b'0' <= c && c <= b'9') || (b'A' <= c && c <= b'F') || (b'a' <= c && c <= b'f'))
            ==> res == 0,
{
    if c >= b'0' && c <= b'9' {
        (c - b'0') as usize
    } else if c >= b'A' && c <= b'F' {
        (c - b'A') as usize + 10
    } else if c >= b'a' && c <= b'f' {
        (c - b'a') as usize + 10
    } else {
        0
    }
}

/// Verified fractional base conversion step and hexadecimal LUT indexing (`math.rs:306-318`).
///
/// Given $0 \le \text{num} < \text{den}$ and $2 \le \text{obase} \le 16$:
/// 1. Proves that `d = (num * obase) / den` satisfies $0 \le d < \text{obase} \le 16$.
/// 2. Proves that indexing `hex_lut[d as usize]` is 100% bounds-safe (never panics).
/// 3. Proves that `next_num = (num * obase) % den` preserves the loop invariant $0 \le \text{next\_num} < \text{den}$.
pub fn verified_obase_frac_step_and_lut(
    num: u64,
    den: u64,
    obase: u64,
    hex_lut: &[u8],
) -> (res: (u64, u64, u8))
    requires
        den >= 1,
        num < den,
        2 <= obase <= 16,
        (den as int) * (obase as int) <= u64::MAX as int,
        hex_lut@.len() == 16,
    ensures
        // res = (digit_d, next_num, ascii_hex_char)
        res.0 < obase,
        res.0 < 16,
        res.1 < den,
        (num as int) * (obase as int) == (res.0 as int) * (den as int) + (res.1 as int),
        res.2 == hex_lut@[res.0 as int],
{
    proof {
        assert((num as int) * (obase as int) < (den as int) * (obase as int)) by (nonlinear_arith)
            requires
                num < den,
                obase >= 2,
        ;
    }
    let prod: u64 = num * obase;
    let d: u64 = prod / den;
    let next_num: u64 = prod % den;

    proof {
        assert((prod as int) == (d as int) * (den as int) + (next_num as int)) by (nonlinear_arith)
            requires
                prod == num * obase,
                d == prod / den,
                next_num == prod % den,
                den >= 1,
        ;
        assert(next_num < den) by (nonlinear_arith)
            requires
                next_num == prod % den,
                den >= 1,
        ;
        assert(d < obase) by (nonlinear_arith)
            requires
                (prod as int) < (den as int) * (obase as int),
                (prod as int) == (d as int) * (den as int) + (next_num as int),
                next_num >= 0,
                den >= 1,
        ;
    }

    let ch: u8 = hex_lut[d as usize];
    (d, next_num, ch)
}

/// Verified multi-digit base (`obase > 16`) zero-padding width calculation (`math.rs:268-271`).
///
/// Proves that `digit_width - rem_len` never underflows when `1 <= rem_len <= digit_width`,
/// and that the resulting padded chunk has exact width `digit_width` (plus 1 leading separator).
pub fn verified_multi_digit_obase_padding(
    digit_width: usize,
    rem_len: usize,
) -> (res: (usize, usize))
    requires
        digit_width >= 2,
        digit_width <= 32,
        1 <= rem_len <= digit_width,
    ensures
        // res = (zero_pad_count, total_padded_digit_len)
        res.0 == digit_width - rem_len,
        res.1 == digit_width,
        res.0 + rem_len == res.1,
{
    let mut pad_count: usize = 0;
    let target_pads: usize = digit_width - rem_len;

    while pad_count < target_pads
        invariant
            0 <= pad_count <= target_pads,
            target_pads == digit_width - rem_len,
            1 <= rem_len <= digit_width,
            digit_width <= 32,
        decreases target_pads - pad_count,
    {
        pad_count = pad_count + 1;
    }

    let total_len: usize = pad_count + rem_len;
    (pad_count, total_len)
}

// ============================================================================
// Target 6: Transcendental Math (`Decimal`) Roundtrip & Argument Reduction
// ============================================================================

/// Abstract specification of fixed-point `Decimal` (`crates/bc_core/src/math.rs:350-402`).
pub ghost struct SpecDecimal {
    pub value: int,
    pub prec: nat,
}

impl SpecDecimal {
    /// Specification of `Decimal::from_bc_num` when `prec >= num.scale`.
    pub open spec fn spec_from_bc_num(num: SpecBCNum, prec: nat) -> SpecDecimal
        recommends
            prec >= num.scale,
    {
        SpecDecimal {
            value: num.coeff * pow10((prec - num.scale) as nat),
            prec,
        }
    }

    /// Specification of `Decimal::to_bc_num` when `self.prec >= target_scale`.
    pub open spec fn spec_to_bc_num(self, target_scale: nat) -> SpecBCNum
        recommends
            self.prec >= target_scale,
    {
        SpecBCNum {
            coeff: self.value / pow10((self.prec - target_scale) as nat),
            scale: target_scale,
        }
    }
}

/// Proof that converting `BCNum` to `Decimal` at higher guard precision (`prec >= num.scale`,
/// e.g. `max(x.scale, global_scale) + 15`) and converting back to `num.scale` is 100% lossless.
pub proof fn lemma_decimal_bcnum_roundtrip(num: SpecBCNum, prec: nat)
    requires
        prec >= num.scale,
    ensures
        SpecDecimal::spec_from_bc_num(num, prec).spec_to_bc_num(num.scale) == num,
{
    let shift = (prec - num.scale) as nat;
    lemma_pow10_pos(shift);
    let p10 = pow10(shift);
    assert((num.coeff * p10) / p10 == num.coeff) by (nonlinear_arith)
        requires
            p10 >= 1,
    ;
}

/// Verified trigonometric argument reduction modulo $2\pi$ into $[-\pi, \pi]$
/// (`crates/bc_core/src/math.rs:516-522, 564-570` in `decimal_sin` / `decimal_cos`).
///
/// Given any signed fixed-point angle `x_val` and positive `pi_val`, proves that:
/// 1. The reduced angle `res.0` lies strictly within $[-\pi, \pi]$.
/// 2. There exists an exact integer multiple $k$ (`res.1@`) of $2\pi$ such that
///    `x_val == res.0 + k * (2 * pi_val)`, guaranteeing periodicity invariance.
pub fn verified_trig_range_reduction(x_val: i64, pi_val: i64) -> (res: (i64, Ghost<int>))
    requires
        pi_val > 0,
        pi_val <= 1_000_000_000_000_000_000i64,
        x_val > i64::MIN,
    ensures
        -pi_val <= res.0 && res.0 <= pi_val,
        (x_val as int) == (res.0 as int) + res.1@ * (2 * (pi_val as int)),
{
    let two_pi: i64 = 2 * pi_val;
    let is_neg: bool = x_val < 0;
    let abs_x_i64: i64 = if is_neg { -x_val } else { x_val };
    let abs_x: u64 = abs_x_i64 as u64;
    let two_pi_u64: u64 = two_pi as u64;

    let q_u64: u64 = abs_x / two_pi_u64;
    let rem_u64: u64 = abs_x % two_pi_u64;
    let q_abs: i64 = q_u64 as i64;
    let rem_abs: i64 = rem_u64 as i64;

    proof {
        assert((abs_x as int) == (q_u64 as int) * (two_pi_u64 as int) + (rem_u64 as int))
            by (nonlinear_arith)
            requires
                two_pi_u64 > 0,
                q_u64 == abs_x / two_pi_u64,
                rem_u64 == abs_x % two_pi_u64,
        ;
        assert(rem_u64 < two_pi_u64) by (nonlinear_arith)
            requires
                two_pi_u64 > 0,
                rem_u64 == abs_x % two_pi_u64,
        ;
    }

    let mut rem: i64 = if is_neg { -rem_abs } else { rem_abs };
    let ghost mut k: int = if is_neg { -(q_abs as int) } else { q_abs as int };

    proof {
        if is_neg {
            assert((x_val as int) == -(abs_x as int));
            assert(-(abs_x as int) == (-(q_abs as int)) * (two_pi as int) + (-(rem_abs as int)))
                by (nonlinear_arith)
                requires
                    (abs_x as int) == (q_abs as int) * (two_pi as int) + (rem_abs as int),
            ;
        }
        assert((x_val as int) == (rem as int) + k * (two_pi as int));
    }

    if rem > pi_val {
        let prev_rem = rem;
        let ghost prev_k = k;
        rem = rem - two_pi;
        proof {
            k = prev_k + 1;
            assert((prev_rem as int) + prev_k * (two_pi as int)
                == (rem as int) + k * (two_pi as int)) by (nonlinear_arith)
                requires
                    rem == prev_rem - two_pi,
                    k == prev_k + 1,
            ;
        }
    } else if rem < -pi_val {
        let prev_rem = rem;
        let ghost prev_k = k;
        rem = rem + two_pi;
        proof {
            k = prev_k - 1;
            assert((prev_rem as int) + prev_k * (two_pi as int)
                == (rem as int) + k * (two_pi as int)) by (nonlinear_arith)
                requires
                    rem == prev_rem + two_pi,
                    k == prev_k - 1,
            ;
        }
    }

    (rem, Ghost(k))
}

/// Verified exponential argument reduction $x = n \cdot \ln(2) + r$ (`math.rs:758-760`).
///
/// Proves that for any non-negative fixed-point value `x_abs >= 0` and `ln2_val > 0`,
/// the reduced Taylor series argument $r$ satisfies $0 \le r < \ln(2)$ and reconstructs $x$ exactly.
pub fn verified_exp_ln2_reduction(x_abs: i64, ln2_val: i64) -> (res: (i64, i64))
    requires
        x_abs >= 0,
        ln2_val > 0,
    ensures
        // res = (n, r)
        res.0 >= 0,
        0 <= res.1 && res.1 < ln2_val,
        (x_abs as int) == (res.0 as int) * (ln2_val as int) + (res.1 as int),
{
    let n: i64 = x_abs / ln2_val;
    proof {
        assert(0 <= (n as int) * (ln2_val as int) && (n as int) * (ln2_val as int) <= (x_abs as int))
            by (nonlinear_arith)
            requires
                n == x_abs / ln2_val,
                x_abs >= 0,
                ln2_val > 0,
        ;
        assert((x_abs as int) - (n as int) * (ln2_val as int) < (ln2_val as int))
            by (nonlinear_arith)
            requires
                n == x_abs / ln2_val,
                x_abs >= 0,
                ln2_val > 0,
        ;
    }
    let r: i64 = x_abs - n * ln2_val;
    (n, r)
}

} // verus!
