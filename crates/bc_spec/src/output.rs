// SPDX-License-Identifier: MIT

//! Output: `BCNum::format_obase`, the 70-column wrapping of `WrappedStdout`, and decimal
//! strings of machine integers.

use crate::num::*;
use crate::power::*;
use vstd::contrib::exec_spec::*;
use vstd::prelude::*;

verus! {

exec_spec_verified! {

/// The ASCII decimal digits of `x` (`"0"` for zero), most significant first.
pub open spec fn dec_str(x: u64) -> Seq<u8>
    decreases x
{
    if x < 10 { seq![(48 + x) as u8] } else { dec_str(x / 10).push((48 + x % 10) as u8) }
}

/// The digit character of `d < 16` (`0123456789ABCDEF`).
pub open spec fn hex_digit(d: u64) -> u8 {
    if d < 10 { (48 + d) as u8 } else if d < 16 { (55 + d) as u8 } else { 63u8 }
}

/// `d` in decimal, left-padded with zeros to `width` digits.
pub open spec fn padded(d: u64, width: u64) -> Seq<u8> {
    let s = dec_str(d);
    zeros(if width > s.len() as u64 { (width - s.len() as u64) as u64 } else { 0u64 }).add(s)
}

pub open spec fn zeros(n: u64) -> Seq<u8>
    decreases n
{
    if n == 0 { seq![] } else { zeros((n - 1) as u64).push(48u8) }
}

/// The text of one output digit: a character for `obase <= 16`, otherwise the zero-padded
/// decimal value preceded by `sep` (a space, or `.` for the first fraction digit).
pub open spec fn out_digit(d: u64, obase: u32, sep: u8) -> Seq<u8> {
    if obase <= 16 {
        seq![hex_digit(d)]
    } else {
        let w = dec_str((obase - 1) as u64).len() as u64;
        seq![sep].add(padded(d, w))
    }
}

/// The digits of the integer `m` in base `ob`, most significant first, after `acc`; `steps`
/// bounds the number of divisions (each one divides by at least 2).
pub open spec fn int_digits(m: Seq<u8>, ob: u32, steps: u64, acc: Seq<u8>) -> Seq<u8>
    decreases steps
{
    if steps == 0 || is_zero_mag(m) {
        acc
    } else {
        let qr = divmod_mag(m, u64_mag(ob as u64));
        let d = out_digit(mag_to_u64(qr.1), ob, 32u8);
        int_digits(qr.0, ob, (steps - 1) as u64, d.add(acc))
    }
}

/// The number of fraction digits printed in `obase`: `scale` for base 10, otherwise the
/// smallest `k` with `obase^k >= 10^scale`, searched from `k` with `cur = obase^k`.
pub open spec fn frac_count(cur: Seq<u8>, target: Seq<u8>, ob: u32, k: u64, limit: u64) -> u64
    decreases limit - k
{
    if k >= limit || cmp_mag(cur, target) >= 0 {
        k
    } else {
        frac_count(mul_mag(cur, u64_mag(ob as u64)), target, ob, (k + 1) as u64, limit)
    }
}

/// `n` fraction digits of `num / den` in base `ob` (`num < den`), after `acc`.
pub open spec fn frac_digits(num: Seq<u8>, den: Seq<u8>, ob: u32, n: u64, first: bool, acc: Seq<u8>) -> Seq<u8>
    decreases n
{
    if n == 0 {
        acc
    } else {
        let qr = divmod_mag(mul_mag(num, u64_mag(ob as u64)), den);
        let d = out_digit(mag_to_u64(qr.0), ob, if first { 46u8 } else { 32u8 });
        frac_digits(qr.1, den, ob, (n - 1) as u64, false, acc.add(d))
    }
}

/// The first `k` digits of `m` (`m mod 10^k`).
pub open spec fn low_digits(m: Seq<u8>, k: u32) -> Seq<u8>
    decreases k
{
    if k == 0 || m.len() == 0 { seq![] } else { seq![m[0]].add(low_digits(m.drop_first(), (k - 1) as u32)) }
}

/// `BCNum::format_obase` (without the newline).
pub open spec fn format_num(v: Num, obase: u32) -> Seq<u8> {
    if is_zero_mag(v.mag) {
        seq![48u8]
    } else {
        let ip = drop_mag(v.mag, v.scale);
        // Enough divisions for any number of digits below 2^60 (each digit is at most 4 bits of
        // value per decimal digit); `u64::MAX` beyond that.
        let steps = if (v.mag.len() as u64) < 0x1000_0000_0000_0000u64 { (4 * (v.mag.len() as u64) + 4) as u64 } else { 0xffff_ffff_ffff_ffffu64 };
        let int_str = int_digits(ip, obase, steps, seq![]);
        let frac_str = if v.scale == 0 {
            seq![]
        } else {
            let den = shift_mag(seq![1u8], v.scale);
            let n = if obase == 10 { v.scale as u64 } else { frac_count(seq![1u8], den, obase, 0u64, (4 * (v.scale as u64) + 4) as u64) };
            let fd = frac_digits(low_digits(v.mag, v.scale), den, obase, n, true, seq![]);
            if obase <= 16 { seq![46u8].add(fd) } else { fd }
        };
        let body = int_str.add(frac_str);
        if v.neg { seq![45u8].add(body) } else { body }
    }
}

/// `WrappedStdout::write_str`: appends `s` to `out` starting at column `col`; before a
/// character at column 68 or beyond it writes a backslash-newline. Columns count characters
/// (UTF-8 continuation bytes do not advance them). Returns the output and the new column.
pub open spec fn write_wrapped(out: Seq<u8>, col: u64, s: Seq<u8>) -> (Seq<u8>, u64)
    decreases s.len()
{
    if s.len() == 0 {
        (out, col)
    } else {
        let c = s[0];
        if c == 10u8 {
            write_wrapped(out.push(10u8), 0u64, s.drop_first())
        } else if 0x80 <= c && c <= 0xbf {
            write_wrapped(out.push(c), col, s.drop_first())
        } else if col >= 68 {
            write_wrapped(out.push(92u8).push(10u8).push(c), 1u64, s.drop_first())
        } else {
            write_wrapped(out.push(c), (col + 1) as u64, s.drop_first())
        }
    }
}

} // exec_spec_verified!

} // verus!
