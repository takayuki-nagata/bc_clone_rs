// SPDX-License-Identifier: MIT

//! Inputs that use the whole nesting limit, and a stack high-water mark for RV32.
//!
//! Shared by the QEMU runner and the M5Stamp C3 application. Each workload builds its input from a
//! depth `n`, and [`deepest`] searches for the largest `n` that the limit accepts, so a workload
//! always reaches the limit whatever its number of levels per `n`.

use alloc::format;
use alloc::string::String;

/// Evaluates `(code, math_enabled, scale)` under the nesting limit and returns the output.
pub type Run<'a> = &'a mut dyn FnMut(&str, bool, usize) -> String;

/// The output a workload must have at its deepest `n`.
#[derive(Clone, Copy)]
pub enum Expect {
    Fixed(&'static str),
    Computed(fn(usize) -> String),
    /// The output at `n = 0`: the work at the bottom does not depend on the depth above it.
    SameAsShallow,
}

#[derive(Clone, Copy)]
pub struct Workload {
    pub name: &'static str,
    pub math: bool,
    pub scale: usize,
    pub build: fn(usize) -> String,
    pub expect: Expect,
}

// coverage: miri(test_workloads_build_their_inputs); why: string
pub fn recursion(n: usize) -> String {
    format!("define f(n) {{\n  if (n == 0) return (0)\n  return (f(n - 1))\n}}\nf({n})\n")
}

// coverage: miri(test_workloads_build_their_inputs); why: string
pub fn parens(n: usize) -> String {
    format!("{}1{}\n", "(".repeat(n), ")".repeat(n))
}

// coverage: miri(test_workloads_build_their_inputs); why: string
pub fn blocks(n: usize) -> String {
    format!("{}1{}\n", "{".repeat(n), "}".repeat(n))
}

// coverage: miri(test_workloads_build_their_inputs); why: string
/// A recursion `n` calls deep that runs `bottom` (statements ending in a `return`) at the end.
fn recursion_to(n: usize, bottom: &str) -> String {
    format!("define f(n) {{\n  if (n == 0) {{\n{bottom}\n  }}\n  return (f(n - 1))\n}}\nf({n})\n")
}

// coverage: miri(test_deepest); why: string
const fn plain(name: &'static str, build: fn(usize) -> String, expect: Expect) -> Workload {
    Workload {
        name,
        math: false,
        scale: 0,
        build,
        expect,
    }
}

// coverage: miri(test_deepest); why: string
const fn bottom(
    name: &'static str,
    math: bool,
    scale: usize,
    build: fn(usize) -> String,
) -> Workload {
    Workload {
        name,
        math,
        scale,
        build,
        expect: Expect::SameAsShallow,
    }
}

pub const WORKLOADS: [Workload; 26] = [
    plain("parentheses", parens, Expect::Fixed("1")),
    plain(
        "unary minus",
        |n| format!("{}1\n", "- ".repeat(n)),
        Expect::Computed(|n| String::from(if n % 2 == 0 { "1" } else { "-1" })),
    ),
    plain(
        "power chain",
        |n| format!("{}1\n", "1^".repeat(n)),
        Expect::Fixed("1"),
    ),
    plain(
        "assignment chain",
        |n| format!("{}1\na\n", "a=".repeat(n)),
        Expect::Fixed("1"),
    ),
    plain(
        "sum chain",
        |n| format!("{}1\n", "1+".repeat(n)),
        Expect::Computed(|n| format!("{}", n + 1)),
    ),
    plain("blocks", blocks, Expect::Fixed("1")),
    plain(
        "nested if",
        |n| format!("{}1\n", "if(1)".repeat(n)),
        Expect::Fixed("1"),
    ),
    plain(
        "nested while",
        |n| format!("{}i=1\ni\n", "while(i==0)".repeat(n)),
        Expect::Fixed("1"),
    ),
    plain(
        "nested for",
        |n| format!("{}1\n", "for(i=0;i<1;i++)".repeat(n)),
        Expect::Fixed("1"),
    ),
    plain(
        "blocks in a function",
        |n| {
            format!(
                "define f() {{\n{}return (1){}\n}}\nf()\n",
                "{".repeat(n),
                "}".repeat(n)
            )
        },
        Expect::Fixed("1"),
    ),
    plain("recursion", recursion, Expect::Fixed("0")),
    plain(
        "recursion with arrays",
        |n| {
            format!(
                "define f(n, a[]) {{\n  auto x, b[]\n  x = n; b[0] = a[0]\n  if (n == 0) return (a[0])\n  return (f(n - 1, b[]))\n}}\na[0] = 7\nf({n}, a[])\n"
            )
        },
        Expect::Fixed("7"),
    ),
    plain(
        "syntax error at the bottom",
        |n| format!("{}*\n", "(".repeat(n)),
        Expect::Fixed("(standard_in) 1: syntax error"),
    ),
    bottom("Divide by zero at the bottom", false, 0, |n| {
        recursion_to(n, "return (1 / 0)")
    }),
    bottom("l() at the bottom", true, 20, |n| {
        recursion_to(n, "return (l(2))")
    }),
    bottom("e() at the bottom", true, 20, |n| {
        recursion_to(n, "return (e(1))")
    }),
    bottom("s() at the bottom", true, 20, |n| {
        recursion_to(n, "return (s(1))")
    }),
    bottom("c() at the bottom", true, 20, |n| {
        recursion_to(n, "return (c(1))")
    }),
    bottom("a() at the bottom", true, 20, |n| {
        recursion_to(n, "return (a(2))")
    }),
    bottom("j() at the bottom", true, 20, |n| {
        recursion_to(n, "return (j(1, 1))")
    }),
    bottom("sqrt at the bottom", false, 20, |n| {
        recursion_to(n, "return (sqrt(2))")
    }),
    bottom("power at the bottom", false, 0, |n| {
        recursion_to(n, "return (3 ^ 200)")
    }),
    bottom("division at the bottom", false, 40, |n| {
        recursion_to(n, "return (1 / 7 % 3)")
    }),
    bottom("output in base 7 at the bottom", false, 0, |n| {
        recursion_to(n, "obase = 7; 3 ^ 200; obase = 10\nreturn (0)")
    }),
    bottom("fraction in base 7 at the bottom", false, 20, |n| {
        recursion_to(n, "obase = 7; 1 / 3; obase = 10\nreturn (0)")
    }),
    bottom("long output at the bottom", false, 0, |n| {
        recursion_to(n, "3 ^ 400\nreturn (0)")
    }),
];

// coverage: miri(test_deepest); why: string
fn too_deep(output: &str) -> bool {
    output.contains("nesting too deep")
}

// coverage: miri(test_deepest, test_deepest_on_the_evaluator); why: dyn, string
/// The largest `n` for which `limit` accepts the workload, after checking its output there.
pub fn deepest(workload: &Workload, run: Run, limit: usize) -> Result<usize, String> {
    let mut eval = |n: usize| run(&(workload.build)(n), workload.math, workload.scale);
    if !too_deep(&eval(limit)) {
        return Err(format!("{limit} levels of it are not rejected"));
    }
    let (mut accepted, mut rejected) = (0, limit);
    while rejected - accepted > 1 {
        let middle = accepted + (rejected - accepted) / 2;
        if too_deep(&eval(middle)) {
            rejected = middle;
        } else {
            accepted = middle;
        }
    }
    let actual = eval(accepted);
    let expected = match workload.expect {
        Expect::Fixed(text) => String::from(text),
        Expect::Computed(text) => text(accepted),
        Expect::SameAsShallow => eval(0),
    };
    if actual.trim() == expected.trim() {
        Ok(accepted)
    } else {
        Err(format!(
            "at depth {accepted}: expected {:?}, got {:?}",
            expected.trim(),
            actual.trim()
        ))
    }
}

/// Word written to the unused stack by [`paint_stack`].
const STACK_PAINT: u32 = 0x5A5A_A5A5;

/// Bytes below the stack pointer that [`paint_stack`] leaves unpainted. The frames of the
/// functions it calls lie there (at `opt-level = 0` even `write_volatile` and the closure are
/// calls), so painting them would overwrite their return addresses. The high-water mark is the
/// first painted word above `bottom` that a workload overwrote, far below this margin, so its
/// size does not change a measurement.
#[cfg(target_arch = "riscv32")]
const PAINT_MARGIN: usize = 1024;

// coverage: miri(test_for_each_word); why: hw
/// Calls `f` with every word address from `from` (word-aligned) up to, but not including, `to`.
pub fn for_each_word(from: usize, to: usize, mut f: impl FnMut(usize)) {
    let mut word = from;
    while word < to {
        f(word);
        word += 4;
    }
}

// coverage: miri(test_first_unpainted); why: hw
/// The address of the first word from `from` (word-aligned) below `to` for which `read` does not
/// return [`STACK_PAINT`], or `to` if there is none.
pub fn first_unpainted(from: usize, to: usize, mut read: impl FnMut(usize) -> u32) -> usize {
    let mut word = from;
    while word < to && read(word) == STACK_PAINT {
        word += 4;
    }
    word
}

// coverage: shim(scripts/run_qemu_riscv32_tests.sh); why: hw
/// The stack pointer of the caller.
#[cfg(target_arch = "riscv32")]
#[inline(always)]
fn current_sp() -> usize {
    let sp: usize;
    // SAFETY: reads a register.
    unsafe { core::arch::asm!("mv {}, sp", out(reg) sp) };
    sp
}

// coverage: shim(scripts/run_qemu_riscv32_tests.sh); why: hw
/// Fills the stack from `bottom` up to [`PAINT_MARGIN`] bytes below the current stack pointer
/// with [`STACK_PAINT`].
///
/// # Safety
/// `bottom` must be word-aligned, and the memory from it up to the stack pointer must be unused
/// stack. The caller must not rely on data below its own frame.
#[cfg(target_arch = "riscv32")]
#[inline(never)]
pub unsafe fn paint_stack(bottom: usize) {
    for_each_word(bottom, current_sp() - PAINT_MARGIN, |word| {
        // SAFETY: the caller's contract.
        unsafe { core::ptr::write_volatile(word as *mut u32, STACK_PAINT) }
    });
}

// coverage: shim(scripts/run_qemu_riscv32_tests.sh); why: hw
/// Bytes of stack used below `top` since [`paint_stack`] painted down to `bottom`.
///
/// # Safety
/// The same `bottom` as in [`paint_stack`], and `top` above the current stack pointer.
#[inline(never)]
pub unsafe fn stack_high_water(bottom: usize, top: usize) -> usize {
    // SAFETY: the words from `bottom` up to the stack in use are readable RAM.
    top - first_unpainted(bottom, top, |word| unsafe {
        core::ptr::read_volatile(word as *const u32)
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::vec::Vec;

    /// A fake evaluator: an input nests `n` levels when it is `n` repetitions of `x`, and
    /// `limit` rejects more than `accepts` of them.
    fn fake(accepts: usize, output: &'static str) -> impl FnMut(&str, bool, usize) -> String {
        move |code, _, _| {
            if code.len() > accepts {
                String::from("nesting too deep")
            } else {
                String::from(output)
            }
        }
    }

    fn xs(n: usize) -> String {
        "x".repeat(n)
    }

    #[test]
    fn test_deepest() {
        let fixed = plain("fixed", xs, Expect::Fixed("ok"));
        assert_eq!(deepest(&fixed, &mut fake(7, "ok"), 20), Ok(7));
        assert_eq!(
            deepest(&fixed, &mut fake(20, "ok"), 20),
            Err(String::from("20 levels of it are not rejected"))
        );
        assert_eq!(
            deepest(&fixed, &mut fake(7, "ko"), 20),
            Err(String::from("at depth 7: expected \"ok\", got \"ko\""))
        );
        let computed = plain("computed", xs, Expect::Computed(|n| format!("{n}")));
        assert_eq!(deepest(&computed, &mut fake(3, "3"), 20), Ok(3));
        let same = bottom("same", false, 0, xs);
        assert_eq!(deepest(&same, &mut fake(0, "ok"), 20), Ok(0));
        assert!(!too_deep("1") && too_deep("f: nesting too deep"));
    }

    #[test]
    fn test_workloads_build_their_inputs() {
        assert_eq!(parens(2), "((1))\n");
        assert_eq!(blocks(1), "{1}\n");
        assert!(recursion(3).ends_with("f(3)\n"));
        assert!(recursion_to(2, "return (5)").contains("return (5)"));
        for w in &WORKLOADS {
            assert!(!(w.build)(2).is_empty(), "{}", w.name);
        }
    }

    #[test]
    fn test_deepest_on_the_evaluator() {
        let mut run =
            |code: &str, math: bool, scale: usize| crate::eval_bc_at_depth(code, math, scale, 12);
        assert_eq!(deepest(&WORKLOADS[0], &mut run, 12), Ok(9));
    }

    #[test]
    fn test_for_each_word() {
        let mut seen = Vec::new();
        for_each_word(8, 20, |w| seen.push(w));
        assert_eq!(seen, [8, 12, 16]);
        for_each_word(8, 8, |w| seen.push(w));
        for_each_word(8, 4, |w| seen.push(w));
        assert_eq!(seen.len(), 3);
    }

    #[test]
    fn test_first_unpainted() {
        let mut words = [STACK_PAINT; 4];
        words[2] = 0;
        let read = |w: usize| words[(w - 100) / 4];
        assert_eq!(first_unpainted(100, 116, read), 108);
        assert_eq!(first_unpainted(100, 108, read), 108);
        assert_eq!(first_unpainted(112, 116, read), 116);
    }

    // Not under Miri: the addresses are integers, which strict provenance does not turn into
    // pointers. It lets cargo-mutants see the arithmetic of the shim.
    #[test]
    #[cfg_attr(miri, ignore)]
    fn test_stack_high_water() {
        let mut words = [STACK_PAINT; 8];
        words[5] = 1;
        let bottom = words.as_ptr() as usize;
        let top = bottom + 32;
        // SAFETY: the words are readable.
        assert_eq!(unsafe { stack_high_water(bottom, top) }, 12);
    }
}
