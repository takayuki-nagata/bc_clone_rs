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

pub fn recursion(n: usize) -> String {
    format!("define f(n) {{\n  if (n == 0) return (0)\n  return (f(n - 1))\n}}\nf({n})\n")
}

pub fn parens(n: usize) -> String {
    format!("{}1{}\n", "(".repeat(n), ")".repeat(n))
}

pub fn blocks(n: usize) -> String {
    format!("{}1{}\n", "{".repeat(n), "}".repeat(n))
}

/// A recursion `n` calls deep that runs `bottom` (statements ending in a `return`) at the end.
fn recursion_to(n: usize, bottom: &str) -> String {
    format!("define f(n) {{\n  if (n == 0) {{\n{bottom}\n  }}\n  return (f(n - 1))\n}}\nf({n})\n")
}

const fn plain(name: &'static str, build: fn(usize) -> String, expect: Expect) -> Workload {
    Workload {
        name,
        math: false,
        scale: 0,
        build,
        expect,
    }
}

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

fn too_deep(output: &str) -> bool {
    output.contains("nesting too deep")
}

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

/// Fills the stack from `bottom` up to just below the current stack pointer with [`STACK_PAINT`].
///
/// # Safety
/// `bottom` must be word-aligned, and the memory from it up to the stack pointer must be unused
/// stack. The caller must not rely on data below its own frame.
#[inline(never)]
pub unsafe fn paint_stack(bottom: usize) {
    let sp: usize;
    // SAFETY: reads a register.
    unsafe { core::arch::asm!("mv {}, sp", out(reg) sp) };
    let mut word = bottom;
    // The 64 bytes left unpainted keep the words next to the stack in use out of the measurement.
    while word < sp - 64 {
        // SAFETY: the caller's contract.
        unsafe { core::ptr::write_volatile(word as *mut u32, STACK_PAINT) };
        word += 4;
    }
}

/// Bytes of stack used below `top` since [`paint_stack`] painted down to `bottom`.
///
/// # Safety
/// The same `bottom` as in [`paint_stack`], and `top` above the current stack pointer.
#[inline(never)]
pub unsafe fn stack_high_water(bottom: usize, top: usize) -> usize {
    let mut word = bottom;
    // SAFETY: the words from `bottom` up to the stack in use are readable RAM.
    while word < top && unsafe { core::ptr::read_volatile(word as *const u32) } == STACK_PAINT {
        word += 4;
    }
    top - word
}
