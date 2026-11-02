// SPDX-License-Identifier: MIT
//
// Runs inputs that use the whole nesting limit on the built Wasm module, and measures how much
// of the stack in linear memory they use. A stack overflow there or in the engine's own stack
// ends in a trap and kills the instance, so reaching the end shows that neither happened.
//
//   node nesting_limit.mjs PKG_DIR          checks the module against WASM_MAX_DEPTH in lib.rs
//   node nesting_limit.mjs PKG_DIR LIMIT    prints the use at LIMIT (needs the stack-probe feature)
//
// The workloads mirror crates/bc_qemu_riscv32/src/stack_workloads.rs.

import fs from "node:fs";
import path from "node:path";
import { pathToFileURL } from "node:url";

/** Largest share of the stack in linear memory that the workloads may use. */
const MAX_STACK_PERCENT = 50;

const [pkgDir, limitArg] = process.argv.slice(2);
const wasmBytes = fs.readFileSync(path.join(pkgDir, "bc_wasm_bg.wasm"));
const pkg = await import(pathToFileURL(path.resolve(pkgDir, "bc_wasm.js")));
const exports_ = await pkg.default({ module_or_path: wasmBytes });

function readLeb(bytes, start) {
  let [value, shift, pos] = [0, 0, start];
  for (;;) {
    const byte = bytes[pos++];
    value |= (byte & 0x7f) << shift;
    shift += 7;
    if (!(byte & 0x80)) return [value, pos];
  }
}

/** The initial value of the stack pointer: the first mutable i32 global of the module. */
function stackTop(bytes) {
  let pos = 8;
  while (pos < bytes.length) {
    const section = bytes[pos];
    const [size, body] = readLeb(bytes, pos + 1);
    if (section === 6) {
      let [count, p] = readLeb(bytes, body);
      for (; count > 0; count--) {
        const [type, mutable, opcode] = [bytes[p], bytes[p + 1], bytes[p + 2]];
        if (opcode !== 0x41) throw new Error("global initializer is not i32.const");
        let top;
        [top, p] = readLeb(bytes, p + 3);
        p += 1; // `end`
        if (type === 0x7f && mutable === 1) return top;
      }
    }
    pos = body + size;
  }
  throw new Error("no stack pointer in the module");
}

const top = stackTop(wasmBytes);
const PAINT = 0xaa;

function measure(f) {
  new Uint8Array(exports_.memory.buffer).fill(PAINT, 0, top);
  const result = f();
  const memory = new Uint8Array(exports_.memory.buffer);
  let low = 0;
  while (low < top && memory[low] === PAINT) low++;
  return [result, top - low];
}

const recursionTo = (bottom) => (n) =>
  `define f(n) {\n  if (n == 0) {\n${bottom}\n  }\n  return (f(n - 1))\n}\nf(${n})\n`;
const parens = (n) => "(".repeat(n) + "1" + ")".repeat(n) + "\n";
const blocks = (n) => "{".repeat(n) + "1" + "}".repeat(n) + "\n";
const same = null; // the output at n = 0
const shallow = (name, math, scale, bottom) => ({ name, math, scale, build: recursionTo(bottom), expect: same });
const plain = (name, build, expect) => ({ name, math: false, scale: 0, build, expect });

const workloads = [
  plain("parentheses", parens, () => "1"),
  plain("unary minus", (n) => "- ".repeat(n) + "1\n", (n) => (n % 2 === 0 ? "1" : "-1")),
  plain("power chain", (n) => "1^".repeat(n) + "1\n", () => "1"),
  plain("assignment chain", (n) => "a=".repeat(n) + "1\na\n", () => "1"),
  plain("sum chain", (n) => "1+".repeat(n) + "1\n", (n) => String(n + 1)),
  plain("blocks", blocks, () => "1"),
  plain("nested if", (n) => "if(1)".repeat(n) + "1\n", () => "1"),
  plain("nested while", (n) => "while(i==0)".repeat(n) + "i=1\ni\n", () => "1"),
  plain("nested for", (n) => "for(i=0;i<1;i++)".repeat(n) + "1\n", () => "1"),
  plain(
    "blocks in a function",
    (n) => `define f() {\n${"{".repeat(n)}return (1)${"}".repeat(n)}\n}\nf()\n`,
    () => "1",
  ),
  plain(
    "recursion",
    (n) => `define f(n) {\n  if (n == 0) return (0)\n  return (f(n - 1))\n}\nf(${n})\n`,
    () => "0",
  ),
  plain(
    "recursion with arrays",
    (n) =>
      `define f(n, a[]) {\n  auto x, b[]\n  x = n; b[0] = a[0]\n  if (n == 0) return (a[0])\n  return (f(n - 1, b[]))\n}\na[0] = 7\nf(${n}, a[])\n`,
    () => "7",
  ),
  plain("syntax error at the bottom", (n) => "(".repeat(n) + "*\n", () => "(standard_in) 1: syntax error"),
  shallow("Divide by zero at the bottom", false, 0, "return (1 / 0)"),
  shallow("l() at the bottom", true, 20, "return (l(2))"),
  shallow("e() at the bottom", true, 20, "return (e(1))"),
  shallow("s() at the bottom", true, 20, "return (s(1))"),
  shallow("c() at the bottom", true, 20, "return (c(1))"),
  shallow("a() at the bottom", true, 20, "return (a(2))"),
  shallow("j() at the bottom", true, 20, "return (j(1, 1))"),
  shallow("sqrt at the bottom", false, 20, "return (sqrt(2))"),
  shallow("power at the bottom", false, 0, "return (3 ^ 200)"),
  shallow("division at the bottom", false, 40, "return (1 / 7 % 3)"),
  shallow("output in base 7 at the bottom", false, 0, "obase = 7; 3 ^ 200; obase = 10\nreturn (0)"),
  shallow("fraction in base 7 at the bottom", false, 20, "obase = 7; 1 / 3; obase = 10\nreturn (0)"),
  shallow("long output at the bottom", false, 0, "3 ^ 400\nreturn (0)"),
];

const probing = limitArg !== undefined;
let limit;
if (probing) {
  limit = Number(limitArg);
} else {
  const source = fs.readFileSync(new URL("../crate/src/lib.rs", import.meta.url), "utf8");
  limit = Number(source.match(/const WASM_MAX_DEPTH: usize = (\d+);/)[1]);
}

function run(workload, n) {
  const session = new pkg.BcSession(workload.math);
  try {
    if (probing) session.set_max_depth(limit);
    session.set_scale(workload.scale);
    return session.eval(workload.build(n));
  } finally {
    session.free();
  }
}

const tooDeep = (output) => output.includes("nesting too deep");
let failed = false;
let maxUsed = 0;
for (const workload of workloads) {
  if (probing) process.stdout.write(`${workload.name}: `);
  const [message, used] = measure(() => {
    if (!tooDeep(run(workload, limit))) return `${limit} levels of it are not rejected`;
    let [accepted, rejected] = [0, limit];
    while (rejected - accepted > 1) {
      const middle = Math.floor((accepted + rejected) / 2);
      if (tooDeep(run(workload, middle))) rejected = middle;
      else accepted = middle;
    }
    const actual = run(workload, accepted).trim();
    const expected = (workload.expect ? workload.expect(accepted) : run(workload, 0)).trim();
    if (actual !== expected) return `at depth ${accepted}: expected ${expected}, got ${actual}`;
    return `n=${accepted}`;
  });
  maxUsed = Math.max(maxUsed, used);
  const bad = !message.startsWith("n=");
  if (probing) console.log(`${message} stack=${used}`);
  else if (bad) console.log(`FAIL ${workload.name}: ${message}`);
  failed ||= bad;
}

// `eval_bc` must have the limit too.
if (!probing) {
  const parensAt = limit - 3;
  if (pkg.eval_bc(parens(parensAt), false, 0) !== "1\n") {
    console.log("FAIL eval_bc at the limit");
    failed = true;
  }
  if (!tooDeep(pkg.eval_bc(parens(parensAt + 1), false, 0))) {
    console.log("FAIL eval_bc beyond the limit");
    failed = true;
  }
}

const percent = (maxUsed * 100) / top;
console.log(`limit ${limit}: at most ${maxUsed} of ${top} bytes of stack (${percent.toFixed(1)}%)`);
if (!probing && percent > MAX_STACK_PERCENT) {
  console.log(`FAIL over ${MAX_STACK_PERCENT}% of the stack`);
  failed = true;
}
process.exit(failed ? 1 : 0);
