// SPDX-License-Identifier: MIT

//! Tree-walking AST evaluator and dynamic scope manager for the bc clone.
//!
//! Complies with POSIX bc specifications for registers, arrays, function definitions,
//! dynamic scope resolution, and WrappedStdout formatting.

use alloc::boxed::Box;
use alloc::collections::BTreeMap;
use alloc::format;
use alloc::string::String;
use alloc::vec;
use alloc::vec::Vec;
use core::cmp::Ordering;
use core::fmt::Write as FmtWrite;
use num_bigint::BigInt;
use num_traits::{Signed, ToPrimitive};

use crate::error::{BcError, RuntimeError};
use crate::format::{push_dec, wrap_output};
use crate::math::pow10_within;
use crate::math::{BCNum, pow10};
use crate::parser::{
    AssignOp, BinOp, DEFAULT_MAX_DEPTH, Expr, ExprOrArray, ExtensionPolicy, FunctionDef, Register,
    RelOp, Stmt,
};
#[cfg(verus_keep_ghost)]
use crate::refine::*;
#[cfg(verus_keep_ghost)]
use crate::spec_num;
#[cfg(verus_keep_ghost)]
use crate::spec_num::SpecBCNum;
#[cfg(verus_keep_ghost)]
use crate::spec_num::lemma_pow10_pos;
#[cfg(verus_keep_ghost)]
use crate::spec_num::spec_tdiv;
#[cfg(verus_keep_ghost)]
use crate::trusted_bigint::{axiom_bigint_size, big_view};
use crate::trusted_bigint::{
    big_abs, big_cmp, big_from_usize, big_is_negative, big_neg, big_tdiv, big_to_u64_small,
};
#[cfg(verus_keep_ghost)]
use crate::trusted_std::axiom_string_obeys_cmp;
use crate::verified_kernels::{
    BC_BASE_MAX, BC_DIM_MAX, BC_SCALE_MAX, IBASE_MAX, verified_clamp_register,
    verified_hex_char_val, verified_loop_post_body_action, verified_nesting_within_limit,
    verified_should_abort_execution,
};
#[cfg(verus_keep_ghost)]
use bc_spec::convert::{lemma_num_from_digits, num_from_digits};
#[cfg(verus_keep_ghost)]
use bc_spec::convert::{lemma_num_length, lemma_num_scale, num_length, num_scale};
#[cfg(verus_keep_ghost)]
use bc_spec::eval::{
    ER, EState, Func, er_ok, ev, ev_node, ev_unary, exec, exec_node, negate, num_u64, reg_get,
    with_depth,
};
#[cfg(verus_keep_ghost)]
use bc_spec::eval::{
    arith as spec_arith, arr_top, array_index, elem_get, hex_val, number_text, one_num, rel_holds,
    resolve, var_get,
};
#[cfg(verus_keep_ghost)]
use bc_spec::format::lemma_format_num;
#[cfg(verus_keep_ghost)]
use bc_spec::fuel::done;
#[cfg(verus_keep_ghost)]
use bc_spec::fuel::lemma_resolve_mono;
#[cfg(verus_keep_ghost)]
use bc_spec::fuel::{lemma_ev_mono, lemma_exec_mono};
#[cfg(verus_keep_ghost)]
use bc_spec::num::lemma_is_zero_mag;
#[cfg(verus_keep_ghost)]
use bc_spec::num::{
    lemma_mag_bounds, lemma_num_add, lemma_num_cmp, lemma_num_div, lemma_num_mod, lemma_num_mul,
    lemma_num_sub, mag_val, num_add, num_cmp, num_coeff, num_sub,
};
#[cfg(verus_keep_ghost)]
use bc_spec::num::{to_l0, wf_num};
#[cfg(verus_keep_ghost)]
use bc_spec::output::{dec_str, write_wrapped};
#[cfg(verus_keep_ghost)]
use bc_spec::parser::Node;
#[cfg(verus_keep_ghost)]
use bc_spec::power::lemma_one_mag;
#[cfg(verus_keep_ghost)]
use bc_spec::power::lemma_u64_mag;
#[cfg(verus_keep_ghost)]
use bc_spec::power::{NumRes, lemma_num_pow, lemma_num_sqrt, num_sqrt};
#[cfg(verus_keep_ghost)]
use bc_spec::values::{int_mag, lemma_array_index_value, lemma_register_input, sat_u64};
#[cfg(not(verus_keep_ghost))]
use verus_builtin::Ghost;
#[cfg(not(verus_keep_ghost))]
use verus_builtin_macros::verus;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

/// Abstract output writer trait compatible with both no_std and std environments.
pub trait BcWriter: FmtWrite + Send {
    /// Flushes any buffered content.
    fn flush(&mut self) -> core::fmt::Result {
        Ok(())
    }
}

impl BcWriter for String {}

impl WrappedStdout {
    /// Creates a new WrappedStdout writing to the given writer.
    pub fn new(writer: Box<dyn BcWriter>) -> Self {
        Self { writer, col: 0 }
    }

    /// Writes a string to the output stream with POSIX line wrapping: a backslash-newline
    /// before a character at column 68 or beyond (`format::wrap_output`, verified against the
    /// specification's `write_wrapped`).
    pub fn write_str(&mut self, s: &str) -> core::fmt::Result {
        let (out, col) = wrap_output(self.col, s.as_bytes());
        self.col = col;
        // Backslash-newlines go only before the first byte of a character, so `out` is UTF-8.
        match core::str::from_utf8(&out) {
            Ok(text) => self.writer.write_str(text),
            Err(_) => Err(core::fmt::Error),
        }
    }

    /// Flushes the underlying writer.
    pub fn flush(&mut self) -> core::fmt::Result {
        self.writer.flush()
    }
}

verus! {

/// Wrapper to write output characters with POSIX-style 70-character line wrapping. Opaque to
/// Verus: the refinement proofs see it through `out_log` and `out_col`.
#[verifier::external_body]
pub struct WrappedStdout {
    writer: Box<dyn BcWriter>,
    col: usize,
}

/// The diagnostic stream. Opaque to Verus: the refinement proofs see it through `err_log`.
#[verifier::external_body]
pub struct ErrWriter {
    writer: Box<dyn BcWriter>,
}

/// The bytes written to standard output so far (the model of the output stream).
pub uninterp spec fn out_log(w: &WrappedStdout) -> Seq<u8>;

/// The output column of standard output (`write_wrapped`'s column).
pub uninterp spec fn out_col(w: &WrappedStdout) -> u64;

/// The bytes written to the diagnostic stream so far.
pub uninterp spec fn err_log(w: &ErrWriter) -> Seq<u8>;

/// Evaluator maintaining registers, scoped variables, functions, and state.
pub struct Evaluator {
    pub variables: BTreeMap<String, Vec<BCNum>>,
    pub arrays: BTreeMap<String, Vec<BTreeMap<usize, BCNum>>>,
    pub functions: BTreeMap<String, FunctionDef>,
    // Registers are private so that every value stays within its valid range; in particular
    // `scale <= BC_SCALE_MAX` is what the verified scale kernels rely on.
    pub(crate) scale: usize,
    pub(crate) ibase: usize,
    pub(crate) obase: usize,
    pub math_enabled: bool,
    pub stdout_writer: WrappedStdout,
    pub stderr_writer: ErrWriter,

    pub break_flag: bool,
    pub return_flag: bool,
    pub return_value: BCNum,
    pub quit_flag: bool,
    /// How non-POSIX syntax is treated (`-s` / `-w`); applied by the input-unit driver.
    pub extension_policy: ExtensionPolicy,

    /// Names of the user functions currently executing, innermost last (for diagnostics).
    pub(crate) call_stack: Vec<String>,

    /// Nesting limit: the syntax tree of an input unit is at most this deep, and at most this
    /// many expressions and statements (across function calls) are evaluated at once. It bounds
    /// the native stack that parsing and evaluation use (`docs/COMPATIBILITY.md` §2), so a
    /// front end sets it for the stack it runs on.
    pub max_depth: usize,
    /// Expressions and statements currently being evaluated.
    pub(crate) eval_depth: usize,
    /// `ibase` when the innermost executing function was invoked (`None` at top level). POSIX:
    /// numeric constants within a function are interpreted in this base.
    pub(crate) invocation_ibase: Option<usize>,
}

/// An assignment target whose array subscript has already been evaluated.
enum Place {
    Variable(String),
    Element(String, usize),
    Register(Register),
}

/// The caller's state saved when a function is entered, restored by `Evaluator::leave_call`.
struct SavedCall {
    return_flag: bool,
    return_value: BCNum,
    invocation_ibase: Option<usize>,
}

/// The output streams as written so far.
pub(crate) open spec fn r_output(out: WrappedStdout, err: ErrWriter, st: EState) -> bool {
    out_log(&out) == st.out && out_col(&out) == st.col && err_log(&err) == st.err
}

/// The whole evaluator state corresponds to the specification's `EState` (without `-l`).
pub(crate) open spec fn r_state(e: Evaluator, st: EState) -> bool {
    &&& !e.math_enabled
    &&& r_vars(e.variables@, st.vars)
    &&& r_arrays(e.arrays@, st.arrays)
    &&& r_funcs(e.functions@, st.funcs)
    &&& e.scale == st.scale && e.ibase == st.ibase && e.obase == st.obase
    &&& e.break_flag == st.brk && e.return_flag == st.ret && r_num(e.return_value, st.ret_val)
    &&& !e.quit_flag
    &&& r_calls(e.call_stack@, st.calls)
    &&& e.eval_depth == st.depth && e.max_depth == st.max_depth
    &&& match e.invocation_ibase {
        Some(b) => st.has_inv && b == st.inv_ibase,
        None => !st.has_inv,
    }
    &&& r_output(e.stdout_writer, e.stderr_writer, st)
}

/// Every number the evaluator holds has a scale of at most `BC_SCALE_MAX` (the precondition of
/// the verified `BCNum` operations), and the registers are in their ranges.
pub(crate) open spec fn nums_ok(s: Seq<BCNum>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> (#[trigger] s[i]).scale <= BC_SCALE_MAX
}

pub(crate) open spec fn frame_ok(f: Map<usize, BCNum>) -> bool {
    forall|k: usize| #[trigger] f.contains_key(k) ==> f[k].scale <= BC_SCALE_MAX
}

pub(crate) open spec fn frames_ok(s: Seq<BTreeMap<usize, BCNum>>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> frame_ok((#[trigger] s[i])@)
}

/// The digit value of a constant's character, as the specification's `digit_val`.
#[allow(
    clippy::manual_range_contains,
    clippy::implicit_saturating_sub,
    reason = "written as the specification's digit_val, which Verus compares directly"
)]
fn digit_val_of(c: u8) -> (r: u8)
    ensures
        r == bc_spec::eval::digit_val(c),
{
    if c <= 57 {
        if c >= 48 { c - 48 } else { 0 }
    } else if c >= 65 {
        c - 55
    } else {
        0
    }
}

/// The integer and fraction digit values of a constant's text (the specification's
/// `literal_digits`): characters before the first `.` and after it; any `.` is skipped.
fn literal_digit_values(t: &[u8]) -> (r: (Vec<u8>, Vec<u8>))
    ensures
        r.0@ == bc_spec::eval::literal_digits(t@, true, false, Seq::empty()),
        r.1@ == bc_spec::eval::literal_digits(t@, false, false, Seq::empty()),
{
    let mut ds: Vec<u8> = Vec::new();
    let mut fs: Vec<u8> = Vec::new();
    let mut seen = false;
    let mut i: usize = 0;
    proof {
        assert(t@.skip(0) =~= t@);
    }
    while i < t.len()
        invariant
            i <= t.len(),
            bc_spec::eval::literal_digits(t@, true, false, Seq::empty())
                == bc_spec::eval::literal_digits(t@.skip(i as int), true, seen, ds@),
            bc_spec::eval::literal_digits(t@, false, false, Seq::empty())
                == bc_spec::eval::literal_digits(t@.skip(i as int), false, seen, fs@),
        decreases t.len() - i,
    {
        let c = t[i];
        proof {
            assert(t@.skip(i as int)[0] == c);
            assert(t@.skip(i as int).drop_first() =~= t@.skip(i as int + 1));
        }
        if c == 46 {
            seen = true;
        } else if seen {
            fs.push(digit_val_of(c));
        } else {
            ds.push(digit_val_of(c));
        }
        i += 1;
    }
    proof {
        assert(t@.skip(i as int) =~= Seq::<u8>::empty());
    }
    (ds, fs)
}

impl Evaluator {
    /// The evaluator's invariant (`docs/COMPATIBILITY.md` §2): registers in range, and every
    /// stored number with a scale of at most `BC_SCALE_MAX`.
    pub closed spec fn inv(&self) -> bool {
        &&& self.scale <= BC_SCALE_MAX
        &&& 2 <= self.ibase <= IBASE_MAX
        &&& 2 <= self.obase <= BC_BASE_MAX
        &&& self.return_value.scale <= BC_SCALE_MAX
        &&& match self.invocation_ibase {
            Some(b) => 2 <= b <= IBASE_MAX,
            None => true,
        }
        &&& forall|k: String| #[trigger] self.variables@.contains_key(k) ==> nums_ok(self.variables@[k]@)
        &&& forall|k: String| #[trigger] self.arrays@.contains_key(k) ==> frames_ok(self.arrays@[k]@)
    }

    /// The current value of variable `name`: the top of its stack, 0 if it has none.
    pub(crate) fn var_get(&self, name: &String) -> (r: BCNum)
        requires
            self.inv(),
        ensures
            r.scale <= BC_SCALE_MAX,
            ({
                let m = self.variables@;
                if m.contains_key(*name) && m[*name]@.len() > 0 {
                    r.val() == m[*name]@.last().val()
                } else {
                    r.val() == BCNum::spec_zero_val()
                }
            }),
    {
        proof {
            axiom_string_obeys_cmp();
            broadcast use vstd::std_specs::btree::group_btree_axioms;
        }
        match self.variables.get(name) {
            Some(stack) => {
                if !stack.is_empty() {
                    stack[stack.len() - 1].copy()
                } else {
                    BCNum::zero()
                }
            },
            None => BCNum::zero(),
        }
    }

    /// Sets the top of variable `name`'s stack to `v` (a new name gets the stack `[v]`).
    pub(crate) fn var_set(&mut self, name: String, v: BCNum)
        requires
            old(self).inv(),
            v.scale <= BC_SCALE_MAX,
        ensures
            final(self).inv(),
            same_but_storage(*old(self), *final(self)),
            ({
                let m = old(self).variables@;
                let s = if m.contains_key(name) { m[name]@ } else { Seq::empty() };
                &&& final(self).variables@.dom() == m.dom().insert(name)
                &&& final(self).variables@[name]@ == if s.len() > 0 { s.drop_last().push(v) } else { s.push(v) }
                &&& forall|k: String| k != name && #[trigger] m.contains_key(k) ==> final(self).variables@[k] == m[k]
            }),
            final(self).arrays@ == old(self).arrays@,
    {
        proof {
            axiom_string_obeys_cmp();
            broadcast use vstd::std_specs::btree::group_btree_axioms;
        }
        let mut stack = self.variables.remove(&name).unwrap_or_default();
        if !stack.is_empty() {
            stack.pop();
        }
        stack.push(v);
        self.variables.insert(name, stack);
    }

    /// Pushes `v` on variable `name`'s stack (a new name first gets its global frame 0).
    pub(crate) fn var_push(&mut self, name: String, v: BCNum)
        requires
            old(self).inv(),
            v.scale <= BC_SCALE_MAX,
        ensures
            final(self).inv(),
            same_but_storage(*old(self), *final(self)),
            ({
                let m = old(self).variables@;
                let t = final(self).variables@[name]@;
                &&& final(self).variables@.dom() == m.dom().insert(name)
                &&& if m.contains_key(name) {
                    t == m[name]@.push(v)
                } else {
                    t.len() == 2 && t[0].val() == BCNum::spec_zero_val() && t[0].scale == 0 && t[1] == v
                }
                &&& forall|k: String| k != name && #[trigger] m.contains_key(k) ==> final(self).variables@[k] == m[k]
            }),
            final(self).arrays@ == old(self).arrays@,
    {
        proof {
            axiom_string_obeys_cmp();
            broadcast use vstd::std_specs::btree::group_btree_axioms;
        }
        let mut stack = match self.variables.remove(&name) {
            Some(s) => s,
            None => vec![BCNum::zero()],
        };
        stack.push(v);
        self.variables.insert(name, stack);
    }

    /// Pops the top of variable `name`'s stack, if it has one.
    pub(crate) fn var_pop(&mut self, name: &String)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            same_but_storage(*old(self), *final(self)),
            ({
                let m = old(self).variables@;
                if m.contains_key(*name) {
                    &&& final(self).variables@.dom() == m.dom()
                    &&& final(self).variables@[*name]@ == if m[*name]@.len() > 0 { m[*name]@.drop_last() } else { m[*name]@ }
                    &&& forall|k: String| k != *name && #[trigger] m.contains_key(k) ==> final(self).variables@[k] == m[k]
                } else {
                    final(self).variables@ == m
                }
            }),
            final(self).arrays@ == old(self).arrays@,
    {
        proof {
            axiom_string_obeys_cmp();
            broadcast use vstd::std_specs::btree::group_btree_axioms;
        }
        if let Some(mut stack) = self.variables.remove(name) {
            if !stack.is_empty() {
                stack.pop();
            }
            self.variables.insert(name.clone(), stack);
        }
    }

    /// Sets element `idx` of array `name`'s current frame to `v` (a new name, or an empty
    /// stack, gets a frame).
    pub(crate) fn arr_set(&mut self, name: String, idx: usize, v: BCNum)
        requires
            old(self).inv(),
            v.scale <= BC_SCALE_MAX,
        ensures
            final(self).inv(),
            same_but_storage(*old(self), *final(self)),
            ({
                let m = old(self).arrays@;
                let s = if m.contains_key(name) { m[name]@ } else { Seq::empty() };
                let t = final(self).arrays@[name]@;
                &&& final(self).arrays@.dom() == m.dom().insert(name)
                &&& t.len() == if s.len() > 0 { s.len() } else { 1 }
                &&& t.drop_last() == if s.len() > 0 { s.drop_last() } else { Seq::empty() }
                &&& t.last()@ == if s.len() > 0 { s.last()@.insert(idx, v) } else { Map::empty().insert(idx, v) }
                &&& forall|k: String| k != name && #[trigger] m.contains_key(k) ==> final(self).arrays@[k] == m[k]
            }),
            final(self).variables@ == old(self).variables@,
    {
        proof {
            axiom_string_obeys_cmp();
            broadcast use vstd::std_specs::btree::group_btree_axioms;
            broadcast use vstd::laws_cmp::group_laws_cmp;
        }
        let mut stack = self.arrays.remove(&name).unwrap_or_default();
        let mut frame = stack.pop().unwrap_or_default();
        frame.insert(idx, v);
        stack.push(frame);
        self.arrays.insert(name, stack);
    }

    /// Pushes `frame` on array `name`'s stack (a new name first gets its empty global frame).
    pub(crate) fn arr_push(&mut self, name: String, frame: BTreeMap<usize, BCNum>)
        requires
            old(self).inv(),
            frame_ok(frame@),
        ensures
            final(self).inv(),
            same_but_storage(*old(self), *final(self)),
            ({
                let m = old(self).arrays@;
                let t = final(self).arrays@[name]@;
                &&& final(self).arrays@.dom() == m.dom().insert(name)
                &&& if m.contains_key(name) {
                    t == m[name]@.push(frame)
                } else {
                    t.len() == 2 && t[0]@ == Map::<usize, BCNum>::empty() && t[1] == frame
                }
                &&& forall|k: String| k != name && #[trigger] m.contains_key(k) ==> final(self).arrays@[k] == m[k]
            }),
            final(self).variables@ == old(self).variables@,
    {
        proof {
            axiom_string_obeys_cmp();
            broadcast use vstd::std_specs::btree::group_btree_axioms;
        }
        let mut stack = match self.arrays.remove(&name) {
            Some(s) => s,
            None => vec![BTreeMap::new()],
        };
        stack.push(frame);
        self.arrays.insert(name, stack);
    }

    /// Pops the current frame of array `name`, if it has one.
    pub(crate) fn arr_pop(&mut self, name: &String)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            same_but_storage(*old(self), *final(self)),
            ({
                let m = old(self).arrays@;
                if m.contains_key(*name) {
                    &&& final(self).arrays@.dom() == m.dom()
                    &&& final(self).arrays@[*name]@ == if m[*name]@.len() > 0 { m[*name]@.drop_last() } else { m[*name]@ }
                    &&& forall|k: String| k != *name && #[trigger] m.contains_key(k) ==> final(self).arrays@[k] == m[k]
                } else {
                    final(self).arrays@ == m
                }
            }),
            final(self).variables@ == old(self).variables@,
    {
        proof {
            axiom_string_obeys_cmp();
            broadcast use vstd::std_specs::btree::group_btree_axioms;
        }
        if let Some(mut stack) = self.arrays.remove(name) {
            if !stack.is_empty() {
                stack.pop();
            }
            self.arrays.insert(name.clone(), stack);
        }
    }

    /// The value of element `idx` of array `name`'s current frame (0 if unset).
    pub(crate) fn arr_get(&self, name: &String, idx: usize) -> (r: BCNum)
        requires
            self.inv(),
        ensures
            r.scale <= BC_SCALE_MAX,
            ({
                let m = self.arrays@;
                if m.contains_key(*name) && m[*name]@.len() > 0 && m[*name]@.last()@.contains_key(idx) {
                    r.val() == m[*name]@.last()@[idx].val()
                } else {
                    r.val() == BCNum::spec_zero_val()
                }
            }),
    {
        proof {
            axiom_string_obeys_cmp();
            broadcast use vstd::std_specs::btree::group_btree_axioms;
            broadcast use vstd::laws_cmp::group_laws_cmp;
        }
        match self.arrays.get(name) {
            Some(stack) => {
                if !stack.is_empty() {
                    match stack[stack.len() - 1].get(&idx) {
                        Some(v) => v.copy(),
                        None => BCNum::zero(),
                    }
                } else {
                    BCNum::zero()
                }
            },
            None => BCNum::zero(),
        }
    }
}

/// The ghost arguments of the refinement proofs; `()` in normal builds, where `verus!` erases
/// the proofs but keeps `Ghost` parameters.
#[cfg(verus_keep_ghost)]
pub(crate) type SpecNodes = Seq<bc_spec::parser::Node>;
#[cfg(not(verus_keep_ghost))]
pub(crate) type SpecNodes = ();
#[cfg(verus_keep_ghost)]
pub(crate) type SpecState = EState;
#[cfg(verus_keep_ghost)]
pub(crate) type SpecNum = bc_spec::num::Num;
#[cfg(verus_keep_ghost)]
pub(crate) type SpecPlace = bc_spec::eval::Place;
#[cfg(not(verus_keep_ghost))]
pub(crate) type SpecPlace = ();
#[cfg(not(verus_keep_ghost))]
pub(crate) type SpecNum = ();
#[cfg(not(verus_keep_ghost))]
pub(crate) type SpecState = ();

/// The result of evaluating corresponds to the specification's `ER`: an error leaves the
/// evaluator at depth `d` (the specification leaves its depth deeper, which `run_unit` resets).
pub(crate) open spec fn r_result(r: Result<BCNum, BcError>, e: Evaluator, x: ER, d: usize) -> bool {
    match r {
        Ok(v) => x.ok && r_num(v, x.val) && r_state(e, x.st),
        Err(err) => !x.ok && r_err(err, x.err) && r_state(e, with_depth(x.st, d as u64)),
    }
}

/// The value part of the specification's `ev_assign` (the `x` it stores): a single hexadecimal
/// digit for `ibase`/`obase`, the value of `=`, or `old <op> value` for `op=`.
pub(crate) open spec fn assign_x(nodes: Seq<bc_spec::parser::Node>, p: bc_spec::eval::Place, op: u8, v: usize, st: EState, f: u64) -> ER {
    if bc_spec::eval::single_digit_base(nodes, p, op, v) {
        let txt = bc_spec::eval::number_text(nodes, v);
        er_ok(st, num_u64(bc_spec::eval::hex_val(if txt.len() > 0 { txt[0] } else { 0u8 })))
    } else if op == 0 {
        ev(nodes, v, st, f)
    } else {
        let old = bc_spec::eval::load(st, p);
        let rhs = ev(nodes, v, st, f);
        if !rhs.ok { rhs } else { spec_arith(rhs.st, (op - 1) as u8, old, rhs.val) }
    }
}

pub(crate) proof fn lemma_assign_x_mono(nodes: Seq<bc_spec::parser::Node>, p: bc_spec::eval::Place, op: u8, v: usize, st: EState, f: u64, g: u64)
    requires
        f <= g,
        done(assign_x(nodes, p, op, v, st, f)),
    ensures
        assign_x(nodes, p, op, v, st, g) == assign_x(nodes, p, op, v, st, f),
{
    if !bc_spec::eval::single_digit_base(nodes, p, op, v) {
        lemma_ev_mono(nodes, v, st, f, g);
    }
}

/// `e1` and `e2` differ at most in their variables and arrays.
pub(crate) open spec fn same_but_storage(e1: Evaluator, e2: Evaluator) -> bool {
    &&& e1.functions == e2.functions
    &&& e1.scale == e2.scale
    &&& e1.ibase == e2.ibase
    &&& e1.obase == e2.obase
    &&& e1.math_enabled == e2.math_enabled
    &&& e1.stdout_writer == e2.stdout_writer
    &&& e1.stderr_writer == e2.stderr_writer
    &&& e1.break_flag == e2.break_flag
    &&& e1.return_flag == e2.return_flag
    &&& e1.return_value == e2.return_value
    &&& e1.quit_flag == e2.quit_flag
    &&& e1.extension_policy == e2.extension_policy
    &&& e1.call_stack == e2.call_stack
    &&& e1.max_depth == e2.max_depth
    &&& e1.eval_depth == e2.eval_depth
    &&& e1.invocation_ibase == e2.invocation_ibase
}

/// A resolved target corresponds to the specification's `Place`.
spec fn r_place(p: Place, sp: bc_spec::eval::Place) -> bool {
    match p {
        Place::Variable(n) => sp.kind == 0 && sp.name == text_view(n),
        Place::Element(n, i) => sp.kind == 1 && sp.name == text_view(n) && sp.idx as int == i as int && i < 16777216,
        Place::Register(r) => sp.kind == 2 && sp.reg == reg_code(r),
    }
}

/// `e1` and `e2` differ at most in their diagnostic stream.
pub(crate) open spec fn same_but_err(e1: Evaluator, e2: Evaluator) -> bool {
    &&& e1.variables == e2.variables
    &&& e1.arrays == e2.arrays
    &&& e1.functions == e2.functions
    &&& e1.scale == e2.scale
    &&& e1.ibase == e2.ibase
    &&& e1.obase == e2.obase
    &&& e1.math_enabled == e2.math_enabled
    &&& e1.stdout_writer == e2.stdout_writer
    &&& e1.break_flag == e2.break_flag
    &&& e1.return_flag == e2.return_flag
    &&& e1.return_value == e2.return_value
    &&& e1.quit_flag == e2.quit_flag
    &&& e1.extension_policy == e2.extension_policy
    &&& e1.call_stack == e2.call_stack
    &&& e1.max_depth == e2.max_depth
    &&& e1.eval_depth == e2.eval_depth
    &&& e1.invocation_ibase == e2.invocation_ibase
}

impl WrappedStdout {
    /// Writes `b` (UTF-8 text) to standard output with POSIX line wrapping (the verified
    /// `format::wrap_output`). Trusted: the stream receives exactly the wrapped bytes, as the
    /// specification's `write_wrapped` describes; a failing writer is outside the model.
    #[verifier::external_body]
    pub(crate) fn write_bytes(&mut self, b: &[u8])
        ensures
            (out_log(final(self)), out_col(final(self))) == write_wrapped(out_log(old(self)), out_col(old(self)), b@),
    {
        let (out, col) = wrap_output(self.col, b);
        self.col = col;
        if let Ok(text) = core::str::from_utf8(&out) {
            let _ = self.writer.write_str(text);
        }
    }

    /// Flushes the underlying writer (no effect on what has been written).
    #[verifier::external_body]
    pub(crate) fn flush_out(&mut self)
        ensures
            out_log(final(self)) == out_log(old(self)),
            out_col(final(self)) == out_col(old(self)),
    {
        let _ = self.writer.flush();
    }
}

impl ErrWriter {
    /// Writes `b` (UTF-8 text) to the diagnostic stream. Trusted: the stream receives exactly
    /// these bytes; a failing writer is outside the model (diagnostics ignore write errors).
    #[verifier::external_body]
    pub(crate) fn write_bytes(&mut self, b: &[u8])
        ensures
            err_log(final(self)) == err_log(old(self)).add(b@),
    {
        if let Ok(text) = core::str::from_utf8(b) {
            let _ = self.writer.write_str(text);
        }
    }
}

/// The result of executing a statement corresponds to the specification's `ER` (as
/// `r_result`, without a value).
pub(crate) open spec fn r_unit(r: Result<(), BcError>, e: Evaluator, x: ER, d: usize) -> bool {
    match r {
        Ok(_) => x.ok && r_state(e, x.st),
        Err(err) => !x.ok && r_err(err, x.err) && r_state(e, with_depth(x.st, d as u64)),
    }
}

/// `e1` and `e2` differ at most in their evaluation depth.
pub(crate) open spec fn same_but_depth(e1: Evaluator, e2: Evaluator) -> bool {
    &&& e1.variables == e2.variables
    &&& e1.arrays == e2.arrays
    &&& e1.functions == e2.functions
    &&& e1.scale == e2.scale
    &&& e1.ibase == e2.ibase
    &&& e1.obase == e2.obase
    &&& e1.math_enabled == e2.math_enabled
    &&& e1.stdout_writer == e2.stdout_writer
    &&& e1.stderr_writer == e2.stderr_writer
    &&& e1.break_flag == e2.break_flag
    &&& e1.return_flag == e2.return_flag
    &&& e1.return_value == e2.return_value
    &&& e1.quit_flag == e2.quit_flag
    &&& e1.extension_policy == e2.extension_policy
    &&& e1.call_stack == e2.call_stack
    &&& e1.max_depth == e2.max_depth
    &&& e1.invocation_ibase == e2.invocation_ibase
}

/// Changing only the depth keeps the state related, at the new depth.
pub(crate) proof fn lemma_r_state_depth(e1: Evaluator, e2: Evaluator, st: EState)
    requires
        r_state(e1, st),
        same_but_depth(e1, e2),
    ensures
        r_state(e2, with_depth(st, e2.eval_depth as u64)),
{
}

impl Evaluator {
    /// Evaluates an AST expression node, returning Err on runtime math/call errors.
    pub fn try_evaluate(&mut self, node: &Expr) -> (r: Result<BCNum, BcError>)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            r is Ok ==> r->Ok_0.scale <= BC_SCALE_MAX,
    {
        self.eval_ref(node, Ghost(arbitrary()), Ghost(0usize), Ghost(arbitrary()))
    }

    /// Executes an AST statement node, returning Err on runtime errors.
    pub fn try_execute(&mut self, node: &Stmt) -> (r: Result<(), BcError>)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
    {
        self.exec_ref(node, Ghost(arbitrary()), Ghost(0usize), Ghost(arbitrary()))
    }

    /// `try_evaluate` with the arena subtree `n` of `nodes` and the specification state `st` it
    /// corresponds to: one nesting level around `eval_node_ref` (the specification's `ev`).
    /// Whenever the specification finishes (with any fuel), the result corresponds to it.
    #[verifier::exec_allows_no_decreases_clause]
    pub(crate) fn eval_ref(
        &mut self,
        node: &Expr,
        Ghost(nodes): Ghost<SpecNodes>,
        Ghost(n): Ghost<usize>,
        Ghost(st): Ghost<SpecState>,
    ) -> (r: Result<BCNum, BcError>)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            final(self).eval_depth == old(self).eval_depth,
            r is Ok ==> r->Ok_0.scale <= BC_SCALE_MAX,
            (r_state(*old(self), st) && r_expr(*node, nodes, n) && in_fragment(*node)) ==> forall|f: u64|
                done(#[trigger] ev(nodes, n, st, f)) ==> r_result(r, *final(self), ev(nodes, n, st, f), old(self).eval_depth),
    {
        let ghost d = self.eval_depth;
        let ghost hyp = r_state(*self, st) && r_expr(*node, nodes, n) && in_fragment(*node);
        if !verified_nesting_within_limit(self.eval_depth, 1, self.max_depth) {
            let r = Err(BcError::Runtime { kind: RuntimeError::NestingTooDeep, func: None });
            proof {
                if hyp {
                    assert(with_depth(st, d as u64) == st);
                    assert forall|f: u64| done(#[trigger] ev(nodes, n, st, f)) implies r_result(r, *self, ev(nodes, n, st, f), d) by {}
                }
            }
            return r;
        }
        let ghost before = *self;
        self.eval_depth += 1;
        let ghost st1 = with_depth(st, (d + 1) as u64);
        proof {
            if hyp {
                lemma_r_state_depth(before, *self, st);
            }
        }
        let r = self.eval_node_ref(node, Ghost(nodes), Ghost(n), Ghost(st1));
        let ghost mid = *self;
        self.eval_depth -= 1;
        proof {
            if hyp {
                assert forall|f: u64| done(#[trigger] ev(nodes, n, st, f)) implies r_result(r, *self, ev(nodes, n, st, f), d) by {
                    let x = ev_node(nodes, n, st1, (f - 1) as u64);
                    assert(done(x));
                    assert(r_result(r, mid, x, (d + 1) as usize));
                    if r is Ok {
                        lemma_r_state_depth(mid, *self, x.st);
                        assert(with_depth(with_depth(x.st, d as u64), st.depth) == with_depth(x.st, st.depth));
                    } else {
                        lemma_r_state_depth(mid, *self, with_depth(x.st, (d + 1) as u64));
                        assert(with_depth(with_depth(x.st, (d + 1) as u64), d as u64) == with_depth(x.st, d as u64));
                    }
                }
            }
        }
        r
    }

    /// `evaluate_node` (the specification's `ev_node`) for the expressions in `in_fragment`;
    /// the others go to `eval_other`.
    #[verifier::exec_allows_no_decreases_clause]
    pub(crate) fn eval_node_ref(
        &mut self,
        node: &Expr,
        Ghost(nodes): Ghost<SpecNodes>,
        Ghost(n): Ghost<usize>,
        Ghost(st): Ghost<SpecState>,
    ) -> (r: Result<BCNum, BcError>)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            final(self).eval_depth == old(self).eval_depth,
            r is Ok ==> r->Ok_0.scale <= BC_SCALE_MAX,
            (r_state(*old(self), st) && r_expr(*node, nodes, n) && in_fragment(*node)) ==> forall|f: u64|
                done(#[trigger] ev_node(nodes, n, st, f)) ==> r_result(r, *final(self), ev_node(nodes, n, st, f), old(self).eval_depth),
    {
        match node {
            Expr::RegisterAccess(reg) => self.eval_register(*reg, Ghost(nodes), Ghost(n), Ghost(st)),
            Expr::Number(t) => self.eval_number(t, Ghost(nodes), Ghost(n), Ghost(st)),
            Expr::Variable(name) => self.eval_variable(name, Ghost(nodes), Ghost(n), Ghost(st)),
            Expr::AssignOp(op, target, value) => self.eval_assign(Ghost(*node), *op, target, value, Ghost(nodes), Ghost(n), Ghost(st)),
            Expr::Update(increment, prefix, target) => self.eval_update(Ghost(*node), *increment, *prefix, target, Ghost(nodes), Ghost(n), Ghost(st)),
            Expr::ArrayAccess(name, index) => self.eval_array(Ghost(*node), name, index, Ghost(nodes), Ghost(n), Ghost(st)),
            Expr::Paren(inner) => self.eval_paren(Ghost(*node), inner, Ghost(nodes), Ghost(n), Ghost(st)),
            Expr::Negate(inner) => self.eval_negate(Ghost(*node), inner, Ghost(nodes), Ghost(n), Ghost(st)),
            Expr::LengthCall(inner) => self.eval_length(Ghost(*node), inner, Ghost(nodes), Ghost(n), Ghost(st)),
            Expr::ScaleCall(inner) => self.eval_scale_of(Ghost(*node), inner, Ghost(nodes), Ghost(n), Ghost(st)),
            Expr::SqrtCall(inner) => self.eval_sqrt(Ghost(*node), inner, Ghost(nodes), Ghost(n), Ghost(st)),
            Expr::BinaryOp(op, left, right) => self.eval_binary(Ghost(*node), *op, left, right, Ghost(nodes), Ghost(n), Ghost(st)),
            Expr::RelationalOp(op, left, right) => self.eval_rel(Ghost(*node), *op, left, right, Ghost(nodes), Ghost(n), Ghost(st)),
            _ => self.eval_other(node),
        }
    }

    fn eval_register(&mut self, reg: Register, Ghost(nodes): Ghost<SpecNodes>, Ghost(n): Ghost<usize>, Ghost(st): Ghost<SpecState>) -> (r: Result<BCNum, BcError>)
        requires
            old(self).inv(),
        ensures
            *final(self) == *old(self),
            r is Ok && r->Ok_0.scale == 0,
            (r_state(*old(self), st) && r_expr(Expr::RegisterAccess(reg), nodes, n)) ==> forall|f: u64|
                done(#[trigger] ev_node(nodes, n, st, f)) ==> r_result(r, *final(self), ev_node(nodes, n, st, f), old(self).eval_depth),
    {
        let value = match reg {
            Register::Scale => self.scale,
            Register::Ibase => self.ibase,
            Register::Obase => self.obase,
        };
        let v = BCNum::new(big_from_usize(value), 0);
        proof {
            let x = num_u64(reg_get(st, reg_code(reg)) as u64);
            lemma_u64_mag(reg_get(st, reg_code(reg)) as u64);
        }
        Ok(v)
    }

    #[verifier::exec_allows_no_decreases_clause]
    fn eval_paren(&mut self, Ghost(node): Ghost<Expr>, inner: &Expr, Ghost(nodes): Ghost<SpecNodes>, Ghost(n): Ghost<usize>, Ghost(st): Ghost<SpecState>) -> (r: Result<BCNum, BcError>)
        requires
            old(self).inv(),
            node == Expr::Paren(Box::new(*inner)),
        ensures
            final(self).inv(),
            final(self).eval_depth == old(self).eval_depth,
            r is Ok ==> r->Ok_0.scale <= BC_SCALE_MAX,
            (r_state(*old(self), st) && r_expr(node, nodes, n) && in_fragment(node)) ==> forall|f: u64|
                done(#[trigger] ev_node(nodes, n, st, f)) ==> r_result(r, *final(self), ev_node(nodes, n, st, f), old(self).eval_depth),
    {
        let ghost d = self.eval_depth;
        let ghost hyp = r_state(*self, st) && r_expr(node, nodes, n) && in_fragment(node);
        let ghost j = if n < nodes.len() { match nodes[n as int] { Node::Paren(j) => j, _ => 0usize } } else { 0usize };
        let r = self.eval_ref(inner, Ghost(nodes), Ghost(j), Ghost(st));
        proof {
            if hyp {
                assert forall|f: u64| done(#[trigger] ev_node(nodes, n, st, f)) implies r_result(r, *self, ev_node(nodes, n, st, f), d) by {
                    assert(f >= 1);
                    assert(ev_node(nodes, n, st, f) == ev(nodes, j, st, (f - 1) as u64));
                }
            }
        }
        r
    }

    #[verifier::exec_allows_no_decreases_clause]
    fn eval_negate(&mut self, Ghost(node): Ghost<Expr>, inner: &Expr, Ghost(nodes): Ghost<SpecNodes>, Ghost(n): Ghost<usize>, Ghost(st): Ghost<SpecState>) -> (r: Result<BCNum, BcError>)
        requires
            old(self).inv(),
            node == Expr::Negate(Box::new(*inner)),
        ensures
            final(self).inv(),
            final(self).eval_depth == old(self).eval_depth,
            r is Ok ==> r->Ok_0.scale <= BC_SCALE_MAX,
            (r_state(*old(self), st) && r_expr(node, nodes, n) && in_fragment(node)) ==> forall|f: u64|
                done(#[trigger] ev_node(nodes, n, st, f)) ==> r_result(r, *final(self), ev_node(nodes, n, st, f), old(self).eval_depth),
    {
        let ghost d = self.eval_depth;
        let ghost hyp = r_state(*self, st) && r_expr(node, nodes, n) && in_fragment(node);
        let ghost j = if n < nodes.len() { match nodes[n as int] { Node::Neg(j) => j, _ => 0usize } } else { 0usize };
        let r0 = self.eval_ref(inner, Ghost(nodes), Ghost(j), Ghost(st));
        let v = match r0 {
            Ok(v) => v,
            Err(e) => {
                proof {
                    if hyp {
                        assert forall|f: u64| done(#[trigger] ev_node(nodes, n, st, f)) implies r_result(Err(e), *self, ev_node(nodes, n, st, f), d) by {
                            let x = ev(nodes, j, st, (f - 2) as u64);
                            assert(f >= 2);
                            assert(done(x));
                        }
                    }
                }
                return Err(e);
            },
        };
        let w = BCNum::new(big_neg(&v.coeff), v.scale);
        proof {
            if hyp {
                assert forall|f: u64| done(#[trigger] ev_node(nodes, n, st, f)) implies r_result(Ok(w), *self, ev_node(nodes, n, st, f), d) by {
                    let x = ev(nodes, j, st, (f - 2) as u64);
                    assert(f >= 2);
                    assert(done(x));
                    lemma_is_zero_mag(x.val.mag);
                    assert(r_num(w, negate(x.val)));
                }
            }
        }
        Ok(w)
    }

    #[verifier::exec_allows_no_decreases_clause]
    fn eval_length(&mut self, Ghost(node): Ghost<Expr>, inner: &Expr, Ghost(nodes): Ghost<SpecNodes>, Ghost(n): Ghost<usize>, Ghost(st): Ghost<SpecState>) -> (r: Result<BCNum, BcError>)
        requires
            old(self).inv(),
            node == Expr::LengthCall(Box::new(*inner)),
        ensures
            final(self).inv(),
            final(self).eval_depth == old(self).eval_depth,
            r is Ok ==> r->Ok_0.scale <= BC_SCALE_MAX,
            (r_state(*old(self), st) && r_expr(node, nodes, n) && in_fragment(node)) ==> forall|f: u64|
                done(#[trigger] ev_node(nodes, n, st, f)) ==> r_result(r, *final(self), ev_node(nodes, n, st, f), old(self).eval_depth),
    {
        let ghost d = self.eval_depth;
        let ghost hyp = r_state(*self, st) && r_expr(node, nodes, n) && in_fragment(node);
        let ghost j = if n < nodes.len() { match nodes[n as int] { Node::Length(j) => j, _ => 0usize } } else { 0usize };
        let r0 = self.eval_ref(inner, Ghost(nodes), Ghost(j), Ghost(st));
        let v = match r0 {
            Ok(v) => v,
            Err(e) => {
                proof {
                    if hyp {
                        assert forall|f: u64| done(#[trigger] ev_node(nodes, n, st, f)) implies r_result(Err(e), *self, ev_node(nodes, n, st, f), d) by {
                            let x = ev(nodes, j, st, (f - 2) as u64);
                            assert(f >= 2);
                            assert(done(x));
                        }
                    }
                }
                return Err(e);
            },
        };
        let w = v.length();
        proof {
            if hyp {
                assert forall|f: u64| done(#[trigger] ev_node(nodes, n, st, f)) implies r_result(Ok(w), *self, ev_node(nodes, n, st, f), d) by {
                    let x = ev(nodes, j, st, (f - 2) as u64);
                    assert(f >= 2);
                    assert(done(x));
                    let a = x.val;
                    axiom_bigint_size(&v.coeff);
                    lemma_mag_bounds(a.mag);
                    lemma_num_length(a);
                    let lr = num_length(a);
                    lemma_pow10_pos(a.scale as nat);
                    let ip = mag_val(a.mag) / spec_num::pow10(a.scale as nat);
                    if ip > 0 {
                        lemma_digit_count_unique(ip, (big_view(&w.coeff) - a.scale) as nat, (mag_val(lr.mag) - a.scale) as nat);
                    }
                    assert(r_num(w, lr));
                }
            }
        }
        Ok(w)
    }

    #[verifier::exec_allows_no_decreases_clause]
    fn eval_scale_of(&mut self, Ghost(node): Ghost<Expr>, inner: &Expr, Ghost(nodes): Ghost<SpecNodes>, Ghost(n): Ghost<usize>, Ghost(st): Ghost<SpecState>) -> (r: Result<BCNum, BcError>)
        requires
            old(self).inv(),
            node == Expr::ScaleCall(Box::new(*inner)),
        ensures
            final(self).inv(),
            final(self).eval_depth == old(self).eval_depth,
            r is Ok ==> r->Ok_0.scale <= BC_SCALE_MAX,
            (r_state(*old(self), st) && r_expr(node, nodes, n) && in_fragment(node)) ==> forall|f: u64|
                done(#[trigger] ev_node(nodes, n, st, f)) ==> r_result(r, *final(self), ev_node(nodes, n, st, f), old(self).eval_depth),
    {
        let ghost d = self.eval_depth;
        let ghost hyp = r_state(*self, st) && r_expr(node, nodes, n) && in_fragment(node);
        let ghost j = if n < nodes.len() { match nodes[n as int] { Node::ScaleOf(j) => j, _ => 0usize } } else { 0usize };
        let r0 = self.eval_ref(inner, Ghost(nodes), Ghost(j), Ghost(st));
        let v = match r0 {
            Ok(v) => v,
            Err(e) => {
                proof {
                    if hyp {
                        assert forall|f: u64| done(#[trigger] ev_node(nodes, n, st, f)) implies r_result(Err(e), *self, ev_node(nodes, n, st, f), d) by {
                            let x = ev(nodes, j, st, (f - 2) as u64);
                            assert(f >= 2);
                            assert(done(x));
                        }
                    }
                }
                return Err(e);
            },
        };
        let w = v.scale_func();
        proof {
            if hyp {
                assert forall|f: u64| done(#[trigger] ev_node(nodes, n, st, f)) implies r_result(Ok(w), *self, ev_node(nodes, n, st, f), d) by {
                    let x = ev(nodes, j, st, (f - 2) as u64);
                    assert(f >= 2);
                    assert(done(x));
                    lemma_num_scale(x.val);
                    assert(r_num(w, num_scale(x.val)));
                }
            }
        }
        Ok(w)
    }

    #[verifier::exec_allows_no_decreases_clause]
    fn eval_sqrt(&mut self, Ghost(node): Ghost<Expr>, inner: &Expr, Ghost(nodes): Ghost<SpecNodes>, Ghost(n): Ghost<usize>, Ghost(st): Ghost<SpecState>) -> (r: Result<BCNum, BcError>)
        requires
            old(self).inv(),
            node == Expr::SqrtCall(Box::new(*inner)),
        ensures
            final(self).inv(),
            final(self).eval_depth == old(self).eval_depth,
            r is Ok ==> r->Ok_0.scale <= BC_SCALE_MAX,
            (r_state(*old(self), st) && r_expr(node, nodes, n) && in_fragment(node)) ==> forall|f: u64|
                done(#[trigger] ev_node(nodes, n, st, f)) ==> r_result(r, *final(self), ev_node(nodes, n, st, f), old(self).eval_depth),
    {
        let ghost d = self.eval_depth;
        let ghost hyp = r_state(*self, st) && r_expr(node, nodes, n) && in_fragment(node);
        let ghost j = if n < nodes.len() { match nodes[n as int] { Node::Sqrt(j) => j, _ => 0usize } } else { 0usize };
        let r0 = self.eval_ref(inner, Ghost(nodes), Ghost(j), Ghost(st));
        let v = match r0 {
            Ok(v) => v,
            Err(e) => {
                proof {
                    if hyp {
                        assert forall|f: u64| done(#[trigger] ev_node(nodes, n, st, f)) implies r_result(Err(e), *self, ev_node(nodes, n, st, f), d) by {
                            let x = ev(nodes, j, st, (f - 2) as u64);
                            assert(f >= 2);
                            assert(done(x));
                        }
                    }
                }
                return Err(e);
            },
        };
        let r1 = v.try_sqrt(self.scale);
        let r = match r1 {
            Ok(w) => Ok(w),
            Err(k) => Err(BcError::Runtime { kind: k, func: None }),
        };
        proof {
            if hyp {
                assert forall|f: u64| done(#[trigger] ev_node(nodes, n, st, f)) implies r_result(r, *self, ev_node(nodes, n, st, f), d) by {
                    let x = ev(nodes, j, st, (f - 2) as u64);
                    assert(f >= 2);
                    assert(done(x));
                    let a = x.val;
                    lemma_num_sqrt(a, x.st.scale);
                    assert(with_depth(x.st, d as u64) == x.st);
                    match num_sqrt(a, x.st.scale) {
                        NumRes::Ok(q) => {
                            let w = r->Ok_0;
                            let sr = w.scale;
                            lemma_isqrt_unique(num_coeff(a) * spec_num::pow10((2 * sr - a.scale) as nat), big_view(&w.coeff), num_coeff(q));
                            assert(r_num(w, q));
                        },
                        _ => {},
                    }
                }
            }
        }
        r
    }

    /// `l <op> r` at the current `scale` (the specification's `arith`), for the specification
    /// numbers `a`, `b` and state `st` that `l`, `r` and the evaluator correspond to. `^` goes
    /// through `power_other` (not proved yet).
    fn arith_ref(&mut self, op: BinOp, l: &BCNum, r: &BCNum, Ghost(a): Ghost<SpecNum>, Ghost(b): Ghost<SpecNum>, Ghost(st): Ghost<SpecState>) -> (res: Result<BCNum, BcError>)
        requires
            old(self).inv(),
            l.scale <= BC_SCALE_MAX,
            r.scale <= BC_SCALE_MAX,
        ensures
            final(self).inv(),
            final(self).eval_depth == old(self).eval_depth,
            res is Ok ==> res->Ok_0.scale <= BC_SCALE_MAX,
            (r_state(*old(self), st) && r_num(*l, a) && r_num(*r, b)) ==>
                r_result(res, *final(self), spec_arith(st, bin_code(op), a, b), old(self).eval_depth),
    {
        let ghost hyp = op != BinOp::Pow && r_state(*self, st) && r_num(*l, a) && r_num(*r, b);
        proof {
            if hyp {
                assert(with_depth(st, self.eval_depth as u64) == st);
                lemma_is_zero_mag(b.mag);
                lemma_mag_bounds(b.mag);
            }
        }
        match op {
            BinOp::Add => {
                let v = l.add(r);
                proof { if hyp { lemma_num_add(a, b); } }
                Ok(v)
            },
            BinOp::Sub => {
                let v = l.sub(r);
                proof { if hyp { lemma_num_sub(a, b); } }
                Ok(v)
            },
            BinOp::Mul => {
                let v = l.mul(r, self.scale);
                proof { if hyp { lemma_num_mul(a, b, st.scale); } }
                Ok(v)
            },
            BinOp::Div => {
                let q = l.try_div(r, self.scale);
                proof { if hyp && mag_val(b.mag) > 0 { lemma_num_div(a, b, st.scale); } }
                match q {
                    Ok(v) => Ok(v),
                    Err(k) => Err(BcError::Runtime { kind: k, func: None }),
                }
            },
            BinOp::Mod => {
                let q = l.try_mod_op(r, self.scale);
                proof { if hyp && mag_val(b.mag) > 0 && st.scale + b.scale <= 1_000_000_000 { lemma_num_mod(a, b, st.scale); } }
                match q {
                    Ok(v) => Ok(v),
                    Err(k) => Err(BcError::Runtime { kind: k, func: None }),
                }
            },
            BinOp::Pow => self.power_ref(l, r, Ghost(a), Ghost(b), Ghost(st)),
        }
    }


    /// `l <op> r` (the specification's `ev_binary`): both operands are evaluated, left first,
    /// before the operator applies.
    #[verifier::exec_allows_no_decreases_clause]
    #[allow(
        clippy::too_many_arguments,
        reason = "three of them are the Ghost arguments of the refinement proof"
    )]
    fn eval_binary(&mut self, Ghost(node): Ghost<Expr>, op: BinOp, left: &Expr, right: &Expr, Ghost(nodes): Ghost<SpecNodes>, Ghost(n): Ghost<usize>, Ghost(st): Ghost<SpecState>) -> (r: Result<BCNum, BcError>)
        requires
            old(self).inv(),
            node == Expr::BinaryOp(op, Box::new(*left), Box::new(*right)),
        ensures
            final(self).inv(),
            final(self).eval_depth == old(self).eval_depth,
            r is Ok ==> r->Ok_0.scale <= BC_SCALE_MAX,
            (r_state(*old(self), st) && r_expr(node, nodes, n) && in_fragment(node)) ==> forall|f: u64|
                done(#[trigger] ev_node(nodes, n, st, f)) ==> r_result(r, *final(self), ev_node(nodes, n, st, f), old(self).eval_depth),
    {
        let ghost d = self.eval_depth;
        let ghost hyp = r_state(*self, st) && r_expr(node, nodes, n) && in_fragment(node);
        let ghost (ja, jb) = if n < nodes.len() {
            match nodes[n as int] {
                Node::Binary(_, a, b) => (a, b),
                Node::Rel(_, a, b) => (a, b),
                _ => (0usize, 0usize),
            }
        } else {
            (0usize, 0usize)
        };
        let ra = self.eval_ref(left, Ghost(nodes), Ghost(ja), Ghost(st));
        let ghost fa = choose|f: u64| done(#[trigger] ev(nodes, ja, st, f));
        let ghost xa = ev(nodes, ja, st, fa);
        let l = match ra {
            Ok(v) => v,
            Err(e) => {
                proof {
                    if hyp {
                        assert forall|f: u64| done(#[trigger] ev_node(nodes, n, st, f)) implies r_result(Err(e), *self, ev_node(nodes, n, st, f), d) by {
                            assert(f >= 2);
                            assert(done(ev(nodes, ja, st, (f - 2) as u64)));
                        }
                    }
                }
                return Err(e);
            },
        };
        let rb = self.eval_ref(right, Ghost(nodes), Ghost(jb), Ghost(xa.st));
        let ghost fb = choose|f: u64| done(#[trigger] ev(nodes, jb, xa.st, f));
        let ghost xb = ev(nodes, jb, xa.st, fb);
        // Whatever fuel finishes, the operands' results are xa and xb.
        proof {
            if hyp {
                assert forall|f: u64| done(#[trigger] ev(nodes, ja, st, f)) implies ev(nodes, ja, st, f) == xa by {
                    if fa <= f { lemma_ev_mono(nodes, ja, st, fa, f); } else { lemma_ev_mono(nodes, ja, st, f, fa); }
                }
                assert forall|f: u64| done(#[trigger] ev(nodes, jb, xa.st, f)) implies ev(nodes, jb, xa.st, f) == xb by {
                    if fb <= f { lemma_ev_mono(nodes, jb, xa.st, fb, f); } else { lemma_ev_mono(nodes, jb, xa.st, f, fb); }
                }
            }
        }
        let r = match rb {
            Ok(v) => v,
            Err(e) => {
                proof {
                    if hyp {
                        assert forall|f: u64| done(#[trigger] ev_node(nodes, n, st, f)) implies r_result(Err(e), *self, ev_node(nodes, n, st, f), d) by {
                            assert(f >= 2);
                            assert(done(ev(nodes, ja, st, (f - 2) as u64)));
                            assert(done(ev(nodes, jb, xa.st, (f - 2) as u64)));
                        }
                    }
                }
                return Err(e);
            },
        };
        let res = self.arith_ref(op, &l, &r, Ghost(xa.val), Ghost(xb.val), Ghost(xb.st));
        proof {
            if hyp {
                assert forall|f: u64| done(#[trigger] ev_node(nodes, n, st, f)) implies r_result(res, *self, ev_node(nodes, n, st, f), d) by {
                    assert(f >= 2);
                    assert(done(ev(nodes, ja, st, (f - 2) as u64)));
                    assert(done(ev(nodes, jb, xa.st, (f - 2) as u64)));
                }
            }
        }
        res
    }

    /// A relational expression (the specification's `ev_rel`): 1 if it holds, else 0.
    #[verifier::exec_allows_no_decreases_clause]
    #[allow(
        clippy::too_many_arguments,
        reason = "three of them are the Ghost arguments of the refinement proof"
    )]
    fn eval_rel(&mut self, Ghost(node): Ghost<Expr>, op: RelOp, left: &Expr, right: &Expr, Ghost(nodes): Ghost<SpecNodes>, Ghost(n): Ghost<usize>, Ghost(st): Ghost<SpecState>) -> (r: Result<BCNum, BcError>)
        requires
            old(self).inv(),
            node == Expr::RelationalOp(op, Box::new(*left), Box::new(*right)),
        ensures
            final(self).inv(),
            final(self).eval_depth == old(self).eval_depth,
            r is Ok ==> r->Ok_0.scale <= BC_SCALE_MAX,
            (r_state(*old(self), st) && r_expr(node, nodes, n) && in_fragment(node)) ==> forall|f: u64|
                done(#[trigger] ev_node(nodes, n, st, f)) ==> r_result(r, *final(self), ev_node(nodes, n, st, f), old(self).eval_depth),
    {
        let ghost d = self.eval_depth;
        let ghost hyp = r_state(*self, st) && r_expr(node, nodes, n) && in_fragment(node);
        let ghost (ja, jb) = if n < nodes.len() {
            match nodes[n as int] {
                Node::Binary(_, a, b) => (a, b),
                Node::Rel(_, a, b) => (a, b),
                _ => (0usize, 0usize),
            }
        } else {
            (0usize, 0usize)
        };
        let ra = self.eval_ref(left, Ghost(nodes), Ghost(ja), Ghost(st));
        let ghost fa = choose|f: u64| done(#[trigger] ev(nodes, ja, st, f));
        let ghost xa = ev(nodes, ja, st, fa);
        let l = match ra {
            Ok(v) => v,
            Err(e) => {
                proof {
                    if hyp {
                        assert forall|f: u64| done(#[trigger] ev_node(nodes, n, st, f)) implies r_result(Err(e), *self, ev_node(nodes, n, st, f), d) by {
                            assert(f >= 2);
                            assert(done(ev(nodes, ja, st, (f - 2) as u64)));
                        }
                    }
                }
                return Err(e);
            },
        };
        let rb = self.eval_ref(right, Ghost(nodes), Ghost(jb), Ghost(xa.st));
        let ghost fb = choose|f: u64| done(#[trigger] ev(nodes, jb, xa.st, f));
        let ghost xb = ev(nodes, jb, xa.st, fb);
        // Whatever fuel finishes, the operands' results are xa and xb.
        proof {
            if hyp {
                assert forall|f: u64| done(#[trigger] ev(nodes, ja, st, f)) implies ev(nodes, ja, st, f) == xa by {
                    if fa <= f { lemma_ev_mono(nodes, ja, st, fa, f); } else { lemma_ev_mono(nodes, ja, st, f, fa); }
                }
                assert forall|f: u64| done(#[trigger] ev(nodes, jb, xa.st, f)) implies ev(nodes, jb, xa.st, f) == xb by {
                    if fb <= f { lemma_ev_mono(nodes, jb, xa.st, fb, f); } else { lemma_ev_mono(nodes, jb, xa.st, f, fb); }
                }
            }
        }
        let r = match rb {
            Ok(v) => v,
            Err(e) => {
                proof {
                    if hyp {
                        assert forall|f: u64| done(#[trigger] ev_node(nodes, n, st, f)) implies r_result(Err(e), *self, ev_node(nodes, n, st, f), d) by {
                            assert(f >= 2);
                            assert(done(ev(nodes, ja, st, (f - 2) as u64)));
                            assert(done(ev(nodes, jb, xa.st, (f - 2) as u64)));
                        }
                    }
                }
                return Err(e);
            },
        };
        let ord = l.cmp_val(&r);
        let holds = match op {
            RelOp::Eq => matches!(ord, Ordering::Equal),
            RelOp::Ne => !matches!(ord, Ordering::Equal),
            RelOp::Lt => matches!(ord, Ordering::Less),
            RelOp::Le => !matches!(ord, Ordering::Greater),
            RelOp::Gt => matches!(ord, Ordering::Greater),
            RelOp::Ge => !matches!(ord, Ordering::Less),
        };
        let v = BCNum::new(big_from_usize(if holds { 1 } else { 0 }), 0);
        proof {
            if hyp {
                lemma_one_mag();
                lemma_u64_mag(0);
                assert forall|f: u64| done(#[trigger] ev_node(nodes, n, st, f)) implies r_result(Ok(v), *self, ev_node(nodes, n, st, f), d) by {
                    assert(f >= 2);
                    assert(done(ev(nodes, ja, st, (f - 2) as u64)));
                    assert(done(ev(nodes, jb, xa.st, (f - 2) as u64)));
                    lemma_num_cmp(xa.val, xb.val);
                    assert(holds == rel_holds(rel_code(op), num_cmp(xa.val, xb.val)));
                }
            }
        }
        Ok(v)
    }

    /// The value of a variable (the specification's `var_get`).
    fn eval_variable(&mut self, name: &String, Ghost(nodes): Ghost<SpecNodes>, Ghost(n): Ghost<usize>, Ghost(st): Ghost<SpecState>) -> (r: Result<BCNum, BcError>)
        requires
            old(self).inv(),
        ensures
            *final(self) == *old(self),
            r is Ok && r->Ok_0.scale <= BC_SCALE_MAX,
            (r_state(*old(self), st) && r_expr(Expr::Variable(*name), nodes, n)) ==> forall|f: u64|
                done(#[trigger] ev_node(nodes, n, st, f)) ==> r_result(r, *final(self), ev_node(nodes, n, st, f), old(self).eval_depth),
    {
        let v = self.var_get(name);
        proof {
            if r_state(*self, st) && r_expr(Expr::Variable(*name), nodes, n) {
                let nm = text_view(*name);
                lemma_var_get(st.vars, nm);
                if self.variables@.contains_key(*name) {
                    let s = var_lookup(st.vars, nm)->Some_0;
                    assert(r_stack(self.variables@[*name]@, s));
                    if s.len() > 0 {
                        assert(r_num(self.variables@[*name]@[s.len() - 1], s[s.len() - 1]));
                    }
                } else {
                    lemma_var_absent(self.variables@, st.vars, *name);
                }
                assert(r_num(v, var_get(st.vars, nm)));
            }
        }
        Ok(v)
    }

    /// Converts the subscript `idx` of array `name` to an index, truncating it to an integer
    /// (the specification's `array_index`). Negative subscripts and subscripts of at least
    /// `BC_DIM_MAX` are runtime errors.
    #[allow(clippy::cast_possible_truncation, reason = "the index is below BC_DIM_MAX = 2^24")]
    #[allow(clippy::ptr_arg, reason = "the specification relates the error to the String")]
    fn array_index_ref(name: &String, idx: &BCNum) -> (r: Result<usize, BcError>)
        requires
            idx.scale <= BC_SCALE_MAX,
        ensures
            forall|x: SpecNum| #[trigger] r_num(*idx, x) ==> match r {
                Ok(i) => array_index(x).0 && array_index(x).1 == i,
                Err(e) => !array_index(x).0 && e == BcError::Runtime {
                    kind: RuntimeError::ArraySubscriptOutOfBounds(*name),
                    func: None,
                },
            },
    {
        proof {
            lemma_pow10_pos(idx.scale as nat);
        }
        let index = big_tdiv(&idx.coeff, &pow10_within(idx.scale));
        let below = matches!(big_cmp(&index, &big_from_usize(BC_DIM_MAX)), Ordering::Less);
        let r = if big_is_negative(&idx.coeff) || !below {
            Err(BcError::Runtime { kind: RuntimeError::ArraySubscriptOutOfBounds(name.clone()), func: None })
        } else {
            Ok(big_to_u64_small(&index) as usize)
        };
        proof {
            assert forall|x: SpecNum| #[trigger] r_num(*idx, x) implies match r {
                Ok(i) => array_index(x).0 && array_index(x).1 == i,
                Err(e) => !array_index(x).0 && e == BcError::Runtime {
                    kind: RuntimeError::ArraySubscriptOutOfBounds(*name),
                    func: None,
                },
            } by {
                lemma_array_index_value(x);
                lemma_mag_bounds(x.mag);
            }
        }
        r
    }

    /// An array element (the specification's `ev_array`): the subscript is evaluated first.
    #[verifier::exec_allows_no_decreases_clause]
    fn eval_array(&mut self, Ghost(node): Ghost<Expr>, name: &String, index: &Expr, Ghost(nodes): Ghost<SpecNodes>, Ghost(n): Ghost<usize>, Ghost(st): Ghost<SpecState>) -> (r: Result<BCNum, BcError>)
        requires
            old(self).inv(),
            node == Expr::ArrayAccess(*name, Box::new(*index)),
        ensures
            final(self).inv(),
            final(self).eval_depth == old(self).eval_depth,
            r is Ok ==> r->Ok_0.scale <= BC_SCALE_MAX,
            (r_state(*old(self), st) && r_expr(node, nodes, n) && in_fragment(node)) ==> forall|f: u64|
                done(#[trigger] ev_node(nodes, n, st, f)) ==> r_result(r, *final(self), ev_node(nodes, n, st, f), old(self).eval_depth),
    {
        let ghost d = self.eval_depth;
        let ghost hyp = r_state(*self, st) && r_expr(node, nodes, n) && in_fragment(node);
        let ghost j = if n < nodes.len() { match nodes[n as int] { Node::Array(_, j) => j, _ => 0usize } } else { 0usize };
        let r0 = self.eval_ref(index, Ghost(nodes), Ghost(j), Ghost(st));
        let v = match r0 {
            Ok(v) => v,
            Err(e) => {
                proof {
                    if hyp {
                        assert forall|f: u64| done(#[trigger] ev_node(nodes, n, st, f)) implies r_result(Err(e), *self, ev_node(nodes, n, st, f), d) by {
                            assert(f >= 2);
                            assert(done(ev(nodes, j, st, (f - 2) as u64)));
                        }
                    }
                }
                return Err(e);
            },
        };
        let i = match Self::array_index_ref(name, &v) {
            Ok(i) => i,
            Err(e) => {
                proof {
                    if hyp {
                        assert forall|f: u64| done(#[trigger] ev_node(nodes, n, st, f)) implies r_result(Err(e), *self, ev_node(nodes, n, st, f), d) by {
                            assert(f >= 2);
                            let x = ev(nodes, j, st, (f - 2) as u64);
                            assert(done(x));
                            assert(r_num(v, x.val));
                            assert(with_depth(x.st, d as u64) == x.st);
                        }
                    }
                }
                return Err(e);
            },
        };
        let w = self.arr_get(name, i);
        proof {
            if hyp {
                assert forall|f: u64| done(#[trigger] ev_node(nodes, n, st, f)) implies r_result(Ok(w), *self, ev_node(nodes, n, st, f), d) by {
                    assert(f >= 2);
                    let x = ev(nodes, j, st, (f - 2) as u64);
                    assert(done(x));
                    assert(r_num(v, x.val));
                    let nm = text_view(*name);
                    lemma_array_index_value(x.val);
                    let idx = array_index(x.val).1;
                    assert(i == idx && (idx as int) < 16777216);
                    lemma_arr_top(x.st.arrays, nm);
                    lemma_elem_get(arr_top(x.st.arrays, nm).elems, idx);
                    let m = self.arrays@;
                    if m.contains_key(*name) {
                        let ss = arr_lookup(x.st.arrays, nm)->Some_0;
                        assert(r_frames(m[*name]@, ss));
                        if ss.len() > 0 {
                            assert(r_frame(m[*name]@[ss.len() - 1]@, ss[ss.len() - 1]));
                            assert(i < 16777216);
                        }
                    } else {
                        lemma_arr_absent(m, x.st.arrays, *name);
                    }
                    assert(r_num(w, elem_get(arr_top(x.st.arrays, nm).elems, idx)));
                }
            }
        }
        Ok(w)
    }

    /// Writes `Runtime warning (func=<current function>): <msg>` to the diagnostic stream (the
    /// specification's `warn`).
    fn warn_ref(&mut self, msg: &[u8], Ghost(st): Ghost<SpecState>)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            same_but_err(*old(self), *final(self)),
            r_state(*old(self), st) ==> r_state(*final(self), bc_spec::eval::warn(st, msg@)),
    {
        let ghost e0 = *self;
        let head: [u8; 22] = [82, 117, 110, 116, 105, 109, 101, 32, 119, 97, 114, 110, 105, 110, 103, 32, 40, 102, 117, 110, 99, 61];
        self.stderr_writer.write_bytes(&head);
        let n = self.call_stack.len();
        let main: [u8; 6] = [40, 109, 97, 105, 110, 41];
        if n > 0 {
            #[allow(
                clippy::redundant_as_str,
                reason = "Verus specifies str::as_bytes and String::as_str, not String::as_bytes"
            )]
            self.stderr_writer.write_bytes(self.call_stack[n - 1].as_str().as_bytes());
        } else {
            self.stderr_writer.write_bytes(&main);
        }
        let sep: [u8; 3] = [41, 58, 32];
        self.stderr_writer.write_bytes(&sep);
        self.stderr_writer.write_bytes(msg);
        let nl: [u8; 1] = [10];
        self.stderr_writer.write_bytes(&nl);
        proof {
            if r_state(e0, st) {
                let w = bc_spec::eval::warn(st, msg@);
                assert(head@ == seq![82u8, 117, 110, 116, 105, 109, 101, 32, 119, 97, 114, 110, 105, 110, 103, 32, 40, 102, 117, 110, 99, 61]);
                assert(main@ == seq![40u8, 109, 97, 105, 110, 41]);
                assert(sep@ == seq![41u8, 58, 32]);
                assert(nl@ == seq![10u8]);
                if n > 0 {
                    assert(text_view(e0.call_stack@[n - 1]) == st.calls[st.calls.len() - 1]);
                }
                assert(err_log(&self.stderr_writer) =~= w.err);
            }
        }
    }

    /// `l ^ r` at the current `scale` (the specification's `arith` for `^`): a warning when the
    /// exponent has a fraction, then the verified `try_pow`.
    fn power_ref(&mut self, l: &BCNum, r: &BCNum, Ghost(a): Ghost<SpecNum>, Ghost(b): Ghost<SpecNum>, Ghost(st): Ghost<SpecState>) -> (res: Result<BCNum, BcError>)
        requires
            old(self).inv(),
            l.scale <= BC_SCALE_MAX,
            r.scale <= BC_SCALE_MAX,
        ensures
            final(self).inv(),
            final(self).eval_depth == old(self).eval_depth,
            res is Ok ==> res->Ok_0.scale <= BC_SCALE_MAX,
            (r_state(*old(self), st) && r_num(*l, a) && r_num(*r, b)) ==>
                r_result(res, *final(self), spec_arith(st, 5u8, a, b), old(self).eval_depth),
    {
        let ghost e0 = *self;
        let ghost st2 = if b.scale > 0 { bc_spec::eval::warn(st, seq![110u8, 111, 110, 45, 122, 101, 114, 111, 32, 115, 99, 97, 108, 101, 32, 105, 110, 32, 101, 120, 112, 111, 110, 101, 110, 116]) } else { st };
        if r.scale > 0 {
            let msg: [u8; 26] = [110, 111, 110, 45, 122, 101, 114, 111, 32, 115, 99, 97, 108, 101, 32, 105, 110, 32, 101, 120, 112, 111, 110, 101, 110, 116];
            proof {
                assert(msg@ == seq![110u8, 111, 110, 45, 122, 101, 114, 111, 32, 115, 99, 97, 108, 101, 32, 105, 110, 32, 101, 120, 112, 111, 110, 101, 110, 116]);
            }
            self.warn_ref(&msg, Ghost(st));
        }
        let q = l.try_pow(r, self.scale);
        let res = match q {
            Ok(v) => Ok(v),
            Err(k) => Err(BcError::Runtime { kind: k, func: None }),
        };
        proof {
            if r_state(e0, st) && r_num(*l, a) && r_num(*r, b) {
                assert(r_state(*self, st2));
                assert(with_depth(st2, self.eval_depth as u64) == st2);
                lemma_num_pow(a, b, st2.scale);
            }
        }
        res
    }

    /// A numeric constant in the `ibase` of the current invocation (the specification's
    /// `literal`): its text split into digit values by `literal_digit_values`, and converted by
    /// the verified `BCNum::from_digit_values`.
    #[allow(clippy::ptr_arg, reason = "the specification relates the constant's String")]
    fn literal_ref(&self, t: &String, Ghost(st): Ghost<SpecState>) -> (r: Result<BCNum, BcError>)
        requires
            self.inv(),
        ensures
            r is Ok ==> r->Ok_0.scale <= BC_SCALE_MAX,
            r_state(*self, st) ==> r_result(r, *self, bc_spec::eval::literal(st, text_view(*t)), self.eval_depth),
    {
        let ib = match self.invocation_ibase {
            Some(b) => b,
            None => self.ibase,
        };
        let (ds, fs) = literal_digit_values(t.as_str().as_bytes());
        if fs.len() > BC_SCALE_MAX {
            let r = Err(BcError::Runtime { kind: RuntimeError::ScaleTooLarge, func: None });
            proof {
                if r_state(*self, st) {
                    assert(with_depth(st, self.eval_depth as u64) == st);
                }
            }
            return r;
        }
        let v = BCNum::from_digit_values(&ds, &fs, ib);
        proof {
            if r_state(*self, st) {
                lemma_num_from_digits(ds@, fs@, ib as u8);
                assert(r_num(v, num_from_digits(ds@, fs@, ib as u8)));
            }
        }
        Ok(v)
    }

    /// The value of a numeric constant (the specification's `ev_node` for `Node::Number`).
    fn eval_number(&mut self, t: &String, Ghost(nodes): Ghost<SpecNodes>, Ghost(n): Ghost<usize>, Ghost(st): Ghost<SpecState>) -> (r: Result<BCNum, BcError>)
        requires
            old(self).inv(),
        ensures
            *final(self) == *old(self),
            r is Ok ==> r->Ok_0.scale <= BC_SCALE_MAX,
            (r_state(*old(self), st) && r_expr(Expr::Number(*t), nodes, n)) ==> forall|f: u64|
                done(#[trigger] ev_node(nodes, n, st, f)) ==> r_result(r, *final(self), ev_node(nodes, n, st, f), old(self).eval_depth),
    {
        self.literal_ref(t, Ghost(st))
    }

    /// The integer part of `|val|`, as `max + 1` if it exceeds `max`, and whether `val` is
    /// negative: what the specification's `store_register` compares with the register's range.
    #[allow(clippy::cast_possible_truncation, reason = "a magnitude of at most max <= 2^31")]
    fn register_magnitude(val: &BCNum, max: usize) -> (r: (usize, bool))
        requires
            val.scale <= BC_SCALE_MAX,
            max <= BC_BASE_MAX,
        ensures
            r.0 <= max + 1,
            forall|x: SpecNum| #[trigger] r_num(*val, x) ==> {
                let m = bc_spec::power::mag_to_u64(bc_spec::num::drop_mag(x.mag, x.scale));
                &&& r.1 == (x.neg && !bc_spec::num::is_zero_mag(x.mag))
                &&& (r.0 > max) == (m > max as u64)
                &&& r.0 <= max ==> r.0 as u64 == m
            },
    {
        proof {
            lemma_pow10_pos(val.scale as nat);
        }
        let ip = big_abs(&big_tdiv(&val.coeff, &pow10_within(val.scale)));
        let negative = big_is_negative(&val.coeff);
        let magnitude = if matches!(big_cmp(&ip, &big_from_usize(max)), Ordering::Greater) {
            max + 1
        } else {
            big_to_u64_small(&ip) as usize
        };
        proof {
            assert forall|x: SpecNum| #[trigger] r_num(*val, x) implies {
                let m = bc_spec::power::mag_to_u64(bc_spec::num::drop_mag(x.mag, x.scale));
                &&& negative == (x.neg && !bc_spec::num::is_zero_mag(x.mag))
                &&& (magnitude > max) == (m > max as u64)
                &&& magnitude <= max ==> magnitude as u64 == m
            } by {
                lemma_register_input(x);
                lemma_mag_bounds(x.mag);
                let c = num_coeff(x);
                let p = spec_num::pow10(x.scale as nat);
                assert(spec_tdiv(c, p) == (if c >= 0 { c / p } else { -((-c) / p) }));
                assert(big_view(&ip) == int_mag(x));
            }
        }
        (magnitude, negative)
    }

    /// The text of a register clamp warning (the specification's `store_register`): `kind` -2
    /// negative, -1 too small, 1 too large.
    fn register_message(reg: Register, kind: i8, min: usize, max: usize) -> (msg: Vec<u8>)
        requires
            kind == -2 || kind == -1 || kind == 1,
        ensures
            msg@ == if kind == -2 {
                seq![110u8, 101, 103, 97, 116, 105, 118, 101, 32].add(bc_spec::eval::reg_name(reg_code(reg)))
                    .add(seq![44u8, 32, 115, 101, 116, 32, 116, 111, 32]).add(dec_str(min as u64))
            } else if kind == -1 {
                bc_spec::eval::reg_name(reg_code(reg)).add(seq![32u8, 116, 111, 111, 32, 115, 109, 97, 108, 108, 44, 32, 115, 101, 116, 32, 116, 111, 32]).add(dec_str(min as u64))
            } else {
                bc_spec::eval::reg_name(reg_code(reg)).add(seq![32u8, 116, 111, 111, 32, 108, 97, 114, 103, 101, 44, 32, 115, 101, 116, 32, 116, 111, 32]).add(dec_str(max as u64))
            },
    {
        let name: [u8; 5] = match reg {
            Register::Scale => [115, 99, 97, 108, 101],
            Register::Ibase => [105, 98, 97, 115, 101],
            Register::Obase => [111, 98, 97, 115, 101],
        };
        proof {
            assert(name@ == bc_spec::eval::reg_name(reg_code(reg)));
        }
        let mut msg: Vec<u8> = Vec::new();
        if kind == -2 {
            let neg: [u8; 9] = [110, 101, 103, 97, 116, 105, 118, 101, 32];
            let set: [u8; 9] = [44, 32, 115, 101, 116, 32, 116, 111, 32];
            msg.extend_from_slice(&neg);
            msg.extend_from_slice(&name);
            msg.extend_from_slice(&set);
            push_dec(&mut msg, min as u64);
            proof {
                assert(neg@ == seq![110u8, 101, 103, 97, 116, 105, 118, 101, 32]);
                assert(set@ == seq![44u8, 32, 115, 101, 116, 32, 116, 111, 32]);
                assert(msg@ =~= neg@.add(name@).add(set@).add(dec_str(min as u64)));
            }
        } else {
            let small: [u8; 19] = [32, 116, 111, 111, 32, 115, 109, 97, 108, 108, 44, 32, 115, 101, 116, 32, 116, 111, 32];
            let large: [u8; 19] = [32, 116, 111, 111, 32, 108, 97, 114, 103, 101, 44, 32, 115, 101, 116, 32, 116, 111, 32];
            msg.extend_from_slice(&name);
            if kind == -1 {
                msg.extend_from_slice(&small);
                push_dec(&mut msg, min as u64);
                proof {
                    assert(small@ == seq![32u8, 116, 111, 111, 32, 115, 109, 97, 108, 108, 44, 32, 115, 101, 116, 32, 116, 111, 32]);
                    assert(msg@ =~= name@.add(small@).add(dec_str(min as u64)));
                }
            } else {
                msg.extend_from_slice(&large);
                push_dec(&mut msg, max as u64);
                proof {
                    assert(large@ == seq![32u8, 116, 111, 111, 32, 108, 97, 114, 103, 101, 44, 32, 115, 101, 116, 32, 116, 111, 32]);
                    assert(msg@ =~= name@.add(large@).add(dec_str(max as u64)));
                }
            }
        }
        msg
    }

    /// Stores `val`, truncated to an integer, into register `reg`, clamping it to the register's
    /// range with a warning (`docs/COMPATIBILITY.md` §3.3; the specification's
    /// `store_register`). Returns the stored value.
    fn store_register_ref(&mut self, reg: Register, val: &BCNum, Ghost(st): Ghost<SpecState>, Ghost(x): Ghost<SpecNum>) -> (r: usize)
        requires
            old(self).inv(),
            val.scale <= BC_SCALE_MAX,
        ensures
            final(self).inv(),
            final(self).eval_depth == old(self).eval_depth,
            (r_state(*old(self), st) && r_num(*val, x)) ==> ({
                let s = bc_spec::eval::store_register(st, reg_code(reg), x);
                &&& r_state(*final(self), s.st)
                &&& to_l0(s.val) == BCNum::spec_new_usize(r) && wf_num(s.val)
            }),
            r <= BC_BASE_MAX,
    {
        let ghost e0 = *self;
        let (min, max) = match reg {
            Register::Scale => (0usize, BC_SCALE_MAX),
            Register::Ibase => (2usize, IBASE_MAX),
            Register::Obase => (2usize, BC_BASE_MAX),
        };
        let (magnitude, negative) = Self::register_magnitude(val, max);
        let (v, kind) = verified_clamp_register(magnitude, negative, min, max);
        let ghost msg_spec: Seq<u8> = Seq::empty();
        if kind != 0 {
            let msg = Self::register_message(reg, kind, min, max);
            proof {
                msg_spec = msg@;
            }
            self.warn_ref(&msg, Ghost(st));
        }
        match reg {
            Register::Scale => self.scale = v,
            Register::Ibase => self.ibase = v,
            Register::Obase => self.obase = v,
        }
        proof {
            if r_state(e0, st) && r_num(*val, x) {
                let r8 = reg_code(reg);
                assert(min as int == bc_spec::eval::reg_min(r8) as int && max as int == bc_spec::eval::reg_max(r8) as int);
                lemma_u64_mag(v as u64);
                let s = bc_spec::eval::store_register(st, r8, x);
                assert(r_state(*self, s.st));
            }
        }
        v
    }

    /// Resolves an assignment target (the specification's `resolve`), evaluating an array
    /// subscript exactly once.
    #[verifier::exec_allows_no_decreases_clause]
    fn resolve_ref(&mut self, target: &Expr, Ghost(nodes): Ghost<SpecNodes>, Ghost(n): Ghost<usize>, Ghost(st): Ghost<SpecState>) -> (r: Result<Place, BcError>)
        requires
            old(self).inv(),
            named(*target),
        ensures
            final(self).inv(),
            final(self).eval_depth == old(self).eval_depth,
            (r_state(*old(self), st) && r_expr(*target, nodes, n) && in_fragment(*target)) ==> forall|f: u64|
                done(#[trigger] resolve(nodes, n, st, f).r) ==> ({
                    let pr = resolve(nodes, n, st, f);
                    match r {
                        Ok(p) => pr.r.ok && r_place(p, pr.place) && r_state(*final(self), pr.r.st),
                        Err(e) => !pr.r.ok && r_err(e, pr.r.err) && r_state(*final(self), with_depth(pr.r.st, old(self).eval_depth as u64)),
                    }
                }),
    {
        let ghost d = self.eval_depth;
        let ghost hyp = r_state(*self, st) && r_expr(*target, nodes, n) && in_fragment(*target);
        match target {
            Expr::Variable(name) => Ok(Place::Variable(name.clone())),
            Expr::RegisterAccess(reg) => Ok(Place::Register(*reg)),
            Expr::ArrayAccess(name, index) => {
                let ghost j = if n < nodes.len() { match nodes[n as int] { Node::Array(_, j) => j, _ => 0usize } } else { 0usize };
                let v = match self.eval_ref(index, Ghost(nodes), Ghost(j), Ghost(st)) {
                    Ok(v) => v,
                    Err(e) => {
                        proof {
                            if hyp {
                                assert forall|f: u64| done(#[trigger] resolve(nodes, n, st, f).r) implies {
                                    let pr = resolve(nodes, n, st, f);
                                    !pr.r.ok && r_err(e, pr.r.err) && r_state(*self, with_depth(pr.r.st, d as u64))
                                } by {
                                    assert(done(ev(nodes, j, st, (f - 1) as u64)));
                                }
                            }
                        }
                        return Err(e);
                    },
                };
                let i = match Self::array_index_ref(name, &v) {
                    Ok(i) => i,
                    Err(e) => {
                        proof {
                            if hyp {
                                assert forall|f: u64| done(#[trigger] resolve(nodes, n, st, f).r) implies {
                                    let pr = resolve(nodes, n, st, f);
                                    !pr.r.ok && r_err(e, pr.r.err) && r_state(*self, with_depth(pr.r.st, d as u64))
                                } by {
                                    let x = ev(nodes, j, st, (f - 1) as u64);
                                    assert(done(x));
                                    assert(r_num(v, x.val));
                                    assert(with_depth(x.st, d as u64) == x.st);
                                }
                            }
                        }
                        return Err(e);
                    },
                };
                let p = Place::Element(name.clone(), i);
                proof {
                    if hyp {
                        assert forall|f: u64| done(#[trigger] resolve(nodes, n, st, f).r) implies {
                            let pr = resolve(nodes, n, st, f);
                            pr.r.ok && r_place(p, pr.place) && r_state(*self, pr.r.st)
                        } by {
                            let x = ev(nodes, j, st, (f - 1) as u64);
                            assert(done(x));
                            assert(r_num(v, x.val));
                            lemma_array_index_value(x.val);
                        }
                    }
                }
                Ok(p)
            },
            _ => Err(BcError::Runtime { kind: RuntimeError::NestingTooDeep, func: None }),
        }
    }

    /// Reads the current value of a resolved target (the specification's `load`).
    fn load_ref(&self, p: &Place, Ghost(sp): Ghost<SpecPlace>, Ghost(st): Ghost<SpecState>) -> (r: BCNum)
        requires
            self.inv(),
        ensures
            r.scale <= BC_SCALE_MAX,
            (r_state(*self, st) && r_place(*p, sp)) ==> r_num(r, bc_spec::eval::load(st, sp)),
    {
        match p {
            Place::Variable(name) => {
                let v = self.var_get(name);
                proof {
                    if r_state(*self, st) && r_place(*p, sp) {
                        let nm = text_view(*name);
                        lemma_var_get(st.vars, nm);
                        if self.variables@.contains_key(*name) {
                            let ss = var_lookup(st.vars, nm)->Some_0;
                            assert(r_stack(self.variables@[*name]@, ss));
                            if ss.len() > 0 {
                                assert(r_num(self.variables@[*name]@[ss.len() - 1], ss[ss.len() - 1]));
                            }
                        } else {
                            lemma_var_absent(self.variables@, st.vars, *name);
                        }
                    }
                }
                v
            },
            Place::Element(name, i) => {
                let v = self.arr_get(name, *i);
                proof {
                    if r_state(*self, st) && r_place(*p, sp) {
                        let nm = text_view(*name);
                        lemma_arr_top(st.arrays, nm);
                        lemma_elem_get(arr_top(st.arrays, nm).elems, sp.idx);
                        let m = self.arrays@;
                        if m.contains_key(*name) {
                            let ss = arr_lookup(st.arrays, nm)->Some_0;
                            assert(r_frames(m[*name]@, ss));
                            if ss.len() > 0 {
                                assert(r_frame(m[*name]@[ss.len() - 1]@, ss[ss.len() - 1]));
                            }
                        } else {
                            lemma_arr_absent(m, st.arrays, *name);
                        }
                    }
                }
                v
            },
            Place::Register(reg) => {
                let value = match reg {
                    Register::Scale => self.scale,
                    Register::Ibase => self.ibase,
                    Register::Obase => self.obase,
                };
                proof {
                    lemma_u64_mag(value as u64);
                }
                BCNum::new(big_from_usize(value), 0)
            },
        }
    }

    /// Writes `val` to a resolved target (the specification's `store`) and returns the value now
    /// held there (registers clamp it).
    fn store_ref(&mut self, p: Place, val: BCNum, Ghost(sp): Ghost<SpecPlace>, Ghost(st): Ghost<SpecState>, Ghost(x): Ghost<SpecNum>) -> (r: BCNum)
        requires
            old(self).inv(),
            val.scale <= BC_SCALE_MAX,
        ensures
            final(self).inv(),
            final(self).eval_depth == old(self).eval_depth,
            r.scale <= BC_SCALE_MAX,
            (r_state(*old(self), st) && r_place(p, sp) && r_num(val, x)) ==> ({
                let s = bc_spec::eval::store(st, sp, x);
                r_state(*final(self), s.st) && r_num(r, s.val)
            }),
    {
        let ghost e0 = *self;
        let ghost hyp = r_state(*self, st) && r_place(p, sp) && r_num(val, x);
        match p {
            Place::Variable(name) => {
                let ghost m = self.variables@;
                let ghost nm = text_view(name);
                let ghost nm_name = name;
                let r = val.copy();
                self.var_set(name, val);
                proof {
                    if hyp {
                        if !m.contains_key(nm_name) {
                            lemma_var_absent(m, st.vars, nm_name);
                        }
                        let m2 = self.variables@;
                        let found = var_lookup(st.vars, nm);
                        assert(r_stack(m2[nm_name]@, upd_stack(found, 0u8, x)->Some_0));
                        lemma_r_vars_update(m, m2, st.vars, nm_name, 0u8, x);
                    }
                }
                r
            },
            Place::Element(name, i) => {
                let ghost m = self.arrays@;
                let ghost nm = text_view(name);
                let ghost nm_name = name;
                let ghost gval = val;
                let r = val.copy();
                self.arr_set(name, i, val);
                proof {
                    if hyp {
                        if !m.contains_key(nm_name) {
                            lemma_arr_absent(m, st.arrays, nm_name);
                        }
                        lemma_arr_top(st.arrays, nm);
                        let top = arr_top(st.arrays, nm);
                        let nf = bc_spec::eval::ArrFrame { elems: bc_spec::eval::elem_set(top.elems, i as u32, x, Seq::empty()) };
                        let m2 = self.arrays@;
                        let found = arr_lookup(st.arrays, nm);
                        let t = m2[nm_name]@;
                        if m.contains_key(nm_name) && m[nm_name]@.len() > 0 {
                            let ps = m[nm_name]@;
                            let ss = found->Some_0;
                            assert(r_frames(ps, ss));
                            assert(r_frame(ps[ps.len() - 1]@, ss[ss.len() - 1]));
                            lemma_r_frame_set(ps.last()@, top, i, gval, x);
                            let sn = bc_spec::eval::frame_op(ss, 0u8, nf);
                            assert(sn == ss.drop_last().push(nf));
                            assert forall|j: int| 0 <= j < t.len() implies #[trigger] r_frame(t[j]@, sn[j]) by {
                                if j < t.len() - 1 {
                                    assert(t[j] == t.drop_last()[j]);
                                    assert(t.drop_last()[j] == ps[j]);
                                }
                            }
                        } else {
                            assert(r_frame(Map::<usize, BCNum>::empty(), bc_spec::eval::ArrFrame { elems: Seq::empty() }));
                            lemma_r_frame_set(Map::<usize, BCNum>::empty(), top, i, gval, x);
                            let sn = upd_frames(found, 0u8, nf)->Some_0;
                            assert(sn.len() == 1 && sn[0] == nf);
                            assert(r_frame(t[0]@, sn[0]));
                        }
                        assert(r_frames(m2[nm_name]@, upd_frames(found, 0u8, nf)->Some_0));
                        lemma_r_arrays_update(m, m2, st.arrays, nm_name, 0u8, nf);
                    }
                }
                r
            },
            Place::Register(reg) => {
                let v = self.store_register_ref(reg, &val, Ghost(st), Ghost(x));
                proof {
                    lemma_u64_mag(v as u64);
                }
                BCNum::new(big_from_usize(v), 0)
            },
        }
    }

    /// An assignment (the specification's `ev_assign`): the target is resolved before the value
    /// is evaluated (as in GNU bc, `a[i++] = i` stores into `a[0]`), and the value of the
    /// assignment is the value assigned, even when a register clamps it. POSIX: a single digit
    /// assigned to `ibase` or `obase` is read as hexadecimal.
    #[verifier::exec_allows_no_decreases_clause]
    #[verifier::rlimit(50)]
    #[allow(
        clippy::too_many_arguments,
        reason = "three of them are the Ghost arguments of the refinement proof"
    )]
    fn eval_assign(&mut self, Ghost(node): Ghost<Expr>, op: AssignOp, target: &Expr, value: &Expr, Ghost(nodes): Ghost<SpecNodes>, Ghost(n): Ghost<usize>, Ghost(st): Ghost<SpecState>) -> (r: Result<BCNum, BcError>)
        requires
            old(self).inv(),
            node == Expr::AssignOp(op, Box::new(*target), Box::new(*value)),
        ensures
            final(self).inv(),
            final(self).eval_depth == old(self).eval_depth,
            r is Ok ==> r->Ok_0.scale <= BC_SCALE_MAX,
            (r_state(*old(self), st) && r_expr(node, nodes, n) && in_fragment(node)) ==> forall|f: u64|
                done(#[trigger] ev_node(nodes, n, st, f)) ==> r_result(r, *final(self), ev_node(nodes, n, st, f), old(self).eval_depth),
    {
        let ghost d = self.eval_depth;
        let ghost hyp = r_state(*self, st) && r_expr(node, nodes, n) && in_fragment(node);
        if !(matches!(target, Expr::Variable(_)) || matches!(target, Expr::ArrayAccess(..)) || matches!(target, Expr::RegisterAccess(_))) {
            // Not a named expression: the parser never builds this.
            return self.eval_other(&Expr::AssignOp(op, Box::new(target.clone()), Box::new(value.clone())));
        }
        let ghost (jt, jv) = if n < nodes.len() { match nodes[n as int] { Node::Assign(_, a, b) => (a, b), _ => (0usize, 0usize) } } else { (0usize, 0usize) };
        let place = match self.resolve_ref(target, Ghost(nodes), Ghost(jt), Ghost(st)) {
            Ok(p) => p,
            Err(e) => {
                proof {
                    if hyp {
                        assert forall|f: u64| done(#[trigger] ev_node(nodes, n, st, f)) implies r_result(Err(e), *self, ev_node(nodes, n, st, f), d) by {
                            assert(done(resolve(nodes, jt, st, (f - 2) as u64).r));
                        }
                    }
                }
                return Err(e);
            },
        };
        let ghost fr = choose|f: u64| done(#[trigger] resolve(nodes, jt, st, f).r);
        let ghost pr = resolve(nodes, jt, st, fr);
        proof {
            if hyp {
                assert forall|f: u64| done(#[trigger] resolve(nodes, jt, st, f).r) implies resolve(nodes, jt, st, f) == pr by {
                    if fr <= f { lemma_resolve_mono(nodes, jt, st, fr, f); } else { lemma_resolve_mono(nodes, jt, st, f, fr); }
                }
            }
        }
        let ghost st1 = pr.r.st;
        let ghost code = assign_code(op);
        let val = match self.assign_value(op, &place, value, Ghost(nodes), Ghost(jv), Ghost(pr.place), Ghost(st1)) {
            Ok(v) => v,
            Err(e) => {
                proof {
                    if hyp {
                        assert forall|f: u64| done(#[trigger] ev_node(nodes, n, st, f)) implies r_result(Err(e), *self, ev_node(nodes, n, st, f), d) by {
                            assert(done(resolve(nodes, jt, st, (f - 2) as u64).r));
                            assert(done(assign_x(nodes, pr.place, code, jv, st1, (f - 2) as u64)));
                        }
                    }
                }
                return Err(e);
            },
        };
        let ghost fx = choose|f: u64| done(#[trigger] assign_x(nodes, pr.place, code, jv, st1, f));
        let ghost x = assign_x(nodes, pr.place, code, jv, st1, fx);
        proof {
            if hyp {
                assert forall|f: u64| done(#[trigger] assign_x(nodes, pr.place, code, jv, st1, f)) implies assign_x(nodes, pr.place, code, jv, st1, f) == x by {
                    if fx <= f { lemma_assign_x_mono(nodes, pr.place, code, jv, st1, fx, f); } else { lemma_assign_x_mono(nodes, pr.place, code, jv, st1, f, fx); }
                }
            }
        }
        let r = val.copy();
        let _ = self.store_ref(place, val, Ghost(pr.place), Ghost(x.st), Ghost(x.val));
        proof {
            if hyp {
                assert forall|f: u64| done(#[trigger] ev_node(nodes, n, st, f)) implies r_result(Ok(r), *self, ev_node(nodes, n, st, f), d) by {
                    assert(done(resolve(nodes, jt, st, (f - 2) as u64).r));
                    assert(done(assign_x(nodes, pr.place, code, jv, st1, (f - 2) as u64)));
                }
            }
        }
        Ok(r)
    }

    /// The value an assignment stores (`assign_x`): a single hexadecimal digit for `ibase` or
    /// `obase`, the value of `=`, or the old value combined with the value of `op=`.
    #[verifier::exec_allows_no_decreases_clause]
    #[allow(
        clippy::too_many_arguments,
        reason = "four of them are the Ghost arguments of the refinement proof"
    )]
    fn assign_value(&mut self, op: AssignOp, place: &Place, value: &Expr, Ghost(nodes): Ghost<SpecNodes>, Ghost(jv): Ghost<usize>, Ghost(sp): Ghost<SpecPlace>, Ghost(st1): Ghost<SpecState>) -> (r: Result<BCNum, BcError>)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            final(self).eval_depth == old(self).eval_depth,
            r is Ok ==> r->Ok_0.scale <= BC_SCALE_MAX,
            (r_state(*old(self), st1) && r_place(*place, sp) && r_expr(*value, nodes, jv) && in_fragment(*value)) ==> forall|f: u64|
                done(#[trigger] assign_x(nodes, sp, assign_code(op), jv, st1, f))
                    ==> r_result(r, *final(self), assign_x(nodes, sp, assign_code(op), jv, st1, f), old(self).eval_depth),
    {
        let ghost d = self.eval_depth;
        let ghost hyp = r_state(*self, st1) && r_place(*place, sp) && r_expr(*value, nodes, jv) && in_fragment(*value);
        let ghost code = assign_code(op);
        let hex = match (place, op, value) {
            (Place::Register(Register::Ibase), AssignOp::Assign, Expr::Number(digits))
            | (Place::Register(Register::Obase), AssignOp::Assign, Expr::Number(digits)) => {
                let b = digits.as_str().as_bytes();
                if b.len() == 1 { Some(verified_hex_char_val(b[0])) } else { None }
            },
            _ => None,
        };
        if let Some(h) = hex {
            let v = BCNum::new(big_from_usize(h), 0);
            proof {
                if hyp {
                    lemma_u64_mag(h as u64);
                    assert(with_depth(st1, d as u64) == st1);
                }
            }
            return Ok(v);
        }
        let ghost fv = choose|f: u64| done(#[trigger] ev(nodes, jv, st1, f));
        let ghost xv = ev(nodes, jv, st1, fv);
        let old_val = match op {
            AssignOp::Assign => None,
            AssignOp::Compound(_) => Some(self.load_ref(place, Ghost(sp), Ghost(st1))),
        };
        let rhs = match self.eval_ref(value, Ghost(nodes), Ghost(jv), Ghost(st1)) {
            Ok(v) => v,
            Err(e) => {
                proof {
                    if hyp {
                        assert forall|f: u64| done(#[trigger] assign_x(nodes, sp, code, jv, st1, f)) implies r_result(Err(e), *self, assign_x(nodes, sp, code, jv, st1, f), d) by {
                            assert(done(ev(nodes, jv, st1, f)));
                        }
                    }
                }
                return Err(e);
            },
        };
        proof {
            if hyp {
                assert forall|f: u64| done(#[trigger] ev(nodes, jv, st1, f)) implies ev(nodes, jv, st1, f) == xv by {
                    if fv <= f { lemma_ev_mono(nodes, jv, st1, fv, f); } else { lemma_ev_mono(nodes, jv, st1, f, fv); }
                }
            }
        }
        match (op, old_val) {
            (AssignOp::Compound(bin), Some(old_v)) => {
                let res = self.arith_ref(bin, &old_v, &rhs, Ghost(bc_spec::eval::load(st1, sp)), Ghost(xv.val), Ghost(xv.st));
                proof {
                    if hyp {
                        assert forall|f: u64| done(#[trigger] assign_x(nodes, sp, code, jv, st1, f)) implies r_result(res, *self, assign_x(nodes, sp, code, jv, st1, f), d) by {
                            assert(done(ev(nodes, jv, st1, f)));
                        }
                    }
                }
                res
            },
            _ => {
                proof {
                    if hyp {
                        assert forall|f: u64| done(#[trigger] assign_x(nodes, sp, code, jv, st1, f)) implies r_result(Ok(rhs), *self, assign_x(nodes, sp, code, jv, st1, f), d) by {
                            assert(done(ev(nodes, jv, st1, f)));
                        }
                    }
                }
                Ok(rhs)
            },
        }
    }

    /// `++` / `--` (the specification's `ev_update`): a prefix form gives the stored value, a
    /// postfix form the old one.
    #[verifier::exec_allows_no_decreases_clause]
    #[allow(
        clippy::too_many_arguments,
        reason = "three of them are the Ghost arguments of the refinement proof"
    )]
    fn eval_update(&mut self, Ghost(node): Ghost<Expr>, increment: bool, prefix: bool, target: &Expr, Ghost(nodes): Ghost<SpecNodes>, Ghost(n): Ghost<usize>, Ghost(st): Ghost<SpecState>) -> (r: Result<BCNum, BcError>)
        requires
            old(self).inv(),
            node == Expr::Update(increment, prefix, Box::new(*target)),
        ensures
            final(self).inv(),
            final(self).eval_depth == old(self).eval_depth,
            r is Ok ==> r->Ok_0.scale <= BC_SCALE_MAX,
            (r_state(*old(self), st) && r_expr(node, nodes, n) && in_fragment(node)) ==> forall|f: u64|
                done(#[trigger] ev_node(nodes, n, st, f)) ==> r_result(r, *final(self), ev_node(nodes, n, st, f), old(self).eval_depth),
    {
        let ghost d = self.eval_depth;
        let ghost hyp = r_state(*self, st) && r_expr(node, nodes, n) && in_fragment(node);
        if !(matches!(target, Expr::Variable(_)) || matches!(target, Expr::ArrayAccess(..)) || matches!(target, Expr::RegisterAccess(_))) {
            // Not a named expression: the parser never builds this.
            return self.eval_other(&Expr::Update(increment, prefix, Box::new(target.clone())));
        }
        let ghost jt = if n < nodes.len() { match nodes[n as int] { Node::Update(_, _, a) => a, _ => 0usize } } else { 0usize };
        let place = match self.resolve_ref(target, Ghost(nodes), Ghost(jt), Ghost(st)) {
            Ok(p) => p,
            Err(e) => {
                proof {
                    if hyp {
                        assert forall|f: u64| done(#[trigger] ev_node(nodes, n, st, f)) implies r_result(Err(e), *self, ev_node(nodes, n, st, f), d) by {
                            assert(done(resolve(nodes, jt, st, (f - 2) as u64).r));
                        }
                    }
                }
                return Err(e);
            },
        };
        let ghost fr = choose|f: u64| done(#[trigger] resolve(nodes, jt, st, f).r);
        let ghost pr = resolve(nodes, jt, st, fr);
        proof {
            if hyp {
                assert forall|f: u64| done(#[trigger] resolve(nodes, jt, st, f).r) implies resolve(nodes, jt, st, f) == pr by {
                    if fr <= f { lemma_resolve_mono(nodes, jt, st, fr, f); } else { lemma_resolve_mono(nodes, jt, st, f, fr); }
                }
            }
        }
        let ghost st1 = pr.r.st;
        let ghost sold = bc_spec::eval::load(st1, pr.place);
        let old_val = self.load_ref(&place, Ghost(pr.place), Ghost(st1));
        let step = BCNum::new(big_from_usize(1), 0);
        let new_val = if increment { old_val.add(&step) } else { old_val.sub(&step) };
        let ghost snew = if increment { num_add(sold, one_num()) } else { num_sub(sold, one_num()) };
        proof {
            if hyp && exists|f: u64| done(#[trigger] resolve(nodes, jt, st, f).r) {
                lemma_one_mag();
                if increment { lemma_num_add(sold, one_num()); } else { lemma_num_sub(sold, one_num()); }
            }
        }
        let stored = self.store_ref(place, new_val, Ghost(pr.place), Ghost(st1), Ghost(snew));
        let r = if prefix { stored } else { old_val };
        proof {
            if hyp {
                assert forall|f: u64| done(#[trigger] ev_node(nodes, n, st, f)) implies r_result(Ok(r), *self, ev_node(nodes, n, st, f), d) by {
                    assert(done(resolve(nodes, jt, st, (f - 2) as u64).r));
                }
            }
        }
        Ok(r)
    }

    /// `try_execute` with the arena subtree `n` of `nodes` and the specification state `st`:
    /// one nesting level around `exec_node_ref` (the specification's `exec`).
    #[verifier::exec_allows_no_decreases_clause]
    pub(crate) fn exec_ref(
        &mut self,
        node: &Stmt,
        Ghost(nodes): Ghost<SpecNodes>,
        Ghost(n): Ghost<usize>,
        Ghost(st): Ghost<SpecState>,
    ) -> (r: Result<(), BcError>)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            final(self).eval_depth == old(self).eval_depth,
            (r_state(*old(self), st) && r_stmt(*node, nodes, n) && in_fragment_stmt(*node)) ==> forall|f: u64|
                done(#[trigger] exec(nodes, n, st, f)) ==> r_unit(r, *final(self), exec(nodes, n, st, f), old(self).eval_depth),
    {
        let ghost d = self.eval_depth;
        let ghost hyp = r_state(*self, st) && r_stmt(*node, nodes, n) && in_fragment_stmt(*node);
        if !verified_nesting_within_limit(self.eval_depth, 1, self.max_depth) {
            let r = Err(BcError::Runtime { kind: RuntimeError::NestingTooDeep, func: None });
            proof {
                if hyp {
                    assert(with_depth(st, d as u64) == st);
                    assert forall|f: u64| done(#[trigger] exec(nodes, n, st, f)) implies r_unit(r, *self, exec(nodes, n, st, f), d) by {}
                }
            }
            return r;
        }
        let ghost before = *self;
        self.eval_depth += 1;
        let ghost st1 = with_depth(st, (d + 1) as u64);
        proof {
            if hyp {
                lemma_r_state_depth(before, *self, st);
            }
        }
        let r = self.exec_node_ref(node, Ghost(nodes), Ghost(n), Ghost(st1));
        let ghost mid = *self;
        self.eval_depth -= 1;
        proof {
            if hyp {
                assert forall|f: u64| done(#[trigger] exec(nodes, n, st, f)) implies r_unit(r, *self, exec(nodes, n, st, f), d) by {
                    let x = exec_node(nodes, n, st1, (f - 1) as u64);
                    assert(done(x));
                    assert(r_unit(r, mid, x, (d + 1) as usize));
                    if r is Ok {
                        lemma_r_state_depth(mid, *self, x.st);
                        assert(with_depth(with_depth(x.st, d as u64), st.depth) == with_depth(x.st, st.depth));
                    } else {
                        lemma_r_state_depth(mid, *self, with_depth(x.st, (d + 1) as u64));
                        assert(with_depth(with_depth(x.st, (d + 1) as u64), d as u64) == with_depth(x.st, d as u64));
                    }
                }
            }
        }
        r
    }

    /// One statement (the specification's `exec_node`): nothing runs while a `break` or `return`
    /// is pending.
    #[verifier::exec_allows_no_decreases_clause]
    pub(crate) fn exec_node_ref(
        &mut self,
        node: &Stmt,
        Ghost(nodes): Ghost<SpecNodes>,
        Ghost(n): Ghost<usize>,
        Ghost(st): Ghost<SpecState>,
    ) -> (r: Result<(), BcError>)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            final(self).eval_depth == old(self).eval_depth,
            (r_state(*old(self), st) && r_stmt(*node, nodes, n) && in_fragment_stmt(*node)) ==> forall|f: u64|
                done(#[trigger] exec_node(nodes, n, st, f)) ==> r_unit(r, *final(self), exec_node(nodes, n, st, f), old(self).eval_depth),
    {
        let ghost d = self.eval_depth;
        let ghost hyp = r_state(*self, st) && r_stmt(*node, nodes, n) && in_fragment_stmt(*node);
        if verified_should_abort_execution(self.break_flag, self.return_flag, self.quit_flag) {
            proof {
                if hyp {
                    assert forall|f: u64| done(#[trigger] exec_node(nodes, n, st, f)) implies r_unit(Ok(()), *self, exec_node(nodes, n, st, f), d) by {}
                }
            }
            return Ok(());
        }
        match node {
            Stmt::Block(list) => self.exec_block(Ghost(*node), list, Ghost(nodes), Ghost(n), Ghost(st)),
            Stmt::Expr(e) => self.exec_expr_stmt(Ghost(*node), e, Ghost(nodes), Ghost(n), Ghost(st)),
            Stmt::StringLiteral(t) => {
                self.stdout_writer.write_bytes(t.as_str().as_bytes());
                self.stdout_writer.flush_out();
                proof {
                    if hyp {
                        assert forall|f: u64| done(#[trigger] exec_node(nodes, n, st, f)) implies r_unit(Ok(()), *self, exec_node(nodes, n, st, f), d) by {}
                    }
                }
                Ok(())
            },
            Stmt::Break => {
                self.break_flag = true;
                proof {
                    if hyp {
                        assert forall|f: u64| done(#[trigger] exec_node(nodes, n, st, f)) implies r_unit(Ok(()), *self, exec_node(nodes, n, st, f), d) by {}
                    }
                }
                Ok(())
            },
            Stmt::Quit => {
                self.quit_flag = true;
                Ok(())
            },
            Stmt::Return(v) => self.exec_return(Ghost(*node), v, Ghost(nodes), Ghost(n), Ghost(st)),
            Stmt::If(c, b) => self.exec_if(Ghost(*node), c, b, Ghost(nodes), Ghost(n), Ghost(st)),
            Stmt::While(c, b) => {
                let ghost (jc, jb) = if n < nodes.len() { match nodes[n as int] { Node::While(a, b) => (a, b), _ => (0usize, 0usize) } } else { (0usize, 0usize) };
                let r = self.exec_loop_ref(c, None, b, Ghost(nodes), Ghost(jc), Ghost(0usize), Ghost(jb), Ghost(st));
                proof {
                    if hyp {
                        assert forall|f: u64| done(#[trigger] exec_node(nodes, n, st, f)) implies r_unit(r, *self, exec_node(nodes, n, st, f), d) by {
                            assert(exec_node(nodes, n, st, f) == bc_spec::eval::exec_loop(nodes, jc, 0usize, false, jb, st, (f - 1) as u64));
                        }
                    }
                }
                r
            },
            Stmt::For(i, c, p, b) => self.exec_for_ref(Ghost(*node), i, c, p, b, Ghost(nodes), Ghost(n), Ghost(st)),
            Stmt::FunctionDef(fd) => {
                let ghost m = self.functions@;
                proof {
                    axiom_string_obeys_cmp();
                    broadcast use vstd::std_specs::btree::group_btree_axioms;
                }
                self.functions.insert(fd.name.clone(), fd.clone());
                proof {
                    if hyp {
                        match nodes[n as int] {
                            Node::Define(name, ps, autos, body) => {
                                let g = Func { name: name, params: ps, autos: autos, body: body, nodes: nodes };
                                assert(r_func(*fd, g));
                                lemma_r_funcs_define(m, st.funcs, *fd, g);
                            },
                            _ => {},
                        }
                        assert forall|f: u64| done(#[trigger] exec_node(nodes, n, st, f)) implies r_unit(Ok(()), *self, exec_node(nodes, n, st, f), d) by {}
                    }
                }
                Ok(())
            },
        }
    }

    /// A block (the specification's `exec_list`): its statements in order, stopping when a
    /// `break` or `return` is pending.
    #[verifier::exec_allows_no_decreases_clause]
    #[allow(clippy::ptr_arg, reason = "the precondition relates the list to the `Stmt::Block` it comes from")]
    fn exec_block(&mut self, Ghost(node): Ghost<Stmt>, list: &Vec<Stmt>, Ghost(nodes): Ghost<SpecNodes>, Ghost(n): Ghost<usize>, Ghost(st): Ghost<SpecState>) -> (r: Result<(), BcError>)
        requires
            old(self).inv(),
            !old(self).break_flag && !old(self).return_flag && !old(self).quit_flag,
            node == Stmt::Block(*list),
        ensures
            final(self).inv(),
            final(self).eval_depth == old(self).eval_depth,
            (r_state(*old(self), st) && r_stmt(node, nodes, n) && in_fragment_stmt(node)) ==> forall|f: u64|
                done(#[trigger] exec_node(nodes, n, st, f)) ==> r_unit(r, *final(self), exec_node(nodes, n, st, f), old(self).eval_depth),
    {
        let ghost d = self.eval_depth;
        let ghost hyp = r_state(*self, st) && r_stmt(node, nodes, n) && in_fragment_stmt(node);
        let ghost ns = if n < nodes.len() { match nodes[n as int] { Node::Block(ns) => ns, _ => Seq::empty() } } else { Seq::empty() };
        let ghost fin = exists|f: u64| done(#[trigger] exec_node(nodes, n, st, f));
        let ghost mut sti = st;
        let mut i: usize = 0;
        proof {
            if hyp {
                assert(ns.skip(0) =~= ns);
                assert(n < nodes.len());
                assert(nodes[n as int] is Block);
                assert(nodes[n as int] == Node::Block(ns));
                assert(r_stmts(list@, nodes, ns));
                assert(in_fragment_stmts(list@));
            }
        }
        while i < list.len()
            invariant
                self.inv(),
                self.eval_depth == d,
                d == old(self).eval_depth,
                hyp == (r_state(*old(self), st) && r_stmt(node, nodes, n) && in_fragment_stmt(node)),
                hyp ==> nodes[n as int] == Node::Block(ns),
                i <= list.len(),
                hyp ==> r_stmts(list@, nodes, ns) && in_fragment_stmts(list@),
                fin == exists|f: u64| done(#[trigger] exec_node(nodes, n, st, f)),
                hyp && fin ==> r_state(*self, sti) && !sti.brk && !sti.ret,
                hyp ==> forall|f: u64| done(#[trigger] exec_node(nodes, n, st, f)) ==> f as int > i + 1
                    && exec_node(nodes, n, st, f) == bc_spec::eval::exec_list(nodes, ns.skip(i as int), sti, (f - 1 - i) as u64),
            decreases list.len() - i,
        {
            let ghost si = sti;
            let ghost ji = ns[i as int];
            proof {
                if hyp {
                    assert(ns.skip(i as int)[0] == ji);
                    assert(ns.skip(i as int).drop_first() =~= ns.skip(i as int + 1));
                }
            }
            proof {
                if hyp {
                    lemma_r_stmts_index(list@, nodes, ns, i as int);
                    lemma_in_fragment_stmts_index(list@, i as int);
                }
            }
            let ghost e_before = *self;
            let ri = self.exec_ref(&list[i], Ghost(nodes), Ghost(ji), Ghost(si));
            if let Err(e) = ri {
                proof {
                    if hyp {
                        assert forall|f: u64| done(#[trigger] exec_node(nodes, n, st, f)) implies r_unit(Err(e), *self, exec_node(nodes, n, st, f), d) by {
                            let g = (f - 1 - i) as u64;
                            assert(ns.skip(i as int).len() > 0);
                            assert(bc_spec::eval::exec_list(nodes, ns.skip(i as int), si, g) == {
                                let r0 = exec(nodes, ji, si, (g - 1) as u64);
                                if !r0.ok { r0 } else if r0.st.brk || r0.st.ret { r0 } else { bc_spec::eval::exec_list(nodes, ns.skip(i as int + 1), r0.st, (g - 1) as u64) }
                            });
                            assert(done(exec(nodes, ji, si, (g - 1) as u64)));
                        }
                    }
                }
                return Err(e);
            }
            let ghost fi = choose|f: u64| done(#[trigger] exec(nodes, ji, si, f));
            let ghost x = exec(nodes, ji, si, fi);
            proof {
                if hyp {
                    assert forall|f: u64| done(#[trigger] exec(nodes, ji, si, f)) implies exec(nodes, ji, si, f) == x by {
                        if fi <= f { lemma_exec_mono(nodes, ji, si, fi, f); } else { lemma_exec_mono(nodes, ji, si, f, fi); }
                    }
                }
            }
            if verified_should_abort_execution(self.break_flag, self.return_flag, self.quit_flag) {
                proof {
                    if hyp {
                        assert forall|f: u64| done(#[trigger] exec_node(nodes, n, st, f)) implies r_unit(Ok(()), *self, exec_node(nodes, n, st, f), d) by {
                            assert(done(exec(nodes, ji, si, (f - 2 - i) as u64)));
                        }
                    }
                }
                return Ok(());
            }
            proof {
                if hyp && fin {
                    let ff = choose|f: u64| done(#[trigger] exec_node(nodes, n, st, f));
                    let g = (ff - 1 - i) as u64;
                    assert(ns.skip(i as int).len() > 0);
                    assert(bc_spec::eval::exec_list(nodes, ns.skip(i as int), si, g) == {
                        let r0 = exec(nodes, ji, si, (g - 1) as u64);
                        if !r0.ok { r0 } else if r0.st.brk || r0.st.ret { r0 } else { bc_spec::eval::exec_list(nodes, ns.skip(i as int + 1), r0.st, (g - 1) as u64) }
                    });
                    assert(done(exec(nodes, ji, si, (g - 1) as u64)));
                    assert(r_state(e_before, si));
                    assert(r_unit(ri, *self, exec(nodes, ji, si, (g - 1) as u64), d));
                    assert(r_state(*self, x.st));
                }
                if hyp {
                    sti = x.st;
                    assert forall|f: u64| done(#[trigger] exec_node(nodes, n, st, f)) implies f as int > i + 2
                        && exec_node(nodes, n, st, f) == bc_spec::eval::exec_list(nodes, ns.skip(i as int + 1), sti, (f - 2 - i) as u64) by {
                        let g = (f - 1 - i) as u64;
                        assert(ns.skip(i as int).len() > 0);
                        assert(bc_spec::eval::exec_list(nodes, ns.skip(i as int), si, g) == {
                            let r0 = exec(nodes, ji, si, (g - 1) as u64);
                            if !r0.ok { r0 } else if r0.st.brk || r0.st.ret { r0 } else { bc_spec::eval::exec_list(nodes, ns.skip(i as int + 1), r0.st, (g - 1) as u64) }
                        });
                        assert(done(exec(nodes, ji, si, (g - 1) as u64)));
                        if f as int <= i + 2 {
                            assert(bc_spec::eval::exec_list(nodes, ns.skip(i as int + 1), sti, 0) == bc_spec::eval::er_fuel(sti));
                        }
                    }
                }
            }
            i += 1;
        }
        proof {
            if hyp {
                assert(ns.skip(i as int) =~= Seq::<usize>::empty());
                assert forall|f: u64| done(#[trigger] exec_node(nodes, n, st, f)) implies r_unit(Ok(()), *self, exec_node(nodes, n, st, f), d) by {}
            }
        }
        Ok(())
    }

    /// Whether an expression statement is an assignment, whose value is not printed (POSIX).
    /// As in GNU bc, unary minus keeps that property (`-a = 5` prints nothing) and parentheses
    /// remove it (`(a = 5)` prints 5).
    fn is_assignment_ref(e: &Expr) -> (r: bool)
        ensures
            r == prod_is_assignment(*e),
        decreases e,
    {
        match e {
            Expr::AssignOp(..) => true,
            Expr::Negate(inner) => Self::is_assignment_ref(inner),
            _ => false,
        }
    }

    /// An expression statement (the specification's `exec_expr_stmt`): the value is printed
    /// unless it is an assignment.
    #[verifier::exec_allows_no_decreases_clause]
    fn exec_expr_stmt(&mut self, Ghost(node): Ghost<Stmt>, e: &Expr, Ghost(nodes): Ghost<SpecNodes>, Ghost(n): Ghost<usize>, Ghost(st): Ghost<SpecState>) -> (r: Result<(), BcError>)
        requires
            old(self).inv(),
            !old(self).break_flag && !old(self).return_flag && !old(self).quit_flag,
            node == Stmt::Expr(*e),
        ensures
            final(self).inv(),
            final(self).eval_depth == old(self).eval_depth,
            (r_state(*old(self), st) && r_stmt(node, nodes, n) && in_fragment_stmt(node)) ==> forall|f: u64|
                done(#[trigger] exec_node(nodes, n, st, f)) ==> r_unit(r, *final(self), exec_node(nodes, n, st, f), old(self).eval_depth),
    {
        let ghost d = self.eval_depth;
        let ghost hyp = r_state(*self, st) && r_stmt(node, nodes, n) && in_fragment_stmt(node);
        let ghost j = if n < nodes.len() { match nodes[n as int] { Node::ExprStmt(j) => j, _ => 0usize } } else { 0usize };
        let v = match self.eval_ref(e, Ghost(nodes), Ghost(j), Ghost(st)) {
            Ok(v) => v,
            Err(err) => {
                proof {
                    if hyp {
                        assert forall|f: u64| done(#[trigger] exec_node(nodes, n, st, f)) implies r_unit(Err(err), *self, exec_node(nodes, n, st, f), d) by {
                            assert(done(ev(nodes, j, st, (f - 2) as u64)));
                        }
                    }
                }
                return Err(err);
            },
        };
        let assignment = Self::is_assignment_ref(e);
        let ghost e1 = *self;
        if !assignment {
            let mut text = v.format_bytes(self.obase);
            text.push(10);
            self.stdout_writer.write_bytes(&text);
            self.stdout_writer.flush_out();
        }
        proof {
            if hyp {
                assert forall|f: u64| done(#[trigger] exec_node(nodes, n, st, f)) implies r_unit(Ok(()), *self, exec_node(nodes, n, st, f), d) by {
                    let x = ev(nodes, j, st, (f - 2) as u64);
                    assert(done(x));
                    lemma_prod_is_assignment(*e, nodes, j, st, (f - 2) as u64);
                    if !assignment {
                        axiom_bigint_size(&v.coeff);
                        lemma_mag_bounds(x.val.mag);
                        lemma_format_num(x.val, x.st.obase);
                    }
                }
            }
        }
        Ok(())
    }

    /// `return` and `return (e)` (the specification's `exec_return`).
    #[verifier::exec_allows_no_decreases_clause]
    fn exec_return(&mut self, Ghost(node): Ghost<Stmt>, v: &Option<Expr>, Ghost(nodes): Ghost<SpecNodes>, Ghost(n): Ghost<usize>, Ghost(st): Ghost<SpecState>) -> (r: Result<(), BcError>)
        requires
            old(self).inv(),
            !old(self).break_flag && !old(self).return_flag && !old(self).quit_flag,
            node == Stmt::Return(*v),
        ensures
            final(self).inv(),
            final(self).eval_depth == old(self).eval_depth,
            (r_state(*old(self), st) && r_stmt(node, nodes, n) && in_fragment_stmt(node)) ==> forall|f: u64|
                done(#[trigger] exec_node(nodes, n, st, f)) ==> r_unit(r, *final(self), exec_node(nodes, n, st, f), old(self).eval_depth),
    {
        let ghost d = self.eval_depth;
        let ghost hyp = r_state(*self, st) && r_stmt(node, nodes, n) && in_fragment_stmt(node);
        let ghost j = if n < nodes.len() { match nodes[n as int] { Node::Return(_, j) => j, _ => 0usize } } else { 0usize };
        match v {
            Some(e) => {
                let x = match self.eval_ref(e, Ghost(nodes), Ghost(j), Ghost(st)) {
                    Ok(x) => x,
                    Err(err) => {
                        proof {
                            if hyp {
                                assert forall|f: u64| done(#[trigger] exec_node(nodes, n, st, f)) implies r_unit(Err(err), *self, exec_node(nodes, n, st, f), d) by {
                                    assert(done(ev(nodes, j, st, (f - 2) as u64)));
                                }
                            }
                        }
                        return Err(err);
                    },
                };
                self.return_value = x;
            },
            None => {
                self.return_value = BCNum::zero();
            },
        }
        self.return_flag = true;
        proof {
            if hyp {
                assert forall|f: u64| done(#[trigger] exec_node(nodes, n, st, f)) implies r_unit(Ok(()), *self, exec_node(nodes, n, st, f), d) by {
                    if v is Some {
                        assert(done(ev(nodes, j, st, (f - 2) as u64)));
                    }
                }
            }
        }
        Ok(())
    }

    /// `if (c) s` (the specification's `exec_if`).
    #[verifier::exec_allows_no_decreases_clause]
    fn exec_if(&mut self, Ghost(node): Ghost<Stmt>, c: &Expr, b: &Stmt, Ghost(nodes): Ghost<SpecNodes>, Ghost(n): Ghost<usize>, Ghost(st): Ghost<SpecState>) -> (r: Result<(), BcError>)
        requires
            old(self).inv(),
            !old(self).break_flag && !old(self).return_flag && !old(self).quit_flag,
            node == Stmt::If(*c, Box::new(*b)),
        ensures
            final(self).inv(),
            final(self).eval_depth == old(self).eval_depth,
            (r_state(*old(self), st) && r_stmt(node, nodes, n) && in_fragment_stmt(node)) ==> forall|f: u64|
                done(#[trigger] exec_node(nodes, n, st, f)) ==> r_unit(r, *final(self), exec_node(nodes, n, st, f), old(self).eval_depth),
    {
        let ghost d = self.eval_depth;
        let ghost hyp = r_state(*self, st) && r_stmt(node, nodes, n) && in_fragment_stmt(node);
        let ghost (jc, jb) = if n < nodes.len() { match nodes[n as int] { Node::If(a, b) => (a, b), _ => (0usize, 0usize) } } else { (0usize, 0usize) };
        let x = match self.eval_ref(c, Ghost(nodes), Ghost(jc), Ghost(st)) {
            Ok(x) => x,
            Err(err) => {
                proof {
                    if hyp {
                        assert forall|f: u64| done(#[trigger] exec_node(nodes, n, st, f)) implies r_unit(Err(err), *self, exec_node(nodes, n, st, f), d) by {
                            assert(done(ev(nodes, jc, st, (f - 2) as u64)));
                        }
                    }
                }
                return Err(err);
            },
        };
        let ghost fc = choose|f: u64| done(#[trigger] ev(nodes, jc, st, f));
        let ghost xc = ev(nodes, jc, st, fc);
        proof {
            if hyp {
                assert forall|f: u64| done(#[trigger] ev(nodes, jc, st, f)) implies ev(nodes, jc, st, f) == xc by {
                    if fc <= f { lemma_ev_mono(nodes, jc, st, fc, f); } else { lemma_ev_mono(nodes, jc, st, f, fc); }
                }
            }
        }
        if x.is_zero() {
            proof {
                if hyp {
                    assert forall|f: u64| done(#[trigger] exec_node(nodes, n, st, f)) implies r_unit(Ok(()), *self, exec_node(nodes, n, st, f), d) by {
                        assert(done(ev(nodes, jc, st, (f - 2) as u64)));
                        lemma_is_zero_mag(xc.val.mag);
                    }
                }
            }
            return Ok(());
        }
        let ghost e1 = *self;
        let r = self.exec_ref(b, Ghost(nodes), Ghost(jb), Ghost(xc.st));
        proof {
            if hyp {
                assert forall|f: u64| done(#[trigger] exec_node(nodes, n, st, f)) implies r_unit(r, *self, exec_node(nodes, n, st, f), d) by {
                    assert(done(ev(nodes, jc, st, (f - 2) as u64)));
                    assert(r_result(Ok(x), e1, xc, d));
                    assert(r_state(e1, xc.st));
                    lemma_is_zero_mag(xc.val.mag);
                    assert(done(exec(nodes, jb, xc.st, (f - 2) as u64)));
                }
            }
        }
        r
    }

    /// The loop of `while` (no `post`) and `for` (the specification's `exec_loop`): after the
    /// body, a pending `break` or `return` ends the loop and `break` is cleared.
    #[verifier::exec_allows_no_decreases_clause]
    #[verifier::rlimit(30)]
    #[allow(
        clippy::too_many_arguments,
        reason = "five of them are the Ghost arguments of the refinement proof"
    )]
    fn exec_loop_ref(&mut self, c: &Expr, post: Option<&Expr>, b: &Stmt, Ghost(nodes): Ghost<SpecNodes>, Ghost(jc): Ghost<usize>, Ghost(jp): Ghost<usize>, Ghost(jb): Ghost<usize>, Ghost(st): Ghost<SpecState>) -> (r: Result<(), BcError>)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            final(self).eval_depth == old(self).eval_depth,
            ({
                let has_post = post is Some;
                (r_state(*old(self), st) && r_expr(*c, nodes, jc) && in_fragment(*c) && r_stmt(*b, nodes, jb) && in_fragment_stmt(*b)
                    && (has_post ==> r_expr(*post->Some_0, nodes, jp) && in_fragment(*post->Some_0))) ==> forall|f: u64|
                    done(#[trigger] bc_spec::eval::exec_loop(nodes, jc, jp, has_post, jb, st, f))
                        ==> r_unit(r, *final(self), bc_spec::eval::exec_loop(nodes, jc, jp, has_post, jb, st, f), old(self).eval_depth)
            }),
    {
        let ghost d = self.eval_depth;
        let ghost has_post = post is Some;
        let ghost hyp = r_state(*self, st) && r_expr(*c, nodes, jc) && in_fragment(*c) && r_stmt(*b, nodes, jb) && in_fragment_stmt(*b)
            && (has_post ==> r_expr(*post->Some_0, nodes, jp) && in_fragment(*post->Some_0));
        let ghost fin = exists|f: u64| done(#[trigger] bc_spec::eval::exec_loop(nodes, jc, jp, has_post, jb, st, f));
        let ghost mut sk = st;
        let ghost mut k: int = 0;
        loop
            invariant
                self.inv(),
                self.eval_depth == d,
                d == old(self).eval_depth,
                has_post == (post is Some),
                hyp == (r_state(*old(self), st) && r_expr(*c, nodes, jc) && in_fragment(*c) && r_stmt(*b, nodes, jb) && in_fragment_stmt(*b)
                    && (has_post ==> r_expr(*post->Some_0, nodes, jp) && in_fragment(*post->Some_0))),
                k >= 0,
                fin == exists|f: u64| done(#[trigger] bc_spec::eval::exec_loop(nodes, jc, jp, has_post, jb, st, f)),
                hyp && fin ==> r_state(*self, sk),
                hyp ==> forall|f: u64| done(#[trigger] bc_spec::eval::exec_loop(nodes, jc, jp, has_post, jb, st, f)) ==> f as int > k
                    && bc_spec::eval::exec_loop(nodes, jc, jp, has_post, jb, st, f) == bc_spec::eval::exec_loop(nodes, jc, jp, has_post, jb, sk, (f - k) as u64),
        {
            let ghost s0 = sk;
            let ghost e0 = *self;
            let cv = match self.eval_ref(c, Ghost(nodes), Ghost(jc), Ghost(s0)) {
                Ok(cv) => cv,
                Err(err) => {
                    proof {
                        if hyp {
                            assert forall|f: u64| done(#[trigger] bc_spec::eval::exec_loop(nodes, jc, jp, has_post, jb, st, f)) implies r_unit(Err(err), *self, bc_spec::eval::exec_loop(nodes, jc, jp, has_post, jb, st, f), d) by {
                                assert(done(ev(nodes, jc, s0, (f - k - 1) as u64)));
                                assert(r_state(e0, s0));
                            }
                        }
                    }
                    return Err(err);
                },
            };
            let ghost e1 = *self;
            let ghost fc = choose|f: u64| done(#[trigger] ev(nodes, jc, s0, f));
            let ghost xc = ev(nodes, jc, s0, fc);
            proof {
                if hyp {
                    assert forall|f: u64| done(#[trigger] ev(nodes, jc, s0, f)) implies ev(nodes, jc, s0, f) == xc by {
                        if fc <= f { lemma_ev_mono(nodes, jc, s0, fc, f); } else { lemma_ev_mono(nodes, jc, s0, f, fc); }
                    }
                }
            }
            if cv.is_zero() || self.quit_flag {
                proof {
                    if hyp {
                        assert forall|f: u64| done(#[trigger] bc_spec::eval::exec_loop(nodes, jc, jp, has_post, jb, st, f)) implies r_unit(Ok(()), *self, bc_spec::eval::exec_loop(nodes, jc, jp, has_post, jb, st, f), d) by {
                            assert(done(ev(nodes, jc, s0, (f - k - 1) as u64)));
                                assert(r_state(e0, s0));
                            lemma_is_zero_mag(xc.val.mag);
                        }
                    }
                }
                return Ok(());
            }
            let rb = self.exec_ref(b, Ghost(nodes), Ghost(jb), Ghost(xc.st));
            if let Err(err) = rb {
                proof {
                    if hyp {
                        assert forall|f: u64| done(#[trigger] bc_spec::eval::exec_loop(nodes, jc, jp, has_post, jb, st, f)) implies r_unit(Err(err), *self, bc_spec::eval::exec_loop(nodes, jc, jp, has_post, jb, st, f), d) by {
                            assert(done(ev(nodes, jc, s0, (f - k - 1) as u64)));
                                assert(r_state(e0, s0));
                            lemma_is_zero_mag(xc.val.mag);
                            assert(r_state(e1, xc.st));
                                assert(done(exec(nodes, jb, xc.st, (f - k - 1) as u64)));
                        }
                    }
                }
                return Err(err);
            }
            let ghost fb = choose|f: u64| done(#[trigger] exec(nodes, jb, xc.st, f));
            let ghost xb = exec(nodes, jb, xc.st, fb);
            proof {
                if hyp {
                    assert forall|f: u64| done(#[trigger] exec(nodes, jb, xc.st, f)) implies exec(nodes, jb, xc.st, f) == xb by {
                        if fb <= f { lemma_exec_mono(nodes, jb, xc.st, fb, f); } else { lemma_exec_mono(nodes, jb, xc.st, f, fb); }
                    }
                }
            }
            let ghost e2 = *self;
            let (should_break, next_break) = verified_loop_post_body_action(self.break_flag, self.return_flag, self.quit_flag);
            self.break_flag = next_break;
            let ghost st2 = bc_spec::eval::with_flags(xb.st, false, xb.st.ret, xb.st.ret_val);
            if should_break {
                proof {
                    if hyp {
                        assert forall|f: u64| done(#[trigger] bc_spec::eval::exec_loop(nodes, jc, jp, has_post, jb, st, f)) implies r_unit(Ok(()), *self, bc_spec::eval::exec_loop(nodes, jc, jp, has_post, jb, st, f), d) by {
                            assert(done(ev(nodes, jc, s0, (f - k - 1) as u64)));
                                assert(r_state(e0, s0));
                            lemma_is_zero_mag(xc.val.mag);
                            assert(r_state(e1, xc.st));
                                assert(done(exec(nodes, jb, xc.st, (f - k - 1) as u64)));
                        }
                    }
                }
                return Ok(());
            }
            #[allow(clippy::single_match, reason = "the `None` arm holds the proof that the loop state advances")]
            match post {
                Some(p) => {
                    let ghost e3 = *self;
                    let rp = self.eval_ref(p, Ghost(nodes), Ghost(jp), Ghost(st2));
                    if let Err(err) = rp {
                        proof {
                            if hyp {
                                assert forall|f: u64| done(#[trigger] bc_spec::eval::exec_loop(nodes, jc, jp, has_post, jb, st, f)) implies r_unit(Err(err), *self, bc_spec::eval::exec_loop(nodes, jc, jp, has_post, jb, st, f), d) by {
                                    assert(done(ev(nodes, jc, s0, (f - k - 1) as u64)));
                                assert(r_state(e0, s0));
                                    lemma_is_zero_mag(xc.val.mag);
                                    assert(r_state(e1, xc.st));
                                assert(done(exec(nodes, jb, xc.st, (f - k - 1) as u64)));
                                    assert(r_state(e2, xb.st));
                                    assert(done(ev(nodes, jp, st2, (f - k - 1) as u64)));
                                }
                            }
                        }
                        return Err(err);
                    }
                    let ghost fp = choose|f: u64| done(#[trigger] ev(nodes, jp, st2, f));
                    let ghost xp = ev(nodes, jp, st2, fp);
                    proof {
                        if hyp {
                            assert forall|f: u64| done(#[trigger] ev(nodes, jp, st2, f)) implies ev(nodes, jp, st2, f) == xp by {
                                if fp <= f { lemma_ev_mono(nodes, jp, st2, fp, f); } else { lemma_ev_mono(nodes, jp, st2, f, fp); }
                            }
                            let sk2 = xp.st;
                            assert forall|f: u64| done(#[trigger] bc_spec::eval::exec_loop(nodes, jc, jp, has_post, jb, st, f)) implies f as int > k + 1
                                && bc_spec::eval::exec_loop(nodes, jc, jp, has_post, jb, st, f) == bc_spec::eval::exec_loop(nodes, jc, jp, has_post, jb, sk2, (f - k - 1) as u64) by {
                                assert(done(ev(nodes, jc, s0, (f - k - 1) as u64)));
                                assert(r_state(e0, s0));
                                lemma_is_zero_mag(xc.val.mag);
                                assert(r_state(e1, xc.st));
                                assert(done(exec(nodes, jb, xc.st, (f - k - 1) as u64)));
                                assert(r_state(e2, xb.st));
                                    assert(done(ev(nodes, jp, st2, (f - k - 1) as u64)));
                                if f as int <= k + 1 {
                                    assert(bc_spec::eval::exec_loop(nodes, jc, jp, has_post, jb, sk2, 0) == bc_spec::eval::er_fuel(sk2));
                                }
                            }
                            if fin {
                                let ff = choose|f: u64| done(#[trigger] bc_spec::eval::exec_loop(nodes, jc, jp, has_post, jb, st, f));
                                let g = (ff - k) as u64;
                                assert(bc_spec::eval::exec_loop(nodes, jc, jp, has_post, jb, st, ff) == bc_spec::eval::exec_loop(nodes, jc, jp, has_post, jb, s0, g));
                                assert(done(ev(nodes, jc, s0, (g - 1) as u64)));
                                assert(r_state(e0, s0));
                                assert(r_state(e1, xc.st));
                                lemma_is_zero_mag(xc.val.mag);
                                assert(done(exec(nodes, jb, xc.st, (g - 1) as u64)));
                                assert(r_state(e2, xb.st));
                                assert(r_state(e3, st2));
                                assert(done(ev(nodes, jp, st2, (g - 1) as u64)));
                                assert(r_state(*self, sk2));
                            }
                            sk = sk2;
                        }
                    }
                },
                None => {
                    proof {
                        if hyp {
                            assert forall|f: u64| done(#[trigger] bc_spec::eval::exec_loop(nodes, jc, jp, has_post, jb, st, f)) implies f as int > k + 1
                                && bc_spec::eval::exec_loop(nodes, jc, jp, has_post, jb, st, f) == bc_spec::eval::exec_loop(nodes, jc, jp, has_post, jb, st2, (f - k - 1) as u64) by {
                                assert(done(ev(nodes, jc, s0, (f - k - 1) as u64)));
                                assert(r_state(e0, s0));
                                lemma_is_zero_mag(xc.val.mag);
                                assert(r_state(e1, xc.st));
                                assert(done(exec(nodes, jb, xc.st, (f - k - 1) as u64)));
                                if f as int <= k + 1 {
                                    assert(bc_spec::eval::exec_loop(nodes, jc, jp, has_post, jb, st2, 0) == bc_spec::eval::er_fuel(st2));
                                }
                            }
                            if fin {
                                let ff = choose|f: u64| done(#[trigger] bc_spec::eval::exec_loop(nodes, jc, jp, has_post, jb, st, f));
                                let g = (ff - k) as u64;
                                assert(bc_spec::eval::exec_loop(nodes, jc, jp, has_post, jb, st, ff) == bc_spec::eval::exec_loop(nodes, jc, jp, has_post, jb, s0, g));
                                assert(done(ev(nodes, jc, s0, (g - 1) as u64)));
                                assert(r_state(e0, s0));
                                assert(r_state(e1, xc.st));
                                lemma_is_zero_mag(xc.val.mag);
                                assert(done(exec(nodes, jb, xc.st, (g - 1) as u64)));
                                assert(r_state(e2, xb.st));
                                assert(r_state(*self, st2));
                            }
                            sk = st2;
                        }
                    }
                },
            }
            proof {
                k = k + 1;
            }
        }
    }

    /// `for (i; c; p) s` (the specification's `exec_for`).
    #[verifier::exec_allows_no_decreases_clause]
    #[allow(
        clippy::too_many_arguments,
        reason = "four of them are the Ghost arguments of the refinement proof"
    )]
    fn exec_for_ref(&mut self, Ghost(node): Ghost<Stmt>, init: &Expr, c: &Expr, p: &Expr, b: &Stmt, Ghost(nodes): Ghost<SpecNodes>, Ghost(n): Ghost<usize>, Ghost(st): Ghost<SpecState>) -> (r: Result<(), BcError>)
        requires
            old(self).inv(),
            !old(self).break_flag && !old(self).return_flag && !old(self).quit_flag,
            node == Stmt::For(*init, *c, *p, Box::new(*b)),
        ensures
            final(self).inv(),
            final(self).eval_depth == old(self).eval_depth,
            (r_state(*old(self), st) && r_stmt(node, nodes, n) && in_fragment_stmt(node)) ==> forall|f: u64|
                done(#[trigger] exec_node(nodes, n, st, f)) ==> r_unit(r, *final(self), exec_node(nodes, n, st, f), old(self).eval_depth),
    {
        let ghost d = self.eval_depth;
        let ghost hyp = r_state(*self, st) && r_stmt(node, nodes, n) && in_fragment_stmt(node);
        let ghost (ji, jc, jp, jb) = if n < nodes.len() { match nodes[n as int] { Node::For(a, b2, c2, d2) => (a, b2, c2, d2), _ => (0usize, 0usize, 0usize, 0usize) } } else { (0usize, 0usize, 0usize, 0usize) };
        if let Err(err) = self.eval_ref(init, Ghost(nodes), Ghost(ji), Ghost(st)) {
            proof {
                if hyp {
                    assert forall|f: u64| done(#[trigger] exec_node(nodes, n, st, f)) implies r_unit(Err(err), *self, exec_node(nodes, n, st, f), d) by {
                        assert(done(ev(nodes, ji, st, (f - 2) as u64)));
                    }
                }
            }
            return Err(err);
        }
        let ghost fi = choose|f: u64| done(#[trigger] ev(nodes, ji, st, f));
        let ghost xi = ev(nodes, ji, st, fi);
        proof {
            if hyp {
                assert forall|f: u64| done(#[trigger] ev(nodes, ji, st, f)) implies ev(nodes, ji, st, f) == xi by {
                    if fi <= f { lemma_ev_mono(nodes, ji, st, fi, f); } else { lemma_ev_mono(nodes, ji, st, f, fi); }
                }
            }
        }
        let ghost e1 = *self;
        let r = self.exec_loop_ref(c, Some(p), b, Ghost(nodes), Ghost(jc), Ghost(jp), Ghost(jb), Ghost(xi.st));
        proof {
            if hyp {
                assert forall|f: u64| done(#[trigger] exec_node(nodes, n, st, f)) implies r_unit(r, *self, exec_node(nodes, n, st, f), d) by {
                    assert(done(ev(nodes, ji, st, (f - 2) as u64)));
                    assert(r_state(e1, xi.st));
                    assert(done(bc_spec::eval::exec_loop(nodes, jc, jp, true, jb, xi.st, (f - 2) as u64)));
                }
            }
        }
        r
    }

    /// The trusted boundary of the expressions not proved yet: `evaluate_node`'s code for them,
    /// assumed to keep the invariant and the depth.
    #[verifier::external_body]
    fn eval_other(&mut self, node: &Expr) -> (r: Result<BCNum, BcError>)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            final(self).eval_depth == old(self).eval_depth,
            r is Ok ==> r->Ok_0.scale <= BC_SCALE_MAX,
    {
        self.eval_other_impl(node)
    }
}

} // verus!

impl ErrWriter {
    /// Creates the diagnostic stream writing to the given writer.
    pub fn new(writer: Box<dyn BcWriter>) -> Self {
        Self { writer }
    }

    /// Flushes the underlying writer.
    pub fn flush(&mut self) -> core::fmt::Result {
        self.writer.flush()
    }

    /// Writes formatted text, so that `writeln!(evaluator.stderr_writer, ...)` works without
    /// importing `fmt::Write`.
    pub fn write_fmt(&mut self, args: core::fmt::Arguments<'_>) -> core::fmt::Result {
        FmtWrite::write_fmt(self, args)
    }
}

impl FmtWrite for ErrWriter {
    fn write_str(&mut self, s: &str) -> core::fmt::Result {
        self.writer.write_str(s)
    }
}

impl Evaluator {
    /// Creates a new Evaluator with abstract BcWriter streams.
    pub fn new(
        math_enabled: bool,
        stdout_writer: Box<dyn BcWriter>,
        stderr_writer: Box<dyn BcWriter>,
    ) -> Self {
        Self {
            variables: BTreeMap::new(),
            arrays: BTreeMap::new(),
            functions: BTreeMap::new(),
            scale: 0,
            ibase: 10,
            obase: 10,
            math_enabled,
            stdout_writer: WrappedStdout::new(stdout_writer),
            stderr_writer: ErrWriter::new(stderr_writer),
            break_flag: false,
            return_flag: false,
            return_value: BCNum::zero(),
            quit_flag: false,
            extension_policy: ExtensionPolicy::Allow,
            call_stack: Vec::new(),
            max_depth: DEFAULT_MAX_DEPTH,
            eval_depth: 0,
            invocation_ibase: None,
        }
    }

    /// The `scale` register.
    pub fn scale(&self) -> usize {
        self.scale
    }

    /// The `ibase` register.
    pub fn ibase(&self) -> usize {
        self.ibase
    }

    /// The `obase` register.
    pub fn obase(&self) -> usize {
        self.obase
    }

    /// Sets the `scale` register (e.g. a front end's default scale), clamped to `BC_SCALE_MAX`.
    pub fn set_scale(&mut self, scale: usize) {
        self.scale = verified_clamp_register(scale, false, 0, BC_SCALE_MAX).0;
    }

    /// Writes `Runtime warning (func=<current function>): <msg>` to the diagnostic stream.
    fn warn(&mut self, msg: &str) {
        let func = self.call_stack.last().map_or("(main)", String::as_str);
        let _ = writeln!(
            self.stderr_writer,
            "Runtime warning (func={}): {}",
            func, msg
        );
    }

    /// Resolves an assignment target, evaluating an array subscript exactly once. Returns
    /// `None` for an expression that is not a named expression (the parser never produces one).
    fn resolve_place(&mut self, target: &Expr) -> Result<Option<Place>, BcError> {
        Ok(match target {
            Expr::Variable(name) => Some(Place::Variable(name.clone())),
            Expr::ArrayAccess(name, index_expr) => {
                let idx = self.try_evaluate(index_expr)?;
                Some(Place::Element(name.clone(), Self::array_index(name, &idx)?))
            }
            Expr::RegisterAccess(reg) => Some(Place::Register(*reg)),
            _ => None,
        })
    }

    /// Reads the current value of a resolved target.
    fn load(&mut self, place: &Place) -> BCNum {
        match place {
            Place::Variable(name) => self.var_get(name),
            Place::Element(name, index) => self.arr_get(name, *index),
            Place::Register(reg) => BCNum::new(BigInt::from(self.register(*reg)), 0),
        }
    }

    /// Writes `val` to a resolved target and returns the value now held there (registers clamp
    /// it to their range).
    fn store(&mut self, place: Place, val: &BCNum) -> BCNum {
        match place {
            Place::Variable(name) => self.var_set(name, val.clone()),
            Place::Element(name, index) => self.arr_set(name, index, val.clone()),
            Place::Register(reg) => {
                let stored = self.store_register(reg, val);
                return BCNum::new(BigInt::from(stored), 0);
            }
        }
        val.clone()
    }

    fn register(&self, reg: Register) -> usize {
        match reg {
            Register::Scale => self.scale,
            Register::Ibase => self.ibase,
            Register::Obase => self.obase,
        }
    }

    /// A copy of the current frame of array `name` (empty if it has none), for an array
    /// argument. Not verified yet.
    fn arr_frame_clone(&self, name: &str) -> BTreeMap<usize, BCNum> {
        match self.arrays.get(name).and_then(|stack| stack.last()) {
            Some(frame) => frame.clone(),
            None => BTreeMap::new(),
        }
    }

    /// Converts the subscript `idx` of array `name` to an index, truncating it to an integer.
    /// Negative subscripts and subscripts of at least `BC_DIM_MAX` are runtime errors.
    fn array_index(name: &str, idx: &BCNum) -> Result<usize, BcError> {
        let index = &idx.coeff / pow10(idx.scale);
        match index.to_usize() {
            Some(i) if !idx.coeff.is_negative() && i < BC_DIM_MAX => Ok(i),
            _ => Err(RuntimeError::ArraySubscriptOutOfBounds(String::from(name)).into()),
        }
    }

    /// Stores `val`, truncated to an integer, into register `reg`, clamping it to the register's range with a warning (`docs/COMPATIBILITY.md`
    /// §3.3). Returns the stored value.
    fn store_register(&mut self, reg: Register, val: &BCNum) -> usize {
        let magnitude = (&val.coeff / pow10(val.scale))
            .abs()
            .to_usize()
            .unwrap_or(usize::MAX);
        let (min, max) = match reg {
            Register::Scale => (0, BC_SCALE_MAX),
            Register::Ibase => (2, IBASE_MAX),
            Register::Obase => (2, BC_BASE_MAX),
        };
        let name = reg.name();
        let (v, kind) = verified_clamp_register(magnitude, val.coeff.is_negative(), min, max);
        match kind {
            -2 => self.warn(&format!("negative {}, set to {}", name, min)),
            -1 => self.warn(&format!("{} too small, set to {}", name, min)),
            1 => self.warn(&format!("{} too large, set to {}", name, max)),
            _ => {}
        }
        match reg {
            Register::Scale => self.scale = v,
            Register::Ibase => self.ibase = v,
            Register::Obase => self.obase = v,
        }
        v
    }

    /// Converts a numeric literal: at top level in the current `ibase`, and in a function body
    /// in the `ibase` in effect when the function was invoked (POSIX). A literal with more than
    /// `BC_SCALE_MAX` fractional digits is rejected to keep the scale invariant.
    fn literal(&self, digits: &str) -> Result<BCNum, BcError> {
        Ok(BCNum::try_from_string(
            digits,
            self.invocation_ibase.unwrap_or(self.ibase),
        )?)
    }

    /// Computes `base ^ exp`, warning when the exponent has a fractional part.
    fn power(&mut self, base: &BCNum, exp: &BCNum) -> Result<BCNum, BcError> {
        if exp.scale > 0 {
            self.warn("non-zero scale in exponent");
        }
        Ok(base.try_pow(exp, self.scale)?)
    }

    /// Executes a function body, stopping after `return` (or `quit`).
    fn run_body(&mut self, body: &[Stmt]) -> Result<(), BcError> {
        for stmt in body {
            self.try_execute(stmt)?;
            if self.return_flag || self.quit_flag {
                break;
            }
        }
        Ok(())
    }

    /// Leaves function `func`: pops the call, restores the caller's return state and
    /// invocation `ibase`, and pops the `auto` frames and then the parameter frames, each list
    /// last first (the specification's `leave_call`).
    fn leave_call(&mut self, func: &FunctionDef, saved: SavedCall) {
        self.call_stack.pop();
        self.return_flag = saved.return_flag;
        self.return_value = saved.return_value;
        self.invocation_ibase = saved.invocation_ibase;
        for param in func.autos.iter().rev().chain(func.params.iter().rev()) {
            if param.is_array {
                self.arr_pop(&param.name);
            } else {
                self.var_pop(&param.name);
            }
        }
    }

    /// `l <op> r` at the current `scale` (the specification's `arith`).
    fn arith(&mut self, op: BinOp, l: &BCNum, r: &BCNum) -> Result<BCNum, BcError> {
        match op {
            BinOp::Add => Ok(l.add(r)),
            BinOp::Sub => Ok(l.sub(r)),
            BinOp::Mul => Ok(l.mul(r, self.scale)),
            BinOp::Div => Ok(l.try_div(r, self.scale)?),
            BinOp::Mod => Ok(l.try_mod_op(r, self.scale)?),
            BinOp::Pow => self.power(l, r),
        }
    }

    /// The expressions that `eval_node_ref` does not handle yet (not verified).
    /// `eval_other` states what the verified code relies on.
    fn eval_other_impl(&mut self, node: &Expr) -> Result<BCNum, BcError> {
        match node {
            Expr::Number(value) => self.literal(value),
            Expr::Variable(name) => Ok(self.var_get(name)),
            Expr::ArrayAccess(name, index_expr) => {
                let idx = self.try_evaluate(index_expr)?;
                let idx_val = Self::array_index(name, &idx)?;
                Ok(self.arr_get(name, idx_val))
            }
            Expr::RegisterAccess(reg) => Ok(BCNum::new(BigInt::from(self.register(*reg)), 0)),
            Expr::Negate(expr) => {
                let val = self.try_evaluate(expr)?;
                Ok(BCNum::new(-val.coeff, val.scale))
            }
            Expr::BinaryOp(op, left, right) => {
                let l = self.try_evaluate(left)?;
                let r = self.try_evaluate(right)?;
                self.arith(*op, &l, &r)
            }
            Expr::RelationalOp(op, left, right) => {
                let l = self.try_evaluate(left)?;
                let r = self.try_evaluate(right)?;
                let ord = l.cmp_val(&r);
                let res = match op {
                    RelOp::Eq => ord == Ordering::Equal,
                    RelOp::Ne => ord != Ordering::Equal,
                    RelOp::Lt => ord == Ordering::Less,
                    RelOp::Le => ord != Ordering::Greater,
                    RelOp::Gt => ord == Ordering::Greater,
                    RelOp::Ge => ord != Ordering::Less,
                };
                Ok(BCNum::new(BigInt::from(if res { 1 } else { 0 }), 0))
            }
            Expr::AssignOp(op, target, expr) => {
                // The named expression is evaluated once, before the right-hand side, as in
                // GNU bc: `a[i++] = i` stores into a[0], and `c += c++` adds the old value.
                let place = self.resolve_place(target)?;

                let val = match (&place, op, &**expr) {
                    // POSIX: a single digit assigned to ibase or obase is read as hexadecimal.
                    (
                        Some(Place::Register(Register::Ibase | Register::Obase)),
                        AssignOp::Assign,
                        Expr::Number(digits),
                    ) if digits.replace("\\\n", "").len() == 1 => {
                        let b = digits.replace("\\\n", "").as_bytes()[0];
                        BCNum::new(BigInt::from(verified_hex_char_val(b)), 0)
                    }
                    (_, AssignOp::Assign, _) => self.try_evaluate(expr)?,
                    (_, AssignOp::Compound(bin), _) => {
                        let old_val = match &place {
                            Some(place) => self.load(place),
                            None => self.try_evaluate(target)?,
                        };
                        let rhs = self.try_evaluate(expr)?;
                        self.arith(*bin, &old_val, &rhs)?
                    }
                };

                // As in GNU bc, the value of the assignment is the value assigned, even when a
                // register clamps it.
                if let Some(place) = place {
                    self.store(place, &val);
                }
                Ok(val)
            }
            Expr::Update(increment, is_prefix, target) => {
                let place = self.resolve_place(target)?;
                let old_val = match &place {
                    Some(place) => self.load(place),
                    None => self.try_evaluate(target)?,
                };
                let step = BCNum::new(BigInt::from(1), 0);
                let new_val = if *increment {
                    old_val.add(&step)
                } else {
                    old_val.sub(&step)
                };
                let stored = match place {
                    Some(place) => self.store(place, &new_val),
                    None => new_val,
                };
                Ok(if *is_prefix { stored } else { old_val })
            }
            Expr::Call(name, args) => {
                if let Some(func) = self.functions.get(name).cloned() {
                    if args.len() != func.params.len() {
                        return Err(RuntimeError::ParameterMismatch.into());
                    }

                    /// A parameter value, evaluated before any frame is pushed.
                    enum ArgValue {
                        Array(BTreeMap<usize, BCNum>),
                        Scalar(BCNum),
                    }
                    let mut evaluated_args = Vec::new();
                    for (i, arg) in args.iter().enumerate() {
                        let param = &func.params[i];
                        if param.is_array {
                            if let ExprOrArray::ArrayArg(arg_name) = arg {
                                let arr_copy = self.arr_frame_clone(arg_name);
                                evaluated_args
                                    .push((param.name.clone(), ArgValue::Array(arr_copy)));
                            } else {
                                return Err(RuntimeError::ParameterTypeMismatch(
                                    param.name.clone(),
                                )
                                .into());
                            }
                        } else if let ExprOrArray::Expr(expr) = arg {
                            let val = self.try_evaluate(expr)?;
                            evaluated_args.push((param.name.clone(), ArgValue::Scalar(val)));
                        } else {
                            return Err(
                                RuntimeError::ParameterTypeMismatch(param.name.clone()).into()
                            );
                        }
                    }

                    // Every name keeps its global frame at the bottom of its stack, so popping
                    // the function's frames in `leave_call` never leaves an empty stack
                    // (a name first seen as a parameter or `auto` stays usable afterwards).
                    for (pname, value) in evaluated_args {
                        match value {
                            ArgValue::Array(arr) => self.arr_push(pname, arr),
                            ArgValue::Scalar(val) => self.var_push(pname, val),
                        }
                    }

                    for auto in &func.autos {
                        if auto.is_array {
                            self.arr_push(auto.name.clone(), BTreeMap::new());
                        } else {
                            self.var_push(auto.name.clone(), BCNum::zero());
                        }
                    }

                    let saved = SavedCall {
                        return_flag: self.return_flag,
                        return_value: self.return_value.clone(),
                        invocation_ibase: self.invocation_ibase.replace(self.ibase),
                    };
                    self.return_flag = false;
                    self.return_value = BCNum::zero();
                    self.call_stack.push(name.clone());

                    let body = self.run_body(&func.body).map_err(|e| e.in_function(name));
                    let ret_val = self.return_value.clone();
                    // Restored on every return path, including errors.
                    self.leave_call(&func, saved);
                    return body.map(|()| ret_val);
                }

                if self.math_enabled {
                    use crate::math::{bc_atan, bc_bessel, bc_cos, bc_exp, bc_ln, bc_sin};
                    match (name.as_str(), args.as_slice()) {
                        ("s", [ExprOrArray::Expr(expr)]) => {
                            return Ok(bc_sin(&self.try_evaluate(expr)?, self.scale)?);
                        }
                        ("c", [ExprOrArray::Expr(expr)]) => {
                            return Ok(bc_cos(&self.try_evaluate(expr)?, self.scale)?);
                        }
                        ("a", [ExprOrArray::Expr(expr)]) => {
                            return Ok(bc_atan(&self.try_evaluate(expr)?, self.scale)?);
                        }
                        ("l", [ExprOrArray::Expr(expr)]) => {
                            return Ok(bc_ln(&self.try_evaluate(expr)?, self.scale)?);
                        }
                        ("e", [ExprOrArray::Expr(expr)]) => {
                            return Ok(bc_exp(&self.try_evaluate(expr)?, self.scale)?);
                        }
                        ("j", [ExprOrArray::Expr(expr_n), ExprOrArray::Expr(expr_x)]) => {
                            let n_val = self.try_evaluate(expr_n)?;
                            let x_val = self.try_evaluate(expr_x)?;
                            return Ok(bc_bessel(&n_val, &x_val, self.scale)?);
                        }
                        _ => {}
                    }
                }

                Err(RuntimeError::UndefinedFunction(name.clone()).into())
            }
            Expr::LengthCall(expr) => Ok(self.try_evaluate(expr)?.length()),
            Expr::SqrtCall(expr) => self
                .try_evaluate(expr)?
                .try_sqrt(self.scale)
                .map_err(BcError::from),
            Expr::ScaleCall(expr) => Ok(self.try_evaluate(expr)?.scale_func()),
            Expr::Paren(expr) => self.try_evaluate(expr),
        }
    }

    /// Evaluates an AST expression node and returns a BCNum.
    #[cfg(test)]
    pub fn evaluate(&mut self, node: &Expr) -> BCNum {
        self.try_evaluate(node).unwrap_or_else(|e| panic!("{}", e))
    }

    /// Executes an AST statement node.
    #[cfg(test)]
    pub fn execute(&mut self, node: &Stmt) {
        self.try_execute(node).unwrap_or_else(|e| panic!("{}", e))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::Lexer;
    use crate::parser::Param;
    use crate::parser::Parser;
    use alloc::string::ToString;

    #[derive(Clone)]
    struct TestWriter {
        buf: std::sync::Arc<std::sync::Mutex<Vec<u8>>>,
    }

    impl FmtWrite for TestWriter {
        fn write_str(&mut self, s: &str) -> core::fmt::Result {
            self.buf.lock().unwrap().extend_from_slice(s.as_bytes());
            Ok(())
        }
    }

    impl BcWriter for TestWriter {
        fn flush(&mut self) -> core::fmt::Result {
            Ok(())
        }
    }

    fn test_eval(input: &str) -> (String, String) {
        let lexer = Lexer::new(input);
        let mut parser = Parser::new(lexer);
        let stmts = parser.parse_program();

        let stdout_buf = std::sync::Arc::new(std::sync::Mutex::new(Vec::new()));
        let stderr_buf = std::sync::Arc::new(std::sync::Mutex::new(Vec::new()));

        let stdout = TestWriter {
            buf: stdout_buf.clone(),
        };
        let stderr = TestWriter {
            buf: stderr_buf.clone(),
        };

        let mut eval = Evaluator::new(true, Box::new(stdout), Box::new(stderr));

        for stmt in &stmts {
            eval.execute(stmt);
        }

        let out = String::from_utf8(stdout_buf.lock().unwrap().clone()).unwrap();
        let err = String::from_utf8(stderr_buf.lock().unwrap().clone()).unwrap();
        (out, err)
    }

    #[test]
    fn test_emptied_public_scope_stacks_do_not_panic() {
        let stdout_buf = std::sync::Arc::new(std::sync::Mutex::new(Vec::new()));
        let stdout = TestWriter {
            buf: stdout_buf.clone(),
        };
        let stderr = TestWriter {
            buf: std::sync::Arc::new(std::sync::Mutex::new(Vec::new())),
        };
        let mut eval = Evaluator::new(false, Box::new(stdout), Box::new(stderr));
        // An embedder may leave an empty stack in the public fields; reads see the global
        // default and writes recreate the frame.
        eval.variables.insert("x".to_string(), Vec::new());
        eval.arrays.insert("a".to_string(), Vec::new());
        eval.arrays.insert("b".to_string(), Vec::new());
        let summary = eval.run_source(
            "x; a[0]; x += 2; x; a[1] = 3; a[1]\ndefine f(c[]) {\nreturn (c[0])\n}\nf(b[])\n",
            "(test)",
        );
        assert_eq!(summary.errors, 0);
        let out = String::from_utf8(stdout_buf.lock().unwrap().clone()).unwrap();
        assert_eq!(out, "0\n0\n2\n3\n0\n");
    }

    #[test]
    fn test_evaluator_basic() {
        let (out, _) = test_eval("1 + 2; 5 * 6");
        assert_eq!(out, "3\n30\n");
    }

    #[test]
    fn test_scoping_functions() {
        let input = "
            define f(x) {
                auto a;
                a = 10;
                return (x + a);
            }
            f(5)
        ";
        let (out, _) = test_eval(input);
        assert_eq!(out, "15\n");
    }

    #[test]
    fn test_while_loop() {
        let input = "
            a = 0;
            while (a < 3) {
                a = a + 1;
                a;
            }
        ";
        let (out, _) = test_eval(input);
        assert_eq!(out, "1\n2\n3\n");
    }

    #[test]
    fn test_ibase_warning() {
        let (_, err1) = test_eval("ibase = 1");
        assert!(err1.contains("ibase too small"));

        let (_, err2) = test_eval("ibase = 20");
        assert!(err2.contains("ibase too large"));
    }

    #[test]
    fn test_eval_uncovered_lines() {
        use crate::parser::{Expr, ExprOrArray, FunctionDef, Param, Register, Stmt};

        let mut evaluator = Evaluator::new(true, Box::new(String::new()), Box::new(String::new()));

        // 1. Array access with fractional index (lines 108-109)
        evaluator.execute(&Stmt::Expr(Expr::AssignOp(
            AssignOp::Assign,
            Box::new(Expr::ArrayAccess(
                "a".to_string(),
                Box::new(Expr::Number("1.5".to_string())),
            )),
            Box::new(Expr::Number("42".to_string())),
        )));
        evaluator.execute(&Stmt::Expr(Expr::ArrayAccess(
            "a".to_string(),
            Box::new(Expr::Number("1.5".to_string())),
        )));

        // 6. Assign single non-hex char to ibase and obase
        evaluator.execute(&Stmt::Expr(Expr::AssignOp(
            AssignOp::Assign,
            Box::new(Expr::RegisterAccess(Register::Ibase)),
            Box::new(Expr::Number("Z".to_string())),
        )));
        assert_eq!(evaluator.ibase, 2);

        evaluator.execute(&Stmt::Expr(Expr::AssignOp(
            AssignOp::Assign,
            Box::new(Expr::RegisterAccess(Register::Obase)),
            Box::new(Expr::Number("Z".to_string())),
        )));
        assert_eq!(evaluator.obase, 2);

        // Assign single non-hex char to variable (distinguishes is_base_reg && op == "=" from ||)
        evaluator.execute(&Stmt::Expr(Expr::AssignOp(
            AssignOp::Assign,
            Box::new(Expr::Variable("var_g".to_string())),
            Box::new(Expr::Number("G".to_string())),
        )));
        let var_g = evaluator.evaluate(&Expr::Variable("var_g".to_string()));
        assert_eq!(var_g.coeff, BigInt::from(16));

        // 8. Assign fractional value to register (lines 257-258)
        evaluator.execute(&Stmt::Expr(Expr::AssignOp(
            AssignOp::Assign,
            Box::new(Expr::RegisterAccess(Register::Scale)),
            Box::new(Expr::Number("2.5".to_string())),
        )));

        // 9. obase < 2 update (line 290)
        evaluator.execute(&Stmt::Expr(Expr::AssignOp(
            AssignOp::Assign,
            Box::new(Expr::RegisterAccess(Register::Obase)),
            Box::new(Expr::Number("1".to_string())),
        )));

        // 10. Update of a non-named expression (unreachable from the parser)
        let node_update_unreach = Expr::Update(true, true, Box::new(Expr::Number("1".to_string())));
        let res_unreach_val = evaluator.evaluate(&node_update_unreach);
        assert_eq!(res_unreach_val.coeff, BigInt::from(2));

        // 10b. Additional tests for ibase single-character assignment edge cases
        // A) multi-character number (cleaned.len() != 1)
        evaluator.execute(&Stmt::Expr(Expr::AssignOp(
            AssignOp::Assign,
            Box::new(Expr::RegisterAccess(Register::Ibase)),
            Box::new(Expr::Number("10".to_string())),
        )));
        // B) non-number (expr is not Expr::Number)
        evaluator.execute(&Stmt::Expr(Expr::AssignOp(
            AssignOp::Assign,
            Box::new(Expr::RegisterAccess(Register::Ibase)),
            Box::new(Expr::Variable("x".to_string())),
        )));
        // C) single character non-hex digit (c is not ascii digit or A-F)
        evaluator.execute(&Stmt::Expr(Expr::AssignOp(
            AssignOp::Assign,
            Box::new(Expr::RegisterAccess(Register::Ibase)),
            Box::new(Expr::Number(".".to_string())),
        )));

        // AssignOp non-lvalue target fallback (line 301)
        let node_assign_unreach = Expr::AssignOp(
            AssignOp::Assign,
            Box::new(Expr::Number("1".to_string())),
            Box::new(Expr::Number("2".to_string())),
        );
        let res_assign_unreach = evaluator.evaluate(&node_assign_unreach);
        assert_eq!(res_assign_unreach.coeff, BigInt::from(2));

        // 11. Increment/decrement array at a fractional index (lines 325-326)
        evaluator.execute(&Stmt::Expr(Expr::Update(
            true,
            true,
            Box::new(Expr::ArrayAccess(
                "a".to_string(),
                Box::new(Expr::Number("1.5".to_string())),
            )),
        )));

        // 12. Increment/decrement a register with a fractional value (lines 340-341)
        evaluator.execute(&Stmt::Expr(Expr::AssignOp(
            AssignOp::Assign,
            Box::new(Expr::RegisterAccess(Register::Scale)),
            Box::new(Expr::Number("2.5".to_string())),
        )));
        evaluator.execute(&Stmt::Expr(Expr::Update(
            true,
            true,
            Box::new(Expr::RegisterAccess(Register::Scale)),
        )));

        // 13. Update obase with cap (line 360)
        evaluator.execute(&Stmt::Expr(Expr::AssignOp(
            AssignOp::Assign,
            Box::new(Expr::RegisterAccess(Register::Obase)),
            Box::new(Expr::Number("2".to_string())),
        )));
        evaluator.execute(&Stmt::Expr(Expr::Update(
            false,
            true,
            Box::new(Expr::RegisterAccess(Register::Obase)),
        )));

        // 14. Function argument errors (lines 379, 399, 405)
        evaluator.functions.insert(
            "f_param_err".to_string(),
            FunctionDef {
                name: "f_param_err".to_string(),
                params: vec![Param {
                    name: "x".to_string(),
                    is_array: false,
                }],
                autos: vec![],
                body: vec![],
            },
        );
        let res_f_arg_cnt = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            evaluator.evaluate(&Expr::Call("f_param_err".to_string(), vec![]));
        }));
        assert!(res_f_arg_cnt.is_err());

        let res_f_arg_arr_mismatch = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            evaluator.evaluate(&Expr::Call(
                "f_param_err".to_string(),
                vec![ExprOrArray::ArrayArg("a".to_string())],
            ));
        }));
        assert!(res_f_arg_arr_mismatch.is_err());

        evaluator.functions.insert(
            "f_arr_err".to_string(),
            FunctionDef {
                name: "f_arr_err".to_string(),
                params: vec![Param {
                    name: "x".to_string(),
                    is_array: true,
                }],
                autos: vec![],
                body: vec![],
            },
        );
        let res_f_arr_expr_mismatch =
            std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                evaluator.evaluate(&Expr::Call(
                    "f_arr_err".to_string(),
                    vec![ExprOrArray::Expr(Expr::Number("1".to_string()))],
                ));
            }));
        assert!(res_f_arr_expr_mismatch.is_err());

        // 15. Undefined function call in math mode (line 500)
        let res_undef_func = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            evaluator.evaluate(&Expr::Call("nonexistent".to_string(), vec![]));
        }));
        assert!(res_undef_func.is_err());

        // 16. Early execute return (line 515)
        evaluator.break_flag = true;
        evaluator.execute(&Stmt::Expr(Expr::Number("10".to_string())));
        evaluator.break_flag = false;

        // 17. Stmt::Quit execution (lines 544-546)
        evaluator.execute(&Stmt::Quit);
        assert!(evaluator.quit_flag);

        // 18. Uninitialized variables and arrays access to cover entry().or_insert_with() closures
        let _ = evaluator.evaluate(&Expr::Variable("uninit_var".to_string()));
        let _ = evaluator.evaluate(&Expr::ArrayAccess(
            "uninit_arr".to_string(),
            Box::new(Expr::Number("0".to_string())),
        ));
        evaluator.execute(&Stmt::Expr(Expr::AssignOp(
            AssignOp::Assign,
            Box::new(Expr::Variable("uninit_var_assign".to_string())),
            Box::new(Expr::Number("10".to_string())),
        )));
        evaluator.execute(&Stmt::Expr(Expr::AssignOp(
            AssignOp::Assign,
            Box::new(Expr::ArrayAccess(
                "uninit_arr_assign".to_string(),
                Box::new(Expr::Number("0".to_string())),
            )),
            Box::new(Expr::Number("10".to_string())),
        )));
        let _ = evaluator.evaluate(&Expr::Update(
            true,
            true,
            Box::new(Expr::Variable("uninit_var_inc".to_string())),
        ));
        let _ = evaluator.evaluate(&Expr::Update(
            true,
            true,
            Box::new(Expr::ArrayAccess(
                "uninit_arr_inc".to_string(),
                Box::new(Expr::Number("0".to_string())),
            )),
        ));
        evaluator.functions.insert(
            "f_uninit_arr_arg".to_string(),
            FunctionDef {
                name: "f_uninit_arr_arg".to_string(),
                params: vec![Param {
                    name: "x".to_string(),
                    is_array: true,
                }],
                autos: vec![],
                body: vec![],
            },
        );
        let _ = evaluator.evaluate(&Expr::Call(
            "f_uninit_arr_arg".to_string(),
            vec![ExprOrArray::ArrayArg("uninit_arr_arg".to_string())],
        ));

        // 19. Frames are restored when a function returns an error
        evaluator.quit_flag = false;
        evaluator.variables.insert(
            "shadowed_var".to_string(),
            vec![BCNum::new(BigInt::from(99), 0)],
        );
        evaluator.functions.insert(
            "f_panic".to_string(),
            FunctionDef {
                name: "f_panic".to_string(),
                params: vec![],
                autos: vec![Param {
                    name: "shadowed_var".to_string(),
                    is_array: false,
                }],
                body: vec![Stmt::Expr(Expr::BinaryOp(
                    BinOp::Div,
                    Box::new(Expr::Number("1".to_string())),
                    Box::new(Expr::Number("0".to_string())),
                ))],
            },
        );
        let panic_res = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            evaluator.evaluate(&Expr::Call("f_panic".to_string(), vec![]));
        }));
        assert!(panic_res.is_err());
        let restored_val = evaluator.evaluate(&Expr::Variable("shadowed_var".to_string()));
        assert_eq!(restored_val.coeff, BigInt::from(99));
    }

    #[test]
    fn test_evaluator_operator_and_assignment_mutants() {
        let stdout_buf = std::sync::Arc::new(std::sync::Mutex::new(Vec::new()));
        let stderr_buf = std::sync::Arc::new(std::sync::Mutex::new(Vec::new()));
        let stdout = TestWriter {
            buf: stdout_buf.clone(),
        };
        let stderr = TestWriter {
            buf: stderr_buf.clone(),
        };
        let mut evaluator = Evaluator::new(false, Box::new(stdout), Box::new(stderr));

        // Test all relational operations cleanly
        assert_eq!(
            evaluator
                .evaluate(&Expr::RelationalOp(
                    RelOp::Eq,
                    Box::new(Expr::Number("1".to_string())),
                    Box::new(Expr::Number("1".to_string()))
                ))
                .coeff,
            BigInt::from(1)
        );
        assert_eq!(
            evaluator
                .evaluate(&Expr::RelationalOp(
                    RelOp::Eq,
                    Box::new(Expr::Number("1".to_string())),
                    Box::new(Expr::Number("2".to_string()))
                ))
                .coeff,
            BigInt::from(0)
        );

        assert_eq!(
            evaluator
                .evaluate(&Expr::RelationalOp(
                    RelOp::Ne,
                    Box::new(Expr::Number("1".to_string())),
                    Box::new(Expr::Number("2".to_string()))
                ))
                .coeff,
            BigInt::from(1)
        );
        assert_eq!(
            evaluator
                .evaluate(&Expr::RelationalOp(
                    RelOp::Ne,
                    Box::new(Expr::Number("1".to_string())),
                    Box::new(Expr::Number("1".to_string()))
                ))
                .coeff,
            BigInt::from(0)
        );

        assert_eq!(
            evaluator
                .evaluate(&Expr::RelationalOp(
                    RelOp::Lt,
                    Box::new(Expr::Number("1".to_string())),
                    Box::new(Expr::Number("2".to_string()))
                ))
                .coeff,
            BigInt::from(1)
        );
        assert_eq!(
            evaluator
                .evaluate(&Expr::RelationalOp(
                    RelOp::Lt,
                    Box::new(Expr::Number("2".to_string())),
                    Box::new(Expr::Number("2".to_string()))
                ))
                .coeff,
            BigInt::from(0)
        );

        assert_eq!(
            evaluator
                .evaluate(&Expr::RelationalOp(
                    RelOp::Le,
                    Box::new(Expr::Number("2".to_string())),
                    Box::new(Expr::Number("2".to_string()))
                ))
                .coeff,
            BigInt::from(1)
        );
        assert_eq!(
            evaluator
                .evaluate(&Expr::RelationalOp(
                    RelOp::Le,
                    Box::new(Expr::Number("3".to_string())),
                    Box::new(Expr::Number("2".to_string()))
                ))
                .coeff,
            BigInt::from(0)
        );

        assert_eq!(
            evaluator
                .evaluate(&Expr::RelationalOp(
                    RelOp::Gt,
                    Box::new(Expr::Number("3".to_string())),
                    Box::new(Expr::Number("2".to_string()))
                ))
                .coeff,
            BigInt::from(1)
        );
        assert_eq!(
            evaluator
                .evaluate(&Expr::RelationalOp(
                    RelOp::Gt,
                    Box::new(Expr::Number("2".to_string())),
                    Box::new(Expr::Number("2".to_string()))
                ))
                .coeff,
            BigInt::from(0)
        );

        assert_eq!(
            evaluator
                .evaluate(&Expr::RelationalOp(
                    RelOp::Ge,
                    Box::new(Expr::Number("2".to_string())),
                    Box::new(Expr::Number("2".to_string()))
                ))
                .coeff,
            BigInt::from(1)
        );
        assert_eq!(
            evaluator
                .evaluate(&Expr::RelationalOp(
                    RelOp::Ge,
                    Box::new(Expr::Number("1".to_string())),
                    Box::new(Expr::Number("2".to_string()))
                ))
                .coeff,
            BigInt::from(0)
        );

        // Test compound assignments +=, -=, *=, /=, %=, ^=
        evaluator.execute(&Stmt::Expr(Expr::AssignOp(
            AssignOp::Assign,
            Box::new(Expr::Variable("x".to_string())),
            Box::new(Expr::Number("10".to_string())),
        )));
        evaluator.execute(&Stmt::Expr(Expr::AssignOp(
            AssignOp::Compound(BinOp::Add),
            Box::new(Expr::Variable("x".to_string())),
            Box::new(Expr::Number("5".to_string())),
        )));
        assert_eq!(
            evaluator.evaluate(&Expr::Variable("x".to_string())).coeff,
            BigInt::from(15)
        );

        evaluator.execute(&Stmt::Expr(Expr::AssignOp(
            AssignOp::Compound(BinOp::Sub),
            Box::new(Expr::Variable("x".to_string())),
            Box::new(Expr::Number("3".to_string())),
        )));
        assert_eq!(
            evaluator.evaluate(&Expr::Variable("x".to_string())).coeff,
            BigInt::from(12)
        );

        evaluator.execute(&Stmt::Expr(Expr::AssignOp(
            AssignOp::Compound(BinOp::Mul),
            Box::new(Expr::Variable("x".to_string())),
            Box::new(Expr::Number("2".to_string())),
        )));
        assert_eq!(
            evaluator.evaluate(&Expr::Variable("x".to_string())).coeff,
            BigInt::from(24)
        );

        evaluator.execute(&Stmt::Expr(Expr::AssignOp(
            AssignOp::Compound(BinOp::Div),
            Box::new(Expr::Variable("x".to_string())),
            Box::new(Expr::Number("4".to_string())),
        )));
        assert_eq!(
            evaluator.evaluate(&Expr::Variable("x".to_string())).coeff,
            BigInt::from(6)
        );

        evaluator.execute(&Stmt::Expr(Expr::AssignOp(
            AssignOp::Compound(BinOp::Mod),
            Box::new(Expr::Variable("x".to_string())),
            Box::new(Expr::Number("4".to_string())),
        )));
        assert_eq!(
            evaluator.evaluate(&Expr::Variable("x".to_string())).coeff,
            BigInt::from(2)
        );

        evaluator.execute(&Stmt::Expr(Expr::AssignOp(
            AssignOp::Compound(BinOp::Pow),
            Box::new(Expr::Variable("x".to_string())),
            Box::new(Expr::Number("3".to_string())),
        )));
        assert_eq!(
            evaluator.evaluate(&Expr::Variable("x".to_string())).coeff,
            BigInt::from(8)
        );

        // Test pre/post increment and decrement
        let pre_inc = evaluator.evaluate(&Expr::Update(
            true,
            true,
            Box::new(Expr::Variable("x".to_string())),
        ));
        assert_eq!(pre_inc.coeff, BigInt::from(9));

        let post_inc = evaluator.evaluate(&Expr::Update(
            true,
            false,
            Box::new(Expr::Variable("x".to_string())),
        ));
        assert_eq!(post_inc.coeff, BigInt::from(9));
        assert_eq!(
            evaluator.evaluate(&Expr::Variable("x".to_string())).coeff,
            BigInt::from(10)
        );

        let pre_dec = evaluator.evaluate(&Expr::Update(
            false,
            true,
            Box::new(Expr::Variable("x".to_string())),
        ));
        assert_eq!(pre_dec.coeff, BigInt::from(9));

        let post_dec = evaluator.evaluate(&Expr::Update(
            false,
            false,
            Box::new(Expr::Variable("x".to_string())),
        ));
        assert_eq!(post_dec.coeff, BigInt::from(9));
        assert_eq!(
            evaluator.evaluate(&Expr::Variable("x".to_string())).coeff,
            BigInt::from(8)
        );

        // Test Stmt::For and Stmt::If control flow branches
        evaluator.execute(&Stmt::For(
            Expr::AssignOp(
                AssignOp::Assign,
                Box::new(Expr::Variable("var_i".to_string())),
                Box::new(Expr::Number("0".to_string())),
            ),
            Expr::RelationalOp(
                RelOp::Lt,
                Box::new(Expr::Variable("var_i".to_string())),
                Box::new(Expr::Number("3".to_string())),
            ),
            Expr::Update(true, true, Box::new(Expr::Variable("var_i".to_string()))),
            Box::new(Stmt::Block(vec![])),
        ));
        assert_eq!(
            evaluator
                .evaluate(&Expr::Variable("var_i".to_string()))
                .coeff,
            BigInt::from(3)
        );

        // Test Stmt::StringLiteral
        evaluator.execute(&Stmt::StringLiteral("out: hello".to_string()));
        let out_str = String::from_utf8(stdout_buf.lock().unwrap().clone()).unwrap();
        assert!(out_str.contains("out: hello"));
    }

    #[test]
    fn test_fractional_indices_and_register_truncation() {
        let stdout_buf = std::sync::Arc::new(std::sync::Mutex::new(Vec::new()));
        let stderr_buf = std::sync::Arc::new(std::sync::Mutex::new(Vec::new()));
        let stdout = TestWriter {
            buf: stdout_buf.clone(),
        };
        let stderr = TestWriter {
            buf: stderr_buf.clone(),
        };
        let mut evaluator = Evaluator::new(false, Box::new(stdout), Box::new(stderr));

        // 1. Assign to array using fractional index a[3.8] = 99
        evaluator.execute(&Stmt::Expr(Expr::AssignOp(
            AssignOp::Assign,
            Box::new(Expr::ArrayAccess(
                "arr".to_string(),
                Box::new(Expr::Number("3.8".to_string())),
            )),
            Box::new(Expr::Number("99".to_string())),
        )));

        // Read from array using fractional index a[3.1]
        let val_arr = evaluator.evaluate(&Expr::ArrayAccess(
            "arr".to_string(),
            Box::new(Expr::Number("3.1".to_string())),
        ));
        assert_eq!(val_arr.coeff, BigInt::from(99));

        // 2. Assign fractional values to scale, obase, ibase registers
        evaluator.execute(&Stmt::Expr(Expr::AssignOp(
            AssignOp::Assign,
            Box::new(Expr::RegisterAccess(Register::Scale)),
            Box::new(Expr::Number("5.9".to_string())),
        )));
        assert_eq!(evaluator.scale, 5);

        evaluator.execute(&Stmt::Expr(Expr::AssignOp(
            AssignOp::Assign,
            Box::new(Expr::RegisterAccess(Register::Obase)),
            Box::new(Expr::Number("10.4".to_string())),
        )));
        assert_eq!(evaluator.obase, 10);

        evaluator.execute(&Stmt::Expr(Expr::AssignOp(
            AssignOp::Assign,
            Box::new(Expr::RegisterAccess(Register::Ibase)),
            Box::new(Expr::Number("16.7".to_string())),
        )));
        assert_eq!(evaluator.ibase, 16);
    }

    #[test]
    fn test_control_flow_truth_tables() {
        let stdout_buf = std::sync::Arc::new(std::sync::Mutex::new(Vec::new()));
        let stderr_buf = std::sync::Arc::new(std::sync::Mutex::new(Vec::new()));
        let stdout = TestWriter {
            buf: stdout_buf.clone(),
        };
        let stderr = TestWriter {
            buf: stderr_buf.clone(),
        };
        let mut evaluator = Evaluator::new(false, Box::new(stdout), Box::new(stderr));

        // Test if conditions for truth values of relational operators
        for (lhs, rhs, op, expected) in [
            ("5", "5", "==", true),
            ("5", "3", "==", false),
            ("5", "3", "!=", true),
            ("5", "5", "!=", false),
            ("3", "5", "<", true),
            ("5", "5", "<", false),
            ("3", "5", "<=", true),
            ("5", "5", "<=", true),
            ("6", "5", "<=", false),
            ("5", "3", ">", true),
            ("5", "5", ">", false),
            ("5", "3", ">=", true),
            ("5", "5", ">=", true),
            ("3", "5", ">=", false),
        ] {
            evaluator.variables.clear();
            evaluator.execute(&Stmt::If(
                Expr::RelationalOp(
                    RelOp::from_symbol(op),
                    Box::new(Expr::Number(lhs.to_string())),
                    Box::new(Expr::Number(rhs.to_string())),
                ),
                Box::new(Stmt::Expr(Expr::AssignOp(
                    AssignOp::Assign,
                    Box::new(Expr::Variable("hit".to_string())),
                    Box::new(Expr::Number("1".to_string())),
                ))),
            ));
            let hit = evaluator.evaluate(&Expr::Variable("hit".to_string())).coeff;
            assert_eq!(hit == BigInt::from(1), expected);
        }
    }

    #[test]
    fn test_evaluator_compound_assignment_scale_and_scoping() {
        let stdout_buf = std::sync::Arc::new(std::sync::Mutex::new(Vec::new()));
        let stderr_buf = std::sync::Arc::new(std::sync::Mutex::new(Vec::new()));
        let stdout = TestWriter {
            buf: stdout_buf.clone(),
        };
        let stderr = TestWriter {
            buf: stderr_buf.clone(),
        };
        let mut evaluator = Evaluator::new(false, Box::new(stdout), Box::new(stderr));

        // 1. Compound assignment scale propagation
        evaluator.execute(&Stmt::Expr(Expr::AssignOp(
            AssignOp::Assign,
            Box::new(Expr::RegisterAccess(Register::Scale)),
            Box::new(Expr::Number("4".to_string())),
        )));

        evaluator.execute(&Stmt::Expr(Expr::AssignOp(
            AssignOp::Assign,
            Box::new(Expr::Variable("x".to_string())),
            Box::new(Expr::Number("5.5".to_string())),
        )));

        // x += 1.25 -> 6.75 (max scale = 2)
        evaluator.execute(&Stmt::Expr(Expr::AssignOp(
            AssignOp::Compound(BinOp::Add),
            Box::new(Expr::Variable("x".to_string())),
            Box::new(Expr::Number("1.25".to_string())),
        )));
        let x_add = evaluator.evaluate(&Expr::Variable("x".to_string()));
        assert_eq!(x_add.coeff, BigInt::from(675));
        assert_eq!(x_add.scale, 2);

        // x /= 2 -> 3.3750
        evaluator.execute(&Stmt::Expr(Expr::AssignOp(
            AssignOp::Compound(BinOp::Div),
            Box::new(Expr::Variable("x".to_string())),
            Box::new(Expr::Number("2".to_string())),
        )));
        let x_div = evaluator.evaluate(&Expr::Variable("x".to_string()));
        assert_eq!(x_div.coeff, BigInt::from(33750));
        assert_eq!(x_div.scale, 4);

        // 2. Dynamic Scope & Auto Variable Stack
        let f_def = FunctionDef {
            name: "test_fn".to_string(),
            params: vec![Param {
                name: "param1".to_string(),
                is_array: false,
            }],
            autos: vec![Param {
                name: "auto1".to_string(),
                is_array: false,
            }],
            body: vec![
                Stmt::Expr(Expr::AssignOp(
                    AssignOp::Assign,
                    Box::new(Expr::Variable("auto1".to_string())),
                    Box::new(Expr::Number("99".to_string())),
                )),
                Stmt::Return(Some(Expr::Variable("auto1".to_string()))),
            ],
        };
        evaluator.functions.insert("test_fn".to_string(), f_def);

        let call_res = evaluator.evaluate(&Expr::Call(
            "test_fn".to_string(),
            vec![ExprOrArray::Expr(Expr::Number("10".to_string()))],
        ));
        assert_eq!(call_res.coeff, BigInt::from(99));

        // After call, auto1 is restored to 0
        let auto1_after = evaluator.evaluate(&Expr::Variable("auto1".to_string()));
        assert_eq!(auto1_after.coeff, BigInt::from(0));
    }

    #[test]
    fn test_unary_op_scale_preservation_and_assign_registers() {
        let stdout_buf = std::sync::Arc::new(std::sync::Mutex::new(Vec::new()));
        let stderr_buf = std::sync::Arc::new(std::sync::Mutex::new(Vec::new()));
        let stdout = TestWriter {
            buf: stdout_buf.clone(),
        };
        let stderr = TestWriter {
            buf: stderr_buf.clone(),
        };
        let mut evaluator = Evaluator::new(false, Box::new(stdout), Box::new(stderr));

        // 1. Unary minus scale preservation
        let num_expr = Box::new(Expr::Number("5.25".to_string()));

        let uminus = evaluator.evaluate(&Expr::Negate(num_expr));
        assert_eq!(uminus.coeff, BigInt::from(-525));
        assert_eq!(uminus.scale, 2);

        // 2. Register assignments to ibase and obase
        evaluator.execute(&Stmt::Expr(Expr::AssignOp(
            AssignOp::Assign,
            Box::new(Expr::RegisterAccess(Register::Obase)),
            Box::new(Expr::Number("10".to_string())),
        )));
        assert_eq!(evaluator.obase, 10);

        evaluator.execute(&Stmt::Expr(Expr::AssignOp(
            AssignOp::Assign,
            Box::new(Expr::RegisterAccess(Register::Ibase)),
            Box::new(Expr::Number("16".to_string())),
        )));
        assert_eq!(evaluator.ibase, 16);
        assert!(stderr_buf.lock().unwrap().is_empty());

        evaluator.execute(&Stmt::Expr(Expr::AssignOp(
            AssignOp::Assign,
            Box::new(Expr::RegisterAccess(Register::Ibase)),
            Box::new(Expr::Number("2".to_string())),
        )));
        assert_eq!(evaluator.ibase, 2);
        assert!(stderr_buf.lock().unwrap().is_empty());

        // UpdateOp on ibase and obase registers
        evaluator.ibase = 10;
        let ibase_inc = evaluator.evaluate(&Expr::Update(
            true,
            true,
            Box::new(Expr::RegisterAccess(Register::Ibase)),
        ));
        assert_eq!(ibase_inc.coeff, BigInt::from(11));
        assert_eq!(evaluator.ibase, 11);

        evaluator.obase = 10;
        let obase_inc = evaluator.evaluate(&Expr::Update(
            true,
            true,
            Box::new(Expr::RegisterAccess(Register::Obase)),
        ));
        assert_eq!(obase_inc.coeff, BigInt::from(11));
        assert_eq!(evaluator.obase, 11);

        // 3. WrappedStdout flush & 70-char wrapping
        stdout_buf.lock().unwrap().clear();
        let mut wrapped = WrappedStdout::new(Box::new(TestWriter {
            buf: stdout_buf.clone(),
        }));
        assert!(wrapped.write_str(&"1".repeat(70)).is_ok());
        assert!(wrapped.write_str("\n").is_ok());
        assert!(wrapped.flush().is_ok());
        let wrapped_out = String::from_utf8(stdout_buf.lock().unwrap().clone()).unwrap();
        assert_eq!(wrapped_out, format!("{}\\\n11\n", "1".repeat(68)));
    }

    #[test]
    fn test_relational_op_scale_normalization_and_register_scopes() {
        let stdout_buf = std::sync::Arc::new(std::sync::Mutex::new(Vec::new()));
        let stderr_buf = std::sync::Arc::new(std::sync::Mutex::new(Vec::new()));
        let stdout = TestWriter {
            buf: stdout_buf.clone(),
        };
        let stderr = TestWriter {
            buf: stderr_buf.clone(),
        };
        let mut evaluator = Evaluator::new(false, Box::new(stdout), Box::new(stderr));

        // 1. Relational Ops with scale_left < scale_right (diff < 0)
        let expr_eq_lt = Expr::RelationalOp(
            RelOp::Eq,
            Box::new(Expr::Number("1.5".to_string())), // scale 1
            Box::new(Expr::Number("1.500".to_string())), // scale 3
        );
        assert_eq!(evaluator.evaluate(&expr_eq_lt).coeff, BigInt::from(1));

        let expr_lt = Expr::RelationalOp(
            RelOp::Lt,
            Box::new(Expr::Number("1.5".to_string())), // scale 1
            Box::new(Expr::Number("1.501".to_string())), // scale 3
        );
        assert_eq!(evaluator.evaluate(&expr_lt).coeff, BigInt::from(1));

        let expr_gt = Expr::RelationalOp(
            RelOp::Gt,
            Box::new(Expr::Number("1.5".to_string())), // scale 1
            Box::new(Expr::Number("1.499".to_string())), // scale 3
        );
        assert_eq!(evaluator.evaluate(&expr_gt).coeff, BigInt::from(1));

        // 2. Relational Ops with scale_left > scale_right (diff > 0)
        let expr_eq_gt = Expr::RelationalOp(
            RelOp::Eq,
            Box::new(Expr::Number("1.500".to_string())), // scale 3
            Box::new(Expr::Number("1.5".to_string())),   // scale 1
        );
        assert_eq!(evaluator.evaluate(&expr_eq_gt).coeff, BigInt::from(1));

        // 3. Register access for scale
        evaluator.execute(&Stmt::Expr(Expr::AssignOp(
            AssignOp::Assign,
            Box::new(Expr::RegisterAccess(Register::Scale)),
            Box::new(Expr::Number("4".to_string())),
        )));
        assert_eq!(evaluator.scale, 4);

        let scale_res = evaluator.evaluate(&Expr::RegisterAccess(Register::Scale));
        assert_eq!(scale_res.coeff, BigInt::from(4));
    }

    #[test]
    fn test_hex_base_assignment_obase_clamping_and_fractional_index() {
        let stdout_buf = std::sync::Arc::new(std::sync::Mutex::new(Vec::new()));
        let stderr_buf = std::sync::Arc::new(std::sync::Mutex::new(Vec::new()));
        let stdout = TestWriter {
            buf: stdout_buf.clone(),
        };
        let stderr = TestWriter {
            buf: stderr_buf.clone(),
        };
        let mut evaluator = Evaluator::new(false, Box::new(stdout), Box::new(stderr));

        // 1. Single character hex base assignment (ibase = A -> 10, ibase = F -> 15)
        evaluator.execute(&Stmt::Expr(Expr::AssignOp(
            AssignOp::Assign,
            Box::new(Expr::RegisterAccess(Register::Ibase)),
            Box::new(Expr::Number("A".to_string())),
        )));
        assert_eq!(evaluator.ibase, 10);

        evaluator.execute(&Stmt::Expr(Expr::AssignOp(
            AssignOp::Assign,
            Box::new(Expr::RegisterAccess(Register::Ibase)),
            Box::new(Expr::Number("F".to_string())),
        )));
        assert_eq!(evaluator.ibase, 15);

        // Reset ibase back to 10
        evaluator.ibase = 10;

        // 2. obase min clamping (obase < 2 -> 2)
        evaluator.execute(&Stmt::Expr(Expr::AssignOp(
            AssignOp::Assign,
            Box::new(Expr::RegisterAccess(Register::Obase)),
            Box::new(Expr::Number("0".to_string())),
        )));
        assert_eq!(evaluator.obase, 2);

        // 3. Fractional array index truncation (a[2.7] = 42 -> a[2] == 42)
        evaluator.execute(&Stmt::Expr(Expr::AssignOp(
            AssignOp::Assign,
            Box::new(Expr::ArrayAccess(
                "a".to_string(),
                Box::new(Expr::Number("2.7".to_string())),
            )),
            Box::new(Expr::Number("42".to_string())),
        )));

        let arr_val = evaluator.evaluate(&Expr::ArrayAccess(
            "a".to_string(),
            Box::new(Expr::Number("2".to_string())),
        ));
        assert_eq!(arr_val.coeff, BigInt::from(42));

        // Fractional array index truncation in UpdateOp (++b[2.7] -> b[2] == 1)
        evaluator.evaluate(&Expr::Update(
            true,
            true,
            Box::new(Expr::ArrayAccess(
                "b".to_string(),
                Box::new(Expr::Number("2.7".to_string())),
            )),
        ));
        let arr_val_b = evaluator.evaluate(&Expr::ArrayAccess(
            "b".to_string(),
            Box::new(Expr::Number("2".to_string())),
        ));
        assert_eq!(arr_val_b.coeff, BigInt::from(1));

        // 4. Block execution break on quit_flag
        evaluator.execute(&Stmt::Block(vec![
            Stmt::Quit,
            Stmt::Expr(Expr::AssignOp(
                AssignOp::Assign,
                Box::new(Expr::Variable("stopped".to_string())),
                Box::new(Expr::Number("1".to_string())),
            )),
        ]));
        let stopped_var = evaluator.evaluate(&Expr::Variable("stopped".to_string()));
        assert_eq!(stopped_var.coeff, BigInt::from(0));
    }

    #[test]
    fn test_return_inside_while_and_for_loops() {
        let mut evaluator = Evaluator::new(false, Box::new(String::new()), Box::new(String::new()));
        let mut parser_while = Parser::new(Lexer::new(
            "define f_while() { i = 0; while (i < 10) { i = i + 1; return (i); }; return (999); }; f_while()",
        ));
        for stmt in parser_while.parse_program() {
            evaluator.execute(&stmt);
        }
        let res_while = evaluator.evaluate(&Expr::Variable("i".to_string()));
        assert_eq!(res_while.coeff, BigInt::from(1));

        let mut evaluator_for =
            Evaluator::new(false, Box::new(String::new()), Box::new(String::new()));
        let mut parser_for = Parser::new(Lexer::new(
            "define f_for() { for (i = 0; i < 10; i = i + 1) { return (i + 1); }; return (999); }; f_for()",
        ));
        for stmt in parser_for.parse_program() {
            evaluator_for.execute(&stmt);
        }
        let res_for = evaluator_for.evaluate(&Expr::Variable("i".to_string()));
        assert_eq!(res_for.coeff, BigInt::from(0));
    }

    struct FailingFlushWriter;
    impl FmtWrite for FailingFlushWriter {
        fn write_str(&mut self, _s: &str) -> core::fmt::Result {
            Ok(())
        }
    }
    impl BcWriter for FailingFlushWriter {
        fn flush(&mut self) -> core::fmt::Result {
            Err(core::fmt::Error)
        }
    }

    #[test]
    fn test_wrapped_stdout_flush_error_propagation() {
        let mut stdout = WrappedStdout::new(Box::new(FailingFlushWriter));
        assert!(stdout.flush().is_err());
    }

    #[test]
    fn test_function_early_return_short_circuits_body_loop() {
        let mut evaluator = Evaluator::new(false, Box::new(String::new()), Box::new(String::new()));
        let mut parser = Parser::new(Lexer::new(
            "define f() { return (10); x = 99; return (20); }; f()",
        ));
        for stmt in parser.parse_program() {
            evaluator.execute(&stmt);
        }
        let res = evaluator.evaluate(&Expr::Call("f".to_string(), vec![]));
        assert_eq!(res.coeff, BigInt::from(10));
        let x_var = evaluator.evaluate(&Expr::Variable("x".to_string()));
        assert_eq!(x_var.coeff, BigInt::from(0));
    }

    #[test]
    fn test_execute_entry_and_block_guard_when_flags_set() {
        let mut evaluator = Evaluator::new(false, Box::new(String::new()), Box::new(String::new()));
        evaluator.break_flag = true;
        evaluator.execute(&Stmt::Expr(Expr::AssignOp(
            AssignOp::Assign,
            Box::new(Expr::Variable("mut_var".to_string())),
            Box::new(Expr::Number("99".to_string())),
        )));
        let val1 = evaluator.evaluate(&Expr::Variable("mut_var".to_string()));
        assert_eq!(val1.coeff, BigInt::from(0));

        evaluator.break_flag = false;
        evaluator.return_flag = true;
        evaluator.execute(&Stmt::Expr(Expr::AssignOp(
            AssignOp::Assign,
            Box::new(Expr::Variable("mut_var2".to_string())),
            Box::new(Expr::Number("99".to_string())),
        )));
        let val2 = evaluator.evaluate(&Expr::Variable("mut_var2".to_string()));
        assert_eq!(val2.coeff, BigInt::from(0));

        // Block loop short-circuit when statement inside block sets return_flag or break_flag (kills line 530 mutants)
        let mut evaluator2 =
            Evaluator::new(false, Box::new(String::new()), Box::new(String::new()));
        let stmt_ret = Stmt::Return(Some(Expr::Number("10".to_string())));
        let stmt_assign1 = Stmt::Expr(Expr::AssignOp(
            AssignOp::Assign,
            Box::new(Expr::Variable("block_var1".to_string())),
            Box::new(Expr::Number("99".to_string())),
        ));
        let block_ret = Stmt::Block(vec![stmt_ret, stmt_assign1]);
        evaluator2.execute(&block_ret);
        let val3 = evaluator2.evaluate(&Expr::Variable("block_var1".to_string()));
        assert_eq!(val3.coeff, BigInt::from(0));

        let mut evaluator3 =
            Evaluator::new(false, Box::new(String::new()), Box::new(String::new()));
        let stmt_break = Stmt::Break;
        let stmt_assign2 = Stmt::Expr(Expr::AssignOp(
            AssignOp::Assign,
            Box::new(Expr::Variable("block_var2".to_string())),
            Box::new(Expr::Number("99".to_string())),
        ));
        let block_break = Stmt::Block(vec![stmt_break, stmt_assign2]);
        evaluator3.execute(&block_break);
        let val4 = evaluator3.evaluate(&Expr::Variable("block_var2".to_string()));
        assert_eq!(val4.coeff, BigInt::from(0));
    }

    #[test]
    fn test_names_first_seen_as_parameters_or_autos_stay_usable() {
        let out = std::sync::Arc::new(std::sync::Mutex::new(Vec::new()));
        let mut ev = Evaluator::new(
            false,
            Box::new(TestWriter { buf: out.clone() }),
            Box::new(String::new()),
        );
        let src = "define f(p, q[]) {\nauto r, s[]\nr = p; s[0] = q[0]\nreturn (r + s[0])\n}\n\
                   t[0] = 2; f(1, t[])\n\
                   p = 5; q[0] = 6; r++; s[1] = 7; p; q[0]; r; s[1]\n";
        let summary = ev.run_source(src, "test");
        assert_eq!(summary.errors, 0);
        let out = String::from_utf8(out.lock().unwrap().clone()).unwrap();
        assert_eq!(out, "3\n0\n5\n6\n1\n7\n");
    }

    #[test]
    fn test_fallible_evaluator_and_scope_restoration() {
        let mut ev = Evaluator::new(true, Box::new(String::new()), Box::new(String::new()));

        let mut p_setup = Parser::try_new(Lexer::new(
            "x = 42; a[0] = 7\ndefine bad(x, a[]) {\n  auto y, b[]\n  x = 99\n  y = 1 / 0\n  return (y)\n}\n",
        ))
        .unwrap();
        for stmt in p_setup.try_parse_program().unwrap() {
            assert!(ev.try_execute(&stmt).is_ok());
        }

        // Calling bad(10, a[]) must fail with "Divide by zero" inside bad() AND leave_call must restore x = 42
        let mut p_call = Parser::try_new(Lexer::new("bad(10, a[])\n")).unwrap();
        let call_stmts = p_call.try_parse_program().unwrap();
        assert_eq!(
            ev.try_execute(&call_stmts[0]),
            Err(BcError::Runtime {
                kind: RuntimeError::DivideByZero,
                func: Some("bad".to_string())
            })
        );
        let x_after = ev.try_evaluate(&Expr::Variable("x".to_string())).unwrap();
        assert_eq!(x_after.coeff, BigInt::from(42));

        // Argument errors and undefined function
        let mut p_mismatch = Parser::try_new(Lexer::new("bad(10)\n")).unwrap();
        let stmts_mismatch = p_mismatch.try_parse_program().unwrap();
        assert_eq!(
            ev.try_execute(&stmts_mismatch[0]),
            Err(BcError::Runtime {
                kind: RuntimeError::ParameterMismatch,
                func: None
            })
        );

        let mut p_arr_err = Parser::try_new(Lexer::new("bad(10, 20)\n")).unwrap();
        let stmts_arr_err = p_arr_err.try_parse_program().unwrap();
        assert_eq!(
            ev.try_execute(&stmts_arr_err[0]),
            Err(BcError::Runtime {
                kind: RuntimeError::ParameterTypeMismatch("a".to_string()),
                func: None
            })
        );

        let mut p_scalar_err = Parser::try_new(Lexer::new("bad(a[], a[])\n")).unwrap();
        let stmts_scalar_err = p_scalar_err.try_parse_program().unwrap();
        assert_eq!(
            ev.try_execute(&stmts_scalar_err[0]),
            Err(BcError::Runtime {
                kind: RuntimeError::ParameterTypeMismatch("x".to_string()),
                func: None
            })
        );

        let mut p_undef = Parser::try_new(Lexer::new("nonexistent(1)\n")).unwrap();
        let stmts_undef = p_undef.try_parse_program().unwrap();
        assert_eq!(
            ev.try_execute(&stmts_undef[0]),
            Err(BcError::Runtime {
                kind: RuntimeError::UndefinedFunction("nonexistent".to_string()),
                func: None
            })
        );

        let mut p_sqrt = Parser::try_new(Lexer::new("sqrt(-1)\n")).unwrap();
        let stmts_sqrt = p_sqrt.try_parse_program().unwrap();
        assert_eq!(
            ev.try_execute(&stmts_sqrt[0]),
            Err(BcError::Runtime {
                kind: RuntimeError::NegativeSqrt,
                func: None
            })
        );

        // Verify binary operators (-, %, ^) and math library functions (s, c, a, l, e, j) via try_evaluate
        ev.scale = 4;
        let eval_expr = |ev: &mut Evaluator, src: &str| -> BCNum {
            let mut p = Parser::try_new(Lexer::new(src)).unwrap();
            let stmts = p.try_parse_program().unwrap();
            let inner = match &stmts[0] {
                Stmt::Block(b) => &b[0],
                other => other,
            };
            if let Stmt::Expr(e) = inner {
                ev.try_evaluate(e).unwrap()
            } else {
                panic!("expected Stmt::Expr");
            }
        };
        assert_eq!(eval_expr(&mut ev, "10 - 3\n").coeff, BigInt::from(7));
        assert_eq!(eval_expr(&mut ev, "10 % 3\n").coeff, BigInt::from(1));
        assert_eq!(eval_expr(&mut ev, "2 ^ 3\n").coeff, BigInt::from(8));
        assert!(eval_expr(&mut ev, "s(1)\n").coeff > BigInt::from(0));
        assert_eq!(eval_expr(&mut ev, "c(0)\n").coeff, BigInt::from(10000));
        assert!(eval_expr(&mut ev, "a(1)\n").coeff > BigInt::from(0));
        assert!(eval_expr(&mut ev, "l(2)\n").coeff > BigInt::from(0));
        assert_eq!(eval_expr(&mut ev, "e(0)\n").coeff, BigInt::from(10000));
        assert_eq!(eval_expr(&mut ev, "j(0, 0)\n").coeff, BigInt::from(10000));
    }
}
