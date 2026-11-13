// SPDX-License-Identifier: MIT

//! The evaluator: its state, the dynamic scopes of variables and arrays, and the output
//! streams (`WrappedStdout`, `ErrWriter`).
//!
//! This module holds the state, its invariant (`Evaluator::inv`), the relation to the
//! specification's state (`r_state`) and the verified storage layer (`var_get`, …, `arr_pop`).
//! Execution is split into:
//! - `machine`: expressions, statements and calls on an explicit stack of frames, with the
//!   fast path for shallow call-free forms in `machine/quick.rs`;
//! - `leaf`: the forms that the machine does not split into frames;
//! - `ops`: the operations the frames apply to values (arithmetic, constants, registers,
//!   assignment targets);
//! - `call`: entering and leaving a function's scope;
//! - `unit`: the statements of a unit and runtime diagnostics.

use alloc::boxed::Box;
use alloc::collections::BTreeMap;
use alloc::rc::Rc;
use alloc::string::String;
use alloc::vec;
use alloc::vec::Vec;
use core::cmp::Ordering;

#[cfg(verus_keep_ghost)]
use crate::bigint::{axiom_bigint_size, big_view};
use crate::bigint::{
    big_abs, big_cmp, big_from_usize, big_is_negative, big_neg, big_tdiv, big_to_u64_small,
};
use crate::error::{BcError, RuntimeError};
use crate::format::push_dec;
use crate::math::pow10_within;
use crate::math::{BCNum, literal_digit_values};
use crate::mathlib::{bc_atan, bc_bessel, bc_cos, bc_exp, bc_ln, bc_sin};
#[cfg(verus_keep_ghost)]
use crate::mathlib::{lemma_math_ok, math_ok};
use crate::parser::{
    Arg as PArg, AssignOp, BinOp, Code, DEFAULT_MAX_DEPTH, ExtensionPolicy, FunctionDef,
    Node as PNode, Param, Register, RelOp, share_code,
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
    ER, EState, Func, er_ok, ev, ev_node, ev_unary, exec, exec_node, is_assignment, negate,
    num_u64, reg_get, with_depth,
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

mod call;
mod leaf;
mod machine;
mod ops;
#[cfg(test)]
mod tests;
mod trusted_io;
mod unit;

pub use trusted_io::{BcWriter, ErrWriter, WrappedStdout};
#[cfg(verus_keep_ghost)]
pub use trusted_io::{err_log, out_col, out_log};

verus! {

/// Evaluator maintaining registers, scoped variables, functions, and state.
pub struct Evaluator {
    // The state is private, so that `Evaluator::inv` holds for every evaluator a front end can
    // reach (see `inv`); front ends use the methods below.
    pub(crate) variables: BTreeMap<String, Vec<BCNum>>,
    pub(crate) arrays: BTreeMap<String, Vec<BTreeMap<usize, BCNum>>>,
    pub(crate) functions: BTreeMap<String, FunctionDef>,
    pub(crate) scale: usize,
    pub(crate) ibase: usize,
    pub(crate) obase: usize,
    pub(crate) math_enabled: bool,
    pub(crate) stdout_writer: WrappedStdout,
    pub(crate) stderr_writer: ErrWriter,

    pub(crate) break_flag: bool,
    pub(crate) return_flag: bool,
    pub(crate) return_value: BCNum,
    pub(crate) quit_flag: bool,
    /// How non-POSIX syntax is treated (`-s` / `-w`); applied by the input-unit driver.
    pub extension_policy: ExtensionPolicy,

    /// Names of the user functions currently executing, innermost last (for diagnostics).
    pub(crate) call_stack: Vec<String>,

    /// Nesting limit of the syntax: the syntax tree of an input unit is at most this deep. It
    /// bounds the native stack that parsing uses (`docs/COMPATIBILITY.md` §2), so a front end
    /// sets it for the stack it runs on. It does not limit evaluation; `max_eval_depth` does.
    pub max_depth: usize,
    /// How many levels evaluation may nest, function calls included (`docs/COMPATIBILITY.md`
    /// §2). Evaluation runs on the heap, so this bounds the memory of deep recursion.
    pub max_eval_depth: usize,
    /// Expressions and statements currently being evaluated.
    pub(crate) eval_depth: usize,
    /// `ibase` when the innermost executing function was invoked (`None` at top level). POSIX:
    /// numeric constants within a function are interpreted in this base.
    pub(crate) invocation_ibase: Option<usize>,
}

/// An assignment target whose array subscript has already been evaluated.
pub(crate) enum Place {
    Variable(String),
    Element(String, usize),
    Register(Register),
}

/// An evaluated call argument, before any frame is pushed: a copy of an array's current
/// frame, or a value.
pub(crate) enum ArgValue {
    Array(BTreeMap<usize, BCNum>),
    Scalar(BCNum),
}

/// Evaluated arguments keep the scale invariant.
pub(crate) open spec fn args_ok(vals: Seq<(String, ArgValue)>) -> bool {
    forall|i: int| 0 <= i < vals.len() ==> match (#[trigger] vals[i]).1 {
        ArgValue::Array(f) => frame_ok(f@),
        ArgValue::Scalar(v) => v.scale <= BC_SCALE_MAX,
    }
}

/// An evaluated argument (with its parameter's name) corresponds to the specification's.
pub(crate) open spec fn r_argval(p: (String, ArgValue), s: bc_spec::eval::ArgVal) -> bool {
    &&& s.name == text_view(p.0)
    &&& match p.1 {
        ArgValue::Array(f) => s.is_array && r_frame(f@, s.frame),
        ArgValue::Scalar(v) => !s.is_array && r_num(v, s.val),
    }
}

pub(crate) open spec fn r_argvals(ps: Seq<(String, ArgValue)>, ss: Seq<bc_spec::eval::ArgVal>) -> bool {
    ps.len() == ss.len() && forall|i: int| 0 <= i < ps.len() ==> #[trigger] r_argval(ps[i], ss[i])
}

/// The result of evaluating the arguments corresponds to the specification's `ev_args`.
pub(crate) open spec fn r_args_result(r: Result<Vec<(String, ArgValue)>, BcError>, e: Evaluator, a: bc_spec::eval::ArgsR, d: usize) -> bool {
    match r {
        Ok(v) => a.r.ok && r_argvals(v@, a.vals) && r_state(e, a.r.st),
        Err(err) => !a.r.ok && r_err(err, a.r.err) && r_state(e, with_depth(a.r.st, d as u64)),
    }
}

/// The output streams as written so far.
pub(crate) open spec fn r_output(out: WrappedStdout, err: ErrWriter, st: EState) -> bool {
    out_log(&out) == st.out.s && out_col(&out) == st.col && err_log(&err) == st.err.s
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
    &&& r_calls(e.call_stack@, st.calls.s)
    &&& e.eval_depth == st.depth && e.max_eval_depth == st.max_depth
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

impl Evaluator {
    /// The evaluator's invariant (`docs/COMPATIBILITY.md` §2): registers in range, and every
    /// stored number with a scale of at most `BC_SCALE_MAX`.
    ///
    /// It holds for every `Evaluator` outside this crate, which establishes the precondition of
    /// `try_evaluate`, `try_execute` and `run_unit_ref` for their unverified callers (the front
    /// ends, and the glue `run_unit`): `new` establishes it (`with_streams`); every public
    /// method that changes a field it reads is verified to keep it (`set_scale`, `try_*`, …);
    /// and those fields are `pub(crate)` and written only by verified code. The public fields
    /// `max_depth`, `max_eval_depth` and `extension_policy` are not part of it.
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
#[cfg(verus_keep_ghost)]
pub(crate) type SpecParams = Seq<bc_spec::parser::Param>;
#[cfg(not(verus_keep_ghost))]
pub(crate) type SpecParams = ();
#[cfg(verus_keep_ghost)]
pub(crate) type SpecArgVals = Seq<bc_spec::eval::ArgVal>;
#[cfg(not(verus_keep_ghost))]
pub(crate) type SpecArgVals = ();
#[cfg(verus_keep_ghost)]
pub(crate) type SpecFunc = Func;
#[cfg(not(verus_keep_ghost))]
pub(crate) type SpecFunc = ();
#[cfg(verus_keep_ghost)]
pub(crate) type SpecSaved = bc_spec::eval::Saved;
#[cfg(not(verus_keep_ghost))]
pub(crate) type SpecSaved = ();
#[cfg(verus_keep_ghost)]
pub(crate) type SpecFrame = bc_spec::eval::ArrFrame;
#[cfg(not(verus_keep_ghost))]
pub(crate) type SpecFrame = ();
#[cfg(verus_keep_ghost)]
pub(crate) type SpecIndices = Seq<usize>;
#[cfg(not(verus_keep_ghost))]
pub(crate) type SpecIndices = ();

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

/// `e1` and `e2` agree on every field except their variables, arrays, diagnostic stream and
/// evaluation depth: the part that `same_but_storage`, `same_but_err` and `same_but_depth`
/// share. A new field of `Evaluator` goes here, or in each of those three that keeps it.
pub(crate) open spec fn same_fixed(e1: Evaluator, e2: Evaluator) -> bool {
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
    &&& e1.max_eval_depth == e2.max_eval_depth
    &&& e1.invocation_ibase == e2.invocation_ibase
}

/// `e1` and `e2` differ at most in their variables and arrays.
pub(crate) open spec fn same_but_storage(e1: Evaluator, e2: Evaluator) -> bool {
    &&& same_fixed(e1, e2)
    &&& e1.stderr_writer == e2.stderr_writer
    &&& e1.eval_depth == e2.eval_depth
}

/// `e1` and `e2` differ at most in their diagnostic stream.
pub(crate) open spec fn same_but_err(e1: Evaluator, e2: Evaluator) -> bool {
    &&& same_fixed(e1, e2)
    &&& e1.variables == e2.variables
    &&& e1.arrays == e2.arrays
    &&& e1.eval_depth == e2.eval_depth
}

/// `e1` and `e2` differ at most in their evaluation depth.
pub(crate) open spec fn same_but_depth(e1: Evaluator, e2: Evaluator) -> bool {
    &&& same_fixed(e1, e2)
    &&& e1.variables == e2.variables
    &&& e1.arrays == e2.arrays
    &&& e1.stderr_writer == e2.stderr_writer
}

/// A resolved target corresponds to the specification's `Place`.
pub(crate) open spec fn r_place(p: Place, sp: bc_spec::eval::Place) -> bool {
    match p {
        Place::Variable(n) => sp.kind == 0 && sp.name == text_view(n),
        Place::Element(n, i) => sp.kind == 1 && sp.name == text_view(n) && sp.idx as int == i as int && i < 16777216,
        Place::Register(r) => sp.kind == 2 && sp.reg == reg_code(r),
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

/// The invariant does not depend on the output streams, the control-flow flags, the depth or
/// the call stack, and holds without an invocation `ibase`.
pub(crate) proof fn lemma_inv_frame(e1: Evaluator, e2: Evaluator)
    requires
        e1.inv(),
        e2.variables == e1.variables,
        e2.arrays == e1.arrays,
        e2.scale == e1.scale,
        e2.ibase == e1.ibase,
        e2.obase == e1.obase,
        e2.return_value == e1.return_value,
        e2.invocation_ibase is None || e2.invocation_ibase == e1.invocation_ibase,
    ensures
        e2.inv(),
{
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
    /// The initial state with the given streams and nesting limit (`new`).
    pub(crate) fn with_streams(math_enabled: bool, stdout_writer: WrappedStdout, stderr_writer: ErrWriter, max_depth: usize) -> (r: Self)
        ensures
            r.inv(),
            r.math_enabled == math_enabled,
            r.max_depth == max_depth,
            r.max_eval_depth == max_depth,
            r.extension_policy == ExtensionPolicy::Allow,
            (!math_enabled && out_log(&stdout_writer) == Seq::<u8>::empty() && out_col(&stdout_writer) == 0
                && err_log(&stderr_writer) == Seq::<u8>::empty())
                ==> crate::driver::r_top(r, bc_spec::top::initial(max_depth as u64)),
    {
        let r = Self {
            variables: BTreeMap::new(),
            arrays: BTreeMap::new(),
            functions: BTreeMap::new(),
            scale: 0,
            ibase: 10,
            obase: 10,
            math_enabled,
            stdout_writer,
            stderr_writer,
            break_flag: false,
            return_flag: false,
            return_value: BCNum::zero(),
            quit_flag: false,
            extension_policy: ExtensionPolicy::Allow,
            call_stack: Vec::new(),
            max_depth,
            max_eval_depth: max_depth,
            eval_depth: 0,
            invocation_ibase: None,
        };
        proof {
            assert(r.variables@ =~= Map::<String, Vec<BCNum>>::empty());
            assert(r.arrays@ =~= Map::<String, Vec<BTreeMap<usize, BCNum>>>::empty());
            assert(r.functions@ =~= Map::<String, FunctionDef>::empty());
            assert(r.call_stack@ =~= Seq::<String>::empty());
        }
        r
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
    pub fn set_scale(&mut self, scale: usize)
        ensures
            old(self).inv() ==> final(self).inv(),
    {
        self.scale = verified_clamp_register(scale, false, 0, BC_SCALE_MAX).0;
    }

    /// Stops processing after the current unit, as `quit` does.
    pub fn request_quit(&mut self)
        ensures
            old(self).inv() ==> final(self).inv(),
    {
        self.quit_flag = true;
    }

    /// Clears a `quit` request, so that a front end that keeps running (a REPL) can go on.
    pub fn clear_quit(&mut self)
        ensures
            old(self).inv() ==> final(self).inv(),
    {
        self.quit_flag = false;
    }

    /// Clears the `break` and `return` flags, e.g. after a unit was abandoned by a panic.
    pub fn reset_control_flags(&mut self)
        ensures
            old(self).inv() ==> final(self).inv(),
    {
        self.break_flag = false;
        self.return_flag = false;
    }

    /// Evaluates an AST expression node, returning Err on runtime math/call errors.
    pub fn try_evaluate(&mut self, code: &Rc<Code>, node: usize) -> (r: Result<BCNum, BcError>)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            r is Ok ==> r->Ok_0.scale <= BC_SCALE_MAX,
    {
        self.eval_ref(code, node, Ghost(arbitrary()), Ghost(arbitrary()))
    }

    /// Executes an AST statement node, returning Err on runtime errors.
    pub fn try_execute(&mut self, code: &Rc<Code>, node: usize) -> (r: Result<(), BcError>)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
    {
        self.exec_ref(code, node, Ghost(arbitrary()), Ghost(arbitrary()))
    }
}

} // verus!

impl Evaluator {
    /// Creates a new Evaluator with abstract BcWriter streams.
    pub fn new(
        math_enabled: bool,
        stdout_writer: Box<dyn BcWriter>,
        stderr_writer: Box<dyn BcWriter>,
    ) -> Self {
        // The streams and the nesting limit are outside `inv`; `with_streams` establishes it.
        Self::with_streams(
            math_enabled,
            WrappedStdout::new(stdout_writer),
            ErrWriter::new(stderr_writer),
            DEFAULT_MAX_DEPTH,
        )
    }

    /// The diagnostic stream, for a front end's own messages (e.g. a file that cannot be read).
    pub fn stderr_writer(&mut self) -> &mut ErrWriter {
        &mut self.stderr_writer
    }
}
