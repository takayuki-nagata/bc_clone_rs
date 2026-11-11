// SPDX-License-Identifier: MIT

//! Shared representations for the compiled specification.
//!
//! `exec_spec_verified!` passes arguments by reference and returns owned values, so building a
//! struct copies each of its fields (`deep_clone`). A field that holds a `Seq` is copied in
//! full at every step that returns a state, which makes the oracle quadratic in the size of the
//! state. The types here are spec types with an `ExecSpecType` of their own: the compiled code
//! shares their contents through `Rc`, so copying one is constant time. Their operations are
//! `open spec fn`s whose compiled `exec_*` versions are written here by hand and verified with
//! the contract that `exec_spec_verified!` expects (`res.deep_view() =~~= f(args.deep_view())`).
//! The specification uses these types only through those operations.

use crate::eval::*;
use crate::num::*;
use std::rc::Rc;
use vstd::contrib::exec_spec::*;
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------------------------
// Persistent stacks
// ---------------------------------------------------------------------------------------------

/// One cell of a persistent stack: its top value and the cells below it.
#[derive(Eq, Hash, PartialEq)]
pub struct PNode<T> {
    pub val: T,
    pub next: Option<Rc<PNode<T>>>,
}

/// The values of the cells from the bottom up (the last one is `n`'s value).
pub open spec fn pnodes_view<T: DeepView>(n: Option<Rc<PNode<T>>>) -> Seq<T::V>
    decreases n,
{
    match n {
        None => Seq::empty(),
        Some(r) => pnodes_view(r.next).push(r.val.deep_view()),
    }
}

fn pnodes_to_vec<T: DeepViewClone>(n: &Option<Rc<PNode<T>>>) -> (res: Vec<T>)
    ensures
        res.deep_view() =~= pnodes_view(*n),
    decreases *n,
{
    match n {
        None => Vec::new(),
        Some(r) => {
            let mut v = pnodes_to_vec(&r.next);
            let ghost before = v.deep_view();
            v.push(r.val.deep_clone());
            assert(v.deep_view() =~= before.push(r.val.deep_view()));
            v
        },
    }
}

fn pnodes_clone<T>(n: &Option<Rc<PNode<T>>>) -> (res: Option<Rc<PNode<T>>>)
    ensures
        res == *n,
{
    match n {
        None => None,
        Some(r) => Some(Rc::clone(r)),
    }
}

} // verus!

/// Defines a stack type `$spec { s: Seq<$elem> }` (innermost value last), compiled to a
/// persistent stack of `$xelem` (whose reference type is `$xref`), with its operations: `$empty`, `$has` (not empty), `$top`
/// (the innermost value, `$dflt` / `$xdflt` if there is none), `$push` and `$pop` (which keeps
/// an empty stack), and their compiled versions.
macro_rules! persistent_stack {
    ($spec:ident, $exec:ident, $elem:ty, $xelem:ty, $xref:ty, $dflt:expr, $xdflt:expr,
     $empty:ident, $has:ident, $top:ident, $push:ident, $pop:ident,
     $xempty:ident, $xhas:ident, $xtop:ident, $xpush:ident, $xpop:ident) => {
        verus! {

        pub struct $spec {
            pub s: Seq<$elem>,
        }

        /// The compiled stack. The derived traits are those of the structs that
        /// `exec_spec_verified!` generates; the compiled code compares with `exec_eq`.
        #[derive(Eq, Hash, PartialEq)]
        pub struct $exec {
            pub top: Option<Rc<PNode<$xelem>>>,
        }

        impl DeepView for $exec {
            type V = $spec;

            open spec fn deep_view(&self) -> $spec {
                $spec { s: pnodes_view(self.top) }
            }
        }

        impl DeepViewClone for $exec {
            fn deep_clone(&self) -> (res: Self) {
                $exec { top: pnodes_clone(&self.top) }
            }
        }

        impl ExecSpecType for $spec {
            type ExecOwnedType = $exec;
            type ExecRefType<'a> = &'a $exec;
        }

        impl<'a> ToRef<&'a $exec> for &'a $exec {
            fn get_ref(self) -> (res: &'a $exec) {
                self
            }
        }

        impl<'a> ToOwned<$exec> for &'a $exec {
            fn get_owned(self) -> (res: $exec) {
                self.deep_clone()
            }
        }

        impl<'a> ExecSpecEq<'a> for &'a $exec {
            type Other = &'a $exec;

            fn exec_eq(this: Self, other: Self::Other) -> (res: bool) {
                let a = pnodes_to_vec(&this.top);
                let b = pnodes_to_vec(&other.top);
                <&[$xelem]>::exec_eq(a.as_slice(), b.as_slice())
            }
        }

        pub open spec fn $empty() -> $spec {
            $spec { s: Seq::empty() }
        }

        pub open spec fn $has(s: $spec) -> bool {
            s.s.len() > 0
        }

        pub open spec fn $top(s: $spec) -> $elem {
            if s.s.len() > 0 { s.s.last() } else { $dflt }
        }

        pub open spec fn $push(s: $spec, v: $elem) -> $spec {
            $spec { s: s.s.push(v) }
        }

        pub open spec fn $pop(s: $spec) -> $spec {
            if s.s.len() > 0 { $spec { s: s.s.drop_last() } } else { s }
        }

        pub fn $xempty() -> (res: $exec)
            ensures
                res.deep_view() =~~= $empty(),
        {
            $exec { top: None }
        }

        pub fn $xhas(s: &$exec) -> (res: bool)
            ensures
                res == $has(s.deep_view()),
        {
            s.top.is_some()
        }

        pub fn $xtop(s: &$exec) -> (res: $xelem)
            ensures
                res.deep_view() =~~= $top(s.deep_view()),
        {
            match &s.top {
                None => $xdflt,
                Some(r) => r.val.deep_clone(),
            }
        }

        pub fn $xpush(s: &$exec, v: $xref) -> (res: $exec)
            ensures
                res.deep_view() =~~= $push(s.deep_view(), v.deep_view()),
        {
            $exec { top: Some(Rc::new(PNode { val: v.get_owned(), next: pnodes_clone(&s.top) })) }
        }

        pub fn $xpop(s: &$exec) -> (res: $exec)
            ensures
                res.deep_view() =~~= $pop(s.deep_view()),
        {
            match &s.top {
                None => $exec { top: None },
                Some(r) => {
                    assert(pnodes_view(r.next) =~= pnodes_view(s.top).drop_last());
                    $exec { top: pnodes_clone(&r.next) }
                },
            }
        }

        } // verus!
    };
}

// The scope stack of a variable (`VarBind::stack`).
persistent_stack!(
    NumStack,
    ExecNumStack,
    Num,
    ExecNum,
    &ExecNum,
    Num {
        neg: false,
        mag: Seq::empty(),
        scale: 0u32
    },
    ExecNum {
        neg: false,
        mag: Vec::new(),
        scale: 0u32
    },
    nstack_empty,
    nstack_has,
    nstack_top,
    nstack_push,
    nstack_pop,
    exec_nstack_empty,
    exec_nstack_has,
    exec_nstack_top,
    exec_nstack_push,
    exec_nstack_pop
);

// The scope stack of an array (`ArrBind::stack`).
persistent_stack!(
    FrameStack,
    ExecFrameStack,
    ArrFrame,
    ExecArrFrame,
    &ExecArrFrame,
    ArrFrame {
        elems: Seq::empty()
    },
    ExecArrFrame { elems: Vec::new() },
    fstack_empty,
    fstack_has,
    fstack_top,
    fstack_push,
    fstack_pop,
    exec_fstack_empty,
    exec_fstack_has,
    exec_fstack_top,
    exec_fstack_push,
    exec_fstack_pop
);

// The names of the executing functions (`EState::calls`).
persistent_stack!(
    NameStack,
    ExecNameStack,
    Seq<u8>,
    Vec<u8>,
    &[u8],
    Seq::empty(),
    Vec::new(),
    names_empty,
    names_has,
    names_top,
    names_push,
    names_pop,
    exec_names_empty,
    exec_names_has,
    exec_names_top,
    exec_names_push,
    exec_names_pop
);
