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
use crate::parser::*;
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

verus! {

// ---------------------------------------------------------------------------------------------
// Arenas
// ---------------------------------------------------------------------------------------------

/// The arena of a parsed unit, as functions and the evaluator keep it.
pub struct Code {
    pub s: Seq<Node>,
}

/// The compiled nodes of a `Code`, shared. Its reference type is a slice, so the specification
/// reads `c.s` without copying.
#[derive(Eq, Hash, PartialEq)]
pub struct SharedNodes {
    pub v: Rc<Vec<ExecNode>>,
}

impl DeepView for SharedNodes {
    type V = Seq<Node>;

    open spec fn deep_view(&self) -> Seq<Node> {
        self.v.deep_view()
    }
}

impl<'a> ToRef<&'a [ExecNode]> for &'a SharedNodes {
    fn get_ref(self) -> (res: &'a [ExecNode]) {
        let v: &Vec<ExecNode> = &self.v;
        let res = v.as_slice();
        assert(res.deep_view() =~= v.deep_view());
        res
    }
}

/// The compiled `Code`. The derived traits are those of the structs that
/// `exec_spec_verified!` generates; the compiled code compares with `exec_eq`.
#[derive(Eq, Hash, PartialEq)]
pub struct ExecCode {
    pub s: SharedNodes,
}

impl DeepView for ExecCode {
    type V = Code;

    open spec fn deep_view(&self) -> Code {
        Code { s: self.s.deep_view() }
    }
}

impl DeepViewClone for ExecCode {
    fn deep_clone(&self) -> (res: Self) {
        ExecCode { s: SharedNodes { v: Rc::clone(&self.s.v) } }
    }
}

impl ExecSpecType for Code {
    type ExecOwnedType = ExecCode;
    type ExecRefType<'a> = &'a ExecCode;
}

impl<'a> ToRef<&'a ExecCode> for &'a ExecCode {
    fn get_ref(self) -> (res: &'a ExecCode) {
        self
    }
}

impl ToOwned<ExecCode> for &ExecCode {
    fn get_owned(self) -> (res: ExecCode) {
        self.deep_clone()
    }
}

impl<'a> ExecSpecEq<'a> for &'a ExecCode {
    type Other = &'a ExecCode;

    fn exec_eq(this: Self, other: Self::Other) -> (res: bool) {
        <&[ExecNode]>::exec_eq((&this.s).get_ref(), (&other.s).get_ref())
    }
}

/// The arena with nodes `s`.
pub open spec fn code_of(s: Seq<Node>) -> Code {
    Code { s: s }
}

pub fn exec_code_of(s: &[ExecNode]) -> (res: ExecCode)
    ensures
        res.deep_view() =~~= code_of(s.deep_view()),
{
    ExecCode { s: SharedNodes { v: Rc::new(s.get_owned()) } }
}

/// The number of nodes in a full chunk of an `ExecArena`.
pub const ARENA_CHUNK: usize = 32;

/// The arena that the parser builds (`PState::nodes`). A node is added unless the arena
/// already holds `usize::MAX` nodes, the most a `Vec` can hold.
pub struct Arena {
    pub s: Seq<Node>,
}

/// The nodes of full chunks `c` followed by `t`.
pub open spec fn chunked_view(c: Seq<Seq<Node>>, t: Seq<Node>) -> Seq<Node> {
    Seq::new(
        (c.len() * ARENA_CHUNK + t.len()) as nat,
        |i: int|
            if i < c.len() * ARENA_CHUNK {
                c[i / ARENA_CHUNK as int][i % ARENA_CHUNK as int]
            } else {
                t[i - c.len() * ARENA_CHUNK]
            },
    )
}

proof fn lemma_chunk_index(i: int, q: int, r: int)
    requires
        0 <= q,
        0 <= r < ARENA_CHUNK,
        i == q * ARENA_CHUNK + r,
    ensures
        i / ARENA_CHUNK as int == q,
        i % ARENA_CHUNK as int == r,
{
    assert(i / 32 == q && i % 32 == r) by (nonlinear_arith)
        requires
            0 <= q,
            0 <= r < 32,
            i == q * 32 + r,
    ;
}

/// The compiled `Arena`: full chunks of `ARENA_CHUNK` nodes and a shorter tail, all shared, so
/// that copying an arena is constant time and adding a node copies at most a chunk and the
/// list of chunks.
#[derive(Eq, Hash, PartialEq)]
pub struct ExecArena {
    full: Rc<Vec<Rc<Vec<ExecNode>>>>,
    tail: Rc<Vec<ExecNode>>,
}

impl ExecArena {
    pub closed spec fn chunks(&self) -> Seq<Seq<Node>> {
        self.full.deep_view()
    }

    pub closed spec fn rest(&self) -> Seq<Node> {
        self.tail.deep_view()
    }

    #[verifier::type_invariant]
    closed spec fn wf(self) -> bool {
        &&& forall|j: int| 0 <= j < self.chunks().len() ==> #[trigger] self.chunks()[j].len() == ARENA_CHUNK
        &&& self.rest().len() < ARENA_CHUNK
        &&& self.chunks().len() * ARENA_CHUNK + self.rest().len() <= usize::MAX
    }
}

impl DeepView for ExecArena {
    type V = Arena;

    closed spec fn deep_view(&self) -> Arena {
        Arena { s: chunked_view(self.chunks(), self.rest()) }
    }
}

impl DeepViewClone for ExecArena {
    fn deep_clone(&self) -> (res: Self) {
        proof { use_type_invariant(self); }
        ExecArena { full: Rc::clone(&self.full), tail: Rc::clone(&self.tail) }
    }
}

impl ExecSpecType for Arena {
    type ExecOwnedType = ExecArena;
    type ExecRefType<'a> = &'a ExecArena;
}

impl<'a> ToRef<&'a ExecArena> for &'a ExecArena {
    fn get_ref(self) -> (res: &'a ExecArena) {
        self
    }
}

impl ToOwned<ExecArena> for &ExecArena {
    fn get_owned(self) -> (res: ExecArena) {
        self.deep_clone()
    }
}

impl<'a> ExecSpecEq<'a> for &'a ExecArena {
    type Other = &'a ExecArena;

    fn exec_eq(this: Self, other: Self::Other) -> (res: bool) {
        let a = arena_to_vec(this);
        let b = arena_to_vec(other);
        <&[ExecNode]>::exec_eq(a.as_slice(), b.as_slice())
    }
}

/// The empty arena.
pub open spec fn arena_empty() -> Arena {
    Arena { s: Seq::empty() }
}

/// The number of nodes.
pub open spec fn arena_len(a: Arena) -> usize {
    a.s.len() as usize
}

/// Node `i` (`Break` past the end).
pub open spec fn arena_at(a: Arena, i: usize) -> Node {
    if i < a.s.len() { a.s[i as int] } else { Node::Break }
}

/// Adds node `n` at the end, unless the arena already holds `usize::MAX` nodes.
pub open spec fn arena_push(a: Arena, n: Node) -> Arena {
    if a.s.len() < usize::MAX { Arena { s: a.s.push(n) } } else { a }
}

/// The arena as functions and the evaluator keep it.
pub open spec fn arena_code(a: Arena) -> Code {
    Code { s: a.s }
}

pub fn exec_arena_empty() -> (res: ExecArena)
    ensures
        res.deep_view() =~~= arena_empty(),
{
    let res = ExecArena { full: Rc::new(Vec::new()), tail: Rc::new(Vec::new()) };
    assert(res.deep_view().s =~= Seq::<Node>::empty());
    res
}

pub fn exec_arena_len(a: &ExecArena) -> (res: usize)
    ensures
        res == arena_len(a.deep_view()),
{
    proof { use_type_invariant(a); }
    let full: &Vec<Rc<Vec<ExecNode>>> = &a.full;
    let tail: &Vec<ExecNode> = &a.tail;
    full.len() * ARENA_CHUNK + tail.len()
}

pub fn exec_arena_at(a: &ExecArena, i: usize) -> (res: ExecNode)
    ensures
        res.deep_view() =~~= arena_at(a.deep_view(), i),
{
    proof { use_type_invariant(a); }
    let full: &Vec<Rc<Vec<ExecNode>>> = &a.full;
    let tail: &Vec<ExecNode> = &a.tail;
    let q = i / ARENA_CHUNK;
    let r = i % ARENA_CHUNK;
    proof { lemma_chunk_index(i as int, q as int, r as int); }
    if q < full.len() {
        let c: &Vec<ExecNode> = &full[q];
        proof { assert(c.deep_view() == a.chunks()[q as int]); }
        c[r].deep_clone()
    } else {
        let k = i - full.len() * ARENA_CHUNK;
        if k < tail.len() {
            tail[k].deep_clone()
        } else {
            ExecNode::Break
        }
    }
}

pub fn exec_arena_push(a: &ExecArena, n: &ExecNode) -> (res: ExecArena)
    ensures
        res.deep_view() =~~= arena_push(a.deep_view(), n.deep_view()),
{
    proof { use_type_invariant(a); }
    let full: &Vec<Rc<Vec<ExecNode>>> = &a.full;
    let tail: &Vec<ExecNode> = &a.tail;
    let ghost c = a.chunks();
    let ghost t = a.rest();
    let ghost old = a.deep_view().s;
    if full.len() * ARENA_CHUNK + tail.len() == usize::MAX {
        return a.deep_clone();
    }
    let mut t2 = tail.deep_clone();
    t2.push(n.get_owned());
    proof { assert(t2.deep_view() =~= t.push(n.deep_view())); }
    if t2.len() < ARENA_CHUNK {
        let res = ExecArena { full: Rc::clone(&a.full), tail: Rc::new(t2) };
        proof {
            assert forall|i: int| 0 <= i < old.len() + 1 implies #[trigger] res.deep_view().s[i] == old.push(n.deep_view())[i] by {
                if i >= c.len() * ARENA_CHUNK && i < old.len() {
                    assert(t2.deep_view()[i - c.len() * ARENA_CHUNK] == t[i - c.len() * ARENA_CHUNK]);
                }
            }
            assert(res.deep_view().s =~= old.push(n.deep_view()));
        }
        res
    } else {
        let mut f2: Vec<Rc<Vec<ExecNode>>> = Vec::new();
        let mut j: usize = 0;
        while j < full.len()
            invariant
                j <= full.len(),
                full.deep_view() == c,
                f2.deep_view() =~= c.subrange(0, j as int),
            decreases full.len() - j,
        {
            let r = Rc::clone(&full[j]);
            let ghost before = f2.deep_view();
            proof { assert(r.deep_view() == c[j as int]); }
            f2.push(r);
            proof {
                assert(f2.deep_view() =~= before.push(c[j as int]));
                assert(c.subrange(0, j as int + 1) =~= c.subrange(0, j as int).push(c[j as int]));
            }
            j += 1;
        }
        let ghost t2v = t2.deep_view();
        let ghost f1 = f2.deep_view();
        proof { assert(f1 =~= c); }
        f2.push(Rc::new(t2));
        proof { assert(f2.deep_view() =~= f1.push(t2v)); }
        let res = ExecArena { full: Rc::new(f2), tail: Rc::new(Vec::new()) };
        proof {
            let c2 = c.push(t.push(n.deep_view()));
            assert(f2.deep_view() =~= c2);
            assert forall|i: int| 0 <= i < old.len() + 1 implies #[trigger] res.deep_view().s[i] == old.push(n.deep_view())[i] by {
                if i < c.len() * ARENA_CHUNK {
                    lemma_chunk_index(i, i / ARENA_CHUNK as int, i % ARENA_CHUNK as int);
                } else {
                    lemma_chunk_index(i, c.len() as int, i - c.len() * ARENA_CHUNK);
                }
            }
            assert(res.deep_view().s =~= old.push(n.deep_view()));
        }
        res
    }
}

/// The nodes of `a` in a vector.
fn arena_to_vec(a: &ExecArena) -> (res: Vec<ExecNode>)
    ensures
        res.deep_view() =~= a.deep_view().s,
{
    let n = exec_arena_len(a);
    let ghost s = a.deep_view().s;
    proof { use_type_invariant(a); }
    let mut v: Vec<ExecNode> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == s.len(),
            i <= n,
            s == a.deep_view().s,
            v.deep_view() =~= s.subrange(0, i as int),
        decreases n - i,
    {
        let x = exec_arena_at(a, i);
        let ghost before = v.deep_view();
        proof { assert(x.deep_view() == s[i as int]); }
        v.push(x);
        proof {
            assert(v.deep_view() =~= before.push(s[i as int]));
            assert(s.subrange(0, i as int + 1) =~= s.subrange(0, i as int).push(s[i as int]));
        }
        i += 1;
    }
    v
}

pub fn exec_arena_code(a: &ExecArena) -> (res: ExecCode)
    ensures
        res.deep_view() =~~= arena_code(a.deep_view()),
{
    let v = arena_to_vec(a);
    ExecCode { s: SharedNodes { v: Rc::new(v) } }
}

} // verus!

verus! {

// ---------------------------------------------------------------------------------------------
// Output streams
// ---------------------------------------------------------------------------------------------

/// The bytes written to an output stream (`EState::out`, `EState::err`).
pub struct Bytes {
    pub s: Seq<u8>,
}

/// The bytes of the chunks from the first written up to `n`.
pub open spec fn pchunks_view(n: Option<Rc<PNode<Vec<u8>>>>) -> Seq<u8>
    decreases n,
{
    match n {
        None => Seq::empty(),
        Some(r) => pchunks_view(r.next).add(r.val@),
    }
}

/// Appends the bytes of the chunks up to `n` to `v`.
fn pchunks_append(n: &Option<Rc<PNode<Vec<u8>>>>, v: &mut Vec<u8>)
    ensures
        final(v)@ == old(v)@.add(pchunks_view(*n)),
    decreases *n,
{
    match n {
        None => {
            assert(v@ =~= v@.add(Seq::<u8>::empty()));
        },
        Some(r) => {
            let ghost v0 = v@;
            pchunks_append(&r.next, v);
            let ghost v1 = v@;
            let c: &Vec<u8> = &r.val;
            let mut i: usize = 0;
            while i < c.len()
                invariant
                    i <= c.len(),
                    v@ =~= v1.add(c@.subrange(0, i as int)),
                decreases c.len() - i,
            {
                v.push(c[i]);
                proof { assert(v@ =~= v1.add(c@.subrange(0, i as int + 1))); }
                i += 1;
            }
            assert(c@.subrange(0, c.len() as int) =~= c@);
            assert(v@ =~= v0.add(pchunks_view(*n)));
        },
    }
}

/// The compiled `Bytes`: the written chunks, last chunk first, shared.
#[derive(Eq, Hash, PartialEq)]
pub struct ExecBytes {
    pub last: Option<Rc<PNode<Vec<u8>>>>,
}

impl DeepView for ExecBytes {
    type V = Bytes;

    open spec fn deep_view(&self) -> Bytes {
        Bytes { s: pchunks_view(self.last) }
    }
}

impl DeepViewClone for ExecBytes {
    fn deep_clone(&self) -> (res: Self) {
        ExecBytes { last: pnodes_clone(&self.last) }
    }
}

impl ExecSpecType for Bytes {
    type ExecOwnedType = ExecBytes;
    type ExecRefType<'a> = &'a ExecBytes;
}

impl<'a> ToRef<&'a ExecBytes> for &'a ExecBytes {
    fn get_ref(self) -> (res: &'a ExecBytes) {
        self
    }
}

impl ToOwned<ExecBytes> for &ExecBytes {
    fn get_owned(self) -> (res: ExecBytes) {
        self.deep_clone()
    }
}

/// The bytes of `b` in a vector.
fn bytes_to_vec(b: &ExecBytes) -> (res: Vec<u8>)
    ensures
        res@ == b.deep_view().s,
{
    let mut v: Vec<u8> = Vec::new();
    pchunks_append(&b.last, &mut v);
    assert(v@ =~= b.deep_view().s);
    v
}

impl<'a> ExecSpecEq<'a> for &'a ExecBytes {
    type Other = &'a ExecBytes;

    fn exec_eq(this: Self, other: Self::Other) -> (res: bool) {
        let a = bytes_to_vec(this);
        let b = bytes_to_vec(other);
        let sa = a.as_slice();
        let sb = b.as_slice();
        proof {
            assert(sa.deep_view() =~= this.deep_view().s);
            assert(sb.deep_view() =~= other.deep_view().s);
        }
        <&[u8]>::exec_eq(sa, sb)
    }
}

/// Nothing written.
pub open spec fn bytes_empty() -> Bytes {
    Bytes { s: Seq::empty() }
}

/// Appends `s`.
pub open spec fn bytes_add(b: Bytes, s: Seq<u8>) -> Bytes {
    Bytes { s: b.s.add(s) }
}

/// Appends the byte `c`.
pub open spec fn bytes_push(b: Bytes, c: u8) -> Bytes {
    Bytes { s: b.s.push(c) }
}

/// The bytes written.
pub open spec fn bytes_seq(b: Bytes) -> Seq<u8> {
    b.s
}

pub fn exec_bytes_empty() -> (res: ExecBytes)
    ensures
        res.deep_view() =~~= bytes_empty(),
{
    ExecBytes { last: None }
}

pub fn exec_bytes_add(b: &ExecBytes, s: &[u8]) -> (res: ExecBytes)
    ensures
        res.deep_view() =~~= bytes_add(b.deep_view(), s.deep_view()),
{
    let c: Vec<u8> = s.get_owned();
    assert(c@ =~= s.deep_view());
    let res = ExecBytes { last: Some(Rc::new(PNode { val: c, next: pnodes_clone(&b.last) })) };
    assert(res.deep_view().s =~= b.deep_view().s.add(s.deep_view()));
    res
}

pub fn exec_bytes_push(b: &ExecBytes, c: u8) -> (res: ExecBytes)
    ensures
        res.deep_view() =~~= bytes_push(b.deep_view(), c),
{
    let v: Vec<u8> = vec![c];
    let res = ExecBytes { last: Some(Rc::new(PNode { val: v, next: pnodes_clone(&b.last) })) };
    assert(res.deep_view().s =~= b.deep_view().s.push(c));
    res
}

pub fn exec_bytes_seq(b: &ExecBytes) -> (res: Vec<u8>)
    ensures
        res.deep_view() =~~= bytes_seq(b.deep_view()),
{
    let v = bytes_to_vec(b);
    assert(v.deep_view() =~= v@);
    v
}

} // verus!
