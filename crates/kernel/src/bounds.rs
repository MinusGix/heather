//! Per-node free-variable bounds for the **local** namespace, kept in the
//! node, so the local-namespace traversals (`SubstLocal`, `ShiftLocal` in
//! `subst.rs`) can return a subtree that provably cannot change in O(1)
//! instead of walking it to discover it was shareable
//! (issues/subst-visits-closed-subtrees.md, route B).
//!
//! ## What is kept
//!
//! [`LocalUse`] summarizes everything a local-namespace operation can act on
//! inside a subtree, relative to the subtree's own root:
//!
//! - `bound` — 1 + the largest free local de Bruijn index (0 = locally
//!   closed). A local operation applied when `at.local >= bound` renumbers
//!   or substitutes nothing.
//! - `has_wk` — whether a weakening tail `wk^k_g` (of a `U^δ` / `u^δ`) is
//!   visible in this local scope. A weakening counts the binders it sits
//!   under, so the local operations rewrite it *unconditionally* (`wk^k_g ∘
//!   δ` recomputes the length even when no variable moves), and a subtree
//!   containing one is never skippable on the bound alone. The empty tail
//!   `·` is no such thing: it records nothing (`term.rs`, `LocalSubst`), no
//!   operation changes it, and a subtree whose references to Ψ are all at
//!   the empty substitution, which is what a mention of a top-level
//!   definition is, is as skippable as one with no reference at all.
//!
//! Both components follow the same scoping rule as the traversal itself:
//! boxed code, contextual-type components, context arguments, and the
//! `ctx`/`ty` annotations of letbox/recursors live in a *different* local
//! context, so they contribute nothing (`box T [δ] = box T`).
//!
//! ## Where it is kept, and who writes it
//!
//! In the node's head (`rc.rs`, [`crate::rc::Head`]): the words the kernel's
//! shared pointer keeps beside the value. The summary is a **pure function
//! of the immutable term**, computed on first demand by this file and
//! written once; `Rc::new` makes an empty head and that is all a
//! construction site has to do with it. So no constructor in this crate or
//! in `elab` maintains anything, which is what storing the bound *at
//! construction* would have asked of every one of them, and the whole
//! trusted surface is this file's arithmetic (whose binder counts must
//! mirror `subst.rs`'s dep table, the one drift hazard, see below and
//! `issues/kernel-binder-count-tables.md`) and the
//! pointer's rule that a value reached mutably has its head emptied first.
//!
//! The first question about a node walks whatever of its subtree has no
//! answer yet, and leaves an answer in every node it passes; after that the
//! question is a read of the node the caller already holds. A node is
//! walked once for as long as it lives.
//!
//! ## Why not a table
//!
//! Address-keyed tables (`issues/free-variable-bounds-in-the-node.md`) cost
//! a cold check more than a larger table recovers, and made which subtrees
//! a substitution skipped depend on what had been asked before and on which
//! addresses collided, so the substitution counters were not functions of
//! the input. In the node, they are.
//!
//! ## How wrong bounds are caught
//!
//! A wrong bound is a silently wrong substitution — a soundness bug, the
//! reason route B was deferred. The defense is the same one the sharing
//! counter uses: every skip taken on this metadata is re-verified in debug
//! builds by running the real traversal and asserting it was a no-op
//! (`sub_ty`/`sub_tm` in subst.rs), and the test suite runs in the dev
//! profile — including the substitution laws over generated terms
//! covering every variant. A binder count here that drifts from the
//! traversal's dep table fails those tests on any skip they take.

use std::cell::RefCell;
use std::sync::{Arc, Weak};

use crate::rc::{Rc, USES_BITS};

use crate::term::{Branches, IWfSig, LocalSubst, MSig, Motives, SubstTail, Term, Type};

/// What a subtree exposes to local-namespace operations, relative to its
/// own root. See the module docs for the two components.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct LocalUse {
    pub bound: u32,
    pub has_wk: bool,
    /// Bit `i` set when the free index `i` occurs, for `i` below
    /// [`USES_BITS`] (larger indices are counted by `bound` alone). No
    /// substitution reads it: it answers [`ignores_innermost`], a question
    /// about cost, which is why a node's head can keep its flags in the
    /// bits above (`rc::Head`).
    pub uses: u64,
}

impl LocalUse {
    const CLOSED: LocalUse = LocalUse {
        bound: 0,
        has_wk: false,
        uses: 0,
    };

    fn join(self, o: LocalUse) -> LocalUse {
        LocalUse {
            bound: self.bound.max(o.bound),
            has_wk: self.has_wk || o.has_wk,
            uses: self.uses | o.uses,
        }
    }

    /// View a child's use from outside `k` local binders: the innermost `k`
    /// free indices are bound by the node itself and stop being visible.
    fn under(self, k: u32) -> LocalUse {
        LocalUse {
            bound: self.bound.saturating_sub(k),
            uses: self.uses.checked_shr(k).unwrap_or(0),
            ..self
        }
    }

    /// Can a local-namespace operation applied at binder depth `d` change
    /// this subtree at all?
    pub fn touched_at(self, d: u32) -> bool {
        self.bound > d || self.has_wk
    }
}

/// The walk that computes an answer, and what it needs beside the nodes:
/// its native depth, and the suffix joins of long item arrays.
///
/// An answer is kept in the node it is about ([`crate::rc::Head`]): written
/// once, by [`Walk::term_use`] or [`Walk::type_use`], and read by whoever
/// holds the node. So a node is walked at most once for as long as it
/// lives, a parent's answer costs one read per child, and nothing is keyed
/// by an address.
struct Walk {
    /// Native depth of [`Walk::term_use`]'s recursion: past
    /// [`crate::term::SPINE_ITERATE_AT`] a node's spine is computed from the
    /// bottom up first ([`Walk::warm_spine`]).
    depth: u32,
    /// Suffix joins of the item arrays whose tail windows were asked about
    /// ([`Walk::window_use`]).
    windows: Vec<WindowSlot>,
}

/// One item array's suffix joins at a stride, under a weak key to the array:
/// the key pins the allocation, so an address match names the array the
/// joins were computed from, whose contents cannot have changed, and a
/// caller asks about an array it holds. `suffix[k]` is the join of
/// `items[k * WINDOW_STRIDE..]`.
///
/// The key pins the array's *block* (one pointer per element) past its
/// death until evicted, never the elements; the table is small and only
/// arrays whose tail windows are queried get an entry, so that is a few
/// blocks.
struct WindowSlot {
    key: Option<Weak<[Rc<Term>]>>,
    suffix: Box<[LocalUse]>,
}

/// Elements between two stored suffix joins: a window's answer is one
/// lookup plus at most this many joins.
const WINDOW_STRIDE: usize = 32;

/// log2 of [`WindowSlot`]s per thread.
const WINDOW_BITS: u32 = 6;

/// What a node's head holds, as a [`LocalUse`].
#[inline]
fn known<T>(t: &Rc<T>) -> Option<LocalUse> {
    Rc::head(t).local().map(|(bound, has_wk, uses)| LocalUse { bound, has_wk, uses })
}

#[inline]
fn keep<T>(t: &Rc<T>, u: LocalUse) {
    Rc::head(t).set_local(u.bound, u.has_wk, u.uses);
}

/// A term whose use is read off the node itself: a variable, or a form
/// with no local variable under it (`box`ed code is another local scope).
#[inline]
fn term_leaf(t: &Term) -> Option<LocalUse> {
    match t {
        Term::Var(v) => Some(LocalUse {
            bound: v.0.saturating_add(1),
            has_wk: false,
            uses: var_bit(v.0),
        }),
        Term::TmNat
        | Term::TmTy(_)
        | Term::TmUnit { .. }
        | Term::TmEmpty { .. }
        | Term::TmSEmpty { .. }
        | Term::Zero
        | Term::NatLit(_)
        | Term::Triv { .. }
        | Term::BoxTy(_)
        | Term::BoxTm(_) => Some(LocalUse::CLOSED),
        _ => None,
    }
}

#[inline]
fn type_leaf(t: &Type) -> Option<LocalUse> {
    match t {
        Type::Nat
        | Type::Ty(_)
        | Type::Unit { .. }
        | Type::Empty { .. }
        | Type::SEmpty { .. }
        | Type::CodeTy { .. }
        | Type::CodeTm { .. } => Some(LocalUse::CLOSED),
        _ => None,
    }
}

/// A term's use when it takes no walk: a leaf, or a node already answered.
#[inline]
fn term_known(t: &Rc<Term>) -> Option<LocalUse> {
    term_leaf(t).or_else(|| known(t))
}

#[inline]
fn type_known(t: &Rc<Type>) -> Option<LocalUse> {
    type_leaf(t).or_else(|| known(t))
}

impl Walk {
    fn new() -> Walk {
        Walk {
            depth: 0,
            windows: (0..1 << WINDOW_BITS)
                .map(|_| WindowSlot { key: None, suffix: Box::new([]) })
                .collect(),
        }
    }

    /// The join of `items[from..]`'s uses: the live window of a
    /// [`Term::VecItems`] node.
    ///
    /// Comparing two vectors by value unfolds one of these nodes per element
    /// (`term::vec_items_unfold`), each tail a *fresh* node one element on,
    /// and the value machine asks every fresh tail's bounds (its closed-term
    /// memo key); walked whole, the windows cost the square of the length
    /// (issues/vec-items-window-bounds.md). A window is a suffix of one
    /// shared array, so the array's suffix joins at a stride, computed once
    /// in a pass from the back, answer any window with one lookup and fewer
    /// than [`WINDOW_STRIDE`] joins. The from-zero window, which every
    /// ordinary walk of a literal asks, is the node's own answer and is
    /// walked directly: an array gets suffix joins only when a tail is
    /// asked about, and only when it is long enough for them to pay.
    fn window_use(&mut self, items: &Arc<[Rc<Term>]>, from: u32) -> LocalUse {
        let from = from as usize;
        let live = items.get(from..).unwrap_or(&[]);
        if from == 0 || live.len() < 2 * WINDOW_STRIDE {
            let mut used = LocalUse::CLOSED;
            for item in live {
                used = used.join(self.term_use(item));
            }
            return used;
        }
        let p = Arc::as_ptr(items).cast::<()>() as usize;
        let i = ((p as u64).wrapping_mul(0x9E37_79B9_7F4A_7C15) >> (64 - WINDOW_BITS)) as usize;
        let hit = matches!(&self.windows[i].key, Some(k) if std::ptr::eq(k.as_ptr().cast::<()>(), Arc::as_ptr(items).cast::<()>()));
        if !hit {
            // From the back, so each stored join is one stride's joins on
            // the next; the elements' own answers come from their nodes.
            let mut suffix = vec![LocalUse::CLOSED; items.len().div_ceil(WINDOW_STRIDE)];
            let mut used = LocalUse::CLOSED;
            for (j, item) in items.iter().enumerate().rev() {
                used = used.join(self.term_use(item));
                if j % WINDOW_STRIDE == 0 {
                    suffix[j / WINDOW_STRIDE] = used;
                }
            }
            self.windows[i] = WindowSlot { key: Some(Arc::downgrade(items)), suffix: suffix.into() };
        }
        // The stored join at the first stride boundary at or past `from`,
        // and the elements before it one by one.
        let k = from.div_ceil(WINDOW_STRIDE);
        let mut used = self.windows[i].suffix.get(k).copied().unwrap_or(LocalUse::CLOSED);
        for item in &items[from..(k * WINDOW_STRIDE).min(items.len())] {
            used = used.join(self.term_use(item));
        }
        used
    }

    fn term_use(&mut self, t: &Rc<Term>) -> LocalUse {
        if let Some(u) = term_known(t) {
            return u;
        }
        if self.depth >= crate::term::SPINE_ITERATE_AT {
            self.warm_spine(t);
        }
        self.depth += 1;
        let u = self.compute_term(t);
        self.depth -= 1;
        keep(t, u);
        u
    }

    /// A deep node's spine answered from the bottom up, so the recursion
    /// that follows meets an answer one level down instead of walking the
    /// chain one native frame per node (docs/kernel/deep-term-walks-design.md).
    /// Each node below `t` is computed with the depth reset: its own spine
    /// child is already answered, so it recurses a level or two.
    fn warm_spine(&mut self, t: &Rc<Term>) {
        let mut path = Vec::new();
        let mut cur = crate::term::spine_child(t);
        while let Some(c) = cur {
            if term_known(c).is_some() {
                break;
            }
            path.push(Rc::clone(c));
            cur = crate::term::spine_child(c);
        }
        let depth = std::mem::replace(&mut self.depth, 0);
        for node in path.iter().rev() {
            self.term_use(node);
        }
        self.depth = depth;
    }

    /// The checked spellings' annotation is optional (design §2.1); an
    /// absent one uses nothing.
    fn opt_type_use(&mut self, t: &Option<Rc<Type>>) -> LocalUse {
        match t {
            Some(t) => self.type_use(t),
            None => LocalUse::CLOSED,
        }
    }

    fn type_use(&mut self, t: &Rc<Type>) -> LocalUse {
        if let Some(u) = type_known(t) {
            return u;
        }
        let u = self.compute_type(t);
        keep(t, u);
        u
    }
}

/// Bit `i` of [`LocalUse::uses`].
fn var_bit(i: u32) -> u64 {
    if i < USES_BITS { 1 << i } else { 0 }
}

thread_local! {
    static WALK: RefCell<Walk> = RefCell::new(Walk::new());
}

/// Captures read by evaluation of a syntactic closure. Weakening tails
/// depend on the ambient base/global shift, not on captured local values.
pub(crate) fn term_captures(t: &Rc<Term>) -> u32 {
    term_local_use(t).bound
}

pub(crate) fn type_captures(t: &Rc<Type>) -> u32 {
    type_local_use(t).bound
}

/// `t`'s local footprint: its bound and whether a weakening tail shows
/// in its local scope. The first question about a node walks what of its
/// subtree has not been answered; every later one is a read.
#[inline]
pub(crate) fn term_local_use(t: &Rc<Term>) -> LocalUse {
    match term_known(t) {
        Some(u) => u,
        None => WALK.with(|c| c.borrow_mut().term_use(t)),
    }
}

#[inline]
pub(crate) fn type_local_use(t: &Rc<Type>) -> LocalUse {
    match type_known(t) {
        Some(u) => u,
        None => WALK.with(|c| c.borrow_mut().type_use(t)),
    }
}

/// [`type_local_use`] for a type the caller holds by reference: the node
/// itself is walked, its children answered from their own nodes.
pub(crate) fn type_ref_local_use(t: &Type) -> LocalUse {
    WALK.with(|c| c.borrow_mut().compute_type(t))
}

/// Whether a type is locally closed: no free local variable and no
/// weakening tail, so that it reads nothing of Γ and is the same syntax
/// under any binders. The one reader that is not a traversal is the
/// closed-type memo in `typing.rs` (`Tc::ty_check`), which judges a locally
/// closed type once whatever Γ it occurs in — so a wrong answer here is a
/// soundness bug there, as a wrong skip is in `subst.rs`.
pub(crate) fn type_locally_closed(t: &Rc<Type>) -> bool {
    let u = type_local_use(t);
    u.bound == 0 && !u.has_wk
}

/// [`type_locally_closed`] for a type the caller holds by reference: the
/// node itself is walked, its children answered from their own nodes. Read by the
/// closed-conversion memo (`Tc::conv_ty`), with the same stakes.
pub(crate) fn type_ref_locally_closed(t: &Type) -> bool {
    let u = type_ref_local_use(t);
    u.bound == 0 && !u.has_wk
}

/// [`type_locally_closed`] for an `IWf` signature, which `Tc::iwf_sig_wf`
/// judges once whatever Γ it occurs in.
pub(crate) fn iwf_sig_locally_closed(sig: &IWfSig) -> bool {
    WALK.with(|c| {
        let u = c.borrow_mut().iwf_sig_use(sig);
        u.bound == 0 && !u.has_wk
    })
}

/// Whether evaluating `t` reads none of its innermost `n` (below
/// [`USES_BITS`]) local variables: no free index below `n` occurs. A wrong
/// answer costs time, never a verdict (`eval/probe.rs`, the one reader).
pub(crate) fn ignores_innermost(t: &Rc<Term>, n: u32) -> bool {
    debug_assert!(n < USES_BITS);
    term_local_use(t).uses & (var_bit(n) - 1) == 0
}

/// Should a local-namespace operation at binder depth `d` skip this
/// subtree? It should when the operation can change nothing in it.
#[inline]
pub(crate) fn skip_term(t: &Rc<Term>, d: u32) -> bool {
    !term_local_use(t).touched_at(d)
}

#[inline]
pub(crate) fn skip_type(t: &Rc<Type>, d: u32) -> bool {
    !type_local_use(t).touched_at(d)
}

impl Walk {
    /// An `IWf` signature: `arity` and `out` under `x : S`, `child` under
    /// `x, i`.
    fn iwf_sig_use(&mut self, sig: &IWfSig) -> LocalUse {
        self.type_use(&sig.idx)
            .join(self.type_use(&sig.shape))
            .join(self.term_use(&sig.arity).under(1))
            .join(self.term_use(&sig.out).under(1))
            .join(self.term_use(&sig.child).under(2))
    }

    /// An `M` signature: `shape` under `i`, `pos` under `i, s`, `next` under
    /// `i, s, p`.
    fn m_sig_use(&mut self, sig: &MSig) -> LocalUse {
        self.type_use(&sig.idx)
            .join(self.type_use(&sig.shape).under(1))
            .join(self.type_use(&sig.pos).under(2))
            .join(self.term_use(&sig.next).under(3))
    }

    /// A weakening tail is rewritten by every local operation, an empty
    /// one by none; the payload terms live in the current scope.
    fn subst_use(&mut self, s: &LocalSubst) -> LocalUse {
        s.terms.iter().fold(
            LocalUse {
                bound: 0,
                has_wk: matches!(s.tail, SubstTail::Wk { .. }),
                uses: 0,
            },
            |a, t| a.join(self.term_use(t)),
        )
    }

    // The binder counts below (the `.under(k)` arguments) are the LOCAL column
    // of subst.rs's traversal — `dep(_, _, k)` in map_type/map_term/map_motives/
    // map_branches — and must stay identical to it. Other-context children
    // (everything subst.rs routes through other_ty/other_tm/other_ctx) are
    // omitted entirely, matching `LOCAL_OP` scoping.

    fn compute_type(&mut self, t: &Type) -> LocalUse {
        match t {
            Type::Nat
            | Type::Ty(_)
            | Type::Unit { .. }
            | Type::Empty { .. }
            | Type::SEmpty { .. }
            | Type::CodeTy { .. }
            | Type::CodeTm { .. } => LocalUse::CLOSED,
            Type::Pi { dom, cod, .. } => self.type_use(dom).join(self.type_use(cod).under(1)),
            Type::UPi { body, .. } => self.type_use(body),
            Type::El { tm, .. } => self.term_use(tm),
            Type::Id { ty, lhs, rhs, .. } | Type::SEq { ty, lhs, rhs, .. } => self
                .type_use(ty)
                .join(self.term_use(lhs))
                .join(self.term_use(rhs)),
            Type::Squash { ty, .. } => self.type_use(ty),
            Type::Sigma { fst, snd, .. } => self.type_use(fst).join(self.type_use(snd).under(1)),
            Type::Sum { lhs, rhs, .. } => self.type_use(lhs).join(self.type_use(rhs)),
            Type::Vec { elem, len, .. } => self.type_use(elem).join(self.term_use(len)),
            Type::Fin { len } => self.term_use(len),
            Type::Wf { shape, arity, .. } => {
                self.type_use(shape).join(self.term_use(arity).under(1))
            }
            Type::W { shape, pos, .. } => self.type_use(shape).join(self.type_use(pos).under(1)),
            Type::DVec { len, fam, .. } => self.term_use(len).join(self.type_use(fam).under(1)),
            Type::IWf { sig, index } => self.iwf_sig_use(sig).join(self.term_use(index)),
            Type::M { sig, index } => self.m_sig_use(sig).join(self.term_use(index)),
            Type::GlobalTy { subst, .. } => self.subst_use(subst),
            Type::CtxPi { body, .. } => self.type_use(body),
            Type::TyPi { body, .. } => self.type_use(body),
        }
    }

    fn compute_term(&mut self, t: &Rc<Term>) -> LocalUse {
        match &**t {
            Term::Var(v) => LocalUse {
                bound: v.0.saturating_add(1),
                has_wk: false,
                uses: var_bit(v.0),
            },
            Term::TmNat
            | Term::TmTy(_)
            | Term::TmUnit { .. }
            | Term::TmEmpty { .. }
            | Term::TmSEmpty { .. }
            | Term::Zero
            | Term::NatLit(_)
            | Term::Triv { .. }
            | Term::BoxTy(_)
            | Term::BoxTm(_) => LocalUse::CLOSED,
            Term::TmPi { dom, cod, .. } => self.term_use(dom).join(self.term_use(cod).under(1)),
            Term::TmId { ty, lhs, rhs, .. } | Term::TmSEq { ty, lhs, rhs, .. } => self
                .term_use(ty)
                .join(self.term_use(lhs))
                .join(self.term_use(rhs)),
            Term::TmSquash { ty, .. } => self.term_use(ty),
            Term::TmSigma { fst, snd, .. } => self.term_use(fst).join(self.term_use(snd).under(1)),
            Term::TmSum { lhs, rhs, .. } => self.term_use(lhs).join(self.term_use(rhs)),
            Term::TmW { shape, pos, .. } => self.term_use(shape).join(self.term_use(pos).under(1)),
            Term::TmVec { elem, len, .. } => self.term_use(elem).join(self.term_use(len)),
            Term::TmFin { len } => self.term_use(len),
            Term::TmWf { shape, arity, .. } => {
                self.term_use(shape).join(self.term_use(arity).under(1))
            }
            Term::TmDVec { len, fam, .. } => self.term_use(len).join(self.term_use(fam).under(1)),
            Term::TmIWf { idx, shape, arity, out, child, index, .. } => self
                .term_use(idx)
                .join(self.term_use(shape))
                .join(self.term_use(arity).under(1))
                .join(self.term_use(out).under(1))
                .join(self.term_use(child).under(2))
                .join(self.term_use(index)),
            Term::TmM { idx, shape, pos, next, index, .. } => self
                .term_use(idx)
                .join(self.term_use(shape).under(1))
                .join(self.term_use(pos).under(2))
                .join(self.term_use(next).under(3))
                .join(self.term_use(index)),
            Term::Succ(t) => self.term_use(t),
            Term::ElimNat {
                motive,
                base,
                step,
                scrut,
                ..
            } => self
                .type_use(motive)
                .under(1)
                .join(self.term_use(base))
                .join(self.term_use(step).under(2))
                .join(self.term_use(scrut)),
            Term::Refl { ty, tm, .. } | Term::SRefl { ty, tm, .. } => {
                self.type_use(ty).join(self.term_use(tm))
            }
            Term::Squash { ty, tm, .. } => self.type_use(ty).join(self.term_use(tm)),
            Term::J {
                ty,
                lhs,
                motive,
                case,
                rhs,
                proof,
                ..
            } => self
                .type_use(ty)
                .join(self.term_use(lhs))
                .join(self.type_use(motive).under(2))
                .join(self.term_use(case))
                .join(self.term_use(rhs))
                .join(self.term_use(proof)),
            Term::ElimSEmpty { motive, scrut, .. } | Term::ElimEmpty { motive, scrut, .. } => {
                self.type_use(motive).under(1).join(self.term_use(scrut))
            }
            Term::ElimSquash { src_ty, motive, case, scrut, .. } => self
                .type_use(src_ty)
                .join(self.type_use(motive).under(1))
                .join(self.term_use(case).under(1))
                .join(self.term_use(scrut)),
            Term::Pair {
                fst_ty,
                snd_ty,
                fst,
                snd,
                ..
            } => self
                .type_use(fst_ty)
                .join(self.type_use(snd_ty).under(1))
                .join(self.term_use(fst))
                .join(self.term_use(snd)),
            Term::Fst {
                fst_ty,
                snd_ty,
                pair,
                ..
            }
            | Term::Snd {
                fst_ty,
                snd_ty,
                pair,
                ..
            } => self
                .type_use(fst_ty)
                .join(self.type_use(snd_ty).under(1))
                .join(self.term_use(pair)),
            Term::Inl { lhs, rhs, val, .. } | Term::Inr { lhs, rhs, val, .. } => self
                .type_use(lhs)
                .join(self.type_use(rhs))
                .join(self.term_use(val)),
            // The checked spellings: one annotation, no binder under it.
            Term::PairAt { ty, fst, snd } => self
                .opt_type_use(ty)
                .join(self.term_use(fst))
                .join(self.term_use(snd)),
            Term::VecLit { elem, zero, one, .. } => self
                .type_use(elem)
                .join(self.term_use(zero))
                .join(self.term_use(one)),
            // A loop, not a fold of joins: the node exists to be shallow.
            // A window past the array's start is an unfolded tail, met once
            // per element as a value comparison walks the vector, so it is
            // answered from the array's suffix joins ([`Walk::window_use`]).
            Term::VecItems { elem, items, from, .. } => {
                self.type_use(elem).join(self.window_use(items, *from))
            }
            Term::InlAt { ty, val: t } | Term::InrAt { ty, val: t } => {
                self.opt_type_use(ty).join(self.term_use(t))
            }
            Term::FstAt { pair: t } | Term::SndAt { pair: t } => self.term_use(t),
            Term::AppAt { fun, arg } => self.term_use(fun).join(self.term_use(arg)),
            Term::Case {
                lhs,
                rhs,
                motive,
                case_l,
                case_r,
                scrut,
                ..
            } => self
                .type_use(lhs)
                .join(self.type_use(rhs))
                .join(self.type_use(motive).under(1))
                .join(self.term_use(case_l).under(1))
                .join(self.term_use(case_r).under(1))
                .join(self.term_use(scrut)),
            Term::Sup {
                shape_ty,
                pos_ty,
                label,
                children,
                ..
            } => self
                .type_use(shape_ty)
                .join(self.type_use(pos_ty).under(1))
                .join(self.term_use(label))
                .join(self.term_use(children)),
            Term::ElimW {
                shape,
                pos,
                motive,
                step,
                scrut,
                ..
            } => self
                .type_use(shape)
                .join(self.type_use(pos).under(1))
                .join(self.type_use(motive).under(1))
                .join(self.term_use(step).under(3))
                .join(self.term_use(scrut)),
            Term::Supf {
                shape,
                arity,
                label,
                children,
                ..
            } => self
                .type_use(shape)
                .join(self.term_use(arity).under(1))
                .join(self.term_use(label))
                .join(self.term_use(children)),
            Term::ElimWf {
                shape,
                arity,
                motive,
                step,
                scrut,
                ..
            } => self
                .type_use(shape)
                .join(self.term_use(arity).under(1))
                .join(self.type_use(motive).under(1))
                .join(self.term_use(step).under(3))
                .join(self.term_use(scrut)),
            Term::Supi { sig, label, children } => self
                .iwf_sig_use(sig)
                .join(self.term_use(label))
                .join(self.term_use(children)),
            Term::ElimIWf { sig, motive, step, index, scrut, .. } => self
                .iwf_sig_use(sig)
                .join(self.type_use(motive).under(2))
                .join(self.term_use(step).under(3))
                .join(self.term_use(index))
                .join(self.term_use(scrut)),
            Term::Corec { sig, carrier, step, index, seed, .. } => self
                .m_sig_use(sig)
                .join(self.type_use(carrier).under(1))
                .join(self.term_use(step).under(2))
                .join(self.term_use(index))
                .join(self.term_use(seed)),
            Term::Out { sig, index, scrut } => self
                .m_sig_use(sig)
                .join(self.term_use(index))
                .join(self.term_use(scrut)),
            Term::Lam { dom, body, .. } => self.type_use(dom).join(self.term_use(body).under(1)),
            Term::App {
                fun, dom, cod, arg, ..
            } => self
                .term_use(fun)
                .join(self.type_use(dom))
                .join(self.type_use(cod).under(1))
                .join(self.term_use(arg)),
            Term::ULam { body, .. } => self.term_use(body),
            Term::UApp { fun, .. } => self.term_use(fun),
            Term::GlobalTm { subst, .. } => self.subst_use(subst),
            Term::CtxLam { body, .. } => self.term_use(body),
            Term::CtxApp { fun, .. } => self.term_use(fun),
            Term::TyLam { body, .. } => self.term_use(body),
            Term::TyApp { fun, .. } => self.term_use(fun),
            Term::LetBoxTy {
                motive,
                body,
                scrut,
                ..
            }
            | Term::LetBoxTm {
                motive,
                body,
                scrut,
                ..
            } => self
                .type_use(motive)
                .under(1)
                .join(self.term_use(body))
                .join(self.term_use(scrut)),
            Term::ElimCodeTy {
                motives,
                branches,
                scrut,
                ..
            }
            | Term::ElimCodeTm {
                motives,
                branches,
                scrut,
                ..
            } => self
                .motives_use(motives)
                .join(self.branches_use(branches))
                .join(self.term_use(scrut)),
        }
    }

    fn motives_use(&mut self, m: &Motives) -> LocalUse {
        self.type_use(&m.ty_motive)
            .under(1)
            .join(self.type_use(&m.tm_motive).under(1))
    }

    fn branches_use(&mut self, b: &Branches) -> LocalUse {
        LocalUse::CLOSED
            .join(self.term_use(&b.ty_nat))
            .join(self.term_use(&b.ty_pi).under(2))
            .join(self.term_use(&b.ty_ty))
            .join(self.term_use(&b.ty_el).under(1))
            .join(self.term_use(&b.ty_id).under(3))
            .join(self.term_use(&b.ty_sigma).under(2))
            .join(self.term_use(&b.ty_unit))
            .join(self.term_use(&b.ty_empty))
            .join(self.term_use(&b.tm_var))
            .join(self.term_use(&b.tm_nat))
            .join(self.term_use(&b.tm_pi).under(2))
            .join(self.term_use(&b.tm_ty))
            .join(self.term_use(&b.tm_zero))
            .join(self.term_use(&b.tm_succ).under(1))
            .join(self.term_use(&b.tm_elim_nat).under(4))
            .join(self.term_use(&b.tm_lam).under(2))
            .join(self.term_use(&b.tm_app).under(4))
            .join(self.term_use(&b.tm_id).under(3))
            .join(self.term_use(&b.tm_refl).under(2))
            .join(self.term_use(&b.tm_j).under(6))
            .join(self.term_use(&b.tm_sigma).under(2))
            .join(self.term_use(&b.tm_pair).under(4))
            .join(self.term_use(&b.tm_fst).under(3))
            .join(self.term_use(&b.tm_snd).under(3))
            .join(self.term_use(&b.tm_unit))
            .join(self.term_use(&b.tm_empty))
            .join(self.term_use(&b.tm_triv))
            .join(self.term_use(&b.tm_elim_empty).under(2))
            .join(self.term_use(&b.ty_sum).under(2))
            .join(self.term_use(&b.tm_sum).under(2))
            .join(self.term_use(&b.tm_inl).under(3))
            .join(self.term_use(&b.tm_inr).under(3))
            .join(self.term_use(&b.tm_case).under(6))
            .join(self.term_use(&b.ty_w).under(2))
            .join(self.term_use(&b.tm_w).under(2))
            .join(self.term_use(&b.tm_sup).under(4))
            .join(self.term_use(&b.tm_elim_w).under(5))
            .join(self.term_use(&b.ty_vec).under(2))
            .join(self.term_use(&b.tm_vec).under(2))
            .join(self.term_use(&b.ty_fin).under(1))
            .join(self.term_use(&b.tm_fin).under(1))
            .join(self.term_use(&b.ty_wf).under(2))
            .join(self.term_use(&b.tm_wf).under(2))
            .join(self.term_use(&b.tm_supf).under(4))
            .join(self.term_use(&b.tm_elim_wf).under(5))
            .join(self.term_use(&b.ty_seq).under(3))
            .join(self.term_use(&b.tm_seq).under(3))
            .join(self.term_use(&b.ty_sempty))
            .join(self.term_use(&b.tm_sempty))
            .join(self.term_use(&b.tm_srefl).under(2))
            .join(self.term_use(&b.tm_elim_sempty).under(2))
            .join(self.term_use(&b.ty_squash).under(1))
            .join(self.term_use(&b.tm_squash).under(1))
            .join(self.term_use(&b.tm_squash_in).under(2))
            .join(self.term_use(&b.tm_elim_squash).under(4))
            .join(self.term_use(&b.ty_m).under(5))
            .join(self.term_use(&b.tm_m).under(5))
            .join(self.term_use(&b.tm_corec).under(8))
            .join(self.term_use(&b.tm_out).under(6))
            .join(self.term_use(&b.ty_dvec).under(2))
            .join(self.term_use(&b.tm_dvec).under(2))
            .join(self.term_use(&b.ty_iwf).under(6))
            .join(self.term_use(&b.tm_iwf).under(6))
            .join(self.term_use(&b.tm_sup_i).under(7))
            .join(self.term_use(&b.tm_elim_iwf).under(9))
    }
}

// ---------------------------------------------------------------------------
// The global namespace
// ---------------------------------------------------------------------------
//
// The same idea one namespace out, for `shift_global` and `apply_global`
// (`issues/psi-references-by-level.md`). A reference to a committed binding
// is a **constant**, which neither operation changes (DESIGN.md, "Constants
// are addressed from the start of Ψ"), so what either can act on in a subtree
// is its free global **variables**: goals and metavariables while a
// declaration is elaborated, a `letbox`'s or a recursor branch's bound code
// inside meta-level terms. A committed statement or body has none, and
// neither does any type copied out of one, which is most of what the
// elaborator rescopes and zonks.
//
// What is cached is `1 +` the largest free global variable index, `0` for
// none: an operation at global binder depth `d` changes nothing when that
// is `<= d`. Unlike the local summary it reads *through* boxed code and the
// other-scope annotations, because the global operations do.
//
// It is kept in the node beside the local summary ([`crate::rc::Head`]),
// and is no part of it: the local summary's arithmetic is this file's own,
// while this one is computed by the traversal it serves
// (`subst::free_global_bound_*`: the generic walk with a mapper that only
// looks), so there is no second binder table to drift.
//
// The soundness argument is the local one's: a head describes the value
// beside it, and every skip taken is re-verified in debug builds against
// the real traversal (`sub_ty`/`sub_tm`).

thread_local! {
    /// Native depth of [`global_bound_term`]'s recursion through the
    /// traversal: past [`crate::term::SPINE_ITERATE_AT`] a node's spine is
    /// answered from the bottom up first, as [`Walk::warm_spine`] does.
    static GLOBAL_DEPTH: std::cell::Cell<u32> = const { std::cell::Cell::new(0) };
}

/// A term whose bound needs no table: no reference at all, or exactly one.
fn global_leaf_term(t: &Term) -> Option<u32> {
    match t {
        Term::Var(_)
        | Term::TmNat
        | Term::TmTy(_)
        | Term::TmUnit { .. }
        | Term::TmEmpty { .. }
        | Term::TmSEmpty { .. }
        | Term::Zero
        | Term::NatLit(_)
        | Term::Triv { .. } => Some(0),
        // `u^·`, what a mention of a top-level definition is.
        Term::GlobalTm { var, subst: LocalSubst { tail: SubstTail::Empty, terms } } if terms.is_empty() => {
            Some(var.rescope())
        }
        _ => None,
    }
}

fn global_leaf_type(t: &Type) -> Option<u32> {
    match t {
        Type::Nat | Type::Ty(_) | Type::Unit { .. } | Type::Empty { .. } | Type::SEmpty { .. } => Some(0),
        _ => None,
    }
}

/// `1 +` the largest global variable free in `t`, `0` when it has none
/// (constants are not variables).
pub(crate) fn global_bound_term(t: &Rc<Term>) -> u32 {
    if let Some(b) = global_leaf_term(t) {
        return b;
    }
    if let Some(b) = Rc::head(t).global() {
        return b;
    }
    let depth = GLOBAL_DEPTH.with(|d| d.get());
    if depth >= crate::term::SPINE_ITERATE_AT {
        // The spine below `t`, bottom up, so the walk of each node meets an
        // answer one level down (docs/kernel/deep-term-walks-design.md).
        let mut path = Vec::new();
        let mut cur = crate::term::spine_child(t);
        while let Some(c) = cur {
            if global_leaf_term(c).is_some() || Rc::head(c).global().is_some() {
                break;
            }
            path.push(Rc::clone(c));
            cur = crate::term::spine_child(c);
        }
        GLOBAL_DEPTH.with(|d| d.set(0));
        for node in path.iter().rev() {
            global_bound_term(node);
        }
        GLOBAL_DEPTH.with(|d| d.set(depth));
    }
    GLOBAL_DEPTH.with(|d| d.set(depth + 1));
    // The walk asks about the node's children through this same function.
    let b = crate::subst::free_global_bound_term(t);
    GLOBAL_DEPTH.with(|d| d.set(depth));
    Rc::head(t).set_global(b);
    b
}

/// [`global_bound_term`] for a type.
pub(crate) fn global_bound_type(t: &Rc<Type>) -> u32 {
    if let Some(b) = global_leaf_type(t) {
        return b;
    }
    if let Some(b) = Rc::head(t).global() {
        return b;
    }
    let depth = GLOBAL_DEPTH.with(|d| d.replace(d.get() + 1));
    let b = crate::subst::free_global_bound_type(t);
    GLOBAL_DEPTH.with(|d| d.set(depth));
    Rc::head(t).set_global(b);
    b
}

/// Should a global-namespace operation at global binder depth `d` skip this
/// subtree?
#[inline]
pub(crate) fn skip_global_term(t: &Rc<Term>, d: u32) -> bool {
    global_bound_term(t) <= d
}

/// [`skip_global_term`] for a type.
#[inline]
pub(crate) fn skip_global_type(t: &Rc<Type>, d: u32) -> bool {
    global_bound_type(t) <= d
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::level::Level;
    use crate::term::{GlobalVar, LocalVar, SubstTail};

    fn term_use(t: &Rc<Term>) -> LocalUse {
        Walk::new().term_use(t)
    }

    fn type_use(t: &Rc<Type>) -> LocalUse {
        Walk::new().type_use(t)
    }

    fn rt(t: Term) -> Rc<Term> {
        Rc::new(t)
    }

    fn v(i: u32) -> Rc<Term> {
        rt(Term::Var(LocalVar(i)))
    }

    #[test]
    fn var_and_leaves() {
        assert_eq!(
            term_use(&v(0)),
            LocalUse {
                bound: 1,
                has_wk: false,
                uses: 1
            }
        );
        assert_eq!(
            term_use(&v(4)),
            LocalUse {
                bound: 5,
                has_wk: false,
                uses: 1 << 4
            }
        );
        assert_eq!(term_use(&rt(Term::Zero)), LocalUse::CLOSED);
        assert_eq!(type_use(&Rc::new(Type::Nat)), LocalUse::CLOSED);
    }

    #[test]
    fn vec_items_windows_are_their_elements_joins() {
        // Every window of an array with open elements scattered through it,
        // asked in a comparison's order (from the front, one on each time)
        // and then out of order, against the plain join of its elements:
        // the stored suffix joins and the stride's remainder must agree with
        // walking the window, at every offset from a stride boundary.
        let n = 5 * WINDOW_STRIDE + 7;
        let items: Arc<[Rc<Term>]> = (0..n)
            .map(|j| match j % 41 {
                0 => v(j as u32 % 70),
                _ => rt(Term::Zero),
            })
            .collect::<Vec<_>>()
            .into();
        let node = |from: u32| {
            rt(Term::VecItems {
                level: Level::Zero,
                elem: Rc::new(Type::Nat),
                items: Arc::clone(&items),
                from,
            })
        };
        let direct = |from: usize| {
            items[from..].iter().fold(LocalUse::CLOSED, |a, t| a.join(term_use(t)))
        };
        let mut c = Walk::new();
        let order = (0..n).chain((0..n).rev().step_by(3));
        for from in order {
            assert_eq!(c.term_use(&node(from as u32)), direct(from), "window from {from}");
        }
    }

    #[test]
    fn binders_lower_the_bound() {
        // λ(x : Nat). x — locally closed; λ(x : Nat). y (Var 1) — one free.
        let lam = |body| {
            rt(Term::Lam {
                dom_level: Level::Zero,
                cod_level: Level::Zero,
                dom: Rc::new(Type::Nat),
                body,
            })
        };
        assert_eq!(term_use(&lam(v(0))), LocalUse::CLOSED);
        assert_eq!(
            term_use(&lam(v(1))),
            LocalUse {
                bound: 1,
                has_wk: false,
                uses: 1
            }
        );

        // elim_Nat's step binds two.
        let elim = |step| {
            rt(Term::ElimNat {
                level: Level::Zero,
                motive: Rc::new(Type::Nat),
                base: rt(Term::Zero),
                step,
                scrut: rt(Term::Zero),
            })
        };
        assert_eq!(term_use(&elim(v(1))), LocalUse::CLOSED);
        assert_eq!(
            term_use(&elim(v(2))),
            LocalUse {
                bound: 1,
                has_wk: false,
                uses: 1
            }
        );
    }

    #[test]
    fn wf_arity_binds_one() {
        let wf = |arity| {
            Rc::new(Type::Wf {
                level: Level::Zero,
                shape: Rc::new(Type::Nat),
                arity,
            })
        };
        assert_eq!(type_use(&wf(v(0))), LocalUse::CLOSED);
        assert_eq!(
            type_use(&wf(v(1))),
            LocalUse {
                bound: 1,
                has_wk: false,
                uses: 1
            }
        );
    }

    #[test]
    fn uses_names_the_innermost_indices() {
        // elim_Nat's step over `k, ih` reading an outer variable only:
        // neither binder occurs, though `bound` counts past both.
        let outer = rt(Term::Succ(v(2)));
        assert!(term_use(&outer).bound == 3 && term_use(&outer).uses == 1 << 2);
        assert!(ignores_innermost(&outer, 2));
        // Reading `k` (index 1) but not `ih` (index 0).
        let k_only = rt(Term::Succ(v(1)));
        assert!(ignores_innermost(&k_only, 1) && !ignores_innermost(&k_only, 2));
        // Under a binder the indices move down by one.
        let lam = rt(Term::Lam {
            dom_level: Level::Zero,
            cod_level: Level::Zero,
            dom: Rc::new(Type::Nat),
            body: v(1),
        });
        assert!(!ignores_innermost(&lam, 1));
        // Past the mask an index is counted by `bound` alone.
        assert_eq!(term_use(&v(USES_BITS - 1)).uses, 1 << (USES_BITS - 1));
        assert_eq!(term_use(&v(USES_BITS)).uses, 0);
        assert_eq!(term_use(&v(70)).uses, 0);
    }

    #[test]
    fn boxes_are_another_scope() {
        assert_eq!(term_use(&rt(Term::BoxTm(v(7)))), LocalUse::CLOSED);
    }

    #[test]
    fn only_a_weakening_tail_shows() {
        let global = |tail| {
            rt(Term::GlobalTm { var: GlobalVar::index(0), subst: LocalSubst { tail, terms: vec![v(2)] } })
        };
        // The empty tail records nothing: the reference is its payloads.
        assert_eq!(
            term_use(&global(SubstTail::Empty)),
            LocalUse {
                bound: 3,
                has_wk: false,
                uses: 1 << 2
            }
        );
        // A weakening counts the binders it sits under.
        assert_eq!(
            term_use(&global(SubstTail::Wk { len: 3, ctx_var: GlobalVar::index(1) })),
            LocalUse {
                bound: 3,
                has_wk: true,
                uses: 1 << 2
            }
        );
    }

    #[test]
    fn an_answer_is_stable_across_queries() {
        let t = rt(Term::Succ(v(3)));
        assert_eq!(term_use(&t), term_use(&t));
        assert_eq!(
            term_use(&t),
            LocalUse {
                bound: 4,
                has_wk: false,
                uses: 1 << 3
            }
        );
    }

    /// The first question leaves its answer in the node and in every node
    /// of the subtree it walked, so the next question about any of them is
    /// a read.
    #[test]
    fn an_answer_is_kept_in_every_node_it_walked() {
        let inner = rt(Term::Succ(v(3)));
        let t = rt(Term::Succ(Rc::clone(&inner)));
        assert_eq!(known(&t), None);
        assert_eq!(known(&inner), None);
        let u = term_local_use(&t);
        assert_eq!(known(&t), Some(u));
        assert_eq!(known(&inner), Some(u));
        // The global bound is another question, with its own answer.
        assert_eq!(Rc::head(&t).global(), None);
        assert_eq!(global_bound_term(&t), 0);
        assert_eq!(Rc::head(&t).global(), Some(0));
        assert_eq!(known(&t), Some(u));
    }

    /// A skip is decided at first sight: there is no second query to wait
    /// for, so what a traversal skips is a function of the term.
    #[test]
    fn a_fresh_node_is_skipped_at_its_first_question() {
        let closed = rt(Term::Succ(rt(Term::Succ(rt(Term::Zero)))));
        assert!(skip_term(&closed, 0));
        let open = rt(Term::Succ(v(2)));
        assert!(!skip_term(&open, 2));
        assert!(skip_term(&open, 3));
        assert!(skip_global_term(&closed, 0));
    }

    /// A node changed in place is asked again: the pointer empties the head
    /// before it hands the value out (`rc.rs`).
    #[test]
    fn a_changed_node_is_answered_afresh() {
        let mut t = rt(Term::Succ(v(3)));
        assert_eq!(term_local_use(&t).bound, 4);
        *Rc::make_mut(&mut t) = Term::Succ(v(0));
        assert_eq!(known(&t), None);
        assert_eq!(term_local_use(&t).bound, 1);
    }
}
