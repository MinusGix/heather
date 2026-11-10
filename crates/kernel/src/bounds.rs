//! Per-node free-variable bounds for the **local** namespace, memoized by
//! subtree identity, so the local-namespace traversals (`SubstLocal`,
//! `ShiftLocal` in `subst.rs`) can return a subtree that provably cannot
//! change in O(1) instead of walking it to discover it was shareable
//! (issues/subst-visits-closed-subtrees.md, route B).
//!
//! ## What is cached
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
//! ## Why a memo table and not a field on the node
//!
//! Storing the bound at construction would make it an invariant of every
//! construction site in this crate *and* in `elab` — the trusted-base
//! spread the issue defers route B over. Here the metadata is instead a
//! **pure function of the immutable term**, computed on first demand and
//! memoized; no constructor anywhere maintains anything, and the whole
//! trusted surface is this file's arithmetic (whose binder counts must
//! mirror `subst.rs`'s dep table — the one drift hazard, see below).
//!
//! ## Why pointer keying is sound
//!
//! The memo key is the subtree's `Rc` address. Terms have no interior
//! mutability (DESIGN.md §Representation), so a given allocation's contents
//! never change while it is alive; and each entry holds a [`Weak`] reference
//! to its key, which keeps the *allocation* from being freed — so its
//! address cannot be recycled — while the entry lives, without keeping the
//! contents (or the subtree below them) alive. Every query comes from a
//! caller holding a strong `Rc` to the node, so an address match names a
//! live allocation the entry was computed from, and a hit always describes
//! exactly the queried term (the full argument is on `Slot`). The table is
//! thread-local (terms are `Rc`, single-threaded by construction),
//! fixed-size and direct-mapped; a colliding insert evicts, which costs only
//! recomputation.
//!
//! ## How wrong bounds are caught
//!
//! A wrong bound is a silently wrong substitution — a soundness bug, the
//! reason route B was deferred. The defense is the same one the sharing
//! counter uses: every skip taken on this metadata is re-verified in debug
//! builds by running the real traversal and asserting it was a no-op
//! (`sub_ty`/`sub_tm` in subst.rs), and the test suite runs in the dev
//! profile — including the 300-seed substitution laws over generated terms
//! covering every variant. A binder count here that drifts from the
//! traversal's dep table fails those tests; it cannot silently ship.

use std::cell::RefCell;
use std::sync::Arc as Rc;
use std::sync::Weak;

use crate::term::{Branches, IWfSig, LocalSubst, MSig, Motives, SubstTail, Term, Type};

/// What a subtree exposes to local-namespace operations, relative to its
/// own root. See the module docs for the two components.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct LocalUse {
    pub bound: u32,
    pub has_wk: bool,
    /// Bit `i` set when the free index `i` occurs, for `i < 64` (larger
    /// indices are counted by `bound` alone). No substitution reads it: it
    /// answers [`ignores_innermost`], a question about cost.
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

/// The memo: two fixed-size direct-mapped caches, one per sort. A slot's
/// key is a [`Weak`] reference to the node it describes (compared by
/// address), which pins the node's *allocation* but not its contents; a
/// colliding insert evicts, which costs only recomputation (usually cheap —
/// the evictee's children are still cached). Fixed size means no growth, no
/// rehash, and no flush policy, and it bounds table memory and how many dead
/// allocations the keys can pin (one node each, never a subtree).
///
/// **Why the key is weak.** A strong keep-alive (the design until
/// 2026-11-02) made the table the last owner of every dead subtree it had
/// seen, so a colliding insert paid for the evictee's whole cascading free —
/// cold memory, pinned since its last query — and the data-oriented survey
/// found that eviction drop at about half of all samples under this file on
/// cold library checks (`issues/bounds-metadata-taxes-one-shot-checking.md`).
/// A weak key lets a dead term free where it dies, while still warm; the
/// eviction is one decrement of a weak count and, at most, one block's
/// deallocation. It also stops the table inflating `Rc::strong_count`,
/// which the substitution memo and `syntax_eq` read as "reachable twice".
///
/// A slot also carries the two-stage marker, so a probe touches one cache
/// line, not two parallel tables.
///
/// Memoization is **two-stage**: a query's first miss stores only a marker
/// (a bare address, no reference), and the bounds are computed when the
/// same address is queried again. This is what keeps the metadata from taxing one-shot terms — an
/// elaborated declaration is built, checked once, and dropped, and paying a
/// bounds walk plus a table entry per node there bought nothing (measured
/// 1.5–2× on `code/check-identity-recursor`, whose fresh telescopes are
/// exactly that shape, for either an eager-compute or `HashMap` variant).
/// The subtrees skips actually help are the ones traversed over and over
/// (an eliminator's step body, a schema's annotations), and those reach
/// their second query within two reduction steps; a marker that gets
/// computed then covers its whole subtree, because the recursive compute
/// ([`Cache::term_use`]) stores unconditionally — stability propagates down.
struct Cache {
    terms: Vec<Slot<Term>>,
    types: Vec<Slot<Type>>,
    /// Native depth of [`Cache::term_use`]'s recursion: past
    /// [`crate::term::SPINE_ITERATE_AT`] a node's spine is computed from the
    /// bottom up first ([`Cache::warm_spine`]).
    depth: u32,
    /// Suffix joins of the item arrays whose tail windows were asked about
    /// ([`Cache::window_use`]).
    windows: Vec<WindowSlot>,
}

/// One item array's suffix joins at a stride, under a weak key to the array
/// (the [`Slot`] argument: the key pins the allocation, so an address match
/// names the array the joins were computed from, whose contents cannot have
/// changed). `suffix[k]` is the join of `items[k * WINDOW_STRIDE..]`.
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

/// log2 of [`WindowSlot`]s per cache.
const WINDOW_BITS: u32 = 6;

/// One direct-mapped entry: the memoized answer under a weak key, and the
/// two-stage marker, side by side so a probe reads one cache line.
///
/// Soundness of the weak key: a caller asks about a node it holds by a
/// strong `Rc`, so the allocation is live; the key pins its own allocation,
/// so no other node can occupy that address while the key lives. An address
/// match therefore names the same allocation the answer was computed from,
/// and an allocation's contents never change while any strong reference
/// exists (no interior mutability, DESIGN.md §Representation) — nor can its
/// strong count climb back from zero. So a hit always describes exactly the
/// queried term. Contents dropped behind a key are never read: the key is
/// only ever compared, never upgraded.
#[repr(align(32))]
struct Slot<T> {
    key: Option<Weak<T>>,
    used: LocalUse,
    /// The two-stage marker: a bare address, or 0.
    mark: usize,
}

impl<T> Slot<T> {
    fn empty() -> Slot<T> {
        Slot {
            key: None,
            used: LocalUse::CLOSED,
            mark: 0,
        }
    }

    /// The memoized answer, when the key is `t`'s own allocation.
    fn hit(&self, t: &Rc<T>) -> Option<LocalUse> {
        match &self.key {
            Some(k) if std::ptr::eq(k.as_ptr(), Rc::as_ptr(t)) => Some(self.used),
            _ => None,
        }
    }

    fn store(&mut self, t: &Rc<T>, u: LocalUse) {
        self.key = Some(Rc::downgrade(t));
        self.used = u;
    }
}

/// log2 of the slot count per sort. 2^16 slots × 32 bytes × 2 sorts = 4 MiB.
const BITS: u32 = 16;

fn slot(p: usize) -> usize {
    // Fibonacci hashing; the top bits are the well-mixed ones.
    ((p as u64).wrapping_mul(0x9E37_79B9_7F4A_7C15) >> (64 - BITS)) as usize
}

impl Cache {
    fn new() -> Cache {
        Cache {
            terms: (0..1 << BITS).map(|_| Slot::empty()).collect(),
            types: (0..1 << BITS).map(|_| Slot::empty()).collect(),
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
    /// ordinary walk of a literal asks, is the node's own memo entry and is
    /// walked directly: an array gets suffix joins only when a tail is
    /// asked about, and only when it is long enough for them to pay.
    fn window_use(&mut self, items: &Rc<[Rc<Term>]>, from: u32) -> LocalUse {
        let from = from as usize;
        let live = items.get(from..).unwrap_or(&[]);
        if from == 0 || live.len() < 2 * WINDOW_STRIDE {
            let mut used = LocalUse::CLOSED;
            for item in live {
                used = used.join(self.term_use(item));
            }
            return used;
        }
        let p = Rc::as_ptr(items).cast::<()>() as usize;
        let i = slot(p) >> (BITS - WINDOW_BITS);
        let hit = matches!(&self.windows[i].key, Some(k) if std::ptr::eq(k.as_ptr().cast::<()>(), Rc::as_ptr(items).cast::<()>()));
        if !hit {
            // From the back, so each stored join is one stride's joins on
            // the next; the elements' own answers come from the term table.
            let mut suffix = vec![LocalUse::CLOSED; items.len().div_ceil(WINDOW_STRIDE)];
            let mut used = LocalUse::CLOSED;
            for (j, item) in items.iter().enumerate().rev() {
                used = used.join(self.term_use(item));
                if j % WINDOW_STRIDE == 0 {
                    suffix[j / WINDOW_STRIDE] = used;
                }
            }
            self.windows[i] = WindowSlot { key: Some(Rc::downgrade(items)), suffix: suffix.into() };
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
        match &**t {
            Term::Var(v) => {
                return LocalUse {
                    bound: v.0.saturating_add(1),
                    has_wk: false,
                    uses: var_bit(v.0),
                }
            }
            Term::TmNat
            | Term::TmTy(_)
            | Term::TmUnit { .. }
            | Term::TmEmpty { .. }
            | Term::TmSEmpty { .. }
            | Term::Zero
            | Term::NatLit(_)
            | Term::Triv { .. }
            | Term::BoxTy(_)
            | Term::BoxTm(_) => return LocalUse::CLOSED,
            _ => {}
        }
        let i = slot(Rc::as_ptr(t) as usize);
        if let Some(u) = self.terms[i].hit(t) {
            return u;
        }
        if self.depth >= crate::term::SPINE_ITERATE_AT {
            self.warm_spine(t);
            if let Some(u) = self.terms[i].hit(t) {
                return u;
            }
        }
        self.depth += 1;
        let u = self.compute_term(t);
        self.depth -= 1;
        self.terms[i].store(t, u);
        u
    }

    /// A deep node's spine answered from the bottom up, so the recursion
    /// that follows meets a stored answer one level down instead of walking
    /// the chain one native frame per node (docs/deep-term-walks-design.md).
    /// Each node below `t` is computed with the depth reset: its own spine
    /// child is already stored, so it recurses a level or two. A collision
    /// that evicted that child costs one more level, never the chain.
    fn warm_spine(&mut self, t: &Rc<Term>) {
        let mut path = Vec::new();
        let mut cur = crate::term::spine_child(t);
        while let Some(c) = cur {
            if self.terms[slot(Rc::as_ptr(c) as usize)].hit(c).is_some() {
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

    /// Two-stage query (see the [`Cache`] docs): `None` means "not seen
    /// twice yet — walk it", and leaves a marker behind. The marker is a
    /// bare address, deliberately: it carries no value, so a later node
    /// reusing the address at worst promotes itself one stage early and
    /// gets bounds computed from the live node — never a stale answer —
    /// and storing it costs no refcount traffic and pins nothing.
    fn term_query(&mut self, t: &Rc<Term>) -> Option<LocalUse> {
        let p = Rc::as_ptr(t) as usize;
        let i = slot(p);
        let s = &mut self.terms[i];
        if let Some(u) = s.hit(t) {
            return Some(u);
        }
        if s.mark == p {
            Some(self.term_use(t))
        } else {
            s.mark = p;
            None
        }
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
        match &**t {
            Type::Nat
            | Type::Ty(_)
            | Type::Unit { .. }
            | Type::Empty { .. }
            | Type::SEmpty { .. }
            | Type::CodeTy { .. }
            | Type::CodeTm { .. } => return LocalUse::CLOSED,
            _ => {}
        }
        let i = slot(Rc::as_ptr(t) as usize);
        if let Some(u) = self.types[i].hit(t) {
            return u;
        }
        let u = self.compute_type(t);
        self.types[i].store(t, u);
        u
    }

    fn type_query(&mut self, t: &Rc<Type>) -> Option<LocalUse> {
        let p = Rc::as_ptr(t) as usize;
        let i = slot(p);
        let s = &mut self.types[i];
        if let Some(u) = s.hit(t) {
            return Some(u);
        }
        if s.mark == p {
            Some(self.type_use(t))
        } else {
            s.mark = p;
            None
        }
    }
}

/// Bit `i` of [`LocalUse::uses`].
fn var_bit(i: u32) -> u64 {
    1u64.checked_shl(i).unwrap_or(0)
}

thread_local! {
    static CACHE: RefCell<Cache> = RefCell::new(Cache::new());
}

/// Captures read by evaluation of a syntactic closure. Weakening tails
/// depend on the ambient base/global shift, not on captured local values.
pub(crate) fn term_captures(t: &Rc<Term>) -> u32 {
    CACHE.with(|c| c.borrow_mut().term_use(t).bound)
}

pub(crate) fn type_captures(t: &Rc<Type>) -> u32 {
    CACHE.with(|c| c.borrow_mut().type_use(t).bound)
}

/// `t`'s local footprint: its bound and whether a weakening tail shows
/// in its local scope, for conversion's closure identity, which reads only
/// the captures a body uses (`conv/dom/values.rs`).
pub(crate) fn term_local_use(t: &Rc<Term>) -> LocalUse {
    CACHE.with(|c| c.borrow_mut().term_use(t))
}

pub(crate) fn type_local_use(t: &Rc<Type>) -> LocalUse {
    CACHE.with(|c| c.borrow_mut().type_use(t))
}

thread_local! {
    /// The typing memo's own table (`typing.rs` §The typing memo), apart from
    /// [`CACHE`]: the memo asks about every elimination it judges, and
    /// answering into the substitutions' table would settle their two-stage
    /// markers early, so which subtrees a substitution skips (and the
    /// `local_subst_nodes` it counts) would depend on what was judged
    /// before. The answers are the same pure function either way.
    static SCOPE_CACHE: RefCell<Cache> = RefCell::new(Cache::new());
}

/// [`term_local_use`] for the typing memo's strengthened scope: a node of
/// bound `k` with no weakening tail is judged by Γ's innermost `k` entries alone.
pub(crate) fn scope_term_use(t: &Rc<Term>) -> LocalUse {
    SCOPE_CACHE.with(|c| c.borrow_mut().term_use(t))
}

pub(crate) fn scope_type_use(t: &Rc<Type>) -> LocalUse {
    SCOPE_CACHE.with(|c| c.borrow_mut().type_use(t))
}

/// [`scope_type_use`] for a type the caller holds by reference: the node
/// itself is walked, its children answered from the table.
pub(crate) fn scope_type_ref_use(t: &Type) -> LocalUse {
    SCOPE_CACHE.with(|c| c.borrow_mut().compute_type(t))
}

/// Whether a type is locally closed: no free local variable and no
/// weakening tail, so that it reads nothing of Γ and is the same syntax
/// under any binders. The one reader that is not a traversal is the
/// closed-type memo in `typing.rs` (`Tc::ty_check`), which judges a locally
/// closed type once whatever Γ it occurs in — so a wrong answer here is a
/// soundness bug there, as a wrong skip is in `subst.rs`. Always computed
/// (never the two-stage marker), so the answer is a function of the type.
pub(crate) fn type_locally_closed(t: &Rc<Type>) -> bool {
    CACHE.with(|c| {
        let u = c.borrow_mut().type_use(t);
        u.bound == 0 && !u.has_wk
    })
}

/// [`type_locally_closed`] for a type the caller holds by reference: the
/// node itself is walked, its children answered from the table. Read by the
/// closed-conversion memo (`Tc::conv_ty`), with the same stakes.
pub(crate) fn type_ref_locally_closed(t: &Type) -> bool {
    CACHE.with(|c| {
        let u = c.borrow_mut().compute_type(t);
        u.bound == 0 && !u.has_wk
    })
}

/// [`type_locally_closed`] for an `IWf` signature, which `Tc::iwf_sig_wf`
/// judges once whatever Γ it occurs in.
pub(crate) fn iwf_sig_locally_closed(sig: &IWfSig) -> bool {
    CACHE.with(|c| {
        let u = c.borrow_mut().iwf_sig_use(sig);
        u.bound == 0 && !u.has_wk
    })
}

/// Whether evaluating `t` reads none of its innermost `n` (< 64) local
/// variables: no free index below `n` occurs. A wrong answer costs time,
/// never a verdict (`eval/probe.rs`, the one reader).
pub(crate) fn ignores_innermost(t: &Rc<Term>, n: u32) -> bool {
    debug_assert!(n < 64);
    CACHE.with(|c| c.borrow_mut().term_use(t).uses & (var_bit(n) - 1) == 0)
}

/// Should a local-namespace operation at binder depth `d` skip this subtree?
///
/// The leaf cases are answered inline — recomputing them is cheaper than a
/// cache slot, and `box`ed code is a leaf here: its contents are another
/// local scope.
pub(crate) fn skip_term(t: &Rc<Term>, d: u32) -> bool {
    match &**t {
        Term::Var(v) => return v.0 < d,
        Term::TmNat
        | Term::TmTy(_)
        | Term::TmUnit { .. }
        | Term::TmEmpty { .. }
        | Term::TmSEmpty { .. }
        | Term::Zero
        | Term::Triv { .. }
        | Term::BoxTy(_)
        | Term::BoxTm(_) => return true,
        _ => {}
    }
    CACHE.with(|c| c.borrow_mut().term_query(t).is_some_and(|u| !u.touched_at(d)))
}

pub(crate) fn skip_type(t: &Rc<Type>, d: u32) -> bool {
    match &**t {
        Type::Nat
        | Type::Ty(_)
        | Type::Unit { .. }
        | Type::Empty { .. }
        | Type::SEmpty { .. }
        | Type::CodeTy { .. }
        | Type::CodeTm { .. } => return true,
        _ => {}
    }
    CACHE.with(|c| c.borrow_mut().type_query(t).is_some_and(|u| !u.touched_at(d)))
}

impl Cache {
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
            // answered from the array's suffix joins ([`Cache::window_use`]).
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
// It is a separate table from the local one on purpose. The two are asked
// about different nodes at different times (a zonk asks about a fresh
// elaborated term's library-typed annotations, a β-step about an
// eliminator's step body), so one slot serving both would settle each
// namespace's two-stage marker on the other's schedule; and the local
// summary's arithmetic is this file's own, while this one is computed by the
// traversal it serves (`subst::free_global_bound_*`: the generic walk with a
// mapper that only looks), so there is no second binder table to drift.
//
// The soundness argument is the local one's: weak keys pin the allocation, a
// hit describes the queried node, and every skip taken is re-verified in
// debug builds against the real traversal (`sub_ty`/`sub_tm`).

/// One direct-mapped entry of the global table: [`Slot`], with the bound in
/// place of a [`LocalUse`].
#[repr(align(32))]
struct GlobalSlot<T> {
    key: Option<Weak<T>>,
    bound: u32,
    /// The two-stage marker: a bare address, or 0.
    mark: usize,
}

impl<T> GlobalSlot<T> {
    fn empty() -> GlobalSlot<T> {
        GlobalSlot { key: None, bound: 0, mark: 0 }
    }

    fn hit(&self, t: &Rc<T>) -> Option<u32> {
        match &self.key {
            Some(k) if std::ptr::eq(k.as_ptr(), Rc::as_ptr(t)) => Some(self.bound),
            _ => None,
        }
    }
}

struct GlobalCache {
    terms: Vec<GlobalSlot<Term>>,
    types: Vec<GlobalSlot<Type>>,
}

thread_local! {
    static GLOBAL_CACHE: RefCell<GlobalCache> = RefCell::new(GlobalCache {
        terms: (0..1 << BITS).map(|_| GlobalSlot::empty()).collect(),
        types: (0..1 << BITS).map(|_| GlobalSlot::empty()).collect(),
    });
    /// Native depth of [`global_bound_term`]'s recursion through the
    /// traversal: past [`crate::term::SPINE_ITERATE_AT`] a node's spine is
    /// answered from the bottom up first, as [`Cache::warm_spine`] does.
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
/// (constants are not variables). Memoized unconditionally, like
/// [`Cache::term_use`]: this is the recursive compute, whose answers for a
/// subtree are what make its parent's cheap.
pub(crate) fn global_bound_term(t: &Rc<Term>) -> u32 {
    if let Some(b) = global_leaf_term(t) {
        return b;
    }
    let i = slot(Rc::as_ptr(t) as usize);
    let hit = |t: &Rc<Term>| GLOBAL_CACHE.with(|c| c.borrow().terms[slot(Rc::as_ptr(t) as usize)].hit(t));
    if let Some(b) = hit(t) {
        return b;
    }
    let depth = GLOBAL_DEPTH.with(|d| d.get());
    if depth >= crate::term::SPINE_ITERATE_AT {
        // The spine below `t`, bottom up, so the walk of each node meets a
        // stored answer one level down (docs/deep-term-walks-design.md).
        let mut path = Vec::new();
        let mut cur = crate::term::spine_child(t);
        while let Some(c) = cur {
            if global_leaf_term(c).is_some() || hit(c).is_some() {
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
        if let Some(b) = hit(t) {
            return b;
        }
    }
    GLOBAL_DEPTH.with(|d| d.set(depth + 1));
    // No borrow of the table is held across the walk: it asks about the
    // node's children through this same function.
    let b = crate::subst::free_global_bound_term(t);
    GLOBAL_DEPTH.with(|d| d.set(depth));
    GLOBAL_CACHE.with(|c| {
        let s = &mut c.borrow_mut().terms[i];
        s.key = Some(Rc::downgrade(t));
        s.bound = b;
    });
    b
}

/// [`global_bound_term`] for a type.
pub(crate) fn global_bound_type(t: &Rc<Type>) -> u32 {
    if let Some(b) = global_leaf_type(t) {
        return b;
    }
    let i = slot(Rc::as_ptr(t) as usize);
    if let Some(b) = GLOBAL_CACHE.with(|c| c.borrow().types[i].hit(t)) {
        return b;
    }
    let depth = GLOBAL_DEPTH.with(|d| d.replace(d.get() + 1));
    let b = crate::subst::free_global_bound_type(t);
    GLOBAL_DEPTH.with(|d| d.set(depth));
    GLOBAL_CACHE.with(|c| {
        let s = &mut c.borrow_mut().types[i];
        s.key = Some(Rc::downgrade(t));
        s.bound = b;
    });
    b
}

/// Should a global-namespace operation at global binder depth `d` skip this
/// subtree? Two-stage, as [`Cache::term_query`]: a node asked about once is
/// only marked, and walked by its caller.
pub(crate) fn skip_global_term(t: &Rc<Term>, d: u32) -> bool {
    if let Some(b) = global_leaf_term(t) {
        return b <= d;
    }
    let p = Rc::as_ptr(t) as usize;
    let seen = GLOBAL_CACHE.with(|c| {
        let s = &mut c.borrow_mut().terms[slot(p)];
        match s.hit(t) {
            Some(b) => Some(Some(b)),
            None if s.mark == p => Some(None),
            None => {
                s.mark = p;
                None
            }
        }
    });
    match seen {
        Some(Some(b)) => b <= d,
        Some(None) => global_bound_term(t) <= d,
        None => false,
    }
}

/// [`skip_global_term`] for a type.
pub(crate) fn skip_global_type(t: &Rc<Type>, d: u32) -> bool {
    if let Some(b) = global_leaf_type(t) {
        return b <= d;
    }
    let p = Rc::as_ptr(t) as usize;
    let seen = GLOBAL_CACHE.with(|c| {
        let s = &mut c.borrow_mut().types[slot(p)];
        match s.hit(t) {
            Some(b) => Some(Some(b)),
            None if s.mark == p => Some(None),
            None => {
                s.mark = p;
                None
            }
        }
    });
    match seen {
        Some(Some(b)) => b <= d,
        Some(None) => global_bound_type(t) <= d,
        None => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::level::Level;
    use crate::term::{GlobalVar, LocalVar, SubstTail};

    fn term_use(t: &Rc<Term>) -> LocalUse {
        Cache::new().term_use(t)
    }

    fn type_use(t: &Rc<Type>) -> LocalUse {
        Cache::new().type_use(t)
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
        let items: Rc<[Rc<Term>]> = (0..n)
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
                items: Rc::clone(&items),
                from,
            })
        };
        let direct = |from: usize| {
            items[from..].iter().fold(LocalUse::CLOSED, |a, t| a.join(term_use(t)))
        };
        let mut c = Cache::new();
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
        // Past 64 an index is counted by `bound` alone.
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
    fn memo_is_stable_across_queries() {
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
}
