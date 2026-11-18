//! The three substitution operations and three shifting operations of DeLaM
//! (docs/delam/05, §Substitution Operations), over the full syntax.
//!
//! All six are instances of one generic traversal ([`Mapper`]) that carries
//! the binder [`Depths`] for the three independent namespaces. The binder
//! bookkeeping (which field of which node is under which binders) therefore
//! exists in exactly one place.
//!
//! Scoping rules the traversal encodes, which the paper's named notation
//! leaves implicit:
//!
//! - Operations on the **local** namespace (`δ`, local shift) do not descend
//!   into subtrees that live in a *different* local context: boxed code,
//!   contextual-type components, context arguments, and the `ctx`/`ty`
//!   annotations of letbox/recursors (`box T [δ] = box T`).
//! - Operations on the **global** and **universe** namespaces descend
//!   everywhere — those contexts are shared across all local contexts.
//! - Inserting a `δ`-payload under binders weakens it in *all three*
//!   namespaces (the `T[δ, x/x]`-style notation hides these weakenings).
//! - Global substitution rewrites local-substitution *tails*: replacing `g`
//!   by a concrete context `Γ'` turns `wk^k_g` into the expanded weakening
//!   `wk^k_{Γ'}` (new tail plus one variable term per entry of `Γ'`), and
//!   leaves the empty tail `·` alone.
//!
//! ## Shifting by zero
//!
//! Every `shift_*` entry point returns `self.clone()` when `by == 0`, which
//! is an `Rc` bump of the root and keeps every subterm shared, instead of
//! rebuilding the whole tree to write the same indices back.
//!
//! **Why it is sound.** `t.shift_local(0) == t` and its two siblings are laws
//! this crate already property-tests over generated terms
//! (`tests/subst_laws.rs`, `shift_composition`), and they hold structurally,
//! not merely up to some equivalence: at `by = 0` each mapper's variable case
//! is `v ↦ v`, each `tail` case adds zero to a length or renumbers by zero,
//! and `Level::shift(0, _)` returns its level unchanged. The `_above` variants are the
//! same operation with a cutoff, and a cutoff only narrows *which* variables
//! move, so at `by = 0` they are identities too. So the fast path cannot be
//! distinguished from the traversal by any caller.
//!
//! **Why it matters.** `SubstLocal::local_var` weakens each payload in all
//! three namespaces at insertion, and at depth zero — the common case,
//! including every `elim_Nat`/`elim_Wf` β-step — all three weakenings are
//! identities. Without this guard a β-step deep-copies the term it
//! substitutes three times, which made `add n n` quadratic in `n`
//! (issues/subst-copies-payloads-at-depth-zero.md, measured by
//! `scripts/bench --filter nat`).
//!
//! What this does *not* fix: a payload inserted under `k > 0` binders still
//! costs a full copy, because that shift is real work. Making *that* cheap
//! needs a representation change (shift-annotated or hash-consed terms), a
//! kernel design decision to take deliberately and not as a follow-on.
//!
//! ## Sharing unchanged subtrees
//!
//! The traversal reports whether it *actually changed anything*, and a subtree
//! that came back unchanged is shared (`Rc::clone`) rather than rebuilt. That
//! matters because the typical substituted term is mostly untouched: a
//! generated recursor arm is closed type annotations (`Vec(Tree; 2)`, `Fin 2`,
//! a case motive) wrapped around a handful of variable occurrences, so
//! rebuilding all of it per β-step is most of the cost of running an
//! eliminator (issues/subst-rebuilds-unchanged-subterms.md).
//!
//! The mechanism is a change counter on the mapper. Each hook calls
//! [`Mapper::note`] when it returns something other than what it was given;
//! [`sub_ty`]/[`sub_tm`] (and the motive/branch bundles) compare the counter
//! before and after a child, and share when it has not moved.
//!
//! Two rules make this safe rather than clever:
//!
//! 1. **"Unchanged" propagates from the leaves.** A node is shared because
//!    nothing *below* it reported a change — never because two terms compared
//!    equal. Deciding no-ops by comparing terms would reintroduce the very
//!    walk being avoided, and would hide it: the bench would look fixed while
//!    `PartialEq` did the traversal.
//! 2. **Every claimed no-op is verified in debug builds.** `shared_ty`/
//!    `shared_tm` `debug_assert!` full structural equality, so a hook that
//!    forgets to `note()` — the one dangerous mistake here — fails the test
//!    suite (which runs in the dev profile, including the substitution laws
//!    over generated terms) instead of silently producing a wrong term in
//!    release. Over-reporting is merely slow, so hooks may be conservative;
//!    under-reporting is caught.
//!
//! ## Skipping closed subtrees
//!
//! Sharing alone still *visits* every node, building a temporary from
//! `Rc`-cloned children only to compare the counter and drop it — most of a
//! substitution's work is walking material that cannot change
//! (issues/subst-visits-closed-subtrees.md). So the **local** operations
//! skip that walk: before descending, [`sub_ty`]/[`sub_tm`] ask the mapper
//! ([`Mapper::skip_ty`]/[`Mapper::skip_tm`]) whether the subtree is provably
//! untouchable, and `ShiftLocal`/`SubstLocal` answer from per-node
//! free-variable bounds (`bounds.rs`: 1 + the largest free local index,
//! plus a "contains a substitution tail" flag — tails are rewritten even
//! when no variable moves). The bounds are a memoized pure function of the
//! immutable subtree, not a field maintained at construction sites, so no
//! invariant spreads to the rest of the kernel or to `elab`.
//!
//! The safety discipline is rule 2's, extended: a skip claims the whole
//! traversal is a no-op on that subtree, and **debug builds verify the
//! claim** by running the real traversal and asserting nothing changed. A
//! binder count in `bounds.rs` that drifts from this file's dep table fails
//! the test suite instead of silently producing a wrong term in release —
//! for the skips the suite takes (`issues/kernel-binder-count-tables.md`).
//!
//! The **global** operations skip on the same terms
//! (`issues/psi-references-by-level.md`). `ShiftGlobal` and `SubstGlobal`
//! act on free global *variables* and nothing else, a constant being named
//! from the start of Ψ, so a subtree with no free variable at or past the
//! operation's depth is its own image. That bound is kept like the local
//! one, in the node's head, but it is not a second copy of the dep table:
//! it is computed by this file's generic walk under a mapper that only looks
//! ([`GlobalBound`]). What it prunes is nearly everything those two
//! operations are applied to outside meta-level code, since a committed
//! statement or body mentions no variable at all.
//!
//! ## Keeping a shared DAG shared
//!
//! A subterm reachable along two paths (a `let` alias's value used twice,
//! `elab`'s `fan` shape in `issues/proof-let-substitution-cost.md`) is one
//! allocation, and a traversal that rebuilds it once per path turns a
//! shared DAG of `k` links into a tree of `2^k` nodes, and everything
//! downstream pays for it: the typing memo of
//! `issues/kernel-typing-memo-on-node-identity.md` cannot share what the
//! shift has already copied apart (`issues/subst-shared-node-memo.md`).
//!
//! So the pure operations memoize, **within one call**, the result for a
//! node by its address and the traversal's [`Depths`] ([`NodeMemo`]). The
//! result for a pure operation is a function of the subtree and the depths
//! alone, so a hit is exactly what walking it again would build, and the
//! second path gets the first path's `Rc`: the output is as shared as the
//! input. The memo is consulted only for nodes whose `Rc::strong_count`
//! is above one, since only those can be reached twice (the topmost node of
//! any repeated region has two parents). The count is a filter, never part
//! of the answer: a node counted shared that is visited once costs a table
//! entry and changes nothing else, so the memo changes allocation and work,
//! never syntax. Each entry holds a keep-alive clone of its key, so an
//! address cannot be reused while the memo lives; the entries are dropped
//! when the call returns.
//! A `Var` leaf is shared by construction ([`Term::var_rc`]), so the memo
//! is never asked about one. What it becomes is the mapper's own node for
//! that payload at that depth ([`Mapper::local_var`], [`Lifted`]): one node
//! along every path, and the substitution's own node wherever the payload
//! needs no lifting, so a payload keeps the identity (and the bounds, and
//! every memo entry keyed by it) that it had before it was substituted.
//!
//! Every mapper whose output depends on the node and depths alone opts in
//! ([`Mapper::memo`]): the global and universe operations as much as the
//! local ones, since one tree-walking pass anywhere loses the sharing for
//! everything after it (`elab` rescopes each committed body with
//! `shift_global_above` and `apply_global`). [`AbstractLocal`] does not:
//! it numbers occurrences in traversal order, and a selected rewrite must
//! see the `k`-th occurrence of a shared subterm as a different position
//! from the first. Nor do [`ReindexGlobal`] (a caller's callback per
//! variable), [`RootTerms`] and [`RebuildChecked`] (state per visit). Debug
//! builds re-run the real traversal behind a sample of hits, as for skips.

use crate::rc::Rc;

use crate::bounds;
use crate::rec;
use crate::few_map::FewMap;
use crate::level::Level;
use crate::term::{
    Branches, CtxBase, CtxEntries, CtxEntry, CtxShape, GlobalBinding, GlobalRef, GlobalVar, IWfSig, LocalCtx, MSig, LocalSubst, LocalVar, Motives,
    SubstTail, Term, Type,
};

/// Binder depths for the three namespaces at the current traversal point.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Hash)]
pub struct Depths {
    pub univ: u32,
    pub global: u32,
    pub local: u32,
}

impl std::ops::Add for Depths {
    type Output = Depths;
    fn add(self, o: Depths) -> Depths {
        Depths {
            univ: self.univ + o.univ,
            global: self.global + o.global,
            local: self.local + o.local,
        }
    }
}

/// Shorthand for a binder increment.
fn dep(univ: u32, global: u32, local: u32) -> Depths {
    Depths { univ, global, local }
}

/// A payload of a global substitution, matching the three binding forms.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum GlobalEntry {
    /// `Γ/g` — a local context for a context variable.
    Ctx(LocalCtx),
    /// `T/U` — a type, scoped in the binding's local context `Δ[σ]`.
    Ty(Rc<Type>),
    /// `t/u` — a term, scoped in the binding's local context `Δ[σ]`.
    Tm(Rc<Term>),
}

/// A global substitution `σ` in *instantiation form*: it substitutes the top
/// (innermost) `entries.len()` bindings of the target global context Ψ and
/// maps the rest identically, renumbering them down by `entries.len()`.
/// `entries[0]` is the payload for the *outermost* substituted binding; all
/// payloads are scoped in the source context (the prefix of Ψ), not
/// telescoped among each other.
///
/// The paper's total `σ : Ψ' ⊢ σ : Ψ` is recovered by taking the prefix
/// empty; the β-rules for letbox and the code recursors use `entries.len()`
/// of 1–5.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct GlobalSubst {
    pub entries: Vec<GlobalEntry>,
}

impl GlobalSubst {
    /// σ instantiating only the innermost binding.
    pub fn single(entry: GlobalEntry) -> GlobalSubst {
        GlobalSubst { entries: vec![entry] }
    }
}

/// The per-call memo of §Keeping a shared DAG shared: a shared node's
/// result at the depths it was reached at, and whether it differs from the
/// node (the change counter is replayed on a hit, so the parent shares or
/// rebuilds exactly as it would have). The first `Rc` of each entry is the
/// keep-alive for the address in its key.
///
/// Most calls record nothing, or one or two nodes, and a few record
/// thousands. So the tables are made at the first node recorded (a mapper
/// is built and dropped by every call, and a call that records nothing
/// should pay for no table), and each is a [`FewMap`]: a call that stays
/// small allocates nothing more and is dropped by dropping its entries,
/// where a pooled hash table would cost its largest call's capacity on every
/// call (`issues/per-call-memos-pay-table-capacity.md`).
#[derive(Default)]
struct NodeMemo {
    tables: Option<Box<NodeTables>>,
}

type Kept<T> = (Rc<T>, Rc<T>, bool);

#[derive(Default)]
struct NodeTables {
    terms: FewMap<(usize, Depths), Kept<Term>>,
    types: FewMap<(usize, Depths), Kept<Type>>,
}

impl NodeMemo {
    #[inline]
    fn term(&self, key: &(usize, Depths)) -> Option<&Kept<Term>> {
        self.tables.as_ref()?.terms.get(key)
    }
    #[inline]
    fn ty(&self, key: &(usize, Depths)) -> Option<&Kept<Type>> {
        self.tables.as_ref()?.types.get(key)
    }
    fn keep_term(&mut self, key: (usize, Depths), kept: Kept<Term>) {
        self.tables.get_or_insert_with(Box::default).terms.insert(key, kept);
    }
    fn keep_type(&mut self, key: (usize, Depths), kept: Kept<Type>) {
        self.tables.get_or_insert_with(Box::default).types.insert(key, kept);
    }
}

// ---------------------------------------------------------------------------
// Generic traversal
// ---------------------------------------------------------------------------

trait Mapper {
    /// True for operations acting on the local namespace. Such operations do
    /// not descend into other-local-scope subtrees (see module docs).
    const LOCAL_OP: bool;

    /// Name of the operation, for the change-reporting assertion only.
    const NAME: &'static str;

    /// The counter bumped per node visited, if any: `shift_global_nodes`
    /// for the global rescoping, whose cost is what the refl-theorem family
    /// pays and no fuel counter sees (`issues/refl-theorem-step-cost.md`),
    /// and `local_subst_nodes` for the local shift and substitutions, whose
    /// node count is the claim §Keeping a shared DAG shared makes.
    const COUNT_NODES: Option<fn(u64)> = None;

    /// Whether a skip this mapper takes ([`Self::skip_ty`], [`Self::skip_tm`])
    /// claims the walk would change nothing, which debug builds then verify
    /// by walking. Every mapper that builds a result says yes.
    #[cfg_attr(not(debug_assertions), allow(dead_code))]
    const VERIFY_SKIPS: bool = true;

    /// Count of *effective* changes this mapper has made — see
    /// §Sharing unchanged subtrees. Every hook below that returns something
    /// other than what it was given must [`Self::note`] it.
    fn changes(&mut self) -> &mut u64;

    /// Record that this mapper actually changed something.
    ///
    /// Over-reporting is safe (a subtree is rebuilt that could have been
    /// shared); under-reporting is not, and is what the `debug_assert!` in
    /// [`shared_ty`]/[`shared_tm`] exists to catch. When in doubt, note.
    fn note(&mut self) {
        *self.changes() += 1;
    }

    /// Report a mapped level, noting a change only if it really moved.
    /// Levels are inline or one shared join, so `==` here is an
    /// exact test at leaf-ish cost — unlike comparing terms, which is the one
    /// thing this design must never do.
    fn mapped(&mut self, new: Level, old: &Level) -> Level {
        if new != *old {
            self.note();
        }
        new
    }

    fn level(&mut self, l: &Level, _at: Depths) -> Level {
        l.clone()
    }
    /// What a local variable becomes, or `None` (the default) when it stays
    /// the variable it is. A `Some` is a change and is noted by the caller,
    /// as [`Self::pre_tm`]'s is. The node is used as it is given, so a
    /// mapper that hands out one node for one payload at one depth keeps
    /// every occurrence of a variable one node (§Keeping a shared DAG
    /// shared), and a payload that needs no lifting is the caller's own.
    fn local_var(&mut self, _v: LocalVar, _at: Depths) -> Option<Rc<Term>> {
        None
    }
    /// `U^δ`; `subst` has already been mapped.
    fn global_ty(&mut self, var: GlobalVar, subst: LocalSubst, _at: Depths) -> Type {
        Type::GlobalTy { var, subst }
    }
    /// `u^δ`; `subst` has already been mapped.
    fn global_tm(&mut self, var: GlobalVar, subst: LocalSubst, _at: Depths) -> Term {
        Term::GlobalTm { var, subst }
    }
    /// Base of a local context; the returned entries are spliced in front of
    /// the context's own (used by σ replacing `g` with a concrete context).
    fn ctx_base(&mut self, base: CtxBase, _at: Depths) -> (CtxBase, CtxEntries) {
        (base, CtxEntries::empty())
    }
    /// Tail of a local substitution; the returned terms are spliced in front
    /// of the substitution's own (used by σ expanding `wk^k_g`).
    fn tail(&mut self, tail: SubstTail, _at: Depths) -> (SubstTail, Vec<Rc<Term>>) {
        (tail, Vec::new())
    }

    /// Replace a whole **term** node, before its children are visited.
    /// `None` — the default — means "descend as usual", which is every
    /// mapper here but [`AbstractLocal`], whose pattern is a *term* rather
    /// than a variable and so cannot be expressed by [`Self::local_var`].
    /// A `Some` is noted by the caller, so a hook may be written without
    /// touching the change counter.
    fn pre_tm(&mut self, _t: &Rc<Term>, _at: Depths) -> Option<Term> {
        None
    }

    /// Whether this subtree provably cannot be changed by this mapper at
    /// these depths, decided in O(1) from cached per-node metadata
    /// (see §Skipping closed subtrees). `false` — the default — means
    /// "walk it and find out", never "changed". The local-namespace
    /// operations and the two global ones that act on variables alone opt
    /// in; every skip taken is re-verified against the real traversal in
    /// debug builds ([`sub_ty`]/[`sub_tm`]).
    fn skip_ty(&mut self, _t: &Rc<Type>, _at: Depths) -> bool {
        false
    }
    fn skip_tm(&mut self, _t: &Rc<Term>, _at: Depths) -> bool {
        false
    }

    /// This call's shared-node memo, for a mapper whose result on a subtree
    /// is a function of the subtree and the depths alone (§Keeping a shared
    /// DAG shared). `None` — the default — never memoizes, which is right
    /// for a mapper with any other state a visit reads or writes.
    fn memo(&mut self) -> Option<&mut NodeMemo> {
        None
    }
}

/// Reuse `orig` for a subtree the traversal did not change.
///
/// `mapped` is dropped: its children are `Rc` clones of `orig`'s, so building
/// it allocated nothing and dropping it is a handful of refcount decrements.
/// What is saved is the allocation *and* the eventual deep drop of a fresh
/// copy of the whole subtree.
///
/// The `debug_assert!` is the load-bearing part of the design: it verifies
/// every claimed no-op by full structural equality, in the profile the tests
/// run in. So an under-reported change — the one dangerous mistake a mapper
/// hook can make — fails the suite (the substitution laws included)
/// rather than silently producing a wrong term in release.
fn shared_ty<M: Mapper>(orig: &Rc<Type>, mapped: Type) -> Rc<Type> {
    debug_assert!(
        mapped == **orig,
        "{} reported no change but the type differs — a Mapper hook is missing a \
         `note()` (term output suppressed: see CLAUDE.md)",
        M::NAME
    );
    drop(mapped);
    Rc::clone(orig)
}

fn shared_tm<M: Mapper>(orig: &Rc<Term>, mapped: Term) -> Rc<Term> {
    debug_assert!(
        mapped == **orig,
        "{} reported no change but the term differs — a Mapper hook is missing a \
         `note()` (term output suppressed: see CLAUDE.md)",
        M::NAME
    );
    drop(mapped);
    Rc::clone(orig)
}

fn sub_ty<M: Mapper>(t: &Rc<Type>, m: &mut M, at: Depths) -> Rc<Type> {
    if let Some(count) = M::COUNT_NODES {
        count(1);
    }
    if !(M::VERIFY_SKIPS && crate::checks::unskipped()) && m.skip_ty(t, at) {
        // A skip claims the whole traversal is a no-op here. Verify the
        // claim in debug builds, exactly as shared_ty verifies the change
        // counter — at the level `checks` sets, because the whole cost of
        // the walk being skipped is paid again: the subtree is walked with
        // no skip taken inside it (`checks::rederive`).
        #[cfg(debug_assertions)]
        if M::VERIFY_SKIPS && crate::checks::verify_this_skip() {
            let before = *m.changes();
            let mapped = crate::checks::rederive(crate::checks::Claim::Skip, || map_type(t, m, at));
            assert!(
                *m.changes() == before && mapped == **t,
                "{} skipped a subtree it would have changed — bounds.rs disagrees with the \
                 traversal (term output suppressed: see CLAUDE.md)",
                M::NAME
            );
        }
        return Rc::clone(t);
    }
    // §Keeping a shared DAG shared: a node only one parent holds cannot be
    // reached twice, so only a shared one is looked up or recorded.
    let key = (Rc::as_ptr(t) as usize, at);
    let shared = Rc::strong_count(t) > 1 && m.memo().is_some();
    if shared {
        if let Some((_, out, changed)) = m.memo().and_then(|memo| memo.ty(&key)) {
            let (out, changed) = (Rc::clone(out), *changed);
            crate::stats::subst_memo_hits(1);
            #[cfg(debug_assertions)]
            if crate::checks::verify_this_skip() {
                let before = *m.changes();
                let again = crate::checks::rederive(crate::checks::Claim::Kept, || map_type(t, m, at));
                assert!(
                    (*m.changes() != before) == changed && again == *out,
                    "{} memoized a shared node's result that walking it again does not build \
                     (term output suppressed: see CLAUDE.md)",
                    M::NAME
                );
                *m.changes() = before;
            }
            if changed {
                m.note();
            }
            return out;
        }
    }
    let before = *m.changes();
    let mapped = map_type(t, m, at);
    let changed = *m.changes() != before;
    let out = if changed { Rc::new(mapped) } else { shared_ty::<M>(t, mapped) };
    if shared {
        if let Some(memo) = m.memo() {
            memo.keep_type(key, (Rc::clone(t), Rc::clone(&out), changed));
        }
    }
    out
}

/// An `IWf` signature (`docs/kernel/iwf-former-design.md` §1.2): `arity` and
/// `out` under `x : S`, `child` under `x, i`. Shared when nothing in it
/// changed, as [`sub_ty`]/[`sub_tm`] share a node.
fn sub_iwf_sig<M: Mapper>(sig: &Rc<IWfSig>, m: &mut M, at: Depths) -> Rc<IWfSig> {
    let before = *m.changes();
    let mapped = IWfSig {
        level: m.level(&sig.level, at),
        idx_level: m.level(&sig.idx_level, at),
        idx: sub_ty(&sig.idx, m, at),
        shape: sub_ty(&sig.shape, m, at),
        arity: sub_tm(&sig.arity, m, at + dep(0, 0, 1)),
        out: sub_tm(&sig.out, m, at + dep(0, 0, 1)),
        child: sub_tm(&sig.child, m, at + dep(0, 0, 2)),
    };
    if *m.changes() == before {
        Rc::clone(sig)
    } else {
        Rc::new(mapped)
    }
}

/// An `M` signature (`docs/kernel/kernel-coinduction-design.md` §1.1): `shape`
/// under `i`, `pos` under `i, s`, `next` under `i, s, p`. Shared when nothing
/// in it changed, as [`sub_iwf_sig`].
fn sub_m_sig<M: Mapper>(sig: &Rc<MSig>, m: &mut M, at: Depths) -> Rc<MSig> {
    let before = *m.changes();
    let mapped = MSig {
        level: m.level(&sig.level, at),
        pos_level: m.level(&sig.pos_level, at),
        idx_level: m.level(&sig.idx_level, at),
        idx: sub_ty(&sig.idx, m, at),
        shape: sub_ty(&sig.shape, m, at + dep(0, 0, 1)),
        pos: sub_ty(&sig.pos, m, at + dep(0, 0, 2)),
        next: sub_tm(&sig.next, m, at + dep(0, 0, 3)),
    };
    if *m.changes() == before {
        Rc::clone(sig)
    } else {
        Rc::new(mapped)
    }
}

thread_local! {
    /// Native depth of [`sub_tm`]: past [`crate::term::SPINE_ITERATE_AT`]
    /// a data spine is mapped by [`sub_tm_spine`]'s loop instead of one
    /// frame per node (docs/kernel/deep-term-walks-design.md).
    static SUB_DEPTH: std::cell::Cell<u32> = const { std::cell::Cell::new(0) };
}

fn sub_tm<M: Mapper>(t: &Rc<Term>, m: &mut M, at: Depths) -> Rc<Term> {
    if let Some(done) = sub_tm_answered(t, m, at) {
        return done;
    }
    let depth = SUB_DEPTH.with(|d| d.get());
    if depth >= crate::term::SPINE_ITERATE_AT && crate::term::spine_child(t).is_some() {
        return sub_tm_spine(t, m, at);
    }
    SUB_DEPTH.with(|d| d.set(depth + 1));
    let out = sub_tm_walked(t, m, at);
    SUB_DEPTH.with(|d| d.set(depth));
    out
}

/// [`sub_tm`]'s answers that take no walk of `t`'s children: a whole-node
/// replacement, a skipped subtree, a variable, a memoized shared node.
/// `None` means "walk it" ([`sub_tm_walked`]).
fn sub_tm_answered<M: Mapper>(t: &Rc<Term>, m: &mut M, at: Depths) -> Option<Rc<Term>> {
    if let Some(count) = M::COUNT_NODES {
        count(1);
    }
    // Whole-node replacement, before anything else: a mapper that matches
    // *terms* has to see a node before its children are rebuilt, and its
    // answer is by construction a change (rule 1's "over-reporting is safe"
    // does not even apply — the node really is different).
    if let Some(r) = m.pre_tm(t, at) {
        m.note();
        return Some(r.into_rc());
    }
    if !(M::VERIFY_SKIPS && crate::checks::unskipped()) && m.skip_tm(t, at) {
        #[cfg(debug_assertions)]
        if M::VERIFY_SKIPS && crate::checks::verify_this_skip() {
            let before = *m.changes();
            let mapped = crate::checks::rederive(crate::checks::Claim::Skip, || map_term(t, m, at));
            assert!(
                *m.changes() == before && mapped == **t,
                "{} skipped a subtree it would have changed — bounds.rs disagrees with the \
                 traversal (term output suppressed: see CLAUDE.md)",
                M::NAME
            );
        }
        return Some(Rc::clone(t));
    }
    // A variable is answered by the mapper and never by the memo: the leaf
    // is shared by construction (`Term::var_rc`), so its count says nothing
    // about a second path, and what it becomes is the mapper's node for
    // that payload at this depth ([`Mapper::local_var`]), the same along
    // every path.
    if let Term::Var(v) = **t {
        return Some(match m.local_var(v, at) {
            None => Rc::clone(t),
            Some(out) => {
                m.note();
                out
            }
        });
    }
    let key = (Rc::as_ptr(t) as usize, at);
    // As in `sub_ty`.
    let shared = Rc::strong_count(t) > 1 && m.memo().is_some();
    if shared {
        if let Some((_, out, changed)) = m.memo().and_then(|memo| memo.term(&key)) {
            let (out, changed) = (Rc::clone(out), *changed);
            crate::stats::subst_memo_hits(1);
            #[cfg(debug_assertions)]
            if crate::checks::verify_this_skip() {
                let before = *m.changes();
                let again = crate::checks::rederive(crate::checks::Claim::Kept, || map_term(t, m, at));
                assert!(
                    (*m.changes() != before) == changed && again == *out,
                    "{} memoized a shared node's result that walking it again does not build \
                     (term output suppressed: see CLAUDE.md)",
                    M::NAME
                );
                *m.changes() = before;
            }
            if changed {
                m.note();
            }
            return Some(out);
        }
    }
    None
}

/// [`sub_tm`] past its answers: map the children, keep `t` when nothing
/// changed, and memoize a shared node.
fn sub_tm_walked<M: Mapper>(t: &Rc<Term>, m: &mut M, at: Depths) -> Rc<Term> {
    let shared = Rc::strong_count(t) > 1;
    let before = *m.changes();
    let mapped = map_term(t, m, at);
    let changed = *m.changes() != before;
    sub_tm_settled(t, m, at, mapped, changed, shared)
}

/// The node `mapped` built for `t`: `t` itself when nothing changed, and
/// the memo's entry for a node that was shared (`strong_count > 1`) before
/// the walk.
fn sub_tm_settled<M: Mapper>(t: &Rc<Term>, m: &mut M, at: Depths, mapped: Term, changed: bool, shared: bool) -> Rc<Term> {
    let out = if changed { mapped.into_rc() } else { shared_tm::<M>(t, mapped) };
    if shared {
        if let Some(memo) = m.memo() {
            memo.keep_term((Rc::as_ptr(t) as usize, at), (Rc::clone(t), Rc::clone(&out), changed));
        }
    }
    out
}

/// A deep data spine mapped by a loop (docs/kernel/deep-term-walks-design.md):
/// down [`crate::term::spine_child`] while each node needs walking, the
/// bottom by an ordinary [`sub_tm`] at depth zero, then back up rebuilding
/// each node around its mapped child ([`map_spine_node`]). Every node gets
/// exactly [`sub_tm`]'s treatment — its answers on the way down, the
/// change test and memo on the way up — so the result is the recursion's;
/// only the order in which siblings are visited differs, and no mapper's
/// result depends on that.
#[inline(never)]
fn sub_tm_spine<M: Mapper>(t: &Rc<Term>, m: &mut M, at: Depths) -> Rc<Term> {
    let mut path = vec![Rc::clone(t)];
    let mut bottom = None;
    while bottom.is_none() {
        let last = path.last().expect("the path starts at t");
        let child = crate::term::spine_child(last).expect("only spine forms join the path");
        if let Some(done) = sub_tm_answered(child, m, at) {
            bottom = Some((done, false));
        } else if crate::term::spine_child(child).is_some() {
            let child = Rc::clone(child);
            path.push(child);
        } else {
            let child = Rc::clone(child);
            let depth = SUB_DEPTH.with(|d| d.replace(0));
            let before = *m.changes();
            let out = sub_tm_walked(&child, m, at);
            let changed = *m.changes() != before;
            SUB_DEPTH.with(|d| d.set(depth));
            bottom = Some((out, changed));
        }
    }
    let (mut acc, mut acc_changed) = bottom.expect("the loop ends at a bottom");
    // `acc_changed` is whether the mapped child differs from the original;
    // an answered child (a skip, a memo hit) reports through the counter,
    // so compare the nodes instead.
    let depth = SUB_DEPTH.with(|d| d.replace(0));
    let shared: Vec<bool> = path.iter().map(|node| Rc::strong_count(node) > 2).collect();
    for (node, shared) in path.iter().zip(shared).rev() {
        let child = crate::term::spine_child(node).expect("a spine form");
        acc_changed = acc_changed || !Rc::ptr_eq(&acc, child);
        let before = *m.changes();
        let mapped = map_spine_node(node, m, at, acc);
        let changed = acc_changed || *m.changes() != before;
        acc = sub_tm_settled(node, m, at, mapped, changed, shared);
        acc_changed = changed;
    }
    SUB_DEPTH.with(|d| d.set(depth));
    acc
}

/// [`map_term`]'s arm for a spine form, with the spine child already
/// mapped to `child`.
fn map_spine_node<M: Mapper>(t: &Term, m: &mut M, at: Depths, child: Rc<Term>) -> Term {
    let on_spine = |c: &Rc<Term>| crate::term::spine_child(t).is_some_and(|s| Rc::ptr_eq(s, c));
    let mut child = Some(child);
    let mut sub = |c: &Rc<Term>, m: &mut M| -> Rc<Term> {
        if on_spine(c) && child.is_some() {
            child.take().expect("checked")
        } else {
            sub_tm(c, m, at)
        }
    };
    match t {
        Term::Pair { fst_level, snd_level, fst_ty, snd_ty, fst, snd } => {
            let (fst_level, snd_level) = (m.level(fst_level, at), m.level(snd_level, at));
            let (fst_ty, snd_ty) = (sub_ty(fst_ty, m, at), sub_ty(snd_ty, m, at + dep(0, 0, 1)));
            let fst = sub(fst, m);
            let snd = sub(snd, m);
            Term::Pair { fst_level, snd_level, fst_ty, snd_ty, fst, snd }
        }
        Term::PairAt { ty, fst, snd } => {
            let ty = ty.as_ref().map(|t| sub_ty(t, m, at));
            let fst = sub(fst, m);
            let snd = sub(snd, m);
            Term::PairAt { ty, fst, snd }
        }
        Term::InlAt { ty, val } => Term::InlAt { ty: ty.as_ref().map(|t| sub_ty(t, m, at)), val: sub(val, m) },
        Term::InrAt { ty, val } => Term::InrAt { ty: ty.as_ref().map(|t| sub_ty(t, m, at)), val: sub(val, m) },
        Term::Inl { lhs_level, rhs_level, lhs, rhs, val } => Term::Inl {
            lhs_level: m.level(lhs_level, at),
            rhs_level: m.level(rhs_level, at),
            lhs: sub_ty(lhs, m, at),
            rhs: sub_ty(rhs, m, at),
            val: sub(val, m),
        },
        Term::Inr { lhs_level, rhs_level, lhs, rhs, val } => Term::Inr {
            lhs_level: m.level(lhs_level, at),
            rhs_level: m.level(rhs_level, at),
            lhs: sub_ty(lhs, m, at),
            rhs: sub_ty(rhs, m, at),
            val: sub(val, m),
        },
        Term::Supf { level, shape, arity, label, children } => {
            let level = m.level(level, at);
            let shape = sub_ty(shape, m, at);
            let arity = sub_tm(arity, m, at + dep(0, 0, 1));
            let label = sub(label, m);
            let children = sub(children, m);
            Term::Supf { level, shape, arity, label, children }
        }
        Term::Supi { sig, label, children } => {
            let sig = sub_iwf_sig(sig, m, at);
            let label = sub(label, m);
            let children = sub(children, m);
            Term::Supi { sig, label, children }
        }
        Term::Succ(n) => Term::Succ(sub(n, m)),
        Term::AppAt { fun, arg } => {
            let fun = sub(fun, m);
            let arg = sub(arg, m);
            Term::AppAt { fun, arg }
        }
        Term::App { fun, dom_level, cod_level, dom, cod, arg } => {
            let fun = sub(fun, m);
            let (dom_level, cod_level) = (m.level(dom_level, at), m.level(cod_level, at));
            let (dom, cod) = (sub_ty(dom, m, at), sub_ty(cod, m, at + dep(0, 0, 1)));
            let arg = sub(arg, m);
            Term::App { fun, dom_level, cod_level, dom, cod, arg }
        }
        _ => unreachable!("map_spine_node is given a spine form"),
    }
}

/// The motive/branch bundles of the code recursors, shared on the same rule.
/// Worth their own functions rather than being inlined: `Branches` is 65
/// terms under 65 telescopes, so sharing it unchanged is the single largest
/// saving in the traversal.
fn sub_motives<M: Mapper>(mo: &Rc<Motives>, m: &mut M, at: Depths) -> Rc<Motives> {
    let before = *m.changes();
    let mapped = map_motives(mo, m, at);
    if *m.changes() == before {
        debug_assert!(mapped == **mo, "{} reported no change but the motives differ", M::NAME);
        drop(mapped);
        Rc::clone(mo)
    } else {
        Rc::new(mapped)
    }
}

fn sub_branches<M: Mapper>(b: &Rc<Branches>, m: &mut M, at: Depths) -> Rc<Branches> {
    let before = *m.changes();
    let mapped = map_branches(b, m, at);
    if *m.changes() == before {
        debug_assert!(mapped == **b, "{} reported no change but the branches differ", M::NAME);
        drop(mapped);
        Rc::clone(b)
    } else {
        Rc::new(mapped)
    }
}

/// A type/term/context living in a *different* local context than the
/// traversal point (boxed code, contextual-type components, context
/// arguments, letbox/recursor annotations). Local operations leave these
/// untouched; other operations descend with the local depth reset (unused).
fn other_ty<M: Mapper>(t: &Rc<Type>, m: &mut M, at: Depths) -> Rc<Type> {
    if M::LOCAL_OP {
        Rc::clone(t)
    } else {
        sub_ty(t, m, Depths { local: 0, ..at })
    }
}

fn other_tm<M: Mapper>(t: &Rc<Term>, m: &mut M, at: Depths) -> Rc<Term> {
    if M::LOCAL_OP {
        Rc::clone(t)
    } else {
        sub_tm(t, m, Depths { local: 0, ..at })
    }
}

fn other_ctx<M: Mapper>(c: &LocalCtx, m: &mut M, at: Depths) -> LocalCtx {
    if M::LOCAL_OP {
        c.clone()
    } else {
        map_ctx(c, m, Depths { local: 0, ..at })
    }
}

fn map_type<M: Mapper>(t: &Type, m: &mut M, at: Depths) -> Type {
    match t {
        Type::Nat => Type::Nat,
        Type::Pi { dom_level, cod_level, dom, cod } => Type::Pi {
            dom_level: m.level(dom_level, at),
            cod_level: m.level(cod_level, at),
            dom: sub_ty(dom, m, at),
            cod: sub_ty(cod, m, at + dep(0, 0, 1)),
        },
        Type::Ty(l) => Type::Ty(m.level(l, at)),
        Type::UPi { num_vars, level, body } => Type::UPi {
            num_vars: *num_vars,
            level: m.level(level, at + dep(*num_vars, 0, 0)),
            body: sub_ty(body, m, at + dep(*num_vars, 0, 0)),
        },
        Type::El { level, tm } => Type::El {
            level: m.level(level, at),
            tm: sub_tm(tm, m, at),
        },
        Type::Id { level, ty, lhs, rhs } => Type::Id {
            level: m.level(level, at),
            ty: sub_ty(ty, m, at),
            lhs: sub_tm(lhs, m, at),
            rhs: sub_tm(rhs, m, at),
        },
        Type::SEq { level, ty, lhs, rhs } => Type::SEq {
            level: m.level(level, at),
            ty: sub_ty(ty, m, at),
            lhs: sub_tm(lhs, m, at),
            rhs: sub_tm(rhs, m, at),
        },
        Type::SEmpty { level } => Type::SEmpty { level: m.level(level, at) },
        Type::Squash { level, ty } => Type::Squash {
            level: m.level(level, at),
            ty: sub_ty(ty, m, at),
        },
        Type::Sigma { fst_level, snd_level, fst, snd } => Type::Sigma {
            fst_level: m.level(fst_level, at),
            snd_level: m.level(snd_level, at),
            fst: sub_ty(fst, m, at),
            snd: sub_ty(snd, m, at + dep(0, 0, 1)),
        },
        Type::Unit { level } => Type::Unit { level: m.level(level, at) },
        Type::Empty { level } => Type::Empty { level: m.level(level, at) },
        Type::Sum { lhs_level, rhs_level, lhs, rhs } => Type::Sum {
            lhs_level: m.level(lhs_level, at),
            rhs_level: m.level(rhs_level, at),
            lhs: sub_ty(lhs, m, at),
            rhs: sub_ty(rhs, m, at),
        },
        // Vec/Fin (extension): the length is a *term* in Γ, so it takes the
        // same depth as the element type — no binder anywhere.
        Type::Vec { level, elem, len } => Type::Vec {
            level: m.level(level, at),
            elem: sub_ty(elem, m, at),
            len: sub_tm(len, m, at),
        },
        Type::Fin { len } => Type::Fin { len: sub_tm(len, m, at) },
        // Wf: `arity` is a term under the shape binder `x : S`.
        Type::Wf { level, shape, arity } => Type::Wf {
            level: m.level(level, at),
            shape: sub_ty(shape, m, at),
            arity: sub_tm(arity, m, at + dep(0, 0, 1)),
        },
        Type::W { shape_level, pos_level, shape, pos } => Type::W {
            shape_level: m.level(shape_level, at),
            pos_level: m.level(pos_level, at),
            shape: sub_ty(shape, m, at),
            pos: sub_ty(pos, m, at + dep(0, 0, 1)),
        },
        // DVec: the family is a type under `i : Fin len`.
        Type::DVec { level, len, fam } => Type::DVec {
            level: m.level(level, at),
            len: sub_tm(len, m, at),
            fam: sub_ty(fam, m, at + dep(0, 0, 1)),
        },
        // IWf: `arity` and `out` under `x : S`, `child` under `x, i`.
        Type::IWf { sig, index } => Type::IWf { sig: sub_iwf_sig(sig, m, at), index: sub_tm(index, m, at) },
        // M: `shape` under `i`, `pos` under `i, s`, `next` under `i, s, p`.
        Type::M { sig, index } => Type::M { sig: sub_m_sig(sig, m, at), index: sub_tm(index, m, at) },
        Type::GlobalTy { var, subst } => {
            let subst = map_subst(subst, m, at);
            m.global_ty(*var, subst, at)
        }
        Type::CtxPi { level, body } => Type::CtxPi {
            level: m.level(level, at),
            body: sub_ty(body, m, at + dep(0, 1, 0)),
        },
        Type::TyPi { ctx, arg_level, body_level, body } => Type::TyPi {
            ctx: other_ctx(ctx, m, at),
            arg_level: m.level(arg_level, at),
            body_level: m.level(body_level, at),
            body: sub_ty(body, m, at + dep(0, 1, 0)),
        },
        Type::CodeTy { ctx, level } => Type::CodeTy {
            ctx: other_ctx(ctx, m, at),
            level: m.level(level, at),
        },
        Type::CodeTm { ctx, ty, level } => Type::CodeTm {
            ctx: other_ctx(ctx, m, at),
            ty: other_ty(ty, m, at),
            level: m.level(level, at),
        },
    }
}

fn map_term<M: Mapper>(t: &Term, m: &mut M, at: Depths) -> Term {
    match t {
        // Reached for a root only: a variable below one is answered in
        // [`sub_tm_answered`], which keeps the mapper's node.
        Term::Var(v) => match m.local_var(*v, at) {
            None => Term::Var(*v),
            Some(out) => {
                m.note();
                (*out).clone()
            }
        },
        Term::TmNat => Term::TmNat,
        Term::TmPi { dom_level, cod_level, dom, cod } => Term::TmPi {
            dom_level: m.level(dom_level, at),
            cod_level: m.level(cod_level, at),
            dom: sub_tm(dom, m, at),
            cod: sub_tm(cod, m, at + dep(0, 0, 1)),
        },
        Term::TmTy(l) => Term::TmTy(m.level(l, at)),
        Term::TmId { level, ty, lhs, rhs } => Term::TmId {
            level: m.level(level, at),
            ty: sub_tm(ty, m, at),
            lhs: sub_tm(lhs, m, at),
            rhs: sub_tm(rhs, m, at),
        },
        Term::TmSEq { level, ty, lhs, rhs } => Term::TmSEq {
            level: m.level(level, at),
            ty: sub_tm(ty, m, at),
            lhs: sub_tm(lhs, m, at),
            rhs: sub_tm(rhs, m, at),
        },
        Term::TmSEmpty { level } => Term::TmSEmpty { level: m.level(level, at) },
        Term::TmSquash { level, ty } => Term::TmSquash {
            level: m.level(level, at),
            ty: sub_tm(ty, m, at),
        },
        Term::TmSigma { fst_level, snd_level, fst, snd } => Term::TmSigma {
            fst_level: m.level(fst_level, at),
            snd_level: m.level(snd_level, at),
            fst: sub_tm(fst, m, at),
            snd: sub_tm(snd, m, at + dep(0, 0, 1)),
        },
        Term::TmUnit { level } => Term::TmUnit { level: m.level(level, at) },
        Term::TmEmpty { level } => Term::TmEmpty { level: m.level(level, at) },
        Term::TmSum { lhs_level, rhs_level, lhs, rhs } => Term::TmSum {
            lhs_level: m.level(lhs_level, at),
            rhs_level: m.level(rhs_level, at),
            lhs: sub_tm(lhs, m, at),
            rhs: sub_tm(rhs, m, at),
        },
        Term::TmW { shape_level, pos_level, shape, pos } => Term::TmW {
            shape_level: m.level(shape_level, at),
            pos_level: m.level(pos_level, at),
            shape: sub_tm(shape, m, at),
            pos: sub_tm(pos, m, at + dep(0, 0, 1)),
        },
        // Vec/Fin codes: the length is a term in the same scope (no binder);
        // the Wf code's arity binds `x : El s`, like the type former's.
        Term::TmVec { level, elem, len } => Term::TmVec {
            level: m.level(level, at),
            elem: sub_tm(elem, m, at),
            len: sub_tm(len, m, at),
        },
        Term::TmFin { len } => Term::TmFin { len: sub_tm(len, m, at) },
        Term::TmWf { level, shape, arity } => Term::TmWf {
            level: m.level(level, at),
            shape: sub_tm(shape, m, at),
            arity: sub_tm(arity, m, at + dep(0, 0, 1)),
        },
        Term::TmDVec { level, len, fam } => Term::TmDVec {
            level: m.level(level, at),
            len: sub_tm(len, m, at),
            fam: sub_tm(fam, m, at + dep(0, 0, 1)),
        },
        Term::TmIWf { level, idx_level, idx, shape, arity, out, child, index } => Term::TmIWf {
            level: m.level(level, at),
            idx_level: m.level(idx_level, at),
            idx: sub_tm(idx, m, at),
            shape: sub_tm(shape, m, at),
            arity: sub_tm(arity, m, at + dep(0, 0, 1)),
            out: sub_tm(out, m, at + dep(0, 0, 1)),
            child: sub_tm(child, m, at + dep(0, 0, 2)),
            index: sub_tm(index, m, at),
        },
        Term::TmM { level, pos_level, idx_level, idx, shape, pos, next, index } => Term::TmM {
            level: m.level(level, at),
            pos_level: m.level(pos_level, at),
            idx_level: m.level(idx_level, at),
            idx: sub_tm(idx, m, at),
            shape: sub_tm(shape, m, at + dep(0, 0, 1)),
            pos: sub_tm(pos, m, at + dep(0, 0, 2)),
            next: sub_tm(next, m, at + dep(0, 0, 3)),
            index: sub_tm(index, m, at),
        },
        Term::Zero => Term::Zero,
        Term::NatLit(n) => Term::NatLit(n.clone()),
        Term::Succ(t) => Term::Succ(sub_tm(t, m, at)),
        Term::ElimNat { level, motive, base, step, scrut } => Term::ElimNat {
            level: m.level(level, at),
            motive: sub_ty(motive, m, at + dep(0, 0, 1)),
            base: sub_tm(base, m, at),
            step: sub_tm(step, m, at + dep(0, 0, 2)),
            scrut: sub_tm(scrut, m, at),
        },
        Term::Refl { level, ty, tm } => Term::Refl {
            level: m.level(level, at),
            ty: sub_ty(ty, m, at),
            tm: sub_tm(tm, m, at),
        },
        Term::J { ty_level, motive_level, ty, lhs, motive, case, rhs, proof } => Term::J {
            ty_level: m.level(ty_level, at),
            motive_level: m.level(motive_level, at),
            ty: sub_ty(ty, m, at),
            lhs: sub_tm(lhs, m, at),
            motive: sub_ty(motive, m, at + dep(0, 0, 2)),
            case: sub_tm(case, m, at),
            rhs: sub_tm(rhs, m, at),
            proof: sub_tm(proof, m, at),
        },
        Term::SRefl { level, ty, tm } => Term::SRefl {
            level: m.level(level, at),
            ty: sub_ty(ty, m, at),
            tm: sub_tm(tm, m, at),
        },
        Term::Squash { level, ty, tm } => Term::Squash {
            level: m.level(level, at),
            ty: sub_ty(ty, m, at),
            tm: sub_tm(tm, m, at),
        },
        Term::ElimSEmpty { level, scrut_level, motive, scrut } => Term::ElimSEmpty {
            level: m.level(level, at),
            scrut_level: m.level(scrut_level, at),
            motive: sub_ty(motive, m, at + dep(0, 0, 1)),
            scrut: sub_tm(scrut, m, at),
        },
        Term::ElimSquash { src_level, dst_level, src_ty, motive, case, scrut } => {
            Term::ElimSquash {
                src_level: m.level(src_level, at),
                dst_level: m.level(dst_level, at),
                src_ty: sub_ty(src_ty, m, at),
                motive: sub_ty(motive, m, at + dep(0, 0, 1)),
                case: sub_tm(case, m, at + dep(0, 0, 1)),
                scrut: sub_tm(scrut, m, at),
            }
        }
        Term::UnsquashEmpty { level, scrut } => Term::UnsquashEmpty {
            level: m.level(level, at),
            scrut: sub_tm(scrut, m, at),
        },
        Term::Pair { fst_level, snd_level, fst_ty, snd_ty, fst, snd } => Term::Pair {
            fst_level: m.level(fst_level, at),
            snd_level: m.level(snd_level, at),
            fst_ty: sub_ty(fst_ty, m, at),
            snd_ty: sub_ty(snd_ty, m, at + dep(0, 0, 1)),
            fst: sub_tm(fst, m, at),
            snd: sub_tm(snd, m, at),
        },
        Term::VecLit { level, elem, zero, one, width, bits } => Term::VecLit {
            level: m.level(level, at),
            elem: sub_ty(elem, m, at),
            zero: sub_tm(zero, m, at),
            one: sub_tm(one, m, at),
            width: *width,
            bits: *bits,
        },
        // The live elements, mapped in a loop; an unchanged array is kept.
        Term::VecItems { level, elem, items, from } => {
            let live = items.get(*from as usize..).unwrap_or(&[]);
            let mapped: Vec<Rc<Term>> = live.iter().map(|item| sub_tm(item, m, at)).collect();
            let same = mapped.iter().zip(live).all(|(a, b)| Rc::ptr_eq(a, b));
            Term::VecItems {
                level: m.level(level, at),
                elem: sub_ty(elem, m, at),
                items: if same { std::sync::Arc::clone(items) } else { mapped.into() },
                from: if same { *from } else { 0 },
            }
        }
        Term::Fst { fst_level, snd_level, fst_ty, snd_ty, pair } => Term::Fst {
            fst_level: m.level(fst_level, at),
            snd_level: m.level(snd_level, at),
            fst_ty: sub_ty(fst_ty, m, at),
            snd_ty: sub_ty(snd_ty, m, at + dep(0, 0, 1)),
            pair: sub_tm(pair, m, at),
        },
        Term::Snd { fst_level, snd_level, fst_ty, snd_ty, pair } => Term::Snd {
            fst_level: m.level(fst_level, at),
            snd_level: m.level(snd_level, at),
            fst_ty: sub_ty(fst_ty, m, at),
            snd_ty: sub_ty(snd_ty, m, at + dep(0, 0, 1)),
            pair: sub_tm(pair, m, at),
        },

        // The checked spellings (docs/elaborator/intro-by-type-design.md): one type
        // annotation each and **no binder in it** — `snd_ty` bound one, `T`
        // binds none — so every walker here loses the `dep(0, 0, 1)` its
        // component sibling needs.
        Term::PairAt { ty, fst, snd } => Term::PairAt {
            ty: ty.as_ref().map(|t| sub_ty(t, m, at)),
            fst: sub_tm(fst, m, at),
            snd: sub_tm(snd, m, at),
        },
        Term::InlAt { ty, val } => Term::InlAt {
            ty: ty.as_ref().map(|t| sub_ty(t, m, at)),
            val: sub_tm(val, m, at),
        },
        Term::InrAt { ty, val } => Term::InrAt {
            ty: ty.as_ref().map(|t| sub_ty(t, m, at)),
            val: sub_tm(val, m, at),
        },
        Term::FstAt { pair } => Term::FstAt { pair: sub_tm(pair, m, at) },
        Term::SndAt { pair } => Term::SndAt { pair: sub_tm(pair, m, at) },
        Term::AppAt { fun, arg } => Term::AppAt { fun: sub_tm(fun, m, at), arg: sub_tm(arg, m, at) },
        Term::Triv { level } => Term::Triv { level: m.level(level, at) },
        Term::ElimEmpty { level, scrut_level, motive, scrut } => Term::ElimEmpty {
            level: m.level(level, at),
            scrut_level: m.level(scrut_level, at),
            motive: sub_ty(motive, m, at + dep(0, 0, 1)),
            scrut: sub_tm(scrut, m, at),
        },
        Term::Inl { lhs_level, rhs_level, lhs, rhs, val } => Term::Inl {
            lhs_level: m.level(lhs_level, at),
            rhs_level: m.level(rhs_level, at),
            lhs: sub_ty(lhs, m, at),
            rhs: sub_ty(rhs, m, at),
            val: sub_tm(val, m, at),
        },
        Term::Inr { lhs_level, rhs_level, lhs, rhs, val } => Term::Inr {
            lhs_level: m.level(lhs_level, at),
            rhs_level: m.level(rhs_level, at),
            lhs: sub_ty(lhs, m, at),
            rhs: sub_ty(rhs, m, at),
            val: sub_tm(val, m, at),
        },
        Term::Case {
            lhs_level,
            rhs_level,
            motive_level,
            lhs,
            rhs,
            motive,
            case_l,
            case_r,
            scrut,
        } => Term::Case {
            lhs_level: m.level(lhs_level, at),
            rhs_level: m.level(rhs_level, at),
            motive_level: m.level(motive_level, at),
            lhs: sub_ty(lhs, m, at),
            rhs: sub_ty(rhs, m, at),
            motive: sub_ty(motive, m, at + dep(0, 0, 1)),
            case_l: sub_tm(case_l, m, at + dep(0, 0, 1)),
            case_r: sub_tm(case_r, m, at + dep(0, 0, 1)),
            scrut: sub_tm(scrut, m, at),
        },
        Term::Sup { shape_level, pos_level, shape_ty, pos_ty, label, children } => Term::Sup {
            shape_level: m.level(shape_level, at),
            pos_level: m.level(pos_level, at),
            shape_ty: sub_ty(shape_ty, m, at),
            pos_ty: sub_ty(pos_ty, m, at + dep(0, 0, 1)),
            label: sub_tm(label, m, at),
            children: sub_tm(children, m, at),
        },
        Term::ElimW {
            shape_level,
            pos_level,
            motive_level,
            shape,
            pos,
            motive,
            step,
            scrut,
        } => Term::ElimW {
            shape_level: m.level(shape_level, at),
            pos_level: m.level(pos_level, at),
            motive_level: m.level(motive_level, at),
            shape: sub_ty(shape, m, at),
            pos: sub_ty(pos, m, at + dep(0, 0, 1)),
            motive: sub_ty(motive, m, at + dep(0, 0, 1)),
            step: sub_tm(step, m, at + dep(0, 0, 3)),
            scrut: sub_tm(scrut, m, at),
        },
        // sup_f / elim_Wf: `arity` binds `x : S`, `motive` binds `z : Wf`,
        // and the step binds three (a, cs, ih) — same depths as `elim_W`'s.
        Term::Supf { level, shape, arity, label, children } => Term::Supf {
            level: m.level(level, at),
            shape: sub_ty(shape, m, at),
            arity: sub_tm(arity, m, at + dep(0, 0, 1)),
            label: sub_tm(label, m, at),
            children: sub_tm(children, m, at),
        },
        Term::ElimWf { level, motive_level, shape, arity, motive, step, scrut } => Term::ElimWf {
            level: m.level(level, at),
            motive_level: m.level(motive_level, at),
            shape: sub_ty(shape, m, at),
            arity: sub_tm(arity, m, at + dep(0, 0, 1)),
            motive: sub_ty(motive, m, at + dep(0, 0, 1)),
            step: sub_tm(step, m, at + dep(0, 0, 3)),
            scrut: sub_tm(scrut, m, at),
        },
        // sup_i / elim_IWf: the signature as `IWf`'s; the motive binds
        // `j, z`, the step `a, cs, ih`.
        Term::Supi { sig, label, children } => Term::Supi {
            sig: sub_iwf_sig(sig, m, at),
            label: sub_tm(label, m, at),
            children: sub_tm(children, m, at),
        },
        Term::ElimIWf { sig, motive_level, motive, step, index, scrut } => Term::ElimIWf {
            sig: sub_iwf_sig(sig, m, at),
            motive_level: m.level(motive_level, at),
            motive: sub_ty(motive, m, at + dep(0, 0, 2)),
            step: sub_tm(step, m, at + dep(0, 0, 3)),
            index: sub_tm(index, m, at),
            scrut: sub_tm(scrut, m, at),
        },
        // corec / out: the signature as `M`'s; the carrier binds `i`, the
        // step `i, x`.
        Term::Corec { sig, carrier_level, carrier, step, index, seed } => Term::Corec {
            sig: sub_m_sig(sig, m, at),
            carrier_level: m.level(carrier_level, at),
            carrier: sub_ty(carrier, m, at + dep(0, 0, 1)),
            step: sub_tm(step, m, at + dep(0, 0, 2)),
            index: sub_tm(index, m, at),
            seed: sub_tm(seed, m, at),
        },
        Term::Out { sig, index, scrut } => Term::Out {
            sig: sub_m_sig(sig, m, at),
            index: sub_tm(index, m, at),
            scrut: sub_tm(scrut, m, at),
        },
        Term::Lam { dom_level, cod_level, dom, body } => Term::Lam {
            dom_level: m.level(dom_level, at),
            cod_level: m.level(cod_level, at),
            dom: sub_ty(dom, m, at),
            body: sub_tm(body, m, at + dep(0, 0, 1)),
        },
        Term::App { fun, dom_level, cod_level, dom, cod, arg } => Term::App {
            fun: sub_tm(fun, m, at),
            dom_level: m.level(dom_level, at),
            cod_level: m.level(cod_level, at),
            dom: sub_ty(dom, m, at),
            cod: sub_ty(cod, m, at + dep(0, 0, 1)),
            arg: sub_tm(arg, m, at),
        },
        Term::ULam { num_vars, level, body } => Term::ULam {
            num_vars: *num_vars,
            level: m.level(level, at + dep(*num_vars, 0, 0)),
            body: sub_tm(body, m, at + dep(*num_vars, 0, 0)),
        },
        Term::UApp { fun, levels } => Term::UApp {
            fun: sub_tm(fun, m, at),
            levels: levels.iter().map(|l| m.level(l, at)).collect(),
        },
        Term::GlobalTm { var, subst } => {
            let subst = map_subst(subst, m, at);
            m.global_tm(*var, subst, at)
        }
        Term::CtxLam { level, body } => Term::CtxLam {
            level: m.level(level, at),
            body: sub_tm(body, m, at + dep(0, 1, 0)),
        },
        Term::CtxApp { fun, ctx } => Term::CtxApp {
            fun: sub_tm(fun, m, at),
            ctx: other_ctx(ctx, m, at),
        },
        Term::TyLam { ctx, arg_level, body_level, body } => Term::TyLam {
            ctx: other_ctx(ctx, m, at),
            arg_level: m.level(arg_level, at),
            body_level: m.level(body_level, at),
            body: sub_tm(body, m, at + dep(0, 1, 0)),
        },
        Term::TyApp { fun, arg } => Term::TyApp {
            fun: sub_tm(fun, m, at),
            arg: other_ty(arg, m, at),
        },
        Term::BoxTy(t) => Term::BoxTy(other_ty(t, m, at)),
        Term::BoxTm(t) => Term::BoxTm(other_tm(t, m, at)),
        Term::LetBoxTy { motive_level, code_level, ctx, motive, body, scrut } => Term::LetBoxTy {
            motive_level: m.level(motive_level, at),
            code_level: m.level(code_level, at),
            ctx: other_ctx(ctx, m, at),
            motive: sub_ty(motive, m, at + dep(0, 0, 1)),
            body: sub_tm(body, m, at + dep(0, 1, 0)),
            scrut: sub_tm(scrut, m, at),
        },
        Term::LetBoxTm { motive_level, code_level, ctx, ty, motive, body, scrut } => {
            Term::LetBoxTm {
                motive_level: m.level(motive_level, at),
                code_level: m.level(code_level, at),
                ctx: other_ctx(ctx, m, at),
                ty: other_ty(ty, m, at),
                motive: sub_ty(motive, m, at + dep(0, 0, 1)),
                body: sub_tm(body, m, at + dep(0, 1, 0)),
                scrut: sub_tm(scrut, m, at),
            }
        }
        Term::ElimCodeTy {
            ty_motive_level,
            tm_motive_level,
            motives,
            branches,
            code_level,
            ctx,
            scrut,
        } => Term::ElimCodeTy {
            ty_motive_level: m.level(ty_motive_level, at),
            tm_motive_level: m.level(tm_motive_level, at),
            motives: sub_motives(motives, m, at),
            branches: sub_branches(branches, m, at),
            code_level: m.level(code_level, at),
            ctx: other_ctx(ctx, m, at),
            scrut: sub_tm(scrut, m, at),
        },
        Term::ElimCodeTm {
            ty_motive_level,
            tm_motive_level,
            motives,
            branches,
            code_level,
            ctx,
            ty,
            scrut,
        } => Term::ElimCodeTm {
            ty_motive_level: m.level(ty_motive_level, at),
            tm_motive_level: m.level(tm_motive_level, at),
            motives: sub_motives(motives, m, at),
            branches: sub_branches(branches, m, at),
            code_level: m.level(code_level, at),
            ctx: other_ctx(ctx, m, at),
            ty: other_ty(ty, m, at),
            scrut: sub_tm(scrut, m, at),
        },
    }
}

/// Motive telescopes (ch. 04): `(ℓ, g, x_T. M_Typ)` and
/// `(ℓ, g, U_T, x_t. M_Trm)`.
fn map_motives<M: Mapper>(mo: &Motives, m: &mut M, at: Depths) -> Motives {
    Motives {
        ty_motive: sub_ty(&mo.ty_motive, m, at + dep(1, 1, 1)),
        tm_motive: sub_ty(&mo.tm_motive, m, at + dep(1, 2, 1)),
    }
}

/// Branch telescopes (ch. 04); the `dep(univ, global, local)` increments
/// must match the telescopes documented on [`Branches`].
fn map_branches<M: Mapper>(b: &Branches, m: &mut M, at: Depths) -> Branches {
    let terms = rec::branch_terms(b);
    rec::branches_from(std::array::from_fn(|i| {
        let (univ, global, local) = rec::BRANCH_DEPTHS[i];
        sub_tm(terms[i], m, at + dep(univ, global, local))
    }))
}

fn map_ctx<M: Mapper>(c: &LocalCtx, m: &mut M, at: Depths) -> LocalCtx {
    let (base, mut entries) = m.ctx_base(c.base, at);
    entries.extend(c.entries.iter().map(|e| CtxEntry {
        ty: sub_ty(&e.ty, m, at),
        level: m.level(&e.level, at),
    }));
    LocalCtx { base, entries }
}

fn map_subst<M: Mapper>(s: &LocalSubst, m: &mut M, at: Depths) -> LocalSubst {
    let (tail, mut terms) = m.tail(s.tail, at);
    terms.extend(s.terms.iter().map(|t| sub_tm(t, m, at)));
    LocalSubst { tail, terms }
}

// ---------------------------------------------------------------------------
// Shifts
// ---------------------------------------------------------------------------

/// Weaken the ambient local context by `by` entries. Any same-local-scope
/// substitution's source grows accordingly (tail length bump).
struct ShiftLocal {
    by: u32,
    changes: u64,
    memo: NodeMemo,
}

impl Mapper for ShiftLocal {
    const LOCAL_OP: bool = true;
    const NAME: &'static str = "shift_local";
    const COUNT_NODES: Option<fn(u64)> = Some(crate::stats::local_subst_nodes);

    fn changes(&mut self) -> &mut u64 {
        &mut self.changes
    }

    fn local_var(&mut self, v: LocalVar, at: Depths) -> Option<Rc<Term>> {
        // `by` is nonzero here (the entry points short-circuit zero), so a
        // free variable is always renumbered.
        (v.0 >= at.local).then(|| Term::var_rc(v.0 + self.by))
    }

    fn tail(&mut self, tail: SubstTail, _at: Depths) -> (SubstTail, Vec<Rc<Term>>) {
        // An empty tail names no variable and records no length: a
        // weakening leaves it as it is.
        let t = match tail {
            SubstTail::Empty => return (tail, Vec::new()),
            SubstTail::Wk { len, ctx_var } => SubstTail::Wk { len: len + self.by, ctx_var },
        };
        // `by` is nonzero here, as for a variable.
        self.note();
        (t, Vec::new())
    }

    fn skip_ty(&mut self, t: &Rc<Type>, at: Depths) -> bool {
        bounds::skip_type(t, at.local)
    }
    fn skip_tm(&mut self, t: &Rc<Term>, at: Depths) -> bool {
        bounds::skip_term(t, at.local)
    }
    fn memo(&mut self) -> Option<&mut NodeMemo> {
        Some(&mut self.memo)
    }
}

/// Weaken the global context by `by` bindings.
struct ShiftGlobal {
    by: u32,
    changes: u64,
    memo: NodeMemo,
}

impl ShiftGlobal {
    fn var(&mut self, v: GlobalVar, at: Depths) -> GlobalVar {
        match v.as_index() {
            // `by` is nonzero here, so a free variable is always renumbered.
            Some(i) if i >= at.global => {
                self.note();
                GlobalVar::index(i + self.by)
            }
            // Bound by a binder passed under, or a constant: a constant is
            // named from the start of Ψ, which no weakening moves.
            _ => v,
        }
    }
}

impl Mapper for ShiftGlobal {
    const LOCAL_OP: bool = false;
    const NAME: &'static str = "shift_global";
    const COUNT_NODES: Option<fn(u64)> = Some(crate::stats::shift_global_nodes);

    fn changes(&mut self) -> &mut u64 {
        &mut self.changes
    }

    fn memo(&mut self) -> Option<&mut NodeMemo> {
        Some(&mut self.memo)
    }

    // A weakening moves free variables and nothing else: a subtree with
    // none at or past the cutoff is its own image (`bounds.rs`, §The
    // global namespace).
    fn skip_ty(&mut self, t: &Rc<Type>, at: Depths) -> bool {
        bounds::skip_global_type(t, at.global)
    }
    fn skip_tm(&mut self, t: &Rc<Term>, at: Depths) -> bool {
        bounds::skip_global_term(t, at.global)
    }

    fn global_ty(&mut self, var: GlobalVar, subst: LocalSubst, at: Depths) -> Type {
        Type::GlobalTy { var: self.var(var, at), subst }
    }

    fn global_tm(&mut self, var: GlobalVar, subst: LocalSubst, at: Depths) -> Term {
        Term::GlobalTm { var: self.var(var, at), subst }
    }

    fn ctx_base(&mut self, base: CtxBase, at: Depths) -> (CtxBase, CtxEntries) {
        let b = match base {
            CtxBase::Nil => CtxBase::Nil,
            CtxBase::Var(g) => CtxBase::Var(self.var(g, at)),
        };
        (b, CtxEntries::empty())
    }

    fn tail(&mut self, tail: SubstTail, at: Depths) -> (SubstTail, Vec<Rc<Term>>) {
        let t = match tail {
            SubstTail::Empty => tail,
            SubstTail::Wk { len, ctx_var } => {
                SubstTail::Wk { len, ctx_var: self.var(ctx_var, at) }
            }
        };
        (t, Vec::new())
    }
}

/// Rename every free global variable through a caller's map: the rescoping a
/// module image needs when the Ψ prefix it was elaborated over is replaced by
/// one in which its referents sit elsewhere
/// (`docs/infrastructure/module-interface-cutoff-design.md` §3). The map sees and returns a
/// free index as counted from the outside of the term, binders crossed
/// already subtracted; `None` from it marks the result unusable rather than
/// guessing, and the whole operation returns `None`.
///
/// A constant is given to the map as it is, and the map may answer in either
/// spelling for either: that is how a variable of the world a term was
/// elaborated in becomes a constant of the world it is committed to.
///
/// Not used by the kernel's own judgements. Its output is untrusted like any
/// other elaborator product, and is checked before it reaches Ψ.
struct ReindexGlobal<'a> {
    map: &'a mut dyn FnMut(GlobalRef) -> Option<GlobalRef>,
    failed: bool,
    changes: u64,
    /// Shared nodes are moved once, as `shift_global` does: a moved module
    /// image (`ModuleDelta::relocate`) was a tree walk over terms the
    /// elaborator shares as a DAG, which a tier-2 type's `W` encoding
    /// makes large (`issues/grind-closure-cost.md`). Sound because `map`
    /// answers by position alone, so a node at one depth moves one way.
    memo: NodeMemo,
}

impl ReindexGlobal<'_> {
    fn var(&mut self, v: GlobalVar, at: Depths) -> GlobalVar {
        let free = match v.view() {
            GlobalRef::Var(i) if i < at.global => return v,
            GlobalRef::Var(i) => GlobalRef::Var(i - at.global),
            c @ GlobalRef::Const(_) => c,
        };
        match (self.map)(free) {
            Some(to) => {
                let moved = match to {
                    GlobalRef::Var(free) => GlobalVar::index(free + at.global),
                    GlobalRef::Const(p) => GlobalVar::constant(p),
                };
                if moved != v {
                    self.note();
                }
                moved
            }
            None => {
                self.failed = true;
                v
            }
        }
    }
}

impl Mapper for ReindexGlobal<'_> {
    const LOCAL_OP: bool = false;
    const NAME: &'static str = "reindex_global";

    fn changes(&mut self) -> &mut u64 {
        &mut self.changes
    }

    fn memo(&mut self) -> Option<&mut NodeMemo> {
        Some(&mut self.memo)
    }

    fn global_ty(&mut self, var: GlobalVar, subst: LocalSubst, at: Depths) -> Type {
        Type::GlobalTy { var: self.var(var, at), subst }
    }

    fn global_tm(&mut self, var: GlobalVar, subst: LocalSubst, at: Depths) -> Term {
        Term::GlobalTm { var: self.var(var, at), subst }
    }

    fn ctx_base(&mut self, base: CtxBase, at: Depths) -> (CtxBase, CtxEntries) {
        let b = match base {
            CtxBase::Nil => CtxBase::Nil,
            CtxBase::Var(g) => CtxBase::Var(self.var(g, at)),
        };
        (b, CtxEntries::empty())
    }

    fn tail(&mut self, tail: SubstTail, at: Depths) -> (SubstTail, Vec<Rc<Term>>) {
        let t = match tail {
            SubstTail::Empty => tail,
            SubstTail::Wk { len, ctx_var } => {
                SubstTail::Wk { len, ctx_var: self.var(ctx_var, at) }
            }
        };
        (t, Vec::new())
    }
}

impl GlobalBinding {
    /// [`Type::reindex_global`] over a whole binding: its context, statement
    /// and body share one global scope (the binding's prefix of Ψ).
    pub fn reindex_global(&self, map: &mut dyn FnMut(GlobalRef) -> Option<GlobalRef>) -> Option<GlobalBinding> {
        let mut m = ReindexGlobal { map, failed: false, changes: 0, memo: NodeMemo::default() };
        let at = Depths::default();
        let out = match self {
            GlobalBinding::Ctx => GlobalBinding::Ctx,
            GlobalBinding::Ty { ctx, layer, level } => {
                GlobalBinding::Ty { ctx: map_ctx(ctx, &mut m, at), layer: *layer, level: level.clone() }
            }
            GlobalBinding::Tm { ctx, layer, ty, level, body } => GlobalBinding::Tm {
                ctx: map_ctx(ctx, &mut m, at),
                layer: *layer,
                ty: sub_ty(ty, &mut m, at),
                level: level.clone(),
                body: body.as_ref().map(|b| sub_tm(b, &mut m, at)),
            },
        };
        (!m.failed).then_some(out)
    }
}

/// The recursor's motive and branch telescopes, weakened by `by` global
/// bindings. The value machine's one materialization site that is a
/// telescope table rather than a term (`docs/kernel/lazy-global-offset-design.md`
/// §5); routed through the generic traversal so the 65 telescopes are not
/// written down again.
pub(crate) fn shift_global_tables(
    motives: &Motives,
    branches: &Branches,
    by: u32,
) -> (Motives, Branches) {
    let at = Depths::default();
    let mut m = ShiftGlobal { by, changes: 0, memo: NodeMemo::default() };
    let mo = map_motives(motives, &mut m, at);
    let br = map_branches(branches, &mut m, at);
    (mo, br)
}

/// Weaken the universe context by `by` variables.
struct ShiftUniv {
    by: u32,
    changes: u64,
    memo: NodeMemo,
}

impl Mapper for ShiftUniv {
    const LOCAL_OP: bool = false;
    const NAME: &'static str = "shift_univ";

    fn changes(&mut self) -> &mut u64 {
        &mut self.changes
    }

    fn memo(&mut self) -> Option<&mut NodeMemo> {
        Some(&mut self.memo)
    }

    fn level(&mut self, l: &Level, at: Depths) -> Level {
        self.mapped(l.shift(self.by, at.univ), l)
    }
}

// ---------------------------------------------------------------------------
// Substitutions
// ---------------------------------------------------------------------------

/// Universe substitution `φ`: `phi[i]` replaces universe variable `i`
/// (innermost = 0), scoped in the source universe context.
struct SubstUniv<'a> {
    phi: &'a [Level],
    changes: u64,
    memo: NodeMemo,
}

impl Mapper for SubstUniv<'_> {
    const LOCAL_OP: bool = false;
    const NAME: &'static str = "apply_univ";

    fn changes(&mut self) -> &mut u64 {
        &mut self.changes
    }

    fn memo(&mut self) -> Option<&mut NodeMemo> {
        Some(&mut self.memo)
    }

    fn level(&mut self, l: &Level, at: Depths) -> Level {
        self.mapped(l.subst_at(self.phi, at.univ), l)
    }
}

/// Universe instantiation: substitute the innermost `phi.len()` universe
/// variables and renumber the rest down — the universe mirror of
/// [`GlobalSubst`]'s instantiation form. Used by the β-rules for `Λ ℓ⃗` and
/// for the recursor branch telescopes. `phi[0]` is the payload for the
/// *innermost* variable.
struct InstUniv<'a> {
    phi: &'a [Level],
    changes: u64,
    memo: NodeMemo,
}

impl Mapper for InstUniv<'_> {
    const LOCAL_OP: bool = false;
    const NAME: &'static str = "inst_univ";

    fn changes(&mut self) -> &mut u64 {
        &mut self.changes
    }

    fn memo(&mut self) -> Option<&mut NodeMemo> {
        Some(&mut self.memo)
    }

    fn level(&mut self, l: &Level, at: Depths) -> Level {
        self.mapped(l.inst_at(self.phi, at.univ), l)
    }
}

/// A substitution's payloads as they read under binders: each lifted to a
/// depth once, and one node for every occurrence at that depth.
///
/// A variable that occurs many times under the same binders (a readback's
/// environment entry, `issues/elab-whnf-family-transport-cost.md`) shares
/// one lifted copy instead of rewalking the payload per occurrence. A
/// payload that lifting does not change is the substitution's own node, at
/// every depth: under no binder always, and under binders when it reads no
/// variable they could capture, which its bounds answer without a walk and
/// without an entry here.
struct Lifted<K> {
    at: FewMap<(K, Depths), Rc<Term>>,
}

impl<K> Default for Lifted<K> {
    fn default() -> Lifted<K> {
        Lifted { at: FewMap::default() }
    }
}

impl<K: Copy + Eq + std::hash::Hash> Lifted<K> {
    fn at(&mut self, which: K, at: Depths, payload: &Rc<Term>) -> Rc<Term> {
        if at.local == 0 && at.global == 0 && at.univ == 0 {
            return Rc::clone(payload);
        }
        // A variable lifts to a variable, whatever the other two
        // namespaces count: the shared leaf, and no entry.
        if let Term::Var(w) = **payload {
            return Term::var_rc(w.0 + at.local);
        }
        // Not while a skip is being derived again: that walk consults no
        // bounds (`checks::unskipped`), and the lift below takes none.
        if at.global == 0 && at.univ == 0 && !crate::checks::unskipped() && bounds::skip_term(payload, 0) {
            return Rc::clone(payload);
        }
        if let Some(hit) = self.at.get(&(which, at)) {
            return Rc::clone(hit);
        }
        let mut out = Rc::clone(payload);
        if at.local != 0 {
            out = sub_tm(&out, &mut ShiftLocal { by: at.local, changes: 0, memo: NodeMemo::default() }, Depths::default());
        }
        if at.global != 0 {
            out = sub_tm(&out, &mut ShiftGlobal { by: at.global, changes: 0, memo: NodeMemo::default() }, Depths::default());
        }
        if at.univ != 0 {
            out = sub_tm(&out, &mut ShiftUniv { by: at.univ, changes: 0, memo: NodeMemo::default() }, Depths::default());
        }
        self.at.insert((which, at), Rc::clone(&out));
        out
    }
}

/// Local substitution `δ`, applied from depth zero; lifting under binders is
/// depth-based (payloads are shifted in all three namespaces at insertion).
struct SubstLocal<'a> {
    delta: &'a LocalSubst,
    changes: u64,
    lifted: Lifted<usize>,
    memo: NodeMemo,
}

impl Mapper for SubstLocal<'_> {
    const LOCAL_OP: bool = true;
    const NAME: &'static str = "apply_local";
    const COUNT_NODES: Option<fn(u64)> = Some(crate::stats::local_subst_nodes);

    fn changes(&mut self) -> &mut u64 {
        &mut self.changes
    }

    fn local_var(&mut self, v: LocalVar, at: Depths) -> Option<Rc<Term>> {
        if v.0 < at.local {
            return None;
        }
        let i = (v.0 - at.local) as usize;
        let n = self.delta.terms.len();
        assert!(
            i < n,
            "kernel invariant violated: local variable {} escapes the substitution's target \
             entries (variables cannot address a context-variable base)",
            v.0
        );
        // terms[0] substitutes the outermost entry; index from the innermost.
        let payload = &self.delta.terms[n - 1 - i];
        if let Term::Var(w) = **payload {
            // A variable lifts to a variable. An *identity* substitution
            // sends this one to itself, and that is common enough to be
            // worth the O(1) test: `t[id]` should share all of `t`, not
            // rebuild it. Any other payload is a change.
            let w = w.0 + at.local;
            return (w != v.0).then(|| Term::var_rc(w));
        }
        Some(self.lifted.at(i, at, payload))
    }

    /// Composition on tails (ch. 02/05): `wk_g^k ∘ δ = wk_g^{δ̂}` and
    /// `· ∘ δ = ·`, where δ is conceptually lifted to the current depth
    /// (source length + local depth).
    ///
    /// δ̂ is read off δ's own weakening: `wk_g ∘ δ` is scoped only when δ
    /// targets a context based at `g`, so that its tail is `wk_g` too
    /// (`term.rs`, [`LocalSubst`]). Against an empty-tailed δ the
    /// composition means nothing, and the length is counted from the binders
    /// passed alone.
    fn tail(&mut self, tail: SubstTail, at: Depths) -> (SubstTail, Vec<Rc<Term>>) {
        let t = match tail {
            SubstTail::Wk { ctx_var, .. } => {
                SubstTail::Wk { len: self.delta.wk_len().unwrap_or(0) + at.local, ctx_var }
            }
            SubstTail::Empty => tail,
        };
        if t != tail {
            self.note();
        }
        (t, Vec::new())
    }

    fn skip_ty(&mut self, t: &Rc<Type>, at: Depths) -> bool {
        bounds::skip_type(t, at.local)
    }
    fn skip_tm(&mut self, t: &Rc<Term>, at: Depths) -> bool {
        bounds::skip_term(t, at.local)
    }
    fn memo(&mut self) -> Option<&mut NodeMemo> {
        Some(&mut self.memo)
    }
}

/// `t[s/x]` read `by` binders further out: `t` is scoped in `Γ, x`, the
/// payload `s` in `Γ, Δ` with `|Δ| = by`, and so is the result — `x` becomes
/// `s` and every variable of `Γ` is weakened past `Δ`. It is
/// `t.apply_local(&id(Γ).shift_local(by).extended(s))`, without needing `Γ`
/// to build the identity: the derived schemas that instantiate a binder of
/// their own former (`DVec`'s family at `inl ⟨⟩`/`inr j`, `dnth`'s at `e i`)
/// are built from syntax alone, as `nth` is (`term.rs`).
///
/// Tails move as [`SubstLocal`]'s would: the source loses `x` and gains
/// `Δ`, so a tail's length changes by `by - 1`; its base does not move.
struct InstTop<'a> {
    payload: &'a Term,
    by: u32,
    changes: u64,
    /// The payload as a node, made at its first occurrence.
    node: Option<Rc<Term>>,
    lifted: Lifted<()>,
    memo: NodeMemo,
}

impl Mapper for InstTop<'_> {
    const LOCAL_OP: bool = true;
    const NAME: &'static str = "inst_top";
    const COUNT_NODES: Option<fn(u64)> = Some(crate::stats::local_subst_nodes);

    fn changes(&mut self) -> &mut u64 {
        &mut self.changes
    }

    fn local_var(&mut self, v: LocalVar, at: Depths) -> Option<Rc<Term>> {
        if v.0 < at.local {
            return None;
        }
        if v.0 == at.local {
            let node = self.node.get_or_insert_with(|| self.payload.clone().into_rc());
            return Some(self.lifted.at((), at, node));
        }
        // `by == 1` keeps Γ's variables where they were.
        let w = v.0 - 1 + self.by;
        (w != v.0).then(|| Term::var_rc(w))
    }

    fn tail(&mut self, tail: SubstTail, _at: Depths) -> (SubstTail, Vec<Rc<Term>>) {
        let t = match tail {
            SubstTail::Empty => tail,
            SubstTail::Wk { len, ctx_var } => SubstTail::Wk { len: len - 1 + self.by, ctx_var },
        };
        if t != tail {
            self.note();
        }
        (t, Vec::new())
    }

    fn skip_ty(&mut self, t: &Rc<Type>, at: Depths) -> bool {
        bounds::skip_type(t, at.local)
    }
    fn skip_tm(&mut self, t: &Rc<Term>, at: Depths) -> bool {
        bounds::skip_term(t, at.local)
    }
    fn memo(&mut self) -> Option<&mut NodeMemo> {
        Some(&mut self.memo)
    }
}

/// Abstraction over a **term**: every occurrence of `pat` becomes the fresh
/// innermost variable `z` (`docs/elaborator/goal-motive-synthesis-design.md` §3).
///
/// The inverse of [`SubstLocal`] at a singleton, and the operation a
/// dependent motive is: `T.abstract_local(s)` is a type over `Γ, z` whose
/// `[s/z]` instance is `T` again — *whatever* subset of the occurrences the
/// walk found, because it only ever replaces a position that literally held
/// `s`. That is why the traversal may be as syntactic as it likes and the
/// eliminator's obligation still holds.
///
/// "Occurrence" is `==` on de Bruijn terms, which is α-equality here — the
/// same decision, for the same reasons, as [`crate::term`]'s neighbour in
/// `elab`'s anti-unifier: no conversion call, so this is linear and its
/// failure (finding nothing) is a fact rather than a fuel accident.
struct AbstractLocal<'a> {
    /// The patterns and what each occurrence becomes. The replacement is `z`
    /// itself for the plain abstraction, and a term *containing* `z` for the
    /// caller that abstracts a field out of the value that carries it.
    /// Several patterns because one abstraction may have to catch a term the
    /// goal spells two ways, and catching only one of them is worse than
    /// catching neither.
    pats: &'a [(Term, Term)],
    /// `witness[k]` is `pats` weakened past `k` further local binders, `pat`
    /// and `rep` alike: the walk reads the goal as it stands, scoped in `Γ`,
    /// where `pat` is scoped, and what it builds is scoped in `Γ, z`, where
    /// `rep` is. Memoized: the walk asks at every node.
    witness: Vec<Vec<(Term, Term)>>,
    /// The same below binders of the global or universe context too (a code
    /// eliminator's branches, `letbox`'s body, a context abstraction), keyed
    /// by all three depths: there `pat` and `rep` are also weakened past
    /// those binders, or a pattern mentioning a global variable would match
    /// (and capture) the one the binder shifted onto its index.
    witness_under: Vec<(Depths, Vec<(Term, Term)>)>,
    /// Occurrences replaced — the caller's "did this find anything".
    hits: u64,
    /// Which occurrences to replace, 1-based in traversal order, when the
    /// caller selects (`elab`'s `rewrite(h, e, at := …)`); `None` replaces
    /// every one. An occurrence passed over is descended into like any other
    /// node, which finds nothing: a term does not contain itself.
    select: Option<&'a [u32]>,
    /// Occurrences met, replaced or not — what a selection is numbered by.
    seen: u32,
    changes: u64,
    /// The shared-node memo, when nothing is selected: then a node's result
    /// is a function of the node and the depths, and a goal that shares a
    /// subterm is abstracted once per depth, not once per path to it
    /// (`docs/surveys/mengine-survey.md` §4.2). A selection numbers occurrences by
    /// path, so it walks the tree.
    memo: Option<NodeMemo>,
    /// Whether every pattern mentions a variable of `Γ`. An occurrence under
    /// `k` binders then mentions a variable past them, so a subtree that
    /// mentions none ([`bounds::skip_type`]) holds no occurrence, and making
    /// room for `z` does not change it either: it is returned as it is.
    open_pats: bool,
}

impl<'a> AbstractLocal<'a> {
    fn new(pats: &'a [(Term, Term)], select: Option<&'a [u32]>) -> AbstractLocal<'a> {
        let open_pats = pats
            .iter()
            .all(|(pat, _)| bounds::term_local_use(&Rc::new(pat.clone())).bound > 0);
        AbstractLocal {
            pats,
            witness: Vec::new(),
            witness_under: Vec::new(),
            hits: 0,
            select,
            seen: 0,
            changes: 0,
            // A selection numbers occurrences by path, so it walks the tree.
            memo: select.is_none().then(NodeMemo::default),
            open_pats,
        }
    }
}

impl Mapper for AbstractLocal<'_> {
    const LOCAL_OP: bool = true;
    const NAME: &'static str = "abstract_local";

    fn changes(&mut self) -> &mut u64 {
        &mut self.changes
    }

    fn memo(&mut self) -> Option<&mut NodeMemo> {
        self.memo.as_mut()
    }

    // The walk makes room for `z` as it goes ([`ShiftLocal`] by one) rather
    // than walking a weakened copy of the goal: one traversal and one
    // result, and nothing built for the parts it can skip.
    fn local_var(&mut self, v: LocalVar, at: Depths) -> Option<Rc<Term>> {
        (v.0 >= at.local).then(|| Term::var_rc(v.0 + 1))
    }

    fn tail(&mut self, tail: SubstTail, _at: Depths) -> (SubstTail, Vec<Rc<Term>>) {
        match tail {
            SubstTail::Empty => (tail, Vec::new()),
            SubstTail::Wk { len, ctx_var } => {
                self.note();
                (SubstTail::Wk { len: len + 1, ctx_var }, Vec::new())
            }
        }
    }

    fn skip_ty(&mut self, t: &Rc<Type>, at: Depths) -> bool {
        self.open_pats && bounds::skip_type(t, at.local)
    }
    fn skip_tm(&mut self, t: &Rc<Term>, at: Depths) -> bool {
        self.open_pats && bounds::skip_term(t, at.local)
    }

    fn pre_tm(&mut self, t: &Rc<Term>, at: Depths) -> Option<Term> {
        // Most nodes are not an occurrence, and the head of an application
        // spine says so without weakening anything: the patterns are only
        // weakened past the binders over a node that could be one. A walk
        // under `k` binders would otherwise copy every pattern `k` times,
        // which for a large test deep in a type is the whole cost
        // (`issues/match-arm-coercion-abstracts-both-types.md`).
        if !self.pats.iter().any(|(pat, _)| could_be_weakened(t, pat, at)) {
            return None;
        }
        let row = if at.global == 0 && at.univ == 0 {
            while self.witness.len() as u32 <= at.local {
                let i = self.witness.len() as u32;
                let row = self
                    .pats
                    .iter()
                    .map(|(p, r)| (p.shift_local(i), r.shift_local(i)))
                    .collect();
                self.witness.push(row);
            }
            &self.witness[at.local as usize]
        } else {
            let k = match self.witness_under.iter().position(|(d, _)| *d == at) {
                Some(k) => k,
                None => {
                    let under = |t: &Term, by: u32| {
                        t.shift_local(by).shift_global(at.global).shift_univ(at.univ)
                    };
                    let row = self
                        .pats
                        .iter()
                        .map(|(p, r)| (under(p, at.local), under(r, at.local)))
                        .collect();
                    self.witness_under.push((at, row));
                    self.witness_under.len() - 1
                }
            };
            &self.witness_under[k].1
        };
        let hit = row
            .iter()
            .find(|(pat, _)| **t == *pat)
            .map(|(_, rep)| rep.clone())?;
        self.seen += 1;
        if self.select.is_some_and(|select| !select.contains(&self.seen)) {
            return None;
        }
        self.hits += 1;
        Some(hit)
    }
}

/// Whether `t` could be `pat` weakened past the binders `at`: a necessary
/// condition, read off the two application spines' heads. Weakening keeps
/// every node's form and a spine's length, and keeps a constant or global
/// head as it is outside global and universe binders (below one it renames
/// the free global variables, so there only the form is compared).
fn could_be_weakened(t: &Term, pat: &Term, at: Depths) -> bool {
    fn spine(mut t: &Term) -> (&Term, usize) {
        let mut n = 0;
        while let Term::App { fun, .. } | Term::AppAt { fun, .. } = t {
            t = fun;
            n += 1;
        }
        (t, n)
    }
    if std::mem::discriminant(t) != std::mem::discriminant(pat) {
        return false;
    }
    let ((th, tn), (ph, pn)) = (spine(t), spine(pat));
    if tn != pn || std::mem::discriminant(th) != std::mem::discriminant(ph) {
        return false;
    }
    match (th, ph) {
        (Term::GlobalTm { var: a, .. }, Term::GlobalTm { var: b, .. }) if at.global == 0 && at.univ == 0 => a == b,
        _ => true,
    }
}

/// [`Type::mentions_local`]: [`AbstractLocal`]'s walk with nothing built.
/// It crosses the binders that one crosses and compares the same weakened
/// patterns at the same nodes ([`AbstractLocal::pre_tm`], whose answer it
/// drops), so it finds an occurrence exactly when that one would; once it
/// has, every subtree left is skipped.
struct OccursLocal<'a> {
    find: AbstractLocal<'a>,
    changes: u64,
    /// Never changes anything, so the memo only records which shared nodes
    /// were walked: a second path to one at the same depths stops there.
    memo: NodeMemo,
}

impl Mapper for OccursLocal<'_> {
    const LOCAL_OP: bool = true;
    const NAME: &'static str = "mentions_local";
    // A skip after the first hit is a stop, not a claim about the subtree;
    // and the walk changes nothing anywhere, skipped or not.
    const VERIFY_SKIPS: bool = false;

    fn changes(&mut self) -> &mut u64 {
        &mut self.changes
    }

    fn memo(&mut self) -> Option<&mut NodeMemo> {
        Some(&mut self.memo)
    }

    fn skip_ty(&mut self, t: &Rc<Type>, at: Depths) -> bool {
        self.find.hits > 0 || self.find.skip_ty(t, at)
    }
    fn skip_tm(&mut self, t: &Rc<Term>, at: Depths) -> bool {
        self.find.hits > 0 || self.find.skip_tm(t, at)
    }

    fn pre_tm(&mut self, t: &Rc<Term>, at: Depths) -> Option<Term> {
        if self.find.hits == 0 {
            let _ = self.find.pre_tm(t, at);
        }
        None
    }
}

/// Collects [`Type::root_terms`]: a mapper that changes nothing and only
/// looks, through [`Mapper::pre_tm`], at the nodes under no binder.
struct RootTerms {
    out: Vec<Rc<Term>>,
    changes: u64,
    /// Never changes anything, so its memo only records which shared nodes
    /// were walked: a second path to one stops there.
    memo: NodeMemo,
}

impl Mapper for RootTerms {
    const LOCAL_OP: bool = true;
    const NAME: &'static str = "root_terms";

    fn changes(&mut self) -> &mut u64 {
        &mut self.changes
    }

    fn memo(&mut self) -> Option<&mut NodeMemo> {
        Some(&mut self.memo)
    }

    fn pre_tm(&mut self, t: &Rc<Term>, at: Depths) -> Option<Term> {
        // `pre_tm` runs before the memo is asked, so a shared node is
        // listed only the first time it is met.
        if at == Depths::default() && self.memo.term(&(Rc::as_ptr(t) as usize, at)).is_none() {
            self.out.push(Rc::clone(t));
        }
        None
    }
}

/// Global substitution `σ` (instantiation form, see [`GlobalSubst`]).
struct SubstGlobal<'a> {
    sigma: &'a GlobalSubst,
    changes: u64,
    memo: NodeMemo,
}

enum Resolved<'a> {
    /// Bound by a binder passed under during traversal, or a constant: σ
    /// instantiates variables, and a constant is named from the start of Ψ,
    /// below anything σ replaces or renumbers.
    Bound,
    /// Substituted: payload (scoped in the source, at depth zero).
    Payload(&'a GlobalEntry),
    /// In the identity region below the substituted bindings: renumbered.
    Renumber(GlobalVar),
}

impl<'a> SubstGlobal<'a> {
    fn resolve(&self, v: GlobalVar, at: Depths) -> Resolved<'a> {
        let n = self.sigma.entries.len() as u32;
        let Some(i) = v.as_index() else { return Resolved::Bound };
        if i < at.global {
            Resolved::Bound
        } else if i - at.global < n {
            let rel = (i - at.global) as usize;
            Resolved::Payload(&self.sigma.entries[n as usize - 1 - rel])
        } else {
            Resolved::Renumber(GlobalVar::index(i - n))
        }
    }

    /// Base and entry count of a context payload, viewed at the current
    /// depths (only the base variable needs shifting).
    fn ctx_payload_shape(c: &LocalCtx, at: Depths) -> (CtxBase, u32) {
        let base = match c.base {
            CtxBase::Nil => CtxBase::Nil,
            CtxBase::Var(g) => CtxBase::Var(g.shifted(at.global)),
        };
        (base, c.entries.len() as u32)
    }
}

impl Mapper for SubstGlobal<'_> {
    const LOCAL_OP: bool = false;
    const NAME: &'static str = "apply_global";

    fn changes(&mut self) -> &mut u64 {
        &mut self.changes
    }

    fn memo(&mut self) -> Option<&mut NodeMemo> {
        Some(&mut self.memo)
    }

    // σ replaces the innermost free variables and renumbers the rest: a
    // subtree with no free variable is its own image.
    fn skip_ty(&mut self, t: &Rc<Type>, at: Depths) -> bool {
        bounds::skip_global_type(t, at.global)
    }
    fn skip_tm(&mut self, t: &Rc<Term>, at: Depths) -> bool {
        bounds::skip_global_term(t, at.global)
    }

    fn global_ty(&mut self, var: GlobalVar, subst: LocalSubst, at: Depths) -> Type {
        match self.resolve(var, at) {
            Resolved::Bound => Type::GlobalTy { var, subst },
            Resolved::Renumber(v) => {
                self.note();
                Type::GlobalTy { var: v, subst }
            }
            Resolved::Payload(GlobalEntry::Ty(t)) => {
                self.note();
                t.shift_global(at.global).shift_univ(at.univ).apply_local(&subst)
            }
            Resolved::Payload(_) => panic!(
                "kernel invariant violated: type-level global variable substituted by a \
                 non-type payload"
            ),
        }
    }

    fn global_tm(&mut self, var: GlobalVar, subst: LocalSubst, at: Depths) -> Term {
        match self.resolve(var, at) {
            Resolved::Bound => Term::GlobalTm { var, subst },
            Resolved::Renumber(v) => {
                self.note();
                Term::GlobalTm { var: v, subst }
            }
            Resolved::Payload(GlobalEntry::Tm(t)) => {
                self.note();
                t.shift_global(at.global).shift_univ(at.univ).apply_local(&subst)
            }
            Resolved::Payload(_) => panic!(
                "kernel invariant violated: term-level global variable substituted by a \
                 non-term payload"
            ),
        }
    }

    fn ctx_base(&mut self, base: CtxBase, at: Depths) -> (CtxBase, CtxEntries) {
        match base {
            CtxBase::Nil => (CtxBase::Nil, CtxEntries::empty()),
            CtxBase::Var(g) => match self.resolve(g, at) {
                Resolved::Bound => (CtxBase::Var(g), CtxEntries::empty()),
                Resolved::Renumber(v) => {
                    self.note();
                    (CtxBase::Var(v), CtxEntries::empty())
                }
                Resolved::Payload(GlobalEntry::Ctx(c)) => {
                    self.note();
                    let shifted = c.shift_global(at.global).shift_univ(at.univ);
                    (shifted.base, shifted.entries)
                }
                Resolved::Payload(_) => panic!(
                    "kernel invariant violated: context variable substituted by a non-context \
                     payload"
                ),
            },
        }
    }

    fn tail(&mut self, tail: SubstTail, at: Depths) -> (SubstTail, Vec<Rc<Term>>) {
        match tail {
            SubstTail::Wk { len, ctx_var } => match self.resolve(ctx_var, at) {
                Resolved::Bound => (SubstTail::Wk { len, ctx_var }, Vec::new()),
                Resolved::Renumber(v) => {
                    self.note();
                    (SubstTail::Wk { len, ctx_var: v }, Vec::new())
                }
                Resolved::Payload(GlobalEntry::Ctx(c)) => {
                    self.note();
                    // wk^k_g becomes the generalized weakening wk^k_{Γ'}: the
                    // spliced entries of Γ' sit below the k source entries,
                    // so entry j (outermost = 0) is variable k + m' - 1 - j.
                    let (base, m_prime) = Self::ctx_payload_shape(c, at);
                    let new_tail = match base {
                        CtxBase::Nil => SubstTail::Empty,
                        CtxBase::Var(g) => SubstTail::Wk { len: len + m_prime, ctx_var: g },
                    };
                    let terms = (0..m_prime)
                        .map(|j| Rc::new(Term::Var(LocalVar(len + m_prime - 1 - j))))
                        .collect();
                    (new_tail, terms)
                }
                Resolved::Payload(_) => panic!(
                    "kernel invariant violated: context variable substituted by a non-context \
                     payload"
                ),
            },
            SubstTail::Empty => (tail, Vec::new()),
        }
    }
}

// ---------------------------------------------------------------------------
// Public API
// ---------------------------------------------------------------------------

macro_rules! ops {
    ($ty:ident, $map:ident) => {
        impl $ty {
            /// Apply a universe substitution `φ`.
            pub fn apply_univ(&self, phi: &[Level]) -> $ty {
                $map(self, &mut SubstUniv { phi, changes: 0, memo: NodeMemo::default() }, Depths::default())
            }

            /// Instantiate the innermost `phi.len()` universe variables
            /// (`phi[0]` innermost), renumbering deeper variables down.
            pub fn inst_univ(&self, phi: &[Level]) -> $ty {
                $map(self, &mut InstUniv { phi, changes: 0, memo: NodeMemo::default() }, Depths::default())
            }

            /// Apply a local substitution `δ` (`self` scoped in δ's target).
            pub fn apply_local(&self, delta: &LocalSubst) -> $ty {
                $map(self, &mut SubstLocal { delta, changes: 0, lifted: Lifted::default(), memo: NodeMemo::default() }, Depths::default())
            }

            /// Apply a global substitution `σ`.
            pub fn apply_global(&self, sigma: &GlobalSubst) -> $ty {
                $map(self, &mut SubstGlobal { sigma, changes: 0, memo: NodeMemo::default() }, Depths::default())
            }

            /// `self[s/x]` weakened past `by` binders: `self` is scoped in
            /// `Γ, x`, `s` and the result in `Γ, Δ` with `|Δ| = by`. See
            /// [`InstTop`].
            pub fn inst_top(&self, by: u32, payload: &Term) -> $ty {
                $map(self, &mut InstTop { payload, by, changes: 0, node: None, lifted: Lifted::default(), memo: NodeMemo::default() }, Depths::default())
            }

            /// [`Self::inst_top`] below `cutoff` binders that stay fixed:
            /// `self` is scoped in `Γ, x, Θ` with `|Θ| = cutoff`, `s` in
            /// `Γ, Δ`, and the result in `Γ, Δ, Θ` (the Coq formalization's
            /// `⟨rlift ↑⟩ⁿ…[llift (lsingle s)]`). `IWf`'s child index is
            /// instantiated at a shape this way, under its position binder.
            pub fn inst_top_above(&self, by: u32, cutoff: u32, payload: &Term) -> $ty {
                $map(
                    self,
                    &mut InstTop { payload, by, changes: 0, node: None, lifted: Lifted::default(), memo: NodeMemo::default() },
                    Depths { local: cutoff, ..Depths::default() },
                )
            }

            /// Weaken the ambient local context by `by` entries.
            pub fn shift_local(&self, by: u32) -> $ty {
                if by == 0 {
                    return self.clone(); // see §Shifting by zero
                }
                $map(self, &mut ShiftLocal { by, changes: 0, memo: NodeMemo::default() }, Depths::default())
            }

            /// Weaken the local context by `by` entries between existing
            /// binders: the innermost `cutoff` locals stay fixed (the Coq
            /// formalization's `⟨rlift ↑⟩`, iterated). See
            /// [`Self::shift_univ_above`].
            pub fn shift_local_above(&self, by: u32, cutoff: u32) -> $ty {
                if by == 0 {
                    return self.clone(); // see §Shifting by zero
                }
                $map(self, &mut ShiftLocal { by, changes: 0, memo: NodeMemo::default() }, Depths { local: cutoff, ..Depths::default() })
            }

            /// Weaken the global context by `by` bindings.
            pub fn shift_global(&self, by: u32) -> $ty {
                if by == 0 {
                    return self.clone(); // see §Shifting by zero
                }
                $map(self, &mut ShiftGlobal { by, changes: 0, memo: NodeMemo::default() }, Depths::default())
            }

            /// Weaken the universe context by `by` variables.
            pub fn shift_univ(&self, by: u32) -> $ty {
                if by == 0 {
                    return self.clone(); // see §Shifting by zero
                }
                $map(self, &mut ShiftUniv { by, changes: 0, memo: NodeMemo::default() }, Depths::default())
            }

            /// Weaken the universe context by `by` variables *between*
            /// existing binders: the innermost `cutoff` variables stay
            /// fixed, everything above shifts. Used by conversion to view a
            /// recursor motive (scoped in `L, ℓ`) under a branch telescope
            /// (scoped in `L, ℓ⃗` with the motive's own binder still to be
            /// instantiated).
            pub fn shift_univ_above(&self, by: u32, cutoff: u32) -> $ty {
                if by == 0 {
                    return self.clone(); // see §Shifting by zero
                }
                $map(self, &mut ShiftUniv { by, changes: 0, memo: NodeMemo::default() }, Depths { univ: cutoff, ..Depths::default() })
            }

            /// Weaken the global context by `by` bindings between existing
            /// binders: the innermost `cutoff` bindings stay fixed. See
            /// [`Self::shift_univ_above`]. The new bindings are variables,
            /// so they go in among the variables: the innermost `cutoff`
            /// bindings must all be variables, as every binder's are. (Among
            /// the constants there is nothing to insert: a signature grows
            /// at its end, and no reference moves when it does.)
            pub fn shift_global_above(&self, by: u32, cutoff: u32) -> $ty {
                if by == 0 {
                    return self.clone(); // see §Shifting by zero
                }
                $map(self, &mut ShiftGlobal { by, changes: 0, memo: NodeMemo::default() }, Depths { global: cutoff, ..Depths::default() })
            }

            /// Rename every free global variable through `map`, which sees
            /// and returns indices counted from outside the term; `None` when
            /// the map refused one. See [`ReindexGlobal`].
            pub fn reindex_global(&self, map: &mut dyn FnMut(GlobalRef) -> Option<GlobalRef>) -> Option<$ty> {
                let mut m = ReindexGlobal { map, failed: false, changes: 0, memo: NodeMemo::default() };
                let out = $map(self, &mut m, Depths::default());
                (!m.failed).then_some(out)
            }
        }
    };
}

ops!(Type, map_type);
ops!(Term, map_term);

impl Type {
    /// Abstract a **term** out of a type: the result is scoped in `Γ, z`
    /// (`z` of the abstracted term's type) with every occurrence of `pat`
    /// replaced by `z`, or `None` when there is no occurrence to replace.
    ///
    /// `None` rather than the constant function, because the two answers are
    /// different *facts* and every caller so far wants to try something else
    /// before settling for the constant one
    /// (`docs/elaborator/goal-motive-synthesis-design.md` §3.2).
    ///
    /// `self` is weakened into `Γ, z` first, so a `pat` occurring under `k`
    /// binders is matched against `pat` weakened by `k + 1` and the variable
    /// planted is `Var(k)`: nothing is captured, and nothing is matched
    /// across a scope this operation does not own (boxed code and the other
    /// foreign-context subtrees are left whole, as for every local operation).
    pub fn abstract_local(&self, pat: &Term) -> Option<Type> {
        self.abstract_local_with(pat, &Term::Var(LocalVar(0)))
    }

    /// [`Self::abstract_local`] over **several** spellings of one term: every
    /// occurrence of every pattern becomes the same `z`.
    ///
    /// One abstraction, not a fold of several: abstracting `a` and then `b`
    /// would bind two variables, and what the caller has is one scrutinee
    /// that the goal spells more than one way (`docs/goal-motive-synthesis-
    /// design.md` §4.4). Catching one spelling and not the other is worse
    /// than catching neither — the arms then face a goal half-specialized.
    pub fn abstract_local_any(&self, pats: &[Term]) -> Option<Type> {
        let z = Term::Var(LocalVar(0));
        let pairs: Vec<(Term, Term)> =
            pats.iter().map(|p| (p.clone(), z.clone())).collect();
        self.abstract_pats(&pairs)
    }

    /// [`Self::abstract_local`] with the planted term given: every occurrence
    /// of `pat` becomes `rep`, which is scoped in `Γ, z` and is expected to
    /// mention `z` (or the result is a constant motive spelled the long way).
    ///
    /// The generality is one caller's, and a real one: a constructor field is
    /// reached from a goal that mentions the *value*, so what abstracting the
    /// field does to that value is rebuild it around `z`
    /// (`docs/elaborator/goal-motive-synthesis-design.md` §5). The `[pat/z]` instance is
    /// then the original only up to `rep[pat/z] ≡ pat` — for that caller,
    /// Σ/Unit-η — which is why this returns a term to be *checked* and not a
    /// proof of anything.
    pub fn abstract_local_with(&self, pat: &Term, rep: &Term) -> Option<Type> {
        self.abstract_pats(&[(pat.clone(), rep.clone())])
    }

    /// [`Self::abstract_local_with`] for several patterns at once, each
    /// planting its own term, all under the one binder `z`: one scrutinee a
    /// goal reaches through several spellings, each rebuilt around `z`. The
    /// `[pat/z]` instance is again the original only up to each
    /// `rep[pat/z] ≡ pat`, so the result is to be checked, not trusted.
    pub fn abstract_local_with_all(&self, pats: &[(Term, Term)]) -> Option<Type> {
        self.abstract_pats(pats)
    }

    /// [`Self::abstract_local`] at **selected** occurrences only: `at` lists
    /// them 1-based, in the order the traversal meets them — left to right
    /// through the goal as written, an application's annotations before its
    /// argument. Also returns how many occurrences there were, which is what
    /// a caller says when a selection names one past the end.
    ///
    /// Still the inverse of the singleton substitution, by the same argument:
    /// every replaced position held `pat`, so `[pat/z]` gives `self` back.
    ///
    /// Several patterns are several spellings of one term, as in
    /// [`Self::abstract_local_any`], numbered together: an occurrence is a
    /// position holding any of them.
    pub fn abstract_local_at(&self, pats: &[Term], at: &[u32]) -> (Option<Type>, u32) {
        let z = Term::Var(LocalVar(0));
        let pats: Vec<(Term, Term)> = pats.iter().map(|p| (p.clone(), z.clone())).collect();
        let mut m = AbstractLocal::new(&pats, Some(at));
        let out = map_type(self, &mut m, Depths::default());
        ((m.hits > 0).then_some(out), m.seen)
    }

    /// Every term node of `self` that sits under no binder of any of the
    /// three namespaces — so is scoped in `self`'s own context — in the order
    /// the traversal meets them (the order [`Self::abstract_local_at`]
    /// numbers by), outermost first. A node's subterms follow it. A shared
    /// node is listed, and walked, once: where the traversal first meets it.
    pub fn root_terms(&self) -> Vec<Rc<Term>> {
        let mut m = RootTerms { out: Vec::new(), changes: 0, memo: NodeMemo::default() };
        map_type(self, &mut m, Depths::default());
        m.out
    }

    /// Whether [`Self::abstract_local`] would find `pat`: the same
    /// occurrences, by the same walk, but only read. Nothing is built (the
    /// abstraction makes room for `z` under every free local, which is a
    /// copy of most of a type) and the walk stops at the first occurrence.
    /// For a caller that only wants to abstract when there is something to
    /// abstract, and usually finds nothing
    /// (`issues/match-arm-coercion-abstracts-both-types.md`).
    pub fn mentions_local(&self, pat: &Term) -> bool {
        let pats = [(pat.clone(), Term::Var(LocalVar(0)))];
        let mut m = OccursLocal { find: AbstractLocal::new(&pats, None), changes: 0, memo: NodeMemo::default() };
        let _ = map_type(self, &mut m, Depths::default());
        debug_assert_eq!(m.changes, 0);
        m.find.hits > 0
    }

    fn abstract_pats(&self, pats: &[(Term, Term)]) -> Option<Type> {
        let mut m = AbstractLocal::new(pats, None);
        let out = map_type(self, &mut m, Depths::default());
        (m.hits > 0).then_some(out)
    }
}

impl LocalCtx {
    pub fn apply_univ(&self, phi: &[Level]) -> LocalCtx {
        map_ctx(self, &mut SubstUniv { phi, changes: 0, memo: NodeMemo::default() }, Depths::default())
    }

    pub fn apply_global(&self, sigma: &GlobalSubst) -> LocalCtx {
        map_ctx(self, &mut SubstGlobal { sigma, changes: 0, memo: NodeMemo::default() }, Depths::default())
    }

    pub fn shift_global(&self, by: u32) -> LocalCtx {
        if by == 0 {
            return self.clone(); // see §Shifting by zero
        }
        map_ctx(self, &mut ShiftGlobal { by, changes: 0, memo: NodeMemo::default() }, Depths::default())
    }

    /// [`Self::shift_global`] between existing bindings: the innermost
    /// `cutoff` stay fixed. See [`Type::shift_global_above`].
    pub fn shift_global_above(&self, by: u32, cutoff: u32) -> LocalCtx {
        if by == 0 {
            return self.clone(); // see §Shifting by zero
        }
        map_ctx(self, &mut ShiftGlobal { by, changes: 0, memo: NodeMemo::default() }, Depths { global: cutoff, ..Depths::default() })
    }

    pub fn shift_univ(&self, by: u32) -> LocalCtx {
        if by == 0 {
            return self.clone(); // see §Shifting by zero
        }
        map_ctx(self, &mut ShiftUniv { by, changes: 0, memo: NodeMemo::default() }, Depths::default())
    }
}

impl LocalSubst {
    /// The identity substitution `id_Γ = wk^0_Γ`, fully expanded. It reads
    /// only Γ's [`CtxShape`].
    pub fn id(ctx: impl Into<CtxShape>) -> LocalSubst {
    let CtxShape { base, len: m } = ctx.into();
    let tail = match base {
            CtxBase::Nil => SubstTail::Empty,
            CtxBase::Var(g) => SubstTail::Wk { len: m, ctx_var: g },
        };
        // Shared leaves: `|Γ|` refcount increments, not `|Γ|` allocations
        // (`issues/subst-per-call-allocations.md`).
        let terms = Term::var_rcs_descending(m);
        LocalSubst { tail, terms }
    }

    /// `δ, t/x` — extend to one more target entry; `t` is scoped in δ's
    /// source. `LocalSubst::id(gamma).extended(s)` is the β-substitution
    /// `[s/x]` for a body scoped in `Γ, x`.
    pub fn extended(mut self, t: Rc<Term>) -> LocalSubst {
        self.terms.push(t);
        self
    }

    /// Composition `self ∘ other`: `t[self][other] == t[self.compose(other)]`.
    pub fn compose(&self, other: &LocalSubst) -> LocalSubst {
        map_subst(self, &mut SubstLocal { delta: other, changes: 0, lifted: Lifted::default(), memo: NodeMemo::default() }, Depths::default())
    }

    pub fn apply_univ(&self, phi: &[Level]) -> LocalSubst {
        map_subst(self, &mut SubstUniv { phi, changes: 0, memo: NodeMemo::default() }, Depths::default())
    }

    pub fn apply_global(&self, sigma: &GlobalSubst) -> LocalSubst {
        map_subst(self, &mut SubstGlobal { sigma, changes: 0, memo: NodeMemo::default() }, Depths::default())
    }

    pub fn shift_local(&self, by: u32) -> LocalSubst {
        if by == 0 {
            return self.clone(); // see §Shifting by zero
        }
        map_subst(self, &mut ShiftLocal { by, changes: 0, memo: NodeMemo::default() }, Depths::default())
    }

    pub fn shift_global(&self, by: u32) -> LocalSubst {
        if by == 0 {
            return self.clone(); // see §Shifting by zero
        }
        map_subst(self, &mut ShiftGlobal { by, changes: 0, memo: NodeMemo::default() }, Depths::default())
    }
}

// ---------------------------------------------------------------------------
// Free global variables, by subtree
// ---------------------------------------------------------------------------

/// The traversal with a mapper that only looks: it changes nothing and
/// records `1 +` the largest global variable free in what it walks (`0` for
/// none), which is what [`ShiftGlobal`] and [`SubstGlobal`] skip on
/// (`bounds.rs`, §The global namespace). Being the same generic walk those
/// two are, it crosses the binders they cross and reads the subtrees they
/// read, by construction.
///
/// It walks one node: a child that is a term or a type is asked for through
/// the memo ([`bounds::global_bound_term`]), which answers from the child's
/// head or by running this on the child, and the child's bound is read from outside
/// the global binders between it and the node.
struct GlobalBound {
    bound: u32,
    changes: u64,
}

impl GlobalBound {
    fn see(&mut self, v: GlobalVar, at: Depths) {
        if let Some(i) = v.as_index() {
            if i >= at.global {
                self.bound = self.bound.max(i - at.global + 1);
            }
        }
    }
}

impl Mapper for GlobalBound {
    const LOCAL_OP: bool = false;
    const NAME: &'static str = "free_global_bound";
    // Its "skips" are memo reads, not claims that a walk would change
    // nothing: there is nothing to verify by walking again.
    const VERIFY_SKIPS: bool = false;

    fn changes(&mut self) -> &mut u64 {
        &mut self.changes
    }

    fn global_ty(&mut self, var: GlobalVar, subst: LocalSubst, at: Depths) -> Type {
        self.see(var, at);
        Type::GlobalTy { var, subst }
    }

    fn global_tm(&mut self, var: GlobalVar, subst: LocalSubst, at: Depths) -> Term {
        self.see(var, at);
        Term::GlobalTm { var, subst }
    }

    fn ctx_base(&mut self, base: CtxBase, at: Depths) -> (CtxBase, CtxEntries) {
        if let CtxBase::Var(g) = base {
            self.see(g, at);
        }
        (base, CtxEntries::empty())
    }

    fn tail(&mut self, tail: SubstTail, at: Depths) -> (SubstTail, Vec<Rc<Term>>) {
        if let SubstTail::Wk { ctx_var, .. } = tail {
            self.see(ctx_var, at);
        }
        (tail, Vec::new())
    }

    fn skip_ty(&mut self, t: &Rc<Type>, at: Depths) -> bool {
        self.bound = self.bound.max(bounds::global_bound_type(t).saturating_sub(at.global));
        true
    }

    fn skip_tm(&mut self, t: &Rc<Term>, at: Depths) -> bool {
        self.bound = self.bound.max(bounds::global_bound_term(t).saturating_sub(at.global));
        true
    }
}

/// One node's walk for [`bounds::global_bound_term`]; call that instead.
pub(crate) fn free_global_bound_term(t: &Term) -> u32 {
    let mut m = GlobalBound { bound: 0, changes: 0 };
    let _ = map_term(t, &mut m, Depths::default());
    debug_assert_eq!(m.changes, 0);
    m.bound
}

/// One node's walk for [`bounds::global_bound_type`]; call that instead.
pub(crate) fn free_global_bound_type(t: &Type) -> u32 {
    let mut m = GlobalBound { bound: 0, changes: 0 };
    let _ = map_type(t, &mut m, Depths::default());
    debug_assert_eq!(m.changes, 0);
    m.bound
}

/// `1 +` the largest global **variable** free in `t`, `0` when it mentions
/// none: constants are not variables. A term or type with bound `0` is
/// closed in Ψ's variables, which is what a committed binding's parts are
/// ([`crate::term::GlobalCtx::commit`]) and what makes `shift_global` and
/// `apply_global` the identity on it.
pub fn global_var_bound_tm(t: &Rc<Term>) -> u32 {
    bounds::global_bound_term(t)
}

/// [`global_var_bound_tm`] for a type.
pub fn global_var_bound_ty(t: &Rc<Type>) -> u32 {
    bounds::global_bound_type(t)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::level::UnivVar;

    fn rt(t: Term) -> Rc<Term> {
        Rc::new(t)
    }

    fn nat_entry() -> CtxEntry {
        CtxEntry { ty: Rc::new(Type::Nat), level: Level::Zero }
    }

    fn nil_ctx(n: u32) -> LocalCtx {
        LocalCtx::from_vec(CtxBase::Nil, (0..n).map(|_| nat_entry()).collect())
    }

    /// §Keeping a shared DAG shared: a chain whose every link holds the
    /// previous one as both children is `k` nodes in memory and `2^k` as a
    /// tree. A shift and a substitution each visit it in O(k) and return it
    /// exactly as shared as it was.
    #[test]
    fn a_shared_chain_stays_shared_through_shift_and_substitution() {
        const K: u32 = 24;
        let nat = Rc::new(Type::Nat);
        let mut t = rt(Term::Var(LocalVar(0)));
        for _ in 0..K {
            t = rt(Term::App {
                fun: Rc::clone(&t),
                dom_level: Level::Zero,
                cod_level: Level::Zero,
                dom: Rc::clone(&nat),
                cod: Rc::clone(&nat),
                arg: t,
            });
        }
        let gamma = nil_ctx(1);
        let succ = |v: u32| Term::Succ(rt(Term::Var(LocalVar(v))));
        let delta = LocalSubst::id(&gamma).extended(rt(succ(0)));
        let ops: [(&str, &dyn Fn(&Term) -> Term, Term); 2] = [
            ("shift_local", &|t: &Term| t.shift_local(1), Term::Var(LocalVar(1))),
            ("apply_local", &|t: &Term| t.apply_local(&delta), succ(0)),
        ];
        for (name, op, leaf) in ops {
            let before = crate::stats::snapshot();
            let out = op(&t);
            let d = crate::stats::snapshot().since(&before);
            assert!(d.local_subst_nodes <= 8 * K as u64, "{name} visited {} nodes", d.local_subst_nodes);
            assert!(d.subst_memo_hits >= K as u64 - 1, "{name} hit its memo {} times", d.subst_memo_hits);
            let mut node: &Term = &out;
            for _ in 0..K {
                let Term::App { fun, arg, .. } = node else { panic!("{name} changed the chain's shape") };
                assert!(Rc::ptr_eq(fun, arg), "{name} copied a shared child apart");
                node = &**fun;
            }
            assert_eq!(*node, leaf, "{name} at the leaf");
        }
    }

    /// A substituted variable is a node the substitution already had, never
    /// a copy of one: the payload itself under no binder and wherever
    /// lifting does not change it, and one lifted node per depth otherwise.
    /// Stated on pointers, since a copy is equal: a copy of the payload's
    /// root would lose its identity, and with it its bounds and every memo
    /// entry keyed by its address.
    #[test]
    fn a_substituted_variable_is_the_payloads_own_node() {
        crate::checks::set_skip_verification(crate::checks::SkipVerification::Full);
        let nat = Rc::new(Type::Nat);
        let app = |fun: Rc<Term>, arg: Rc<Term>| {
            rt(Term::App {
                fun,
                dom_level: Level::Zero,
                cod_level: Level::Zero,
                dom: Rc::clone(&nat),
                cod: Rc::clone(&nat),
                arg,
            })
        };
        let lam = |body: Rc<Term>| {
            rt(Term::Lam { dom_level: Level::Zero, cod_level: Level::Zero, dom: Rc::clone(&nat), body })
        };
        // Two leaves of one variable that are two nodes, so that nothing
        // but the mapper can make their images one.
        let var = |i: u32| Rc::new(Term::Var(LocalVar(i)));
        let children = |t: &Rc<Term>| match &**t {
            Term::App { fun, arg, .. } => (Rc::clone(fun), Rc::clone(arg)),
            _ => panic!("the application's shape changed"),
        };
        let body_of = |t: &Rc<Term>| match &**t {
            Term::Lam { body, .. } => Rc::clone(body),
            _ => panic!("the binder's shape changed"),
        };
        // `x x` at depth zero and under one binder, in `·, y, x`.
        let flat = app(var(0), var(0));
        let under = lam(app(var(1), var(1)));
        let gamma = nil_ctx(1);

        // A closed payload is itself at every depth.
        let closed = rt(Term::Succ(rt(Term::Zero)));
        let delta = LocalSubst::id(&gamma).extended(Rc::clone(&closed));
        let (f, a) = children(&sub_tm(&flat, &mut subst_local(&delta), Depths::default()));
        assert!(Rc::ptr_eq(&f, &closed) && Rc::ptr_eq(&a, &closed), "a payload was copied under no binder");
        let (f, a) = children(&body_of(&sub_tm(&under, &mut subst_local(&delta), Depths::default())));
        assert!(Rc::ptr_eq(&f, &closed) && Rc::ptr_eq(&a, &closed), "a closed payload was copied under a binder");

        // An open one is itself under no binder, and one lifted node for
        // both occurrences under the binder.
        let open = rt(Term::Succ(var(0)));
        let delta = LocalSubst::id(&gamma).extended(Rc::clone(&open));
        let (f, a) = children(&sub_tm(&flat, &mut subst_local(&delta), Depths::default()));
        assert!(Rc::ptr_eq(&f, &open) && Rc::ptr_eq(&a, &open), "an open payload was copied under no binder");
        let (f, a) = children(&body_of(&sub_tm(&under, &mut subst_local(&delta), Depths::default())));
        assert!(Rc::ptr_eq(&f, &a), "an open payload was lifted once per occurrence");
        assert_eq!(*f, Term::Succ(var(1)));
        assert!(!Rc::ptr_eq(&f, &open));

        // `inst_top` has one payload, by value: one node for it per depth.
        let top = |t: &Rc<Term>| {
            let mut m = InstTop { payload: &open, by: 1, changes: 0, node: None, lifted: Lifted::default(), memo: NodeMemo::default() };
            sub_tm(t, &mut m, Depths::default())
        };
        let (f, a) = children(&top(&flat));
        assert!(Rc::ptr_eq(&f, &a) && *f == *open, "inst_top copied its payload per occurrence");
        let (f, a) = children(&body_of(&top(&under)));
        assert!(Rc::ptr_eq(&f, &a) && *f == Term::Succ(var(1)), "inst_top lifted its payload per occurrence");

        // A variable payload is the shared leaf, and the identity is no
        // change at all.
        let delta = LocalSubst::id(&nil_ctx(2)).extended(var(1));
        let (f, _) = children(&body_of(&sub_tm(&under, &mut subst_local(&delta), Depths::default())));
        assert!(Rc::ptr_eq(&f, &Term::var_rc(2)));
        let id = LocalSubst::id(&nil_ctx(2));
        assert!(Rc::ptr_eq(&sub_tm(&under, &mut subst_local(&id), Depths::default()), &under), "t[id] is not t");
    }

    fn subst_local(delta: &LocalSubst) -> SubstLocal<'_> {
        SubstLocal { delta, changes: 0, lifted: Lifted::default(), memo: NodeMemo::default() }
    }

    #[test]
    fn single_instantiation() {
        // Body scoped in (·, x0, x1, x2); substitute s for x2 (= Var 0).
        let gamma = nil_ctx(2);
        let s = rt(Term::Zero);
        let delta = LocalSubst::id(&gamma).extended(s);
        assert_eq!(Term::Var(LocalVar(0)).apply_local(&delta), Term::Zero);
        assert_eq!(
            Term::Var(LocalVar(1)).apply_local(&delta),
            Term::Var(LocalVar(0))
        );
        assert_eq!(
            Term::Var(LocalVar(2)).apply_local(&delta),
            Term::Var(LocalVar(1))
        );
    }

    #[test]
    fn beta_under_binder_shifts_payload() {
        // (Γ, x) ⊢ λy. x — substituting s for x must shift s under the λ.
        let gamma = nil_ctx(1);
        let s = rt(Term::Var(LocalVar(0))); // refers to Γ's entry
        let delta = LocalSubst::id(&gamma).extended(s);
        let body = Term::Lam {
            dom_level: Level::Zero,
            cod_level: Level::Zero,
            dom: Rc::new(Type::Nat),
            body: rt(Term::Var(LocalVar(1))), // x, under the λ binder
        };
        let expect = Term::Lam {
            dom_level: Level::Zero,
            cod_level: Level::Zero,
            dom: Rc::new(Type::Nat),
            body: rt(Term::Var(LocalVar(1))), // Γ's entry, shifted under λ
        };
        assert_eq!(body.apply_local(&delta), expect);
    }

    #[test]
    fn box_blocks_local_substitution() {
        let gamma = nil_ctx(0);
        let delta = LocalSubst::id(&gamma).extended(rt(Term::Zero));
        let boxed = Term::BoxTm(rt(Term::Var(LocalVar(0))));
        assert_eq!(boxed.apply_local(&delta), boxed);
    }

    #[test]
    fn local_payload_univ_shifted_under_ulam() {
        // Substituting Ty ℓ0 for x under Λℓ. …: the payload's level must
        // become ℓ1 inside.
        let delta = LocalSubst {
            tail: SubstTail::Empty,
            terms: vec![rt(Term::TmTy(Level::Var(UnivVar(0))))],
        };
        let t = Term::ULam {
            num_vars: 1,
            level: Level::Zero,
            body: rt(Term::Var(LocalVar(0))),
        };
        let expect = Term::ULam {
            num_vars: 1,
            level: Level::Zero,
            body: rt(Term::TmTy(Level::Var(UnivVar(1)))),
        };
        assert_eq!(t.apply_local(&delta), expect);
    }

    #[test]
    fn ctx_binder_capture_avoidance() {
        // (Πg. □(g ⊢ Ty 0))[σ]: the bound g (Var 0 under the binder) must
        // survive; a free context variable (Var 1 under the binder) is
        // substituted, splicing the payload's entries.
        let payload = GlobalSubst::single(GlobalEntry::Ctx(nil_ctx(1)));
        let bound = Type::CtxPi {
            level: Level::Zero,
            body: Rc::new(Type::CodeTy {
                ctx: LocalCtx::ctx_var(GlobalVar::index(0)),
                level: Level::Zero,
            }),
        };
        assert_eq!(bound.apply_global(&payload), bound);

        let free = Type::CtxPi {
            level: Level::Zero,
            body: Rc::new(Type::CodeTy {
                ctx: LocalCtx::ctx_var(GlobalVar::index(1)),
                level: Level::Zero,
            }),
        };
        let expect = Type::CtxPi {
            level: Level::Zero,
            body: Rc::new(Type::CodeTy { ctx: nil_ctx(1), level: Level::Zero }),
        };
        assert_eq!(free.apply_global(&payload), expect);
    }

    #[test]
    fn sigma_expands_weakening_tail() {
        // Ψ = (g : Ctx, u : Trm(g ⊢ …)); current local context (g, 1 entry).
        // t = u^{wk¹_g}. σ substitutes Γ' = (·, 2 entries) for g and
        // s = Var 0 (innermost of Γ') for u.
        // Expected: δ' = {·³; [Var 2, Var 1]} and result s[δ'] = Var 1.
        let t = Term::GlobalTm {
            var: GlobalVar::index(0),
            subst: LocalSubst {
                tail: SubstTail::Wk { len: 1, ctx_var: GlobalVar::index(1) },
                terms: vec![],
            },
        };
        let sigma = GlobalSubst {
            entries: vec![
                GlobalEntry::Ctx(nil_ctx(2)),
                GlobalEntry::Tm(rt(Term::Var(LocalVar(0)))),
            ],
        };
        assert_eq!(t.apply_global(&sigma), Term::Var(LocalVar(1)));

        // The same, but keeping the substitution un-consumed: a variable
        // payload deeper than Γ' maps through the expanded weakening.
        let t2 = Term::GlobalTm {
            var: GlobalVar::index(0),
            subst: LocalSubst {
                tail: SubstTail::Wk { len: 1, ctx_var: GlobalVar::index(1) },
                terms: vec![],
            },
        };
        let sigma2 = GlobalSubst {
            entries: vec![
                GlobalEntry::Ctx(nil_ctx(2)),
                GlobalEntry::Tm(rt(Term::Var(LocalVar(1)))), // outer entry of Γ'
            ],
        };
        assert_eq!(t2.apply_global(&sigma2), Term::Var(LocalVar(2)));
    }

    #[test]
    fn reindex_global_maps_free_and_keeps_bound() {
        // □(g' ⊢ Ty 0) → Πg. □(g ⊢ Ty 0): the bound g (Var 0 under its
        // binder) stays, the free g' goes through the map, which sees it
        // counted from outside the term.
        let ty = |bound: u32, free: u32| Type::Pi {
            dom_level: Level::Zero,
            cod_level: Level::Zero,
            dom: Rc::new(Type::CodeTy { ctx: LocalCtx::ctx_var(GlobalVar::index(free)), level: Level::Zero }),
            cod: Rc::new(Type::CtxPi {
                level: Level::Zero,
                body: Rc::new(Type::CodeTy { ctx: LocalCtx::ctx_var(GlobalVar::index(bound)), level: Level::Zero }),
            }),
        };
        let t = ty(0, 0);
        let mut seen = Vec::new();
        let out = t.reindex_global(&mut |r| {
            r.map_var(|i| {
                seen.push(i);
                Some(i + 3)
            })
        });
        assert_eq!(seen, vec![0], "the bound variable is not the map's");
        assert_eq!(out, Some(ty(0, 3)));
        // Under the binder the free index is GlobalVar::index(1), seen as 0.
        let under = |g: u32| Type::CtxPi {
            level: Level::Zero,
            body: Rc::new(Type::CodeTy { ctx: LocalCtx::ctx_var(GlobalVar::index(g)), level: Level::Zero }),
        };
        assert_eq!(under(1).reindex_global(&mut |r| Some(r)), Some(under(1)));
        assert_eq!(under(1).reindex_global(&mut |r| r.map_var(|i| Some(i + 2))), Some(under(3)));
        // A refusal anywhere refuses the whole term.
        assert_eq!(t.reindex_global(&mut |_| None), None);
    }

    #[test]
    fn reindex_global_reaches_substitution_tails() {
        // u^{wk¹_g}: both the head and the weakening's context variable are
        // free globals.
        let t = |u: u32, g: u32| Term::GlobalTm {
            var: GlobalVar::index(u),
            subst: LocalSubst { tail: SubstTail::Wk { len: 1, ctx_var: GlobalVar::index(g) }, terms: vec![] },
        };
        assert_eq!(t(0, 1).reindex_global(&mut |r| r.map_var(|i| Some(i * 10))), Some(t(0, 10)));
        assert_eq!(t(0, 1).reindex_global(&mut |r| r.map_var(|i| (i == 0).then_some(5))), None);
    }
}

// -- the quote boundary's rebuild (docs/elaborator/intro-by-type-design.md §2.3) ------

/// [`crate::typing::spell_checked_in_code`]'s second half: every checked
/// spelling the eager checker recorded is replaced by its component form,
/// children first mapped the same way. `base` is the Γ length the record was
/// keyed at the root. A checked spelling with no record is left in place and
/// counted, so the caller can tell "nothing to do" from "could not".
struct RebuildChecked<'a> {
    spelled: &'a std::collections::HashMap<(usize, u32), Option<crate::typing::Spelled>>,
    base: u32,
    /// Whether every checked spelling is rewritten (and counted), or only
    /// the introductions `pair@`, `inl@`, `inr@`: the exporter's spelling
    /// leaves `app@`, `fst@` and `snd@`, which its targets read as an
    /// application and as projections without annotations.
    all: bool,
    replaced: u64,
    seen: u64,
    changes: u64,
}

impl Mapper for RebuildChecked<'_> {
    const LOCAL_OP: bool = false;
    const NAME: &'static str = "rebuild_checked_spellings";

    fn changes(&mut self) -> &mut u64 {
        &mut self.changes
    }

    fn pre_tm(&mut self, t: &Rc<Term>, at: Depths) -> Option<Term> {
        use crate::typing::Spelled;
        // A packed vector literal is a compact spelling too, and needs no
        // recorded view: it carries its own annotations, so its chain is
        // written out directly (`term::vec_lit_chain`).
        if let Term::VecLit { level, elem, zero, one, width, bits } = &**t {
            if !crate::term::vec_lit_in_range(*width, *bits) {
                return None;
            }
            self.seen += 1;
            self.replaced += 1;
            let elem = sub_ty(elem, self, at);
            let (zero, one) = (sub_tm(zero, self, at), sub_tm(one, self, at));
            return Some(crate::term::vec_lit_chain(level, &elem, &zero, &one, *width, *bits));
        }
        // Likewise an items node (`term::vec_items_chain`): the chain is as
        // deep as the literal is long, which a reader of components asks for.
        if let Term::VecItems { level, elem, items, from } = &**t {
            let live = crate::term::vec_items_live(items, *from)?;
            self.seen += 1;
            self.replaced += 1;
            let elem = sub_ty(elem, self, at);
            let live: Vec<Rc<Term>> = live.iter().map(|item| sub_tm(item, self, at)).collect();
            return Some(crate::term::vec_items_chain(level, &elem, &live));
        }
        if !matches!(
            &**t,
            Term::PairAt { .. }
                | Term::InlAt { .. }
                | Term::InrAt { .. }
                | Term::FstAt { .. }
                | Term::SndAt { .. }
                | Term::AppAt { .. }
        ) || (!self.all && matches!(&**t, Term::AppAt { .. } | Term::FstAt { .. } | Term::SndAt { .. }))
        {
            return None;
        }
        self.seen += 1;
        let key = (Rc::as_ptr(t) as usize, self.base + at.local);
        let Some(spelled) = self.spelled.get(&key)?.clone() else {
            // Viewed at two formers: the node is shared between places
            // that mean different things. Each occurrence gets a node of
            // its own, which the next pass records apart.
            self.replaced += 1;
            return Some((**t).clone());
        };
        let out = match (&**t, spelled) {
            (Term::PairAt { fst, snd, .. }, Spelled::Sigma { fst_level, snd_level, fst: s, snd: u }) => {
                Term::Pair {
                    fst_level,
                    snd_level,
                    fst_ty: s,
                    snd_ty: u,
                    fst: sub_tm(fst, self, at),
                    snd: sub_tm(snd, self, at),
                }
            }
            (Term::FstAt { pair }, Spelled::Sigma { fst_level, snd_level, fst: s, snd: u }) => {
                Term::Fst { fst_level, snd_level, fst_ty: s, snd_ty: u, pair: sub_tm(pair, self, at) }
            }
            (Term::SndAt { pair }, Spelled::Sigma { fst_level, snd_level, fst: s, snd: u }) => {
                Term::Snd { fst_level, snd_level, fst_ty: s, snd_ty: u, pair: sub_tm(pair, self, at) }
            }
            (Term::InlAt { val, .. }, Spelled::Sum { lhs_level, rhs_level, lhs, rhs }) => Term::Inl {
                lhs_level,
                rhs_level,
                lhs,
                rhs,
                val: sub_tm(val, self, at),
            },
            (Term::InrAt { val, .. }, Spelled::Sum { lhs_level, rhs_level, lhs, rhs }) => Term::Inr {
                lhs_level,
                rhs_level,
                lhs,
                rhs,
                val: sub_tm(val, self, at),
            },
            (Term::AppAt { fun, arg }, Spelled::Pi { dom_level, cod_level, dom, cod }) => Term::App {
                fun: sub_tm(fun, self, at),
                dom_level,
                cod_level,
                dom,
                cod,
                arg: sub_tm(arg, self, at),
            },
            _ => return None,
        };
        self.replaced += 1;
        Some(out)
    }
}

/// Rebuild `t` with every recorded checked spelling in its component form;
/// returns the term and how many were replaced.
pub(crate) fn rebuild_checked_spellings(
    t: &Rc<Term>,
    spelled: &std::collections::HashMap<(usize, u32), Option<crate::typing::Spelled>>,
    base: u32,
    all: bool,
) -> (Rc<Term>, u64) {
    let mut m = RebuildChecked { spelled, base, all, replaced: 0, seen: 0, changes: 0 };
    let out = sub_tm(t, &mut m, Depths::default());
    (out, m.replaced)
}

/// How many checked spellings `t` holds, anywhere.
pub(crate) fn count_checked_spellings(t: &Rc<Term>, all: bool) -> u64 {
    let empty = std::collections::HashMap::new();
    let mut m = RebuildChecked { spelled: &empty, base: 0, all, replaced: 0, seen: 0, changes: 0 };
    let _ = sub_tm(t, &mut m, Depths::default());
    m.seen
}

/// [`rebuild_checked_spellings`] over a type.
pub(crate) fn rebuild_checked_spellings_ty(
    t: &Rc<Type>,
    spelled: &std::collections::HashMap<(usize, u32), Option<crate::typing::Spelled>>,
    base: u32,
    all: bool,
) -> (Rc<Type>, u64) {
    let mut m = RebuildChecked { spelled, base, all, replaced: 0, seen: 0, changes: 0 };
    let out = sub_ty(t, &mut m, Depths::default());
    (out, m.replaced)
}

/// [`count_checked_spellings`] over a type.
pub(crate) fn count_checked_spellings_ty(t: &Rc<Type>, all: bool) -> u64 {
    let empty = std::collections::HashMap::new();
    let mut m = RebuildChecked { spelled: &empty, base: 0, all, replaced: 0, seen: 0, changes: 0 };
    let _ = sub_ty(t, &mut m, Depths::default());
    m.seen
}

/// Whether `t` holds a checked spelling anywhere — the cheap question a caller
/// asks before paying for [`crate::typing::spell_checked_in_code`].
pub fn holds_checked_spelling(t: &Rc<Term>) -> bool {
    count_checked_spellings(t, true) > 0
}

/// [`holds_checked_spelling`] over a type.
pub fn holds_checked_spelling_ty(t: &Rc<Type>) -> bool {
    count_checked_spellings_ty(t, true) > 0
}

/// 1 + the largest free local de Bruijn index of `t` (0 when it is locally
/// closed), from the bounds the node keeps for the local traversals
/// (`bounds.rs`). For a reader outside the kernel that pairs syntax with
/// captured entries — the elaborator's readback of a closure — and must not
/// pay for the entries the syntax cannot reach.
pub fn local_bound(t: &Rc<Term>) -> u32 {
    bounds::term_captures(t)
}

/// [`local_bound`] over a type.
pub fn local_bound_ty(t: &Rc<Type>) -> u32 {
    bounds::type_captures(t)
}
