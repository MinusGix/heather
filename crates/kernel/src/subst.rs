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
//!   `·^k_g` into `·^{k+|Γ'|}` over `Γ'`'s base.
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
//! and `Level::shift(0, _)` is the identity because `Level::succ`/`max` are
//! plain constructors that normalize nothing. The `_above` variants are the
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
//!    suite (which runs in the dev profile, including the 300-seed
//!    substitution laws) instead of silently producing a wrong term in
//!    release. Over-reporting is merely slow, so hooks may be conservative;
//!    under-reporting is caught.
//!
//! ## Skipping closed subtrees
//!
//! Sharing alone still *visited* every node, building a temporary from
//! `Rc`-cloned children only to compare the counter and drop it — ~70% of
//! what a substitution did was walking material that could not change
//! (issues/subst-visits-closed-subtrees.md). The **local** operations now
//! skip that walk: before descending, [`sub_ty`]/[`sub_tm`] ask the mapper
//! ([`Mapper::skip_ty`]/[`skip_tm`]) whether the subtree is provably
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
//! the test suite (300-seed substitution laws included) instead of silently
//! producing a wrong term in release.

use std::sync::Arc as Rc;

use crate::bounds;
use crate::level::Level;
use crate::term::{
    Branches, CtxBase, CtxEntries, CtxEntry, GlobalVar, IWfSig, LocalCtx, MSig, LocalSubst, LocalVar, Motives,
    SubstTail, Term, Type,
};

/// Binder depths for the three namespaces at the current traversal point.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
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

// ---------------------------------------------------------------------------
// Generic traversal
// ---------------------------------------------------------------------------

trait Mapper {
    /// True for operations acting on the local namespace. Such operations do
    /// not descend into other-local-scope subtrees (see module docs).
    const LOCAL_OP: bool;

    /// Name of the operation, for the change-reporting assertion only.
    const NAME: &'static str;

    /// Bump `stats::shift_global_nodes` per node visited. Only the global
    /// rescoping sets it: its cost is what the refl-theorem family pays and
    /// no fuel counter sees (`issues/refl-theorem-step-cost.md`).
    const COUNT_NODES: bool = false;

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
    /// Levels are tiny trees (`Zero`/`Succ`/`Var`/`Max`), so `==` here is an
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
    fn local_var(&mut self, v: LocalVar, _at: Depths) -> Term {
        Term::Var(v)
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
    /// "walk it and find out", never "changed". Only the local-namespace
    /// operations opt in; every skip taken is re-verified against the real
    /// traversal in debug builds ([`sub_ty`]/[`sub_tm`]).
    fn skip_ty(&mut self, _t: &Rc<Type>, _at: Depths) -> bool {
        false
    }
    fn skip_tm(&mut self, _t: &Rc<Term>, _at: Depths) -> bool {
        false
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
/// hook can make — fails the suite (300-seed substitution laws included)
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
    if M::COUNT_NODES {
        crate::stats::shift_global_nodes(1);
    }
    if m.skip_ty(t, at) {
        // A skip claims the whole traversal is a no-op here. Verify the
        // claim in debug builds, exactly as shared_ty verifies the change
        // counter — at the level `checks` sets, because the whole cost of
        // the walk being skipped is paid again.
        #[cfg(debug_assertions)]
        if crate::checks::verify_this_skip() {
            let before = *m.changes();
            let mapped = map_type(t, m, at);
            assert!(
                *m.changes() == before && mapped == **t,
                "{} skipped a subtree it would have changed — bounds.rs disagrees with the \
                 traversal (term output suppressed: see CLAUDE.md)",
                M::NAME
            );
        }
        return Rc::clone(t);
    }
    let before = *m.changes();
    let mapped = map_type(t, m, at);
    if *m.changes() == before {
        shared_ty::<M>(t, mapped)
    } else {
        Rc::new(mapped)
    }
}

/// An `IWf` signature (`docs/iwf-former-design.md` §1.2): `arity` and
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

/// An `M` signature (`docs/kernel-coinduction-design.md` §1.1): `shape`
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

fn sub_tm<M: Mapper>(t: &Rc<Term>, m: &mut M, at: Depths) -> Rc<Term> {
    if M::COUNT_NODES {
        crate::stats::shift_global_nodes(1);
    }
    // Whole-node replacement, before anything else: a mapper that matches
    // *terms* has to see a node before its children are rebuilt, and its
    // answer is by construction a change (rule 1's "over-reporting is safe"
    // does not even apply — the node really is different).
    if let Some(r) = m.pre_tm(t, at) {
        m.note();
        return Rc::new(r);
    }
    if m.skip_tm(t, at) {
        #[cfg(debug_assertions)]
        if crate::checks::verify_this_skip() {
            let before = *m.changes();
            let mapped = map_term(t, m, at);
            assert!(
                *m.changes() == before && mapped == **t,
                "{} skipped a subtree it would have changed — bounds.rs disagrees with the \
                 traversal (term output suppressed: see CLAUDE.md)",
                M::NAME
            );
        }
        return Rc::clone(t);
    }
    let before = *m.changes();
    let mapped = map_term(t, m, at);
    if *m.changes() == before {
        shared_tm::<M>(t, mapped)
    } else {
        Rc::new(mapped)
    }
}

/// The motive/branch bundles of the code recursors, shared on the same rule.
/// Worth their own functions rather than being inlined: `Branches` is 45
/// terms under 45 telescopes, so sharing it unchanged is the single largest
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
        Term::Var(v) => m.local_var(*v, at),
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
        Term::Transp { ty_level, motive_level, ty, motive, lhs, rhs, proof, tm } => {
            Term::Transp {
                ty_level: m.level(ty_level, at),
                motive_level: m.level(motive_level, at),
                ty: sub_ty(ty, m, at),
                motive: sub_ty(motive, m, at + dep(0, 0, 1)),
                lhs: sub_tm(lhs, m, at),
                rhs: sub_tm(rhs, m, at),
                proof: sub_tm(proof, m, at),
                tm: sub_tm(tm, m, at),
            }
        }
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
        Term::Pair { fst_level, snd_level, fst_ty, snd_ty, fst, snd } => Term::Pair {
            fst_level: m.level(fst_level, at),
            snd_level: m.level(snd_level, at),
            fst_ty: sub_ty(fst_ty, m, at),
            snd_ty: sub_ty(snd_ty, m, at + dep(0, 0, 1)),
            fst: sub_tm(fst, m, at),
            snd: sub_tm(snd, m, at),
        },
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

        // The checked spellings (docs/intro-by-type-design.md): one type
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
    Branches {
        ty_nat: sub_tm(&b.ty_nat, m, at + dep(0, 1, 0)),
        ty_pi: sub_tm(&b.ty_pi, m, at + dep(2, 3, 2)),
        ty_ty: sub_tm(&b.ty_ty, m, at + dep(1, 1, 0)),
        ty_el: sub_tm(&b.ty_el, m, at + dep(1, 2, 1)),
        ty_id: sub_tm(&b.ty_id, m, at + dep(1, 4, 3)),
        ty_sigma: sub_tm(&b.ty_sigma, m, at + dep(2, 3, 2)),
        ty_unit: sub_tm(&b.ty_unit, m, at + dep(1, 1, 0)),
        ty_empty: sub_tm(&b.ty_empty, m, at + dep(1, 1, 0)),
        tm_var: sub_tm(&b.tm_var, m, at + dep(1, 3, 0)),
        tm_nat: sub_tm(&b.tm_nat, m, at + dep(0, 1, 0)),
        tm_pi: sub_tm(&b.tm_pi, m, at + dep(2, 3, 2)),
        tm_ty: sub_tm(&b.tm_ty, m, at + dep(1, 1, 0)),
        tm_zero: sub_tm(&b.tm_zero, m, at + dep(0, 1, 0)),
        tm_succ: sub_tm(&b.tm_succ, m, at + dep(0, 2, 1)),
        tm_elim_nat: sub_tm(&b.tm_elim_nat, m, at + dep(1, 5, 4)),
        tm_lam: sub_tm(&b.tm_lam, m, at + dep(2, 4, 2)),
        tm_app: sub_tm(&b.tm_app, m, at + dep(2, 5, 4)),
        tm_id: sub_tm(&b.tm_id, m, at + dep(1, 4, 3)),
        tm_refl: sub_tm(&b.tm_refl, m, at + dep(1, 3, 2)),
        tm_j: sub_tm(&b.tm_j, m, at + dep(2, 7, 6)),
        tm_sigma: sub_tm(&b.tm_sigma, m, at + dep(2, 3, 2)),
        tm_pair: sub_tm(&b.tm_pair, m, at + dep(2, 5, 4)),
        tm_fst: sub_tm(&b.tm_fst, m, at + dep(2, 4, 3)),
        tm_snd: sub_tm(&b.tm_snd, m, at + dep(2, 4, 3)),
        tm_unit: sub_tm(&b.tm_unit, m, at + dep(1, 1, 0)),
        tm_empty: sub_tm(&b.tm_empty, m, at + dep(1, 1, 0)),
        tm_triv: sub_tm(&b.tm_triv, m, at + dep(1, 1, 0)),
        tm_elim_empty: sub_tm(&b.tm_elim_empty, m, at + dep(2, 3, 2)),
        ty_sum: sub_tm(&b.ty_sum, m, at + dep(2, 3, 2)),
        tm_sum: sub_tm(&b.tm_sum, m, at + dep(2, 3, 2)),
        tm_inl: sub_tm(&b.tm_inl, m, at + dep(2, 4, 3)),
        tm_inr: sub_tm(&b.tm_inr, m, at + dep(2, 4, 3)),
        tm_case: sub_tm(&b.tm_case, m, at + dep(3, 7, 6)),
        ty_w: sub_tm(&b.ty_w, m, at + dep(2, 3, 2)),
        tm_w: sub_tm(&b.tm_w, m, at + dep(2, 3, 2)),
        tm_sup: sub_tm(&b.tm_sup, m, at + dep(2, 5, 4)),
        tm_elim_w: sub_tm(&b.tm_elim_w, m, at + dep(3, 6, 5)),
        ty_vec: sub_tm(&b.ty_vec, m, at + dep(1, 3, 2)),
        tm_vec: sub_tm(&b.tm_vec, m, at + dep(1, 3, 2)),
        ty_fin: sub_tm(&b.ty_fin, m, at + dep(0, 2, 1)),
        tm_fin: sub_tm(&b.tm_fin, m, at + dep(0, 2, 1)),
        ty_wf: sub_tm(&b.ty_wf, m, at + dep(1, 3, 2)),
        tm_wf: sub_tm(&b.tm_wf, m, at + dep(1, 3, 2)),
        tm_supf: sub_tm(&b.tm_supf, m, at + dep(1, 5, 4)),
        tm_elim_wf: sub_tm(&b.tm_elim_wf, m, at + dep(2, 6, 5)),
        ty_seq: sub_tm(&b.ty_seq, m, at + dep(1, 4, 3)),
        tm_seq: sub_tm(&b.tm_seq, m, at + dep(1, 4, 3)),
        ty_sempty: sub_tm(&b.ty_sempty, m, at + dep(1, 1, 0)),
        tm_sempty: sub_tm(&b.tm_sempty, m, at + dep(1, 1, 0)),
        tm_srefl: sub_tm(&b.tm_srefl, m, at + dep(1, 3, 2)),
        tm_transp: sub_tm(&b.tm_transp, m, at + dep(2, 7, 6)),
        tm_elim_sempty: sub_tm(&b.tm_elim_sempty, m, at + dep(2, 3, 2)),
        ty_squash: sub_tm(&b.ty_squash, m, at + dep(1, 2, 1)),
        tm_squash: sub_tm(&b.tm_squash, m, at + dep(1, 2, 1)),
        tm_squash_in: sub_tm(&b.tm_squash_in, m, at + dep(1, 3, 2)),
        tm_elim_squash: sub_tm(&b.tm_elim_squash, m, at + dep(2, 5, 4)),
        ty_m: sub_tm(&b.ty_m, m, at + dep(3, 6, 5)),
        tm_m: sub_tm(&b.tm_m, m, at + dep(3, 6, 5)),
        tm_corec: sub_tm(&b.tm_corec, m, at + dep(4, 9, 8)),
        tm_out: sub_tm(&b.tm_out, m, at + dep(3, 7, 6)),
    }
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
}

impl Mapper for ShiftLocal {
    const LOCAL_OP: bool = true;
    const NAME: &'static str = "shift_local";

    fn changes(&mut self) -> &mut u64 {
        &mut self.changes
    }

    fn local_var(&mut self, v: LocalVar, at: Depths) -> Term {
        if v.0 < at.local {
            Term::Var(v)
        } else {
            // `by` is nonzero here (the entry points short-circuit zero), so
            // a free variable is always renumbered.
            self.note();
            Term::Var(LocalVar(v.0 + self.by))
        }
    }

    fn tail(&mut self, tail: SubstTail, _at: Depths) -> (SubstTail, Vec<Rc<Term>>) {
        let t = match tail {
            SubstTail::Empty { len, base } => SubstTail::Empty { len: len + self.by, base },
            SubstTail::Wk { len, ctx_var } => SubstTail::Wk { len: len + self.by, ctx_var },
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
}

/// Weaken the global context by `by` bindings.
struct ShiftGlobal {
    by: u32,
    changes: u64,
}

impl ShiftGlobal {
    fn var(&mut self, v: GlobalVar, at: Depths) -> GlobalVar {
        if v.0 < at.global {
            v
        } else {
            self.note();
            GlobalVar(v.0 + self.by)
        }
    }
}

impl Mapper for ShiftGlobal {
    const LOCAL_OP: bool = false;
    const NAME: &'static str = "shift_global";
    const COUNT_NODES: bool = true;

    fn changes(&mut self) -> &mut u64 {
        &mut self.changes
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
            SubstTail::Empty { len, base: CtxBase::Var(g) } => {
                SubstTail::Empty { len, base: CtxBase::Var(self.var(g, at)) }
            }
            SubstTail::Empty { .. } => tail,
            SubstTail::Wk { len, ctx_var } => {
                SubstTail::Wk { len, ctx_var: self.var(ctx_var, at) }
            }
        };
        (t, Vec::new())
    }
}

/// The recursor's motive and branch telescopes, weakened by `by` global
/// bindings. The value machine's one materialization site that is a
/// telescope table rather than a term (`docs/lazy-global-offset-design.md`
/// §5); routed through the generic traversal so the 60 telescopes are not
/// written down again.
pub(crate) fn shift_global_tables(
    motives: &Motives,
    branches: &Branches,
    by: u32,
) -> (Motives, Branches) {
    let at = Depths::default();
    let mut m = ShiftGlobal { by, changes: 0 };
    let mo = map_motives(motives, &mut m, at);
    let br = map_branches(branches, &mut m, at);
    (mo, br)
}

/// Weaken the universe context by `by` variables.
struct ShiftUniv {
    by: u32,
    changes: u64,
}

impl Mapper for ShiftUniv {
    const LOCAL_OP: bool = false;
    const NAME: &'static str = "shift_univ";

    fn changes(&mut self) -> &mut u64 {
        &mut self.changes
    }

    fn level(&mut self, l: &Level, at: Depths) -> Level {
        self.mapped(l.shift(self.by, at.univ), l)
    }
}

// ---------------------------------------------------------------------------
// Substitutions
// ---------------------------------------------------------------------------

/// Rewrite every level to the canonical representative of its ≈-class.
/// Not a substitution — a normalization, so that equality *modulo level
/// equivalence* (the quotient DeLaM ch. 05's Static Code lemma takes) is
/// plain `==` on the rewritten syntax. Depth-independent: normalization
/// never renumbers a variable, so binders need no care.
struct NormalizeLevels {
    changes: u64,
}

impl Mapper for NormalizeLevels {
    const LOCAL_OP: bool = false;
    const NAME: &'static str = "normalize_levels";

    fn changes(&mut self) -> &mut u64 {
        &mut self.changes
    }

    fn level(&mut self, l: &Level, _at: Depths) -> Level {
        // `0` and a bare `ℓ` are already their own canonical representatives,
        // and they are almost every level a real term contains; taking them
        // here skips a walk and a `BTreeMap` allocation apiece
        // (issues/level-normalization-allocation.md).
        if matches!(l, Level::Zero | Level::Var(_)) {
            return l.clone();
        }
        self.mapped(l.normalize().canonical(), l)
    }
}

/// Universe substitution `φ`: `phi[i]` replaces universe variable `i`
/// (innermost = 0), scoped in the source universe context.
struct SubstUniv<'a> {
    phi: &'a [Level],
    changes: u64,
}

impl Mapper for SubstUniv<'_> {
    const LOCAL_OP: bool = false;
    const NAME: &'static str = "apply_univ";

    fn changes(&mut self) -> &mut u64 {
        &mut self.changes
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
}

impl Mapper for InstUniv<'_> {
    const LOCAL_OP: bool = false;
    const NAME: &'static str = "inst_univ";

    fn changes(&mut self) -> &mut u64 {
        &mut self.changes
    }

    fn level(&mut self, l: &Level, at: Depths) -> Level {
        self.mapped(l.inst_at(self.phi, at.univ), l)
    }
}

/// Local substitution `δ`, applied from depth zero; lifting under binders is
/// depth-based (payloads are shifted in all three namespaces at insertion).
struct SubstLocal<'a> {
    delta: &'a LocalSubst,
    changes: u64,
}

impl Mapper for SubstLocal<'_> {
    const LOCAL_OP: bool = true;
    const NAME: &'static str = "apply_local";

    fn changes(&mut self) -> &mut u64 {
        &mut self.changes
    }

    fn local_var(&mut self, v: LocalVar, at: Depths) -> Term {
        if v.0 < at.local {
            return Term::Var(v);
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
        let out = payload
            .shift_local(at.local)
            .shift_global(at.global)
            .shift_univ(at.univ);
        // An *identity* substitution sends this variable to itself, and that
        // is common enough to be worth the O(1) test: `t[id]` should share all
        // of `t`, not rebuild it. Any other payload is a change.
        if out != Term::Var(v) {
            self.note();
        }
        out
    }

    /// Composition on tails (ch. 02/05): `wk_g^k ∘ δ = wk_g^{δ̂}`,
    /// `·_{g?}^k ∘ δ = ·_{δ̌}^{δ̂}`, where δ is conceptually lifted to the
    /// current depths (source length + local depth; base shifted by the
    /// global depth).
    fn tail(&mut self, tail: SubstTail, at: Depths) -> (SubstTail, Vec<Rc<Term>>) {
        let len = self.delta.source_len() + at.local;
        let t = match tail {
            SubstTail::Wk { ctx_var, .. } => SubstTail::Wk { len, ctx_var },
            SubstTail::Empty { .. } => {
                let base = match self.delta.source_base() {
                    CtxBase::Nil => CtxBase::Nil,
                    CtxBase::Var(g) => CtxBase::Var(GlobalVar(g.0 + at.global)),
                };
                SubstTail::Empty { len, base }
            }
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
}

impl Mapper for InstTop<'_> {
    const LOCAL_OP: bool = true;
    const NAME: &'static str = "inst_top";

    fn changes(&mut self) -> &mut u64 {
        &mut self.changes
    }

    fn local_var(&mut self, v: LocalVar, at: Depths) -> Term {
        if v.0 < at.local {
            return Term::Var(v);
        }
        if v.0 == at.local {
            self.note();
            return self
                .payload
                .shift_local(at.local)
                .shift_global(at.global)
                .shift_univ(at.univ);
        }
        // `by == 1` keeps Γ's variables where they were.
        let w = v.0 - 1 + self.by;
        if w != v.0 {
            self.note();
        }
        Term::Var(LocalVar(w))
    }

    fn tail(&mut self, tail: SubstTail, _at: Depths) -> (SubstTail, Vec<Rc<Term>>) {
        let t = match tail {
            SubstTail::Empty { len, base } => SubstTail::Empty { len: len - 1 + self.by, base },
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
}

/// Abstraction over a **term**: every occurrence of `pat` becomes the fresh
/// innermost variable `z` (`docs/goal-motive-synthesis-design.md` §3).
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
    /// `witness[k]` is `pats` weakened past `k` further local binders — each
    /// `pat` by `k + 1` (it is scoped in `Γ`, and `z` is one more), each
    /// `rep` by `k` (it already lives under `z`). Memoized: the walk asks at
    /// every node.
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
}

impl Mapper for AbstractLocal<'_> {
    const LOCAL_OP: bool = true;
    const NAME: &'static str = "abstract_local";

    fn changes(&mut self) -> &mut u64 {
        &mut self.changes
    }

    fn pre_tm(&mut self, t: &Rc<Term>, at: Depths) -> Option<Term> {
        let row = if at.global == 0 && at.univ == 0 {
            while self.witness.len() as u32 <= at.local {
                let i = self.witness.len() as u32;
                let row = self
                    .pats
                    .iter()
                    .map(|(p, r)| (p.shift_local(i + 1), r.shift_local(i)))
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
                        .map(|(p, r)| (under(p, at.local + 1), under(r, at.local)))
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

/// Collects [`Type::root_terms`]: a mapper that changes nothing and only
/// looks, through [`Mapper::pre_tm`], at the nodes under no binder.
struct RootTerms {
    out: Vec<Rc<Term>>,
    changes: u64,
}

impl Mapper for RootTerms {
    const LOCAL_OP: bool = true;
    const NAME: &'static str = "root_terms";

    fn changes(&mut self) -> &mut u64 {
        &mut self.changes
    }

    fn pre_tm(&mut self, t: &Rc<Term>, at: Depths) -> Option<Term> {
        if at == Depths::default() {
            self.out.push(Rc::clone(t));
        }
        None
    }
}

/// Global substitution `σ` (instantiation form, see [`GlobalSubst`]).
struct SubstGlobal<'a> {
    sigma: &'a GlobalSubst,
    changes: u64,
}

enum Resolved<'a> {
    /// Bound by a binder passed under during traversal.
    Bound,
    /// Substituted: payload (scoped in the source, at depth zero).
    Payload(&'a GlobalEntry),
    /// In the identity region below the substituted bindings: renumbered.
    Renumber(GlobalVar),
}

impl<'a> SubstGlobal<'a> {
    fn resolve(&self, v: GlobalVar, at: Depths) -> Resolved<'a> {
        let n = self.sigma.entries.len() as u32;
        if v.0 < at.global {
            Resolved::Bound
        } else if v.0 - at.global < n {
            let rel = (v.0 - at.global) as usize;
            Resolved::Payload(&self.sigma.entries[n as usize - 1 - rel])
        } else {
            Resolved::Renumber(GlobalVar(v.0 - n))
        }
    }

    /// Base and entry count of a context payload, viewed at the current
    /// depths (only the base variable needs shifting).
    fn ctx_payload_shape(c: &LocalCtx, at: Depths) -> (CtxBase, u32) {
        let base = match c.base {
            CtxBase::Nil => CtxBase::Nil,
            CtxBase::Var(g) => CtxBase::Var(GlobalVar(g.0 + at.global)),
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
                        CtxBase::Nil => SubstTail::Empty { len: len + m_prime, base: CtxBase::Nil },
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
            SubstTail::Empty { len, base: CtxBase::Var(g) } => match self.resolve(g, at) {
                Resolved::Bound => {
                    (SubstTail::Empty { len, base: CtxBase::Var(g) }, Vec::new())
                }
                Resolved::Renumber(v) => {
                    self.note();
                    (SubstTail::Empty { len, base: CtxBase::Var(v) }, Vec::new())
                }
                Resolved::Payload(GlobalEntry::Ctx(c)) => {
                    self.note();
                    let (base, m_prime) = Self::ctx_payload_shape(c, at);
                    (SubstTail::Empty { len: len + m_prime, base }, Vec::new())
                }
                Resolved::Payload(_) => panic!(
                    "kernel invariant violated: context variable substituted by a non-context \
                     payload"
                ),
            },
            SubstTail::Empty { .. } => (tail, Vec::new()),
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
                $map(self, &mut SubstUniv { phi, changes: 0 }, Depths::default())
            }

            /// Instantiate the innermost `phi.len()` universe variables
            /// (`phi[0]` innermost), renumbering deeper variables down.
            pub fn inst_univ(&self, phi: &[Level]) -> $ty {
                $map(self, &mut InstUniv { phi, changes: 0 }, Depths::default())
            }

            /// Apply a local substitution `δ` (`self` scoped in δ's target).
            pub fn apply_local(&self, delta: &LocalSubst) -> $ty {
                $map(self, &mut SubstLocal { delta, changes: 0 }, Depths::default())
            }

            /// Apply a global substitution `σ`.
            pub fn apply_global(&self, sigma: &GlobalSubst) -> $ty {
                $map(self, &mut SubstGlobal { sigma, changes: 0 }, Depths::default())
            }

            /// Rewrite every level to the canonical representative of its
            /// ≈-class, so that `a.normalize_levels() == b.normalize_levels()`
            /// decides **syntactic equality modulo level equivalence**.
            ///
            /// That quotient is what DeLaM ch. 05's Static Code lemma
            /// (`lem:dt:static`) states: at layers `v`/`c`, equivalence *is*
            /// equality, "quotient over the equivalence of universe levels" —
            /// the paper's own example being that `Ty (ℓ ⊔ ℓ')` and
            /// `Ty (ℓ' ⊔ ℓ)` are equal **as code**. `conv.rs` uses this to
            /// compare boxed code.
            pub fn normalize_levels(&self) -> $ty {
                $map(self, &mut NormalizeLevels { changes: 0 }, Depths::default())
            }

            /// `self[s/x]` weakened past `by` binders: `self` is scoped in
            /// `Γ, x`, `s` and the result in `Γ, Δ` with `|Δ| = by`. See
            /// [`InstTop`].
            pub fn inst_top(&self, by: u32, payload: &Term) -> $ty {
                $map(self, &mut InstTop { payload, by, changes: 0 }, Depths::default())
            }

            /// [`Self::inst_top`] below `cutoff` binders that stay fixed:
            /// `self` is scoped in `Γ, x, Θ` with `|Θ| = cutoff`, `s` in
            /// `Γ, Δ`, and the result in `Γ, Δ, Θ` (the Coq formalization's
            /// `⟨rlift ↑⟩ⁿ…[llift (lsingle s)]`). `IWf`'s child index is
            /// instantiated at a shape this way, under its position binder.
            pub fn inst_top_above(&self, by: u32, cutoff: u32, payload: &Term) -> $ty {
                $map(
                    self,
                    &mut InstTop { payload, by, changes: 0 },
                    Depths { local: cutoff, ..Depths::default() },
                )
            }

            /// Weaken the ambient local context by `by` entries.
            pub fn shift_local(&self, by: u32) -> $ty {
                if by == 0 {
                    return self.clone(); // see §Shifting by zero
                }
                $map(self, &mut ShiftLocal { by, changes: 0 }, Depths::default())
            }

            /// Weaken the local context by `by` entries between existing
            /// binders: the innermost `cutoff` locals stay fixed (the Coq
            /// formalization's `⟨rlift ↑⟩`, iterated). See
            /// [`Self::shift_univ_above`].
            pub fn shift_local_above(&self, by: u32, cutoff: u32) -> $ty {
                if by == 0 {
                    return self.clone(); // see §Shifting by zero
                }
                $map(self, &mut ShiftLocal { by, changes: 0 }, Depths { local: cutoff, ..Depths::default() })
            }

            /// Weaken the global context by `by` bindings.
            pub fn shift_global(&self, by: u32) -> $ty {
                if by == 0 {
                    return self.clone(); // see §Shifting by zero
                }
                $map(self, &mut ShiftGlobal { by, changes: 0 }, Depths::default())
            }

            /// Weaken the universe context by `by` variables.
            pub fn shift_univ(&self, by: u32) -> $ty {
                if by == 0 {
                    return self.clone(); // see §Shifting by zero
                }
                $map(self, &mut ShiftUniv { by, changes: 0 }, Depths::default())
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
                $map(self, &mut ShiftUniv { by, changes: 0 }, Depths { univ: cutoff, ..Depths::default() })
            }

            /// Weaken the global context by `by` bindings between existing
            /// binders: the innermost `cutoff` bindings stay fixed. See
            /// [`Self::shift_univ_above`].
            pub fn shift_global_above(&self, by: u32, cutoff: u32) -> $ty {
                if by == 0 {
                    return self.clone(); // see §Shifting by zero
                }
                $map(self, &mut ShiftGlobal { by, changes: 0 }, Depths { global: cutoff, ..Depths::default() })
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
    /// (`docs/goal-motive-synthesis-design.md` §3.2).
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
    /// (`docs/goal-motive-synthesis-design.md` §5). The `[pat/z]` instance is
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
        let mut m = AbstractLocal {
            pats: &pats, witness: Vec::new(), witness_under: Vec::new(), hits: 0, select: Some(at), seen: 0, changes: 0,
        };
        let out = map_type(&self.shift_local(1), &mut m, Depths::default());
        ((m.hits > 0).then_some(out), m.seen)
    }

    /// Every term node of `self` that sits under no binder of any of the
    /// three namespaces — so is scoped in `self`'s own context — in the order
    /// the traversal meets them (the order [`Self::abstract_local_at`]
    /// numbers by), outermost first. A node's subterms follow it.
    pub fn root_terms(&self) -> Vec<Rc<Term>> {
        let mut m = RootTerms { out: Vec::new(), changes: 0 };
        map_type(self, &mut m, Depths::default());
        m.out
    }

    fn abstract_pats(&self, pats: &[(Term, Term)]) -> Option<Type> {
        let mut m = AbstractLocal {
            pats, witness: Vec::new(), witness_under: Vec::new(), hits: 0, select: None, seen: 0, changes: 0,
        };
        let out = map_type(&self.shift_local(1), &mut m, Depths::default());
        (m.hits > 0).then_some(out)
    }
}

impl LocalCtx {
    pub fn apply_univ(&self, phi: &[Level]) -> LocalCtx {
        map_ctx(self, &mut SubstUniv { phi, changes: 0 }, Depths::default())
    }

    pub fn apply_global(&self, sigma: &GlobalSubst) -> LocalCtx {
        map_ctx(self, &mut SubstGlobal { sigma, changes: 0 }, Depths::default())
    }

    pub fn shift_global(&self, by: u32) -> LocalCtx {
        if by == 0 {
            return self.clone(); // see §Shifting by zero
        }
        map_ctx(self, &mut ShiftGlobal { by, changes: 0 }, Depths::default())
    }

    /// [`Self::shift_global`] between existing bindings: the innermost
    /// `cutoff` stay fixed. See [`Type::shift_global_above`].
    pub fn shift_global_above(&self, by: u32, cutoff: u32) -> LocalCtx {
        if by == 0 {
            return self.clone(); // see §Shifting by zero
        }
        map_ctx(self, &mut ShiftGlobal { by, changes: 0 }, Depths { global: cutoff, ..Depths::default() })
    }

    pub fn shift_univ(&self, by: u32) -> LocalCtx {
        if by == 0 {
            return self.clone(); // see §Shifting by zero
        }
        map_ctx(self, &mut ShiftUniv { by, changes: 0 }, Depths::default())
    }
}

impl LocalSubst {
    /// The identity substitution `id_Γ = wk^0_Γ`, fully expanded.
    pub fn id(ctx: &LocalCtx) -> LocalSubst {
        let m = ctx.entries.len() as u32;
        let tail = match ctx.base {
            CtxBase::Nil => SubstTail::Empty { len: m, base: CtxBase::Nil },
            CtxBase::Var(g) => SubstTail::Wk { len: m, ctx_var: g },
        };
        let terms = (0..m)
            .map(|j| Rc::new(Term::Var(LocalVar(m - 1 - j))))
            .collect();
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
        map_subst(self, &mut SubstLocal { delta: other, changes: 0 }, Depths::default())
    }

    pub fn apply_univ(&self, phi: &[Level]) -> LocalSubst {
        map_subst(self, &mut SubstUniv { phi, changes: 0 }, Depths::default())
    }

    pub fn apply_global(&self, sigma: &GlobalSubst) -> LocalSubst {
        map_subst(self, &mut SubstGlobal { sigma, changes: 0 }, Depths::default())
    }

    pub fn shift_local(&self, by: u32) -> LocalSubst {
        if by == 0 {
            return self.clone(); // see §Shifting by zero
        }
        map_subst(self, &mut ShiftLocal { by, changes: 0 }, Depths::default())
    }

    pub fn shift_global(&self, by: u32) -> LocalSubst {
        if by == 0 {
            return self.clone(); // see §Shifting by zero
        }
        map_subst(self, &mut ShiftGlobal { by, changes: 0 }, Depths::default())
    }
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
            tail: SubstTail::Empty { len: 0, base: CtxBase::Nil },
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
                ctx: LocalCtx::ctx_var(GlobalVar(0)),
                level: Level::Zero,
            }),
        };
        assert_eq!(bound.apply_global(&payload), bound);

        let free = Type::CtxPi {
            level: Level::Zero,
            body: Rc::new(Type::CodeTy {
                ctx: LocalCtx::ctx_var(GlobalVar(1)),
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
            var: GlobalVar(0),
            subst: LocalSubst {
                tail: SubstTail::Wk { len: 1, ctx_var: GlobalVar(1) },
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
            var: GlobalVar(0),
            subst: LocalSubst {
                tail: SubstTail::Wk { len: 1, ctx_var: GlobalVar(1) },
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
}

// -- the quote boundary's rebuild (docs/intro-by-type-design.md §2.3) ------

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
/// closed), from the bounds memo the local traversals already keep
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
