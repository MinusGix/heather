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
//! - `has_tail` — whether a local substitution (`U^δ` / `u^δ`) is visible in
//!   this local scope. Tails are rewritten *unconditionally* by the local
//!   operations (`wk^k_g ∘ δ` recomputes the length even when no variable
//!   moves), so a subtree containing one is never skippable on the bound
//!   alone.
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
//! never change; and each entry holds a strong `Rc` clone of its key, so the
//! allocation cannot be freed and its address cannot be recycled while the
//! entry lives. A hit therefore always describes exactly the queried term.
//! The table is thread-local (terms are `Rc`, single-threaded by
//! construction), fixed-size and direct-mapped; a colliding insert evicts,
//! which costs only recomputation.
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

use crate::term::{Branches, LocalSubst, Motives, Term, Type};

/// What a subtree exposes to local-namespace operations, relative to its
/// own root. See the module docs for the two components.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct LocalUse {
    pub bound: u32,
    pub has_tail: bool,
}

impl LocalUse {
    const CLOSED: LocalUse = LocalUse {
        bound: 0,
        has_tail: false,
    };

    fn join(self, o: LocalUse) -> LocalUse {
        LocalUse {
            bound: self.bound.max(o.bound),
            has_tail: self.has_tail || o.has_tail,
        }
    }

    /// View a child's use from outside `k` local binders: the innermost `k`
    /// free indices are bound by the node itself and stop being visible.
    fn under(self, k: u32) -> LocalUse {
        LocalUse {
            bound: self.bound.saturating_sub(k),
            ..self
        }
    }

    /// Can a local-namespace operation applied at binder depth `d` change
    /// this subtree at all?
    pub fn touched_at(self, d: u32) -> bool {
        self.bound > d || self.has_tail
    }
}

/// The memo: two fixed-size direct-mapped caches, one per sort. A slot's
/// keep-alive `Rc` doubles as its key (`Rc::as_ptr` compare), so key
/// validity and entry liveness are one thing; a colliding insert evicts,
/// which costs only recomputation (usually cheap — the evictee's children
/// are still cached). Fixed size means no growth, no rehash, and no flush
/// policy, and it bounds both table memory and how many dead subtrees the
/// keep-alives can pin.
///
/// Memoization is **two-stage**: a query's first miss stores only a marker
/// (a bare address, no keep-alive), and the bounds are computed when the
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
    terms: Vec<Option<(Rc<Term>, LocalUse)>>,
    term_marks: Vec<usize>,
    types: Vec<Option<(Rc<Type>, LocalUse)>>,
    type_marks: Vec<usize>,
}

/// log2 of the slot count per sort. 2^16 slots × 24 bytes × 2 sorts ≈ 3 MiB.
const BITS: u32 = 16;

fn slot(p: usize) -> usize {
    // Fibonacci hashing; the top bits are the well-mixed ones.
    ((p as u64).wrapping_mul(0x9E37_79B9_7F4A_7C15) >> (64 - BITS)) as usize
}

impl Cache {
    fn new() -> Cache {
        Cache {
            terms: vec![None; 1 << BITS],
            term_marks: vec![0; 1 << BITS],
            types: vec![None; 1 << BITS],
            type_marks: vec![0; 1 << BITS],
        }
    }

    fn term_use(&mut self, t: &Rc<Term>) -> LocalUse {
        match &**t {
            Term::Var(v) => {
                return LocalUse {
                    bound: v.0.saturating_add(1),
                    has_tail: false,
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
        if let Some((k, u)) = &self.terms[i] {
            if Rc::ptr_eq(k, t) {
                return *u;
            }
        }
        let u = self.compute_term(t);
        self.terms[i] = Some((Rc::clone(t), u));
        u
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
        if let Some((k, u)) = &self.terms[i] {
            if Rc::ptr_eq(k, t) {
                return Some(*u);
            }
        }
        if self.term_marks[i] == p {
            Some(self.term_use(t))
        } else {
            self.term_marks[i] = p;
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
        if let Some((k, u)) = &self.types[i] {
            if Rc::ptr_eq(k, t) {
                return *u;
            }
        }
        let u = self.compute_type(t);
        self.types[i] = Some((Rc::clone(t), u));
        u
    }

    fn type_query(&mut self, t: &Rc<Type>) -> Option<LocalUse> {
        let p = Rc::as_ptr(t) as usize;
        let i = slot(p);
        if let Some((k, u)) = &self.types[i] {
            if Rc::ptr_eq(k, t) {
                return Some(*u);
            }
        }
        if self.type_marks[i] == p {
            Some(self.type_use(t))
        } else {
            self.type_marks[i] = p;
            None
        }
    }
}

thread_local! {
    static CACHE: RefCell<Cache> = RefCell::new(Cache::new());
}

/// Captures read by evaluation of a syntactic closure. Substitution tails
/// depend on the ambient base/global shift, not on captured local values.
pub(crate) fn term_captures(t: &Rc<Term>) -> u32 {
    CACHE.with(|c| c.borrow_mut().term_use(t).bound)
}

pub(crate) fn type_captures(t: &Rc<Type>) -> u32 {
    CACHE.with(|c| c.borrow_mut().type_use(t).bound)
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
    /// Every `δ` has a tail, and the local operations rewrite tails
    /// unconditionally; the payload terms live in the current scope.
    fn subst_use(&mut self, s: &LocalSubst) -> LocalUse {
        s.terms.iter().fold(
            LocalUse {
                bound: 0,
                has_tail: true,
            },
            |a, t| a.join(self.term_use(t)),
        )
    }

    // The binder counts below (the `.under(k)` arguments) are the LOCAL column
    // of subst.rs's traversal — `dep(_, _, k)` in map_type/map_term/map_motives/
    // map_branches — and must stay identical to it. Other-context children
    // (everything subst.rs routes through other_ty/other_tm/other_ctx) are
    // omitted entirely, matching `LOCAL_OP` scoping.

    fn compute_type(&mut self, t: &Rc<Type>) -> LocalUse {
        match &**t {
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
            Type::GlobalTy { subst, .. } => self.subst_use(subst),
            Type::CtxPi { body, .. } => self.type_use(body),
            Type::TyPi { body, .. } => self.type_use(body),
        }
    }

    fn compute_term(&mut self, t: &Rc<Term>) -> LocalUse {
        match &**t {
            Term::Var(v) => LocalUse {
                bound: v.0.saturating_add(1),
                has_tail: false,
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
            Term::Transp {
                ty,
                motive,
                lhs,
                rhs,
                proof,
                tm,
                ..
            } => self
                .type_use(ty)
                .join(self.type_use(motive).under(1))
                .join(self.term_use(lhs))
                .join(self.term_use(rhs))
                .join(self.term_use(proof))
                .join(self.term_use(tm)),
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
            .join(self.term_use(&b.tm_transp).under(6))
            .join(self.term_use(&b.tm_elim_sempty).under(2))
            .join(self.term_use(&b.ty_squash).under(1))
            .join(self.term_use(&b.tm_squash).under(1))
            .join(self.term_use(&b.tm_squash_in).under(2))
            .join(self.term_use(&b.tm_elim_squash).under(4))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::level::Level;
    use crate::term::CtxBase;
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
                has_tail: false
            }
        );
        assert_eq!(
            term_use(&v(4)),
            LocalUse {
                bound: 5,
                has_tail: false
            }
        );
        assert_eq!(term_use(&rt(Term::Zero)), LocalUse::CLOSED);
        assert_eq!(type_use(&Rc::new(Type::Nat)), LocalUse::CLOSED);
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
                has_tail: false
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
                has_tail: false
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
                has_tail: false
            }
        );
    }

    #[test]
    fn boxes_are_another_scope() {
        assert_eq!(term_use(&rt(Term::BoxTm(v(7)))), LocalUse::CLOSED);
    }

    #[test]
    fn global_vars_carry_a_tail() {
        let g = rt(Term::GlobalTm {
            var: GlobalVar(0),
            subst: LocalSubst {
                tail: SubstTail::Empty {
                    len: 0,
                    base: CtxBase::Nil,
                },
                terms: vec![v(2)],
            },
        });
        assert_eq!(
            term_use(&g),
            LocalUse {
                bound: 3,
                has_tail: true
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
                has_tail: false
            }
        );
    }
}
