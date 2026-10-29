//! The **comparison domain**: the boundary through which [`super::Conv`]'s
//! arms reach their inputs (docs/nbe-conversion-design.md §13, stage 2a).
//!
//! Conversion is a structural comparison of two weak head normal forms. *What
//! a weak head normal form is* is the only thing that changes when the checker
//! moves from the rewriter to the value machine: the rules, the fuel, the
//! left-biased inference and the layer discipline are all the same. This
//! module names that difference as a trait so the arms are written once.
//!
//! Three kinds of thing live here.
//!
//! - **The five carriers** ([`Dom::Ty`], [`Dom::Tm`], [`Dom::TyC`],
//!   [`Dom::TmC`], [`Dom::Subst`]). A `Ty`/`Tm` is a form already in weak head
//!   normal form; a `TyC`/`TmC` is a *sub-structure* of one, which at the
//!   syntax domain is a plain `Rc<Type>`/`Rc<Term>` and at the value domain is
//!   an environment-plus-syntax closure. Reaching the head of a sub-structure
//!   is therefore work, and work can run out of fuel — which is why **every
//!   accessor that reaches a head returns [`super::R`]** even where the
//!   syntax instantiation is total (design §6: an infallible boundary could
//!   only be instantiated at values through `unwrap`). The two exceptions are
//!   the views, and they are exceptions for a reason: see [`Dom::view_ty`].
//! - **The views** ([`TyView`], [`TmView`]): the head discriminant plus typed
//!   children, borrowed for levels and contexts (which are syntax in both
//!   domains, design §3.1) and owned — a refcount bump — for children. Only
//!   the forms conversion actually inspects get a variant; everything else is
//!   [`TmView::Opaque`], which the arms treat exactly as the old catch-alls
//!   did.
//! - **The operations the arms cannot write as syntax**: instantiating an
//!   annotation at a scrutinee ([`Dom::inst_ty`]), η-expanding a head
//!   ([`Dom::eta_app`] and friends), embedding raw syntax into the domain
//!   ([`Dom::embed_ty`]), and synthesizing the types the rules build
//!   (`Π`, `Vec`, `El`, …). These are methods rather than call-site syntax
//!   because at the value domain they are closure application and environment
//!   extension, not substitution: leaving them at the call sites is what would
//!   make stage 2b a rewrite instead of an instantiation.
//!
//! The syntax instantiation is asymmetric — `Ty = Type` but `Tm = Rc<Term>`
//! — and that is a measured choice, not an oversight. A conversion's *root*
//! is a `&Type` the caller lends us, and wrapping it cost 1.3× on
//! `nat/check-numeral`, whose every conversion is one `Nat ≈ Nat`; a
//! conversion's *neutral spines* hand the same term to the neutral judgment
//! twice over, and copying it there cost as much again. See
//! [`Dom::whnf_ty_root`].
//!
//! Two things are deliberately *not* abstracted, and stage 2b owns both:
//! [`super::Env<'v>`]'s Γ stays a syntactic [`LocalCtx`] (only its length and base
//! are read by the telescope helpers — entry *types* are read only by
//! `tm_ne`'s variable arm, through [`Dom::var_type`]), and the recursor
//! telescope tables in [`crate::rec`] keep producing syntax, which the arms
//! then embed. See the stage-2a log entry in
//! `issues/nbe-conversion-round.md`.

use std::sync::Arc as Rc;

use crate::level::Level;
use crate::rec;
use crate::reduce::{step_term, step_term_delta, step_type, step_type_delta, OutOfFuel};
use crate::subst::{GlobalEntry, GlobalSubst};
use crate::term::{
    iwf_children_ty, iwf_motive_scrut_ty, iwf_step_telescope, m_out_ty, m_step_ty, wf_step_telescope, Branches, IWfSig, MSig, GlobalVar, LocalCtx, LocalSubst, LocalVar, Motives, Term, Type,
};

use super::{Conv, ConvError, Env, R, NC};

pub(super) mod values;

pub(super) use values::Values;

// ---------------------------------------------------------------------------
// Views
// ---------------------------------------------------------------------------

/// The head of a weak head normal **type**, with its children.
///
/// One variant per `Type` former: conversion inspects all of them (the
/// layer-m formers included — the layer index restricts which may *match*,
/// not which may be viewed).
pub(super) enum TyView<'a, 'v, D: Dom<'v>> {
    Nat,
    Ty(&'a Level),
    Unit { level: &'a Level },
    Empty { level: &'a Level },
    SEmpty { level: &'a Level },
    Squash { level: &'a Level, ty: D::TyC },
    Pi { dom_level: &'a Level, cod_level: &'a Level, dom: D::TyC, cod: D::TyC },
    Sigma { fst_level: &'a Level, snd_level: &'a Level, fst: D::TyC, snd: D::TyC },
    W { shape_level: &'a Level, pos_level: &'a Level, shape: D::TyC, pos: D::TyC },
    Wf { level: &'a Level, shape: D::TyC, arity: D::TmC },
    Sum { lhs_level: &'a Level, rhs_level: &'a Level, lhs: D::TyC, rhs: D::TyC },
    Id { level: &'a Level, ty: D::TyC, lhs: D::TmC, rhs: D::TmC },
    SEq { level: &'a Level, ty: D::TyC, lhs: D::TmC, rhs: D::TmC },
    Vec { level: &'a Level, elem: D::TyC, len: D::TmC },
    Fin { len: D::TmC },
    /// `fam` is under one binder, `i : Fin len`.
    DVec { level: &'a Level, len: D::TmC, fam: D::TyC },
    /// `arity` and `out` are under `x : S`, `child` under `x, i : Fin n`.
    IWf {
        level: &'a Level,
        idx_level: &'a Level,
        idx: D::TyC,
        shape: D::TyC,
        arity: D::TmC,
        out: D::TmC,
        child: D::TmC,
        index: D::TmC,
    },
    /// The signature's components are under its own binders (see
    /// [`MSigC`]); `index` is not.
    M { sig: MSigC<'a, 'v, D>, index: D::TmC },
    UPi { num_vars: u32, level: &'a Level, body: D::TyC },
    CtxPi { level: &'a Level, body: D::TyC },
    TyPi { ctx: &'a LocalCtx, arg_level: &'a Level, body_level: &'a Level, body: D::TyC },
    CodeTy { ctx: &'a LocalCtx, level: &'a Level },
    CodeTm { ctx: &'a LocalCtx, ty: &'a Rc<Type>, level: &'a Level },
    /// `El^l ν` — a neutral type.
    El { level: &'a Level, tm: D::TmC },
    /// `U^δ` — a neutral type.
    GlobalTy { var: GlobalVar, subst: &'a D::Subst },
}

impl<'v, D: Dom<'v>> TyView<'_, 'v, D> {
    /// Is this one of ch. 06's two neutral type forms (`U^δ`, `El^l ν`)?
    pub(super) fn is_neutral(&self) -> bool {
        matches!(self, TyView::El { .. } | TyView::GlobalTy { .. })
    }
}

/// The head of a weak head normal **term**, with its children.
///
/// Only the forms conversion inspects get a variant. `λ`, `Λ`, pairs, `⟨⟩` and
/// `srefl` are [`TmView::Opaque`]: every rule that could see them is either
/// type-directed η (which never looks at the term) or an irrelevance arm
/// (which accepts anything), and the remaining paths reject them through the
/// neutral judgment's catch-all — exactly as before this abstraction, where
/// they fell through the same `_` arms.
pub(super) enum TmView<'a, 'v, D: Dom<'v>> {
    // -- encodings (compared under `Ty l`) --
    TmNat,
    TmTy(&'a Level),
    TmUnit { level: &'a Level },
    TmEmpty { level: &'a Level },
    TmSEmpty { level: &'a Level },
    TmSquash { level: &'a Level, ty: D::TmC },
    TmPi { dom_level: &'a Level, cod_level: &'a Level, dom: D::TmC, cod: D::TmC },
    TmSigma { fst_level: &'a Level, snd_level: &'a Level, fst: D::TmC, snd: D::TmC },
    TmW { shape_level: &'a Level, pos_level: &'a Level, shape: D::TmC, pos: D::TmC },
    TmWf { level: &'a Level, shape: D::TmC, arity: D::TmC },
    TmM {
        level: &'a Level,
        pos_level: &'a Level,
        idx_level: &'a Level,
        idx: D::TmC,
        shape: D::TmC,
        pos: D::TmC,
        next: D::TmC,
        index: D::TmC,
    },
    TmDVec { level: &'a Level, len: D::TmC, fam: D::TmC },
    TmIWf {
        level: &'a Level,
        idx_level: &'a Level,
        idx: D::TmC,
        shape: D::TmC,
        arity: D::TmC,
        out: D::TmC,
        child: D::TmC,
        index: D::TmC,
    },
    TmId { level: &'a Level, ty: D::TmC, lhs: D::TmC, rhs: D::TmC },
    TmSEq { level: &'a Level, ty: D::TmC, lhs: D::TmC, rhs: D::TmC },
    TmSum { lhs_level: &'a Level, rhs_level: &'a Level, lhs: D::TmC, rhs: D::TmC },
    TmVec { level: &'a Level, elem: D::TmC, len: D::TmC },
    TmFin { len: D::TmC },

    // -- data --
    Zero,
    Succ(D::TmC),
    Refl { tm: D::TmC },
    Inl { val: D::TmC },
    Inr { val: D::TmC },
    Sup { label: D::TmC, children: D::TmC },
    Supf { label: D::TmC, children: D::TmC },
    Supi { label: D::TmC, children: D::TmC },
    /// A `corec`: the carrier under `i`, the step under `i, x`. The
    /// signature is its own, which the step's type is built from; its index
    /// is not shown, being forced by the type compared at.
    Corec { sig: MSigC<'a, 'v, D>, carrier_level: &'a Level, carrier: D::TyC, step: D::TmC, seed: D::TmC },
    BoxTy(&'a Rc<Type>),
    BoxTm(&'a Rc<Term>),

    // -- neutrals --
    Var(LocalVar),
    GlobalTm { var: GlobalVar, subst: &'a D::Subst },
    ElimNat { level: &'a Level, motive: D::TyC, base: D::TmC, step: D::TmC, scrut: D::TmC },
    ElimEmpty { level: &'a Level, scrut_level: &'a Level, motive: D::TyC, scrut: D::TmC },
    ElimSEmpty { level: &'a Level, scrut_level: &'a Level, motive: D::TyC, scrut: D::TmC },
    ElimSquash {
        src_level: &'a Level,
        dst_level: &'a Level,
        src_ty: D::TyC,
        motive: D::TyC,
        scrut: D::TmC,
    },
    Case {
        lhs_level: &'a Level,
        rhs_level: &'a Level,
        motive_level: &'a Level,
        lhs: D::TyC,
        rhs: D::TyC,
        motive: D::TyC,
        case_l: D::TmC,
        case_r: D::TmC,
        scrut: D::TmC,
    },
    ElimW {
        shape_level: &'a Level,
        pos_level: &'a Level,
        motive_level: &'a Level,
        shape: D::TyC,
        pos: D::TyC,
        motive: D::TyC,
        step: D::TmC,
        scrut: D::TmC,
    },
    ElimWf {
        level: &'a Level,
        motive_level: &'a Level,
        shape: D::TyC,
        arity: D::TmC,
        motive: D::TyC,
        step: D::TmC,
        scrut: D::TmC,
    },
    /// The motive is under `j, z`, the step under `a, cs, ih`.
    ElimIWf {
        level: &'a Level,
        idx_level: &'a Level,
        motive_level: &'a Level,
        idx: D::TyC,
        shape: D::TyC,
        arity: D::TmC,
        out: D::TmC,
        child: D::TmC,
        motive: D::TyC,
        step: D::TmC,
        index: D::TmC,
        scrut: D::TmC,
    },
    /// `out`, whose signature and index build its result type.
    Out { sig: MSigC<'a, 'v, D>, index: D::TmC, scrut: D::TmC },
    J {
        ty_level: &'a Level,
        motive_level: &'a Level,
        ty: D::TyC,
        lhs: D::TmC,
        motive: D::TyC,
        case: D::TmC,
        rhs: D::TmC,
        proof: D::TmC,
    },
    // The stored Π / Σ annotations are not part of these views: the typed
    // application and projection rules read the head's inferred type
    // instead, so the view never builds closures for them. `levels` is `None`
    // for the checked spelling `app@` (docs/app-by-head-type-design.md §4),
    // for the reason given at `Fst` below.
    App { levels: Option<(&'a Level, &'a Level)>, fun: D::TmC, arg: D::TmC },
    // `levels` is `None` for the checked spellings `fst@` / `snd@`
    // (docs/intro-by-type-design.md), which store no levels at all — their
    // annotation is one whole type and finding the levels inside it would
    // mean reducing, which a view may not do. The arms read them as a
    // redundant cross-check on the *component* spelling and take the real
    // answer from the Σ the head infers, so `None` costs nothing but the
    // check, and it is what makes `fst@(T;p)` convertible with
    // `fst(x:S.U;p)` — which the translation `⌊·⌋` requires.
    Fst { levels: Option<(&'a Level, &'a Level)>, pair: D::TmC },
    Snd { levels: Option<(&'a Level, &'a Level)>, pair: D::TmC },
    UApp { levels: &'a [Level], fun: D::TmC },
    CtxApp { ctx: &'a LocalCtx, fun: D::TmC },
    TyApp { arg: &'a Rc<Type>, fun: D::TmC },
    LetBoxTy {
        motive_level: &'a Level,
        code_level: &'a Level,
        ctx: &'a LocalCtx,
        motive: D::TyC,
        body: D::TmC,
        scrut: D::TmC,
    },
    LetBoxTm {
        motive_level: &'a Level,
        code_level: &'a Level,
        ctx: &'a LocalCtx,
        ty: &'a Rc<Type>,
        motive: D::TyC,
        body: D::TmC,
        scrut: D::TmC,
    },
    ElimCodeTy {
        ty_motive_level: &'a Level,
        tm_motive_level: &'a Level,
        motives: Rc<Motives>,
        branches: Rc<Branches>,
        code_level: &'a Level,
        ctx: &'a LocalCtx,
        scrut: D::TmC,
        rec: D::RecCtx,
    },
    ElimCodeTm {
        ty_motive_level: &'a Level,
        tm_motive_level: &'a Level,
        motives: Rc<Motives>,
        branches: Rc<Branches>,
        code_level: &'a Level,
        ctx: &'a LocalCtx,
        ty: &'a Rc<Type>,
        scrut: D::TmC,
        rec: D::RecCtx,
    },

    /// A canonical form no rule inspects: `λ`, `Λ`, a pair, `⟨⟩`, `srefl`.
    Opaque,
}

impl<'v, D: Dom<'v>> TmView<'_, 'v, D> {
    /// A neutral form: a variable, a global, or an elimination stuck on one.
    /// Every other view is canonical (an introduction form or an encoding).
    pub(super) fn is_neutral(&self) -> bool {
        matches!(
            self,
            TmView::Var(..)
                | TmView::GlobalTm { .. }
                | TmView::ElimNat { .. }
                | TmView::ElimEmpty { .. }
                | TmView::ElimSEmpty { .. }
                | TmView::ElimSquash { .. }
                | TmView::Case { .. }
                | TmView::ElimW { .. }
                | TmView::ElimWf { .. }
                | TmView::ElimIWf { .. }
                | TmView::Out { .. }
                | TmView::J { .. }
                | TmView::App { .. }
                | TmView::Fst { .. }
                | TmView::Snd { .. }
                | TmView::UApp { .. }
                | TmView::CtxApp { .. }
                | TmView::TyApp { .. }
                | TmView::LetBoxTy { .. }
                | TmView::LetBoxTm { .. }
                | TmView::ElimCodeTy { .. }
                | TmView::ElimCodeTm { .. }
                | TmView::Opaque
        )
    }
}

impl<'v, D: Dom<'v>> TmView<'_, 'v, D> {
    /// Is this one of the 14 type *encodings* — the canonical inhabitants of
    /// `Ty l`? A mismatched pair where either side is one is not convertible;
    /// this is the ch. 06 note that positive types reject across constructors.
    pub(super) fn is_encoding(&self) -> bool {
        matches!(
            self,
            TmView::TmNat
                | TmView::TmTy(_)
                | TmView::TmUnit { .. }
                | TmView::TmEmpty { .. }
                | TmView::TmSEmpty { .. }
                | TmView::TmPi { .. }
                | TmView::TmSigma { .. }
                | TmView::TmW { .. }
                | TmView::TmWf { .. }
                | TmView::TmM { .. }
                | TmView::TmDVec { .. }
                | TmView::TmIWf { .. }
                | TmView::TmId { .. }
                | TmView::TmSEq { .. }
                | TmView::TmSum { .. }
                | TmView::TmVec { .. }
                | TmView::TmFin { .. }
        )
    }

    /// Is this a canonical inhabitant of `Nat`?
    pub(super) fn is_nat_data(&self) -> bool {
        matches!(self, TmView::Zero | TmView::Succ(_))
    }
}

/// An `IWf` signature as the views carry it (see `term::IWfSig`): the
/// components the elimination's telescope is built from.
pub(super) struct IWfSigC<'a, 'v, D: Dom<'v>> {
    pub level: &'a Level,
    pub idx_level: &'a Level,
    pub idx: &'a D::TyC,
    pub shape: &'a D::TyC,
    pub arity: &'a D::TmC,
    pub out: &'a D::TmC,
    pub child: &'a D::TmC,
}

/// An `M` signature as the views carry it (see `term::MSig`): `shape` is
/// under `i : I`, `pos` under `i, s`, `next` under `i, s, p`.
pub(super) struct MSigC<'a, 'v, D: Dom<'v>> {
    pub level: &'a Level,
    pub pos_level: &'a Level,
    pub idx_level: &'a Level,
    pub idx: D::TyC,
    pub shape: D::TyC,
    pub pos: D::TyC,
    pub next: D::TmC,
}

impl<'v, D: Dom<'v>> MSigC<'_, 'v, D> {
    /// The family's level, `l ⊔ l' ⊔ li`.
    pub(super) fn family_level(&self) -> Level {
        Level::join(Level::join(self.level.clone(), self.pos_level.clone()), self.idx_level.clone())
    }
}

// ---------------------------------------------------------------------------
// The domain
// ---------------------------------------------------------------------------

/// What the comparison arms are generic over.
///
/// Implementors are zero-sized markers; every method takes the checker
/// explicitly, because the operations that differ between domains are the ones
/// that spend fuel.
pub(super) trait Dom<'v>: Sized {
    /// Identity of a compared closure pair for [`Conv`]'s verdict memo;
    /// `None` opts a domain out. A key must determine the pair's denotation:
    /// the closures, the scope each is read in, and the Ψ they are read
    /// under.
    type MemoKey: std::hash::Hash + Eq;
    fn tm_memo_key(env: &Env<'v>, a: &Self::TmC, b: &Self::TmC) -> Option<Self::MemoKey>;
    /// A **type** in weak head normal form.
    type Ty;
    /// A **term** in weak head normal form.
    type Tm;
    /// A type sub-structure of a value, possibly under one binder of the
    /// former that carries it. Reaching its head is [`Dom::whnf_ty`].
    type TyC: Clone;
    /// A term sub-structure; see [`Dom::TyC`].
    type TmC: Clone;
    /// The local substitution `δ` of a global variable `u^δ` / `U^δ`.
    type Subst;
    /// The scope a code recursor's Γ-scoped raw syntax (`motives`,
    /// `branches`) is read in. The recursors' branch tables are the only
    /// syntax a value carries that the *rewriter* would have rewritten at
    /// every enclosing β, so it agrees with the value only through the
    /// elimination's stored environment; at the syntax domain that
    /// environment is the identity, i.e. nothing.
    type RecCtx: Clone;

    // -- reduction ----------------------------------------------------------

    /// `T ⇝* W` with δ, spending one fuel per step.
    fn whnf_ty(cv: &mut Conv<'v, Self>, env: &Env<'v>, t: &Self::TyC) -> R<Self::Ty>;
    /// The two **roots**: raw syntax, δ-opaquely reduced into the domain.
    ///
    /// A conversion starts from syntax the caller lends us, not from a
    /// sub-structure of anything, so entering the domain is its own
    /// operation — at the value domain, evaluation in the identity
    /// environment of Γ (design §3.2). It exists as a method rather than as
    /// `embed` + [`Dom::whnf_ty`] because the syntax domain can then reduce
    /// the borrow in place: wrapping every root cost 1.3× on
    /// `nat/check-numeral`, whose every conversion is one `Nat ≈ Nat`.
    fn whnf_ty_root(cv: &mut Conv<'v, Self>, env: &Env<'v>, t: &Type) -> R<Self::Ty>;
    fn whnf_tm_root(cv: &mut Conv<'v, Self>, env: &Env<'v>, t: &Term) -> R<Self::Tm>;
    fn whnf_tm(cv: &mut Conv<'v, Self>, env: &Env<'v>, t: &Self::TmC) -> R<Self::Tm>;
    /// `T ⇝* W` **without** δ: stops at a definition's spine.
    fn whnf_ty_opaque(cv: &mut Conv<'v, Self>, env: &Env<'v>, t: &Self::TyC) -> R<Self::Ty>;
    fn whnf_tm_opaque(cv: &mut Conv<'v, Self>, env: &Env<'v>, t: &Self::TmC) -> R<Self::Tm>;
    /// Advance exactly one defined head from a δ-opaque weak head normal
    /// form, then resume non-δ reduction. Conversion can therefore retry a
    /// newly exposed same-head spine before unfolding further.
    fn delta_ty(cv: &mut Conv<'v, Self>, env: &Env<'v>, w: &Self::Ty) -> R<Self::Ty>;
    fn delta_tm(cv: &mut Conv<'v, Self>, env: &Env<'v>, w: &Self::Tm) -> R<Self::Tm>;
    /// Unfold a term's defined heads until none remains: the δ-transparent
    /// weak head normal form. Exactly the unfoldings that iterating
    /// [`Dom::delta_tm`] performs, and the same fuel; the value domain
    /// runs it inside the machine so that a spine stuck on a glued
    /// scrutinee is replayed once rather than once per unfolding.
    fn delta_whnf_tm(cv: &mut Conv<'v, Self>, env: &Env<'v>, w: Self::Tm) -> R<Self::Tm>;
    /// The definition at the head of a δ-stuck spine, if any.
    fn delta_head(cv: &Conv<'v, Self>, env: &Env<'v>, w: &Self::Tm) -> Option<GlobalVar>;
    fn delta_head_ty(cv: &Conv<'v, Self>, env: &Env<'v>, w: &Self::Ty) -> Option<GlobalVar>;

    /// Is this δ-stuck term a **bare application** of its defined head —
    /// `f a⃗`, with nothing but applications between the head and the root?
    /// The alternative is an elimination stuck on a glued scrutinee,
    /// `E[f a⃗]`, whose δ-head is only what its scrutinee happens to
    /// compute with. [`Conv::tm_w`]'s same-head arm keys its reaction to a
    /// failed meet on the distinction; asked only there, after
    /// [`Dom::delta_head`] has answered `Some`.
    fn is_application_spine(w: &Self::Tm) -> bool;

    // -- views --------------------------------------------------------------

    /// The two views. Unlike every other accessor these are **total**: they
    /// inspect a form that is already in weak head normal form, and neither
    /// domain has to reduce anything to name its head or hand back its
    /// children. Fallibility lives one step earlier, in the operations that
    /// reach a head at all ([`Dom::whnf_ty`], [`Dom::head_tm`]).
    fn view_ty<'a>(cv: &mut Conv<'v, Self>, env: &Env<'v>, w: &'a Self::Ty) -> TyView<'a, 'v, Self>;
    /// A sub-structure that is *spelled* `Vec^l(T; k)`, **before** any
    /// reduction — its level and its two children as sub-structures, or
    /// `None` when the carrier's head is anything else (a definition that
    /// unfolds to a `Vec` is not one). `Conv::ty`'s `Vec` congruence reads
    /// this so that two vectors at a canonical length are compared by length
    /// and element once, instead of through the `Σ` encoding both reduce
    /// to, which repeats the element comparison per level
    /// (docs/wf-former-design.md §5).
    fn vec_former(cv: &Conv<'v, Self>, env: &Env<'v>, t: &Self::TyC) -> Option<(Level, Self::TyC, Self::TmC)>;
    fn view_tm<'a>(cv: &mut Conv<'v, Self>, env: &Env<'v>, w: &'a Self::Tm) -> TmView<'a, 'v, Self>;
    /// The weak head form of a sub-structure that is **already** in weak head
    /// normal form because the form carrying it is: an eliminator's scrutinee,
    /// an application's function. At the syntax domain this is a clone; at the
    /// value domain it is a force, which is why it is fallible.
    fn head_tm(cv: &mut Conv<'v, Self>, env: &Env<'v>, t: &Self::TmC) -> R<Self::Tm>;
    /// A weak head normal type seen as a sub-structure — the `W` and `Wf` arms
    /// build the children's types out of the type they are comparing at.
    fn as_child_ty(cv: &mut Conv<'v, Self>, env: &Env<'v>, w: &Self::Ty) -> R<Self::TyC>;

    // -- scope --------------------------------------------------------------

    /// `Γ, x : T @ l`.
    fn push_entry(env: &Env<'v>, ty: &Self::TyC, level: &Level) -> Env<'v>;
    /// Push a recursor telescope's universe, global and local binders.
    fn push_spec(env: &Env<'v>, tele: &rec::Tele) -> Env<'v>;
    /// The type and level of a local, looked up in Γ and weakened to the
    /// variable's own scope.
    fn var_type(cv: &mut Conv<'v, Self>, env: &Env<'v>, x: LocalVar) -> R<(Self::TyC, Level)>;
    /// Weaken past `by` binders pushed on the right. Free at the value domain
    /// (variables are levels), a `shift_local` at the syntax one.
    fn weaken_ty(env: &Env<'v>, t: &Self::TyC, by: u32) -> Self::TyC;
    fn weaken_tm(env: &Env<'v>, t: &Self::TmC, by: u32) -> Self::TmC;

    // -- embedding raw syntax -----------------------------------------------

    /// Raw syntax scoped in `env`'s Γ, as a sub-structure of the domain.
    fn embed_ty(env: &Env<'v>, t: Rc<Type>) -> Self::TyC;
    /// Raw syntax scoped in `env`'s Γ but *read in* `rec`'s scope — the code
    /// recursors' motives and branches, plus everything derived from them.
    fn embed_ty_at(rec: &Self::RecCtx, env: &Env<'v>, t: Rc<Type>) -> Self::TyC;
    fn embed_tm_at(rec: &Self::RecCtx, env: &Env<'v>, t: Rc<Term>) -> Self::TmC;

    // -- instantiation ------------------------------------------------------

    /// `M[a⃗/x⃗]` — instantiate an annotation at scrutinees. `home` is the
    /// scope `M` binds over, `cur` the (possibly longer) scope the arguments
    /// live in; at the syntax domain that difference is the weakening of the
    /// identity substitution, at the value domain it is nothing and the
    /// closure is simply applied.
    ///
    /// This is *the* operation that must not be spelled at the call sites:
    /// substitution and closure application have no common syntax.
    fn inst_ty(
        cv: &mut Conv<'v, Self>,
        home: &Env<'v>,
        cur: &Env<'v>,
        m: &Self::TyC,
        args: &[Self::TmC],
    ) -> R<Self::TyC>;
    /// [`Dom::inst_ty`] for a *term* annotation — `Wf`'s arity, the one
    /// sub-structure under a former's binder that is a term.
    fn inst_tm(
        cv: &mut Conv<'v, Self>,
        home: &Env<'v>,
        cur: &Env<'v>,
        m: &Self::TmC,
        args: &[Self::TmC],
    ) -> R<Self::TmC>;
    /// Weaken past `by` **global** binders: the `letbox` arms compare their
    /// bodies under a Ψ extended by the code variable, and the motive they
    /// instantiate comes from outside it.
    fn shift_global_ty(cv: &mut Conv<'v, Self>, env: &Env<'v>, t: &Self::TyC, by: u32) -> R<Self::TyC>;
    /// `T[ℓ⃗/L]` under a `ΠΠ` binder.
    fn inst_univ_ty(cv: &mut Conv<'v, Self>, env: &Env<'v>, body: &Self::TyC, phi: &[Level])
        -> R<Self::TyC>;
    /// `T[Δ/g]` under a `(g : Ctx) ⇒` binder.
    fn inst_ctx_ty(cv: &mut Conv<'v, Self>, env: &Env<'v>, body: &Self::TyC, ctx: &LocalCtx)
        -> R<Self::TyC>;
    /// `T[S/U]` under a `(U : Typ) ⇒` binder.
    fn inst_tyarg_ty(
        cv: &mut Conv<'v, Self>,
        env: &Env<'v>,
        body: &Self::TyC,
        arg: &Rc<Type>,
    ) -> R<Self::TyC>;

    /// Read a sub-structure that sits **under** `tu` universe and `tg`
    /// global binders the comparison has just pushed.
    ///
    /// At the syntax domain this is nothing: the body of a `ΠΠ`, a
    /// `(g:Ctx)⇒`, a `(U:Typ)⇒` or a `letbox` is already scoped in the
    /// extended context, and de Bruijn does the rest. At the value domain
    /// only the *body syntax* is; the environment the closure captured is
    /// still in the outer scope, and the two have to be brought back together
    /// (`value::shift`, and the stage-2b log for why stage 1's argument does
    /// not cover this case).
    fn under_tele_ty(
        cv: &mut Conv<'v, Self>,
        env: &Env<'v>,
        t: &Self::TyC,
        tu: u32,
        tg: u32,
    ) -> R<Self::TyC>;
    fn under_tele_tm(
        cv: &mut Conv<'v, Self>,
        env: &Env<'v>,
        t: &Self::TmC,
        tu: u32,
        tg: u32,
    ) -> R<Self::TmC>;

    // -- local substitutions ------------------------------------------------

    fn subst_len(d: &Self::Subst) -> usize;
    /// The `k`th step term of a substitution, read in `env`.
    fn subst_term(env: &Env<'v>, d: &Self::Subst, k: usize) -> Self::TmC;
    /// Do the two substitutions have the same tail? Stated as a predicate
    /// rather than as equality because the value domain's tail deliberately
    /// carries less than the syntax's (`VTail` drops the source context's
    /// length, which an environment machine has no opportunity to renormalize
    /// — stage 1's log).
    fn subst_tails_agree(a: &Self::Subst, b: &Self::Subst) -> bool;
    /// `T[δ|ₖ]` — a target-context entry type carried back along the first
    /// `k` steps of `δ`. With `k = δ.terms.len()` this is `T[δ]`, the type of
    /// a global variable's instance.
    fn apply_subst_ty(
        cv: &mut Conv<'v, Self>,
        env: &Env<'v>,
        d: &Self::Subst,
        k: usize,
        t: &Rc<Type>,
    ) -> R<Self::TyC>;

    // -- synthesized types --------------------------------------------------

    /// `Nat` and `ze`, the two closed forms conversion synthesizes on its
    /// hottest paths (every length, arity and `elim_Nat` base). Scope-free in
    /// both domains — they close over nothing — so the checker builds each
    /// once and clones the handle.
    fn nat(env: &Env<'v>) -> Self::TyC;
    fn univ(env: &Env<'v>, level: &Level) -> Self::TyC;
    fn empty(env: &Env<'v>, level: &Level) -> Self::TyC;
    fn sempty(env: &Env<'v>, level: &Level) -> Self::TyC;
    fn squash(env: &Env<'v>, level: &Level, ty: &Self::TyC) -> Self::TyC;
    fn code_ty(env: &Env<'v>, ctx: &LocalCtx, level: &Level) -> Self::TyC;
    fn code_tm(env: &Env<'v>, ctx: &LocalCtx, ty: &Rc<Type>, level: &Level) -> Self::TyC;
    /// `El^l s` at an encoding that is a domain object — the arms that compare
    /// under `Ty l` push its own `El` as a binder type.
    fn el(cv: &mut Conv<'v, Self>, env: &Env<'v>, level: &Level, tm: &Self::TmC) -> R<Self::TyC>;
    /// `Π(x : S). T`, with `T` scoped one binder deeper.
    fn pi(
        cv: &mut Conv<'v, Self>,
        env: &Env<'v>,
        dom_level: &Level,
        cod_level: &Level,
        dom: &Self::TyC,
        cod: &Self::TyC,
    ) -> R<Self::TyC>;
    fn sum(
        cv: &mut Conv<'v, Self>,
        env: &Env<'v>,
        lhs_level: &Level,
        rhs_level: &Level,
        lhs: &Self::TyC,
        rhs: &Self::TyC,
    ) -> R<Self::TyC>;
    fn w(
        cv: &mut Conv<'v, Self>,
        env: &Env<'v>,
        shape_level: &Level,
        pos_level: &Level,
        shape: &Self::TyC,
        pos: &Self::TyC,
    ) -> R<Self::TyC>;
    fn wf(
        cv: &mut Conv<'v, Self>,
        env: &Env<'v>,
        level: &Level,
        shape: &Self::TyC,
        arity: &Self::TmC,
    ) -> R<Self::TyC>;
    fn vec(
        cv: &mut Conv<'v, Self>,
        env: &Env<'v>,
        level: &Level,
        elem: &Self::TyC,
        len: &Self::TmC,
    ) -> R<Self::TyC>;
    fn id(
        cv: &mut Conv<'v, Self>,
        env: &Env<'v>,
        level: &Level,
        ty: &Self::TyC,
        lhs: &Self::TmC,
        rhs: &Self::TmC,
    ) -> R<Self::TyC>;
    /// `Fin(k)`, the binder type a `DVec`'s family is compared under.
    fn fin(cv: &mut Conv<'v, Self>, env: &Env<'v>, len: &Self::TmC) -> R<Self::TyC>;

    // -- synthesized terms --------------------------------------------------

    fn zero(env: &Env<'v>) -> Self::TmC;
    fn succ(cv: &mut Conv<'v, Self>, env: &Env<'v>, t: &Self::TmC) -> R<Self::TmC>;
    /// The local variable `x` as a term of the domain.
    fn local(env: &Env<'v>, x: LocalVar) -> Self::TmC;
    fn refl(
        cv: &mut Conv<'v, Self>,
        env: &Env<'v>,
        level: &Level,
        ty: &Self::TyC,
        tm: &Self::TmC,
    ) -> R<Self::TmC>;
    /// `inl`/`inr` at the given summand types; `left` picks the injection.
    #[allow(clippy::too_many_arguments)]
    fn inj(
        cv: &mut Conv<'v, Self>,
        env: &Env<'v>,
        left: bool,
        lhs_level: &Level,
        rhs_level: &Level,
        lhs: &Self::TyC,
        rhs: &Self::TyC,
        val: &Self::TmC,
    ) -> R<Self::TmC>;
    /// `sup(a; f)` at the annotations of the `W` type `w`, read `by` binders
    /// deeper than `w`'s own scope.
    ///
    /// The annotations are taken from the type rather than passed in because
    /// `W`'s positions are a *body under the shape binder*: weakening the
    /// ambient scope of such a body is not the whole-node shift
    /// [`Dom::weaken_ty`] performs, and at the value domain it is not an
    /// operation at all. Destructuring the weakened `W` is what the rule
    /// itself does.
    fn sup_at(
        cv: &mut Conv<'v, Self>,
        env: &Env<'v>,
        w: &Self::TyC,
        by: u32,
        label: &Self::TmC,
        children: &Self::TmC,
    ) -> R<Self::TmC>;
    /// Syntactic equality of two type sub-structures, as a fast path only:
    /// `false` must always be safe (the caller falls back to a full
    /// comparison).
    fn ty_eq_fast(a: &Self::TyC, b: &Self::TyC) -> bool;
    /// Scoped pointer identity of two term sub-structures, for the general
    /// reflexivity shortcut. It must imply that the two carriers denote the
    /// same term in their present scope.
    fn tm_identity_fast(a: &Self::TmC, b: &Self::TmC) -> bool;
    /// If both weak heads expose compressed repetitions of the same unary
    /// constructor context, cancel their equal outer prefix and return the
    /// residual sub-structures. `None` means only that this domain has no
    /// justified compressed step; ordinary structural comparison follows.
    fn cancel_nat_prefix(
        _cv: &mut Conv<'v, Self>,
        _env: &Env<'v>,
        _a: &Self::Tm,
        _b: &Self::Tm,
    ) -> R<Option<(Self::TmC, Self::TmC)>> {
        Ok(None)
    }
    /// Decide two values at a Σ the `Vec` type rule produced by comparing a
    /// common prefix of their **bits** as a machine word, instead of taking
    /// the chain one η-projection at a time
    /// (`docs/native-bitvector-values-design.md` §7).
    ///
    /// `Ok(None)` means only that this domain — or this Σ, or these values —
    /// has no word to compare; the ordinary η arm follows and decides exactly
    /// the pairs it decides today, so this is a fast path and never a new
    /// verdict. `Err(NotConvertible)` is a verdict: two canonical bits that
    /// differ, which is one comparison rather than a walk to the difference.
    #[allow(clippy::too_many_arguments)]
    fn bit_vec_eq(
        _cv: &mut Conv<'v, Self>,
        _env: &Env<'v>,
        _a: &Self::Tm,
        _b: &Self::Tm,
        _fst_ty: &Self::TyC,
        _snd_ty: &Self::TyC,
        _snd_level: &Level,
    ) -> R<Option<()>> {
        Ok(None)
    }
    #[allow(clippy::too_many_arguments)]
    fn app(
        cv: &mut Conv<'v, Self>,
        env: &Env<'v>,
        dom_level: &Level,
        cod_level: &Level,
        dom: &Self::TyC,
        cod: &Self::TyC,
        fun: &Self::TmC,
        arg: &Self::TmC,
    ) -> R<Self::TmC>;
    /// `fst`/`snd` of a sub-structure (not of a compared head — that is
    /// [`Dom::eta_proj`]).
    #[allow(clippy::too_many_arguments)]
    fn proj(
        cv: &mut Conv<'v, Self>,
        env: &Env<'v>,
        first: bool,
        fst_level: &Level,
        snd_level: &Level,
        fst_ty: &Self::TyC,
        snd_ty: &Self::TyC,
        pair: &Self::TmC,
    ) -> R<Self::TmC>;
    /// `box U^{id_Δ}` / `box u^{id_Δ}` for the freshly pushed global — the
    /// `letbox` arms' payload. Code is syntax in both domains (design §3.5).
    fn box_ty(env: &Env<'v>, code: Rc<Type>) -> Self::TmC;
    fn box_tm(env: &Env<'v>, code: Rc<Term>) -> Self::TmC;
    /// The payload of a `box`, if this sub-structure is one. `Ok(None)` means
    /// "not a box", which the code recursors' scrutinee arms distinguish from
    /// "a box of the wrong thing".
    fn box_ty_payload(cv: &mut Conv<'v, Self>, env: &Env<'v>, t: &Self::TmC) -> R<Option<Rc<Type>>>;
    fn box_tm_payload(cv: &mut Conv<'v, Self>, env: &Env<'v>, t: &Self::TmC) -> R<Option<Rc<Term>>>;

    // -- η -----------------------------------------------------------------

    /// `w↑ x` in `Γ, x : S` — the Π η arm, for *both* sides at once so the
    /// codomain annotation is built once, as it was before this abstraction.
    /// `outer` is the scope `w` lives in, `inner` the extended one.
    #[allow(clippy::too_many_arguments)]
    fn eta_app(
        cv: &mut Conv<'v, Self>,
        outer: &Env<'v>,
        inner: &Env<'v>,
        a: &Self::Tm,
        b: &Self::Tm,
        dom_level: &Level,
        cod_level: &Level,
        dom: &Self::TyC,
        cod: &Self::TyC,
    ) -> R<(Self::TmC, Self::TmC)>;
    /// `w↑ $ ℓ⃗` in `L, ℓ⃗`.
    fn eta_uapp(
        cv: &mut Conv<'v, Self>,
        outer: &Env<'v>,
        inner: &Env<'v>,
        a: &Self::Tm,
        b: &Self::Tm,
        num_vars: u32,
    ) -> R<(Self::TmC, Self::TmC)>;
    /// `w↑ @ g` in `Ψ, g : Ctx`.
    fn eta_ctxapp(
        cv: &mut Conv<'v, Self>,
        outer: &Env<'v>,
        inner: &Env<'v>,
        a: &Self::Tm,
        b: &Self::Tm,
    ) -> R<(Self::TmC, Self::TmC)>;
    /// `w↑ @ U^{id_Δ}` in `Ψ, U : Typ_p(Δ, l)`.
    fn eta_tyapp(
        cv: &mut Conv<'v, Self>,
        outer: &Env<'v>,
        inner: &Env<'v>,
        a: &Self::Tm,
        b: &Self::Tm,
        ctx: &LocalCtx,
    ) -> R<(Self::TmC, Self::TmC)>;
    /// `fst w` / `snd w` — the Σ η arm, on compared heads.
    #[allow(clippy::too_many_arguments)]
    fn eta_proj(
        cv: &mut Conv<'v, Self>,
        env: &Env<'v>,
        first: bool,
        a: &Self::Tm,
        b: &Self::Tm,
        fst_level: &Level,
        snd_level: &Level,
        fst_ty: &Self::TyC,
        snd_ty: &Self::TyC,
    ) -> R<(Self::TmC, Self::TmC)>;

    // -- recursors ----------------------------------------------------------

    /// The `elim_Wf` step telescope `(cs, ih, s)` of ch. 04, shared with
    /// `typing.rs` at the syntax domain.
    #[allow(clippy::too_many_arguments)]
    fn wf_step_telescope(
        cv: &mut Conv<'v, Self>,
        env: &Env<'v>,
        level: &Level,
        motive_level: &Level,
        shape: &Self::TyC,
        arity: &Self::TmC,
        motive: &Self::TyC,
    ) -> R<(Self::TyC, Self::TyC, Self::TyC)>;
    /// The `elim_IWf` telescope of ch. 04's extension, from the shared
    /// schemas (`term::iwf_motive_scrut_ty`, `term::iwf_step_telescope`):
    /// the motive's scrutinee type `IWf(…)(j)` in `(Γ, j)`, and the step's
    /// `(cs, ih, s)` in `(Γ, a)`, `(Γ, a, cs)`, `(Γ, a, cs, ih)`.
    #[allow(clippy::too_many_arguments)]
    fn iwf_telescope(
        cv: &mut Conv<'v, Self>,
        env: &Env<'v>,
        sig: &IWfSigC<'_, 'v, Self>,
        motive_level: &Level,
        motive: &Self::TyC,
    ) -> R<(Self::TyC, Self::TyC, Self::TyC, Self::TyC)>;
    /// The children's type `DVec^{l⊔li}(n[a/x]; k. IWf(…)(c[a/x, k/i]))` of a
    /// `sup_i(a; _)` at the weak head `IWf` type `w`.
    fn iwf_children(
        cv: &mut Conv<'v, Self>,
        env: &Env<'v>,
        w: &Self::Ty,
        label: &Self::TmC,
    ) -> R<Self::TyC>;
    /// `out`'s result type `Σ(s : S[j]). Π(p : P[j, s]). M(o[j, s, p])` at
    /// index `j`, from the shared schema `term::m_out_ty`.
    fn m_out_ty(cv: &mut Conv<'v, Self>, env: &Env<'v>, sig: &MSigC<'_, 'v, Self>, index: &Self::TmC)
        -> R<Self::TyC>;
    /// A `corec` step's type in `(Γ, i, x)`, from the shared schema
    /// `term::m_step_ty` at the corec's own signature and carrier (`carrier`
    /// under `i`).
    fn m_step_ty(
        cv: &mut Conv<'v, Self>,
        env: &Env<'v>,
        sig: &MSigC<'_, 'v, Self>,
        carrier_level: &Level,
        carrier: &Self::TyC,
    ) -> R<Self::TyC>;
    /// `M_Typ[l/ℓ, Δ/g, t/x_T]` — the code type recursor's conclusion.
    #[allow(clippy::too_many_arguments)]
    fn inst_ty_motive(
        cv: &mut Conv<'v, Self>,
        env: &Env<'v>,
        rec: &Self::RecCtx,
        motive: &Rc<Type>,
        code_level: &Level,
        ctx: &LocalCtx,
        scrut: &Self::TmC,
    ) -> R<Self::TyC>;
    /// `M_Trm[l/ℓ, Δ/g, T/U_T, t/x_t]` — the code term recursor's conclusion.
    #[allow(clippy::too_many_arguments)]
    fn inst_tm_motive(
        cv: &mut Conv<'v, Self>,
        env: &Env<'v>,
        rec: &Self::RecCtx,
        motive: &Rc<Type>,
        code_level: &Level,
        ctx: &LocalCtx,
        ty: &Rc<Type>,
        scrut: &Self::TmC,
    ) -> R<Self::TyC>;
}

// ---------------------------------------------------------------------------
// The syntax instantiation
// ---------------------------------------------------------------------------

/// The rewriter domain: a weak head normal form is a `Type`/`Term` that
/// [`crate::reduce`] cannot step, and a sub-structure is the syntax itself.
/// Every accessor is total, so every one returns `Ok`.
///
/// Every method is `#[inline]`: they are thin adapters that must fold into
/// the arms, and leaving them as calls — a view returned through memory, a
/// whnf moved twice — cost 1.3× on `nat/check-numeral`.
pub(super) struct Syn;

/// `Γ ⊢ x : T` — the identity substitution of `env`'s Γ, weakened past the
/// `k` binders `cur` has and `home` does not.
fn id_at<'v>(home: &Env<'v>, cur: &Env<'v>) -> LocalSubst {
    let k = (cur.gamma.entries.len() - home.gamma.entries.len()) as u32;
    LocalSubst::id(&home.gamma).shift_local(k)
}

/// An `M` signature's view at the syntax domain: its own components.
fn syn_m_sig<'a, 'v>(sig: &'a MSig) -> MSigC<'a, 'v, Syn> {
    MSigC {
        level: &sig.level,
        pos_level: &sig.pos_level,
        idx_level: &sig.idx_level,
        idx: Rc::clone(&sig.idx),
        shape: Rc::clone(&sig.shape),
        pos: Rc::clone(&sig.pos),
        next: Rc::clone(&sig.next),
    }
}

/// The signature a view carries, as syntax again, for the shared schemas.
fn syn_m_sig_rc(sig: &MSigC<'_, '_, Syn>) -> Rc<MSig> {
    Rc::new(MSig {
        level: sig.level.clone(),
        pos_level: sig.pos_level.clone(),
        idx_level: sig.idx_level.clone(),
        idx: Rc::clone(&sig.idx),
        shape: Rc::clone(&sig.shape),
        pos: Rc::clone(&sig.pos),
        next: Rc::clone(&sig.next),
    })
}

fn var0() -> Rc<Term> {
    Rc::new(Term::Var(LocalVar(0)))
}

impl<'v> Dom<'v> for Syn {
    type MemoKey = ();
    fn tm_memo_key(_env: &Env<'v>, _a: &Rc<Term>, _b: &Rc<Term>) -> Option<()> {
        None
    }

    type Ty = Type;
    type Tm = Rc<Term>;
    type TyC = Rc<Type>;
    type TmC = Rc<Term>;
    type Subst = LocalSubst;
    /// The syntax domain reads Γ-scoped syntax in Γ; there is nothing to
    /// carry.
    type RecCtx = ();

    // -- reduction ----------------------------------------------------------

    #[inline]
    fn whnf_ty(cv: &mut Conv<'v, Self>, env: &Env<'v>, t: &Rc<Type>) -> R<Type> {
        let defs = cv.defs(env);
        step_ty(cv, env, t, |t, g| step_type_delta(t, g, defs))
    }

    #[inline]
    fn whnf_ty_root(cv: &mut Conv<'v, Self>, env: &Env<'v>, t: &Type) -> R<Type> {
        step_ty(cv, env, t, step_type)
    }

    #[inline]
    fn whnf_tm_root(cv: &mut Conv<'v, Self>, env: &Env<'v>, t: &Term) -> R<Rc<Term>> {
        let mut cur = t.clone();
        while let Some(next) = stepped(step_term(&cur, &env.gamma))? {
            cv.spend()?;
            cur = next;
        }
        Ok(Rc::new(cur))
    }

    #[inline]
    fn whnf_tm(cv: &mut Conv<'v, Self>, env: &Env<'v>, t: &Rc<Term>) -> R<Rc<Term>> {
        let defs = cv.defs(env);
        step_tm(cv, env, t, |t, g| step_term_delta(t, g, defs))
    }

    #[inline]
    fn whnf_ty_opaque(cv: &mut Conv<'v, Self>, env: &Env<'v>, t: &Rc<Type>) -> R<Type> {
        step_ty(cv, env, t, step_type)
    }

    #[inline]
    fn whnf_tm_opaque(cv: &mut Conv<'v, Self>, env: &Env<'v>, t: &Rc<Term>) -> R<Rc<Term>> {
        step_tm(cv, env, t, step_term)
    }

    #[inline]
    fn delta_ty(cv: &mut Conv<'v, Self>, env: &Env<'v>, w: &Type) -> R<Type> {
        let defs = cv.defs(env);
        let Some(first) = stepped(step_type_delta(w, &env.gamma, defs))? else {
            return Ok(w.clone());
        };
        cv.spend()?;
        step_ty(cv, env, &first, step_type)
    }

    #[inline]
    fn delta_tm(cv: &mut Conv<'v, Self>, env: &Env<'v>, w: &Rc<Term>) -> R<Rc<Term>> {
        let defs = cv.defs(env);
        let Some(first) = stepped(step_term_delta(w, &env.gamma, defs))? else {
            return Ok(Rc::clone(w));
        };
        cv.spend()?;
        step_tm(cv, env, &Rc::new(first), step_term)
    }

    fn delta_whnf_tm(cv: &mut Conv<'v, Self>, env: &Env<'v>, mut w: Rc<Term>) -> R<Rc<Term>> {
        while Self::delta_head(cv, env, &w).is_some() {
            w = Self::delta_tm(cv, env, &w)?;
        }
        Ok(w)
    }

    #[inline]
    fn delta_head(cv: &Conv<'v, Self>, env: &Env<'v>, w: &Rc<Term>) -> Option<GlobalVar> {
        super::delta_head(w, cv.defs(env))
    }

    #[inline]
    fn delta_head_ty(cv: &Conv<'v, Self>, env: &Env<'v>, w: &Type) -> Option<GlobalVar> {
        super::delta_head_ty(w, cv.defs(env))
    }


    fn is_application_spine(w: &Rc<Term>) -> bool {
        let mut t: &Term = w;
        loop {
            match t {
                Term::GlobalTm { .. } => return true,
                Term::App { fun, .. }
                | Term::AppAt { fun, .. }
                | Term::UApp { fun, .. }
                | Term::CtxApp { fun, .. }
                | Term::TyApp { fun, .. } => t = fun,
                _ => return false,
            }
        }
    }

    // -- views --------------------------------------------------------------

    fn vec_former(_cv: &Conv<'v, Self>, _env: &Env<'v>, t: &Rc<Type>) -> Option<(Level, Rc<Type>, Rc<Term>)> {
        match &**t {
            Type::Vec { level, elem, len } => Some((level.clone(), Rc::clone(elem), Rc::clone(len))),
            _ => None,
        }
    }

    #[inline]
    fn view_ty<'a>(_cv: &mut Conv<'v, Self>, _env: &Env<'v>, w: &'a Type) -> TyView<'a, 'v, Self> {
        match w {
            Type::Nat => TyView::Nat,
            Type::Ty(l) => TyView::Ty(l),
            Type::Unit { level } => TyView::Unit { level },
            Type::Empty { level } => TyView::Empty { level },
            Type::SEmpty { level } => TyView::SEmpty { level },
            Type::Squash { level, ty } => TyView::Squash { level, ty: Rc::clone(ty) },
            Type::Pi { dom_level, cod_level, dom, cod } => TyView::Pi {
                dom_level,
                cod_level,
                dom: Rc::clone(dom),
                cod: Rc::clone(cod),
            },
            Type::Sigma { fst_level, snd_level, fst, snd } => TyView::Sigma {
                fst_level,
                snd_level,
                fst: Rc::clone(fst),
                snd: Rc::clone(snd),
            },
            Type::W { shape_level, pos_level, shape, pos } => TyView::W {
                shape_level,
                pos_level,
                shape: Rc::clone(shape),
                pos: Rc::clone(pos),
            },
            Type::Wf { level, shape, arity } => {
                TyView::Wf { level, shape: Rc::clone(shape), arity: Rc::clone(arity) }
            }
            Type::Sum { lhs_level, rhs_level, lhs, rhs } => TyView::Sum {
                lhs_level,
                rhs_level,
                lhs: Rc::clone(lhs),
                rhs: Rc::clone(rhs),
            },
            Type::Id { level, ty, lhs, rhs } => TyView::Id {
                level,
                ty: Rc::clone(ty),
                lhs: Rc::clone(lhs),
                rhs: Rc::clone(rhs),
            },
            Type::SEq { level, ty, lhs, rhs } => TyView::SEq {
                level,
                ty: Rc::clone(ty),
                lhs: Rc::clone(lhs),
                rhs: Rc::clone(rhs),
            },
            Type::Vec { level, elem, len } => {
                TyView::Vec { level, elem: Rc::clone(elem), len: Rc::clone(len) }
            }
            Type::Fin { len } => TyView::Fin { len: Rc::clone(len) },
            Type::DVec { level, len, fam } => {
                TyView::DVec { level, len: Rc::clone(len), fam: Rc::clone(fam) }
            }
            Type::IWf { sig, index } => TyView::IWf {
                level: &sig.level,
                idx_level: &sig.idx_level,
                idx: Rc::clone(&sig.idx),
                shape: Rc::clone(&sig.shape),
                arity: Rc::clone(&sig.arity),
                out: Rc::clone(&sig.out),
                child: Rc::clone(&sig.child),
                index: Rc::clone(index),
            },
            Type::M { sig, index } => TyView::M { sig: syn_m_sig(sig), index: Rc::clone(index) },
            Type::UPi { num_vars, level, body } => {
                TyView::UPi { num_vars: *num_vars, level, body: Rc::clone(body) }
            }
            Type::CtxPi { level, body } => TyView::CtxPi { level, body: Rc::clone(body) },
            Type::TyPi { ctx, arg_level, body_level, body } => {
                TyView::TyPi { ctx, arg_level, body_level, body: Rc::clone(body) }
            }
            Type::CodeTy { ctx, level } => TyView::CodeTy { ctx, level },
            Type::CodeTm { ctx, ty, level } => TyView::CodeTm { ctx, ty, level },
            Type::El { level, tm } => TyView::El { level, tm: Rc::clone(tm) },
            Type::GlobalTy { var, subst } => TyView::GlobalTy { var: *var, subst },
        }
    }

    #[inline]
    fn view_tm<'a>(_cv: &mut Conv<'v, Self>, _env: &Env<'v>, w: &'a Rc<Term>) -> TmView<'a, 'v, Self> {
        match &**w {
            Term::TmNat => TmView::TmNat,
            Term::TmTy(l) => TmView::TmTy(l),
            Term::TmUnit { level } => TmView::TmUnit { level },
            Term::TmEmpty { level } => TmView::TmEmpty { level },
            Term::TmSEmpty { level } => TmView::TmSEmpty { level },
            Term::TmSquash { level, ty } => TmView::TmSquash { level, ty: Rc::clone(ty) },
            Term::TmPi { dom_level, cod_level, dom, cod } => TmView::TmPi {
                dom_level,
                cod_level,
                dom: Rc::clone(dom),
                cod: Rc::clone(cod),
            },
            Term::TmSigma { fst_level, snd_level, fst, snd } => TmView::TmSigma {
                fst_level,
                snd_level,
                fst: Rc::clone(fst),
                snd: Rc::clone(snd),
            },
            Term::TmW { shape_level, pos_level, shape, pos } => TmView::TmW {
                shape_level,
                pos_level,
                shape: Rc::clone(shape),
                pos: Rc::clone(pos),
            },
            Term::TmWf { level, shape, arity } => {
                TmView::TmWf { level, shape: Rc::clone(shape), arity: Rc::clone(arity) }
            }
            Term::TmDVec { level, len, fam } => {
                TmView::TmDVec { level, len: Rc::clone(len), fam: Rc::clone(fam) }
            }
            Term::TmIWf { level, idx_level, idx, shape, arity, out, child, index } => TmView::TmIWf {
                level,
                idx_level,
                idx: Rc::clone(idx),
                shape: Rc::clone(shape),
                arity: Rc::clone(arity),
                out: Rc::clone(out),
                child: Rc::clone(child),
                index: Rc::clone(index),
            },
            Term::TmM { level, pos_level, idx_level, idx, shape, pos, next, index } => TmView::TmM {
                level,
                pos_level,
                idx_level,
                idx: Rc::clone(idx),
                shape: Rc::clone(shape),
                pos: Rc::clone(pos),
                next: Rc::clone(next),
                index: Rc::clone(index),
            },
            Term::TmId { level, ty, lhs, rhs } => TmView::TmId {
                level,
                ty: Rc::clone(ty),
                lhs: Rc::clone(lhs),
                rhs: Rc::clone(rhs),
            },
            Term::TmSEq { level, ty, lhs, rhs } => TmView::TmSEq {
                level,
                ty: Rc::clone(ty),
                lhs: Rc::clone(lhs),
                rhs: Rc::clone(rhs),
            },
            Term::TmSum { lhs_level, rhs_level, lhs, rhs } => TmView::TmSum {
                lhs_level,
                rhs_level,
                lhs: Rc::clone(lhs),
                rhs: Rc::clone(rhs),
            },
            Term::TmVec { level, elem, len } => {
                TmView::TmVec { level, elem: Rc::clone(elem), len: Rc::clone(len) }
            }
            Term::TmFin { len } => TmView::TmFin { len: Rc::clone(len) },

            Term::Zero => TmView::Zero,
            Term::NatLit(n) if n.is_zero() => TmView::Zero,
            Term::NatLit(n) => TmView::Succ(Rc::new(crate::term::nat_lit_pred(n))),
            Term::Succ(t) => TmView::Succ(Rc::clone(t)),
            Term::Refl { tm, .. } => TmView::Refl { tm: Rc::clone(tm) },
            Term::Inl { val, .. } => TmView::Inl { val: Rc::clone(val) },
            Term::Inr { val, .. } => TmView::Inr { val: Rc::clone(val) },
            Term::Sup { label, children, .. } => {
                TmView::Sup { label: Rc::clone(label), children: Rc::clone(children) }
            }
            Term::Supf { label, children, .. } => {
                TmView::Supf { label: Rc::clone(label), children: Rc::clone(children) }
            }
            Term::Supi { label, children, .. } => {
                TmView::Supi { label: Rc::clone(label), children: Rc::clone(children) }
            }
            Term::Corec { sig, carrier_level, carrier, step, seed, .. } => TmView::Corec {
                sig: syn_m_sig(sig),
                carrier_level,
                carrier: Rc::clone(carrier),
                step: Rc::clone(step),
                seed: Rc::clone(seed),
            },
            Term::BoxTy(t) => TmView::BoxTy(t),
            Term::BoxTm(t) => TmView::BoxTm(t),

            Term::Var(x) => TmView::Var(*x),
            Term::GlobalTm { var, subst } => TmView::GlobalTm { var: *var, subst },
            Term::ElimNat { level, motive, base, step, scrut } => TmView::ElimNat {
                level,
                motive: Rc::clone(motive),
                base: Rc::clone(base),
                step: Rc::clone(step),
                scrut: Rc::clone(scrut),
            },
            Term::ElimEmpty { level, scrut_level, motive, scrut } => TmView::ElimEmpty {
                level,
                scrut_level,
                motive: Rc::clone(motive),
                scrut: Rc::clone(scrut),
            },
            Term::ElimSEmpty { level, scrut_level, motive, scrut } => TmView::ElimSEmpty {
                level,
                scrut_level,
                motive: Rc::clone(motive),
                scrut: Rc::clone(scrut),
            },
            Term::ElimSquash { src_level, dst_level, src_ty, motive, scrut, .. } => {
                TmView::ElimSquash {
                    src_level,
                    dst_level,
                    src_ty: Rc::clone(src_ty),
                    motive: Rc::clone(motive),
                    scrut: Rc::clone(scrut),
                }
            }
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
            } => TmView::Case {
                lhs_level,
                rhs_level,
                motive_level,
                lhs: Rc::clone(lhs),
                rhs: Rc::clone(rhs),
                motive: Rc::clone(motive),
                case_l: Rc::clone(case_l),
                case_r: Rc::clone(case_r),
                scrut: Rc::clone(scrut),
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
            } => TmView::ElimW {
                shape_level,
                pos_level,
                motive_level,
                shape: Rc::clone(shape),
                pos: Rc::clone(pos),
                motive: Rc::clone(motive),
                step: Rc::clone(step),
                scrut: Rc::clone(scrut),
            },
            Term::ElimWf { level, motive_level, shape, arity, motive, step, scrut } => {
                TmView::ElimWf {
                    level,
                    motive_level,
                    shape: Rc::clone(shape),
                    arity: Rc::clone(arity),
                    motive: Rc::clone(motive),
                    step: Rc::clone(step),
                    scrut: Rc::clone(scrut),
                }
            }
            Term::ElimIWf { sig, motive_level, motive, step, index, scrut } => TmView::ElimIWf {
                level: &sig.level,
                idx_level: &sig.idx_level,
                motive_level,
                idx: Rc::clone(&sig.idx),
                shape: Rc::clone(&sig.shape),
                arity: Rc::clone(&sig.arity),
                out: Rc::clone(&sig.out),
                child: Rc::clone(&sig.child),
                motive: Rc::clone(motive),
                step: Rc::clone(step),
                index: Rc::clone(index),
                scrut: Rc::clone(scrut),
            },
            Term::Out { sig, index, scrut } => {
                TmView::Out { sig: syn_m_sig(sig), index: Rc::clone(index), scrut: Rc::clone(scrut) }
            }
            Term::J { ty_level, motive_level, ty, lhs, motive, case, rhs, proof } => TmView::J {
                ty_level,
                motive_level,
                ty: Rc::clone(ty),
                lhs: Rc::clone(lhs),
                motive: Rc::clone(motive),
                case: Rc::clone(case),
                rhs: Rc::clone(rhs),
                proof: Rc::clone(proof),
            },
            Term::App { fun, dom_level, cod_level, arg, .. } => TmView::App {
                levels: Some((dom_level, cod_level)),
                fun: Rc::clone(fun),
                arg: Rc::clone(arg),
            },
            Term::AppAt { fun, arg } => {
                TmView::App { levels: None, fun: Rc::clone(fun), arg: Rc::clone(arg) }
            }
            Term::Fst { fst_level, snd_level, pair, .. } => {
                TmView::Fst { levels: Some((fst_level, snd_level)), pair: Rc::clone(pair) }
            }
            Term::Snd { fst_level, snd_level, pair, .. } => {
                TmView::Snd { levels: Some((fst_level, snd_level)), pair: Rc::clone(pair) }
            }
            Term::UApp { fun, levels } => {
                TmView::UApp { levels, fun: Rc::clone(fun) }
            }
            Term::CtxApp { fun, ctx } => TmView::CtxApp { ctx, fun: Rc::clone(fun) },
            Term::TyApp { fun, arg } => TmView::TyApp { arg, fun: Rc::clone(fun) },
            Term::LetBoxTy { motive_level, code_level, ctx, motive, body, scrut } => {
                TmView::LetBoxTy {
                    motive_level,
                    code_level,
                    ctx,
                    motive: Rc::clone(motive),
                    body: Rc::clone(body),
                    scrut: Rc::clone(scrut),
                }
            }
            Term::LetBoxTm { motive_level, code_level, ctx, ty, motive, body, scrut } => {
                TmView::LetBoxTm {
                    motive_level,
                    code_level,
                    ctx,
                    ty,
                    motive: Rc::clone(motive),
                    body: Rc::clone(body),
                    scrut: Rc::clone(scrut),
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
            } => TmView::ElimCodeTy {
                ty_motive_level,
                tm_motive_level,
                motives: Rc::clone(motives),
                branches: Rc::clone(branches),
                code_level,
                ctx,
                scrut: Rc::clone(scrut),
                rec: (),
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
            } => TmView::ElimCodeTm {
                ty_motive_level,
                tm_motive_level,
                motives: Rc::clone(motives),
                branches: Rc::clone(branches),
                code_level,
                ctx,
                ty,
                scrut: Rc::clone(scrut),
                rec: (),
            },

            // The checked spellings view exactly as the forms they spell
            // (docs/intro-by-type-design.md §9.0 item 3): the annotation is
            // not part of any of these views, so there is nothing to see
            // through and nothing to reduce. This is also what makes
            // `inl@(T;a)` and `inl(A;B;a)` convertible without a new arm.
            Term::InlAt { val, .. } => TmView::Inl { val: Rc::clone(val) },
            Term::InrAt { val, .. } => TmView::Inr { val: Rc::clone(val) },
            Term::FstAt { pair, .. } => TmView::Fst { levels: None, pair: Rc::clone(pair) },
            Term::SndAt { pair, .. } => TmView::Snd { levels: None, pair: Rc::clone(pair) },

            Term::Lam { .. }
            | Term::ULam { .. }
            | Term::CtxLam { .. }
            | Term::TyLam { .. }
            | Term::Pair { .. }
            | Term::PairAt { .. }
            | Term::VecLit { .. }
            | Term::Triv { .. }
            | Term::SRefl { .. }
            | Term::Squash { .. } => TmView::Opaque,
        }
    }

    #[inline]
    fn head_tm(_cv: &mut Conv<'v, Self>, _env: &Env<'v>, t: &Rc<Term>) -> R<Rc<Term>> {
        Ok(Rc::clone(t))
    }

    #[inline]
    fn as_child_ty(_cv: &mut Conv<'v, Self>, _env: &Env<'v>, w: &Type) -> R<Rc<Type>> {
        Ok(Rc::new(w.clone()))
    }

    // -- scope --------------------------------------------------------------

    #[inline]
    fn push_entry(env: &Env<'v>, ty: &Rc<Type>, level: &Level) -> Env<'v> {
        env.push_entry_syn(Rc::clone(ty), level.clone())
    }

    #[inline]
    fn push_spec(env: &Env<'v>, tele: &rec::Tele) -> Env<'v> {
        let mut e = env.push_tele(tele.univs, tele.globals.clone());
        for (ty, level) in &tele.locals {
            e = e.push_entry_syn(Rc::clone(ty), level.clone());
        }
        e.tele.2 = tele.locals.len() as u32;
        e
    }

    #[inline]
    fn var_type(_cv: &mut Conv<'v, Self>, env: &Env<'v>, x: LocalVar) -> R<(Rc<Type>, Level)> {
        let Some(e) = env.gamma.entries.nth_inner(x.0) else {
            return Err(NC);
        };
        Ok((Rc::new(e.ty.shift_local(x.0 + 1)), e.level.clone()))
    }

    #[inline]
    fn weaken_ty(_env: &Env<'v>, t: &Rc<Type>, by: u32) -> Rc<Type> {
        Rc::new(t.shift_local(by))
    }

    #[inline]
    fn weaken_tm(_env: &Env<'v>, t: &Rc<Term>, by: u32) -> Rc<Term> {
        Rc::new(t.shift_local(by))
    }

    // -- embedding ----------------------------------------------------------

    #[inline]
    fn embed_ty(_env: &Env<'v>, t: Rc<Type>) -> Rc<Type> {
        t
    }

    #[inline]
    fn embed_ty_at(_rec: &(), _env: &Env<'v>, t: Rc<Type>) -> Rc<Type> {
        t
    }

    #[inline]
    fn embed_tm_at(_rec: &(), _env: &Env<'v>, t: Rc<Term>) -> Rc<Term> {
        t
    }

    // -- instantiation ------------------------------------------------------

    #[inline]
    fn inst_ty(
        _cv: &mut Conv<'v, Self>,
        home: &Env<'v>,
        cur: &Env<'v>,
        m: &Rc<Type>,
        args: &[Rc<Term>],
    ) -> R<Rc<Type>> {
        let mut d = id_at(home, cur);
        for a in args {
            d = d.extended(Rc::clone(a));
        }
        Ok(Rc::new(m.apply_local(&d)))
    }

    #[inline]
    fn inst_tm(
        _cv: &mut Conv<'v, Self>,
        home: &Env<'v>,
        cur: &Env<'v>,
        m: &Rc<Term>,
        args: &[Rc<Term>],
    ) -> R<Rc<Term>> {
        let mut d = id_at(home, cur);
        for a in args {
            d = d.extended(Rc::clone(a));
        }
        Ok(Rc::new(m.apply_local(&d)))
    }

    #[inline]
    fn shift_global_ty(
        _cv: &mut Conv<'v, Self>,
        _env: &Env<'v>,
        t: &Rc<Type>,
        by: u32,
    ) -> R<Rc<Type>> {
        Ok(Rc::new(t.shift_global(by)))
    }

    #[inline]
    fn inst_univ_ty(
        _cv: &mut Conv<'v, Self>,
        _env: &Env<'v>,
        body: &Rc<Type>,
        phi: &[Level],
    ) -> R<Rc<Type>> {
        Ok(Rc::new(body.inst_univ(phi)))
    }

    #[inline]
    fn inst_ctx_ty(
        _cv: &mut Conv<'v, Self>,
        _env: &Env<'v>,
        body: &Rc<Type>,
        ctx: &LocalCtx,
    ) -> R<Rc<Type>> {
        Ok(Rc::new(
            body.apply_global(&GlobalSubst::single(GlobalEntry::Ctx(ctx.clone()))),
        ))
    }

    #[inline]
    fn inst_tyarg_ty(
        _cv: &mut Conv<'v, Self>,
        _env: &Env<'v>,
        body: &Rc<Type>,
        arg: &Rc<Type>,
    ) -> R<Rc<Type>> {
        Ok(Rc::new(
            body.apply_global(&GlobalSubst::single(GlobalEntry::Ty(Rc::clone(arg)))),
        ))
    }

    // -- local substitutions ------------------------------------------------

    #[inline]
    fn subst_len(d: &LocalSubst) -> usize {
        d.terms.len()
    }

    #[inline]
    fn subst_term(_env: &Env<'v>, d: &LocalSubst, k: usize) -> Rc<Term> {
        Rc::clone(&d.terms[k])
    }

    /// Already in the extended scope: the syntax under a binder is written
    /// there.
    #[inline]
    fn under_tele_ty(
        _cv: &mut Conv<'v, Self>,
        _env: &Env<'v>,
        t: &Rc<Type>,
        _tu: u32,
        _tg: u32,
    ) -> R<Rc<Type>> {
        Ok(Rc::clone(t))
    }

    #[inline]
    fn under_tele_tm(
        _cv: &mut Conv<'v, Self>,
        _env: &Env<'v>,
        t: &Rc<Term>,
        _tu: u32,
        _tg: u32,
    ) -> R<Rc<Term>> {
        Ok(Rc::clone(t))
    }

    #[inline]
    fn subst_tails_agree(a: &LocalSubst, b: &LocalSubst) -> bool {
        a.tail == b.tail
    }

    #[inline]
    fn apply_subst_ty(
        _cv: &mut Conv<'v, Self>,
        _env: &Env<'v>,
        d: &LocalSubst,
        k: usize,
        t: &Rc<Type>,
    ) -> R<Rc<Type>> {
        let prefix = LocalSubst { tail: d.tail, terms: d.terms[..k].to_vec() };
        Ok(Rc::new(t.apply_local(&prefix)))
    }

    // -- synthesized types --------------------------------------------------

    #[inline]
    fn nat(_env: &Env<'v>) -> Rc<Type> {
        NAT.with(Rc::clone)
    }

    #[inline]
    fn univ(_env: &Env<'v>, level: &Level) -> Rc<Type> {
        Rc::new(Type::Ty(level.clone()))
    }

    #[inline]
    fn empty(_env: &Env<'v>, level: &Level) -> Rc<Type> {
        Rc::new(Type::Empty { level: level.clone() })
    }

    #[inline]
    fn sempty(_env: &Env<'v>, level: &Level) -> Rc<Type> {
        Rc::new(Type::SEmpty { level: level.clone() })
    }

    fn squash(_env: &Env<'v>, level: &Level, ty: &Rc<Type>) -> Rc<Type> {
        Rc::new(Type::Squash { level: level.clone(), ty: Rc::clone(ty) })
    }

    #[inline]
    fn code_ty(_env: &Env<'v>, ctx: &LocalCtx, level: &Level) -> Rc<Type> {
        Rc::new(Type::CodeTy { ctx: ctx.clone(), level: level.clone() })
    }

    #[inline]
    fn code_tm(_env: &Env<'v>, ctx: &LocalCtx, ty: &Rc<Type>, level: &Level) -> Rc<Type> {
        Rc::new(Type::CodeTm {
            ctx: ctx.clone(),
            ty: Rc::clone(ty),
            level: level.clone(),
        })
    }

    #[inline]
    fn el(_cv: &mut Conv<'v, Self>, _env: &Env<'v>, level: &Level, tm: &Rc<Term>) -> R<Rc<Type>> {
        Ok(Rc::new(Type::El { level: level.clone(), tm: Rc::clone(tm) }))
    }

    #[inline]
    fn pi(
        _cv: &mut Conv<'v, Self>,
        _env: &Env<'v>,
        dom_level: &Level,
        cod_level: &Level,
        dom: &Rc<Type>,
        cod: &Rc<Type>,
    ) -> R<Rc<Type>> {
        Ok(Rc::new(Type::Pi {
            dom_level: dom_level.clone(),
            cod_level: cod_level.clone(),
            dom: Rc::clone(dom),
            cod: Rc::clone(cod),
        }))
    }

    #[inline]
    fn sum(
        _cv: &mut Conv<'v, Self>,
        _env: &Env<'v>,
        lhs_level: &Level,
        rhs_level: &Level,
        lhs: &Rc<Type>,
        rhs: &Rc<Type>,
    ) -> R<Rc<Type>> {
        Ok(Rc::new(Type::Sum {
            lhs_level: lhs_level.clone(),
            rhs_level: rhs_level.clone(),
            lhs: Rc::clone(lhs),
            rhs: Rc::clone(rhs),
        }))
    }

    #[inline]
    fn w(
        _cv: &mut Conv<'v, Self>,
        _env: &Env<'v>,
        shape_level: &Level,
        pos_level: &Level,
        shape: &Rc<Type>,
        pos: &Rc<Type>,
    ) -> R<Rc<Type>> {
        Ok(Rc::new(Type::W {
            shape_level: shape_level.clone(),
            pos_level: pos_level.clone(),
            shape: Rc::clone(shape),
            pos: Rc::clone(pos),
        }))
    }

    #[inline]
    fn wf(
        _cv: &mut Conv<'v, Self>,
        _env: &Env<'v>,
        level: &Level,
        shape: &Rc<Type>,
        arity: &Rc<Term>,
    ) -> R<Rc<Type>> {
        Ok(Rc::new(Type::Wf {
            level: level.clone(),
            shape: Rc::clone(shape),
            arity: Rc::clone(arity),
        }))
    }

    #[inline]
    fn vec(
        _cv: &mut Conv<'v, Self>,
        _env: &Env<'v>,
        level: &Level,
        elem: &Rc<Type>,
        len: &Rc<Term>,
    ) -> R<Rc<Type>> {
        Ok(Rc::new(Type::Vec {
            level: level.clone(),
            elem: Rc::clone(elem),
            len: Rc::clone(len),
        }))
    }

    #[inline]
    fn fin(_cv: &mut Conv<'v, Self>, _env: &Env<'v>, len: &Rc<Term>) -> R<Rc<Type>> {
        Ok(Rc::new(Type::Fin { len: Rc::clone(len) }))
    }

    #[inline]
    fn id(
        _cv: &mut Conv<'v, Self>,
        _env: &Env<'v>,
        level: &Level,
        ty: &Rc<Type>,
        lhs: &Rc<Term>,
        rhs: &Rc<Term>,
    ) -> R<Rc<Type>> {
        Ok(Rc::new(Type::Id {
            level: level.clone(),
            ty: Rc::clone(ty),
            lhs: Rc::clone(lhs),
            rhs: Rc::clone(rhs),
        }))
    }

    // -- synthesized terms --------------------------------------------------

    #[inline]
    fn zero(_env: &Env<'v>) -> Rc<Term> {
        ZERO.with(Rc::clone)
    }

    #[inline]
    fn succ(_cv: &mut Conv<'v, Self>, _env: &Env<'v>, t: &Rc<Term>) -> R<Rc<Term>> {
        Ok(Rc::new(Term::Succ(Rc::clone(t))))
    }

    #[inline]
    fn local(_env: &Env<'v>, x: LocalVar) -> Rc<Term> {
        Rc::new(Term::Var(x))
    }

    #[inline]
    fn refl(
        _cv: &mut Conv<'v, Self>,
        _env: &Env<'v>,
        level: &Level,
        ty: &Rc<Type>,
        tm: &Rc<Term>,
    ) -> R<Rc<Term>> {
        Ok(Rc::new(Term::Refl {
            level: level.clone(),
            ty: Rc::clone(ty),
            tm: Rc::clone(tm),
        }))
    }

    #[inline]
    #[allow(clippy::too_many_arguments)]
    fn inj(
        _cv: &mut Conv<'v, Self>,
        _env: &Env<'v>,
        left: bool,
        lhs_level: &Level,
        rhs_level: &Level,
        lhs: &Rc<Type>,
        rhs: &Rc<Type>,
        val: &Rc<Term>,
    ) -> R<Rc<Term>> {
        let (ll, rl) = (lhs_level.clone(), rhs_level.clone());
        let (l, r, v) = (Rc::clone(lhs), Rc::clone(rhs), Rc::clone(val));
        Ok(Rc::new(if left {
            Term::Inl { lhs_level: ll, rhs_level: rl, lhs: l, rhs: r, val: v }
        } else {
            Term::Inr { lhs_level: ll, rhs_level: rl, lhs: l, rhs: r, val: v }
        }))
    }

    #[inline]
    fn sup_at(
        _cv: &mut Conv<'v, Self>,
        _env: &Env<'v>,
        w: &Rc<Type>,
        by: u32,
        label: &Rc<Term>,
        children: &Rc<Term>,
    ) -> R<Rc<Term>> {
        let Type::W { shape_level, pos_level, shape, pos } = w.shift_local(by) else {
            return Err(NC);
        };
        Ok(Rc::new(Term::Sup {
            shape_level,
            pos_level,
            shape_ty: shape,
            pos_ty: pos,
            label: Rc::clone(label),
            children: Rc::clone(children),
        }))
    }

    #[inline]
    fn ty_eq_fast(a: &Rc<Type>, b: &Rc<Type>) -> bool {
        Rc::ptr_eq(a, b)
    }

    #[inline]
    fn tm_identity_fast(a: &Rc<Term>, b: &Rc<Term>) -> bool {
        Rc::ptr_eq(a, b)
    }

    #[inline]
    fn app(
        _cv: &mut Conv<'v, Self>,
        _env: &Env<'v>,
        dom_level: &Level,
        cod_level: &Level,
        dom: &Rc<Type>,
        cod: &Rc<Type>,
        fun: &Rc<Term>,
        arg: &Rc<Term>,
    ) -> R<Rc<Term>> {
        Ok(Rc::new(Term::App {
            fun: Rc::clone(fun),
            dom_level: dom_level.clone(),
            cod_level: cod_level.clone(),
            dom: Rc::clone(dom),
            cod: Rc::clone(cod),
            arg: Rc::clone(arg),
        }))
    }

    #[inline]
    fn proj(
        _cv: &mut Conv<'v, Self>,
        _env: &Env<'v>,
        first: bool,
        fst_level: &Level,
        snd_level: &Level,
        fst_ty: &Rc<Type>,
        snd_ty: &Rc<Type>,
        pair: &Rc<Term>,
    ) -> R<Rc<Term>> {
        Ok(Rc::new(proj_syn(first, fst_level, snd_level, fst_ty, snd_ty, Rc::clone(pair))))
    }

    #[inline]
    fn box_ty(_env: &Env<'v>, code: Rc<Type>) -> Rc<Term> {
        Rc::new(Term::BoxTy(code))
    }

    #[inline]
    fn box_tm(_env: &Env<'v>, code: Rc<Term>) -> Rc<Term> {
        Rc::new(Term::BoxTm(code))
    }

    #[inline]
    fn box_ty_payload(
        _cv: &mut Conv<'v, Self>,
        _env: &Env<'v>,
        t: &Rc<Term>,
    ) -> R<Option<Rc<Type>>> {
        Ok(match &**t {
            Term::BoxTy(c) => Some(Rc::clone(c)),
            _ => None,
        })
    }

    #[inline]
    fn box_tm_payload(
        _cv: &mut Conv<'v, Self>,
        _env: &Env<'v>,
        t: &Rc<Term>,
    ) -> R<Option<Rc<Term>>> {
        Ok(match &**t {
            Term::BoxTm(c) => Some(Rc::clone(c)),
            _ => None,
        })
    }

    // -- η -----------------------------------------------------------------

    #[inline]
    fn eta_app(
        _cv: &mut Conv<'v, Self>,
        outer: &Env<'v>,
        _inner: &Env<'v>,
        a: &Rc<Term>,
        b: &Rc<Term>,
        dom_level: &Level,
        cod_level: &Level,
        dom: &Rc<Type>,
        cod: &Rc<Type>,
    ) -> R<(Rc<Term>, Rc<Term>)> {
        // The `cod` annotation moves under the App binder: the Π variable maps
        // to the App's bound variable, Γ weakens by 2. Built once and shared
        // by the two sides.
        let cod_ann = Rc::new(
            cod.apply_local(&LocalSubst::id(&outer.gamma).shift_local(2).extended(var0())),
        );
        let dom_up = Rc::new(dom.shift_local(1));
        let app = |t: &Rc<Term>| {
            Rc::new(Term::App {
                fun: Rc::new(t.shift_local(1)),
                dom_level: dom_level.clone(),
                cod_level: cod_level.clone(),
                dom: Rc::clone(&dom_up),
                cod: Rc::clone(&cod_ann),
                arg: var0(),
            })
        };
        Ok((app(a), app(b)))
    }

    #[inline]
    fn eta_uapp(
        _cv: &mut Conv<'v, Self>,
        _outer: &Env<'v>,
        _inner: &Env<'v>,
        a: &Rc<Term>,
        b: &Rc<Term>,
        num_vars: u32,
    ) -> R<(Rc<Term>, Rc<Term>)> {
        let levels: Vec<Level> = (0..num_vars).rev().map(rec::lvar).collect();
        let uapp = |t: &Rc<Term>| {
            Rc::new(Term::UApp {
                fun: Rc::new(t.shift_univ(num_vars)),
                levels: levels.clone(),
            })
        };
        Ok((uapp(a), uapp(b)))
    }

    #[inline]
    fn eta_ctxapp(
        _cv: &mut Conv<'v, Self>,
        _outer: &Env<'v>,
        _inner: &Env<'v>,
        a: &Rc<Term>,
        b: &Rc<Term>,
    ) -> R<(Rc<Term>, Rc<Term>)> {
        let capp = |t: &Rc<Term>| {
            Rc::new(Term::CtxApp { fun: Rc::new(t.shift_global(1)), ctx: rec::g_ctx(0) })
        };
        Ok((capp(a), capp(b)))
    }

    #[inline]
    fn eta_tyapp(
        _cv: &mut Conv<'v, Self>,
        _outer: &Env<'v>,
        _inner: &Env<'v>,
        a: &Rc<Term>,
        b: &Rc<Term>,
        ctx: &LocalCtx,
    ) -> R<(Rc<Term>, Rc<Term>)> {
        let arg = Rc::new(rec::gty(0, &ctx.shift_global(1)));
        let tapp = |t: &Rc<Term>| {
            Rc::new(Term::TyApp { fun: Rc::new(t.shift_global(1)), arg: Rc::clone(&arg) })
        };
        Ok((tapp(a), tapp(b)))
    }

    #[inline]
    fn eta_proj(
        _cv: &mut Conv<'v, Self>,
        _env: &Env<'v>,
        first: bool,
        a: &Rc<Term>,
        b: &Rc<Term>,
        fst_level: &Level,
        snd_level: &Level,
        fst_ty: &Rc<Type>,
        snd_ty: &Rc<Type>,
    ) -> R<(Rc<Term>, Rc<Term>)> {
        let p = |t: &Rc<Term>| {
            Rc::new(proj_syn(first, fst_level, snd_level, fst_ty, snd_ty, Rc::clone(t)))
        };
        Ok((p(a), p(b)))
    }

    // -- recursors ----------------------------------------------------------

    #[inline]
    fn wf_step_telescope(
        _cv: &mut Conv<'v, Self>,
        env: &Env<'v>,
        level: &Level,
        motive_level: &Level,
        shape: &Rc<Type>,
        arity: &Rc<Term>,
        motive: &Rc<Type>,
    ) -> R<(Rc<Type>, Rc<Type>, Rc<Type>)> {
        let (cs, ih, step) =
            wf_step_telescope(&env.gamma, level, motive_level, shape, arity, motive);
        Ok((Rc::new(cs), Rc::new(ih), Rc::new(step)))
    }

    fn iwf_telescope(
        _cv: &mut Conv<'v, Self>,
        _env: &Env<'v>,
        sig: &IWfSigC<'_, 'v, Self>,
        motive_level: &Level,
        motive: &Rc<Type>,
    ) -> R<(Rc<Type>, Rc<Type>, Rc<Type>, Rc<Type>)> {
        let sig = Rc::new(IWfSig {
            level: sig.level.clone(),
            idx_level: sig.idx_level.clone(),
            idx: Rc::clone(sig.idx),
            shape: Rc::clone(sig.shape),
            arity: Rc::clone(sig.arity),
            out: Rc::clone(sig.out),
            child: Rc::clone(sig.child),
        });
        let mot = iwf_motive_scrut_ty(&sig);
        let (cs, ih, step) = iwf_step_telescope(&sig, motive_level, motive);
        Ok((Rc::new(mot), Rc::new(cs), Rc::new(ih), Rc::new(step)))
    }

    fn m_out_ty(_cv: &mut Conv<'v, Self>, _env: &Env<'v>, sig: &MSigC<'_, 'v, Self>, index: &Rc<Term>)
        -> R<Rc<Type>> {
        Ok(Rc::new(m_out_ty(&syn_m_sig_rc(sig), index)))
    }

    fn m_step_ty(
        _cv: &mut Conv<'v, Self>,
        _env: &Env<'v>,
        sig: &MSigC<'_, 'v, Self>,
        carrier_level: &Level,
        carrier: &Rc<Type>,
    ) -> R<Rc<Type>> {
        Ok(Rc::new(m_step_ty(&syn_m_sig_rc(sig), carrier_level, carrier).shift_local(1)))
    }

    fn iwf_children(
        _cv: &mut Conv<'v, Self>,
        _env: &Env<'v>,
        w: &Type,
        label: &Rc<Term>,
    ) -> R<Rc<Type>> {
        let Type::IWf { sig, .. } = w else {
            return Err(NC);
        };
        Ok(Rc::new(iwf_children_ty(sig, label)))
    }

    #[inline]
    fn inst_ty_motive(
        _cv: &mut Conv<'v, Self>,
        env: &Env<'v>,
        _rec: &(),
        motive: &Rc<Type>,
        code_level: &Level,
        ctx: &LocalCtx,
        scrut: &Rc<Term>,
    ) -> R<Rc<Type>> {
        Ok(Rc::new(rec::inst_ty_motive(
            motive,
            (0, 0, 0),
            code_level.clone(),
            ctx.clone(),
            (**scrut).clone(),
            &env.gamma,
        )))
    }

    #[inline]
    fn inst_tm_motive(
        _cv: &mut Conv<'v, Self>,
        env: &Env<'v>,
        _rec: &(),
        motive: &Rc<Type>,
        code_level: &Level,
        ctx: &LocalCtx,
        ty: &Rc<Type>,
        scrut: &Rc<Term>,
    ) -> R<Rc<Type>> {
        Ok(Rc::new(rec::inst_tm_motive(
            motive,
            (0, 0, 0),
            code_level.clone(),
            ctx.clone(),
            (**ty).clone(),
            (**scrut).clone(),
            &env.gamma,
        )))
    }
}

thread_local! {
    /// The two closed forms of [`Dom::nat`] / [`Dom::zero`], allocated once
    /// per thread. Conversion synthesizes them once per comparison node on
    /// its hottest paths, and an `Rc::new` there is measurable: building them
    /// per checker cost 1.5× on `nat/check-numeral` (`scripts/bench --check`,
    /// 2026-07-31).
    static NAT: Rc<Type> = Rc::new(Type::Nat);
    static ZERO: Rc<Term> = Rc::new(Term::Zero);
}

/// Weak-head reduce to a fixed point under `step`, spending one fuel per
/// step. A form that does not step is returned by handle: the rewriter's
/// normal forms are shared, not copied, which matters because most
/// sub-structures conversion reaches are already normal.
/// A step past its frame budget leaves the check without a verdict, as
/// spent fuel does.
fn stepped<T>(next: Result<Option<T>, OutOfFuel>) -> R<Option<T>> {
    next.map_err(|OutOfFuel| ConvError::OutOfFuel)
}

fn step_ty<'v>(
    cv: &mut Conv<'v, Syn>,
    env: &Env<'v>,
    t: &Type,
    step: impl Fn(&Type, &LocalCtx) -> Result<Option<Type>, OutOfFuel>,
) -> R<Type> {
    let mut cur = t.clone();
    while let Some(next) = stepped(step(&cur, &env.gamma))? {
        cv.spend()?;
        cur = next;
    }
    Ok(cur)
}

fn step_tm<'v>(
    cv: &mut Conv<'v, Syn>,
    env: &Env<'v>,
    t: &Rc<Term>,
    step: impl Fn(&Term, &LocalCtx) -> Result<Option<Term>, OutOfFuel>,
) -> R<Rc<Term>> {
    let Some(mut cur) = stepped(step(t, &env.gamma))? else {
        return Ok(Rc::clone(t));
    };
    cv.spend()?;
    while let Some(next) = stepped(step(&cur, &env.gamma))? {
        cv.spend()?;
        cur = next;
    }
    Ok(Rc::new(cur))
}

/// `fst p` / `snd p` at the given `Σ` annotations (shared by [`Dom::proj`]
/// and [`Dom::eta_proj`]).
fn proj_syn<'v>(
    first: bool,
    fst_level: &Level,
    snd_level: &Level,
    fst_ty: &Rc<Type>,
    snd_ty: &Rc<Type>,
    pair: Rc<Term>,
) -> Term {
    let (fl, sl) = (fst_level.clone(), snd_level.clone());
    let (ft, st) = (Rc::clone(fst_ty), Rc::clone(snd_ty));
    if first {
        Term::Fst { fst_level: fl, snd_level: sl, fst_ty: ft, snd_ty: st, pair }
    } else {
        Term::Snd { fst_level: fl, snd_level: sl, fst_ty: ft, snd_ty: st, pair }
    }
}
