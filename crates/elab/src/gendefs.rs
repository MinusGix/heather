//! Machine-named Ψ **definitions** for generator-emitted artifacts
//! (`issues/generated-term-defs.md`).
//!
//! The kernel has had bodied globals with layer-indexed transparency since
//! `issues/simulate-conversion-cost.md`, and a user `fn` is Ψ-referenced
//! rather than inlined (`lib.rs`'s header). The *generator's own* artifacts
//! were not: `μ` — route 2b's index measure — was a whole `elim_Wf` written
//! out afresh in the family type, twice per Σ projection and several times
//! per eliminator arm, and form A at a declared index additionally wrote out
//! one tag predicate per *other* index constructor and one child projection
//! per child. That is `docs/inductive-fording-lowering.md` §14.2 and §14.9,
//! and this module is their fix.
//!
//! The shape is the `#skel` precedent (§14.6): **registered once, at
//! declaration time, under a name the surface cannot write, and never edited
//! afterwards.** Emitted terms reference the definition; δ-unfolding at the
//! computing layers recovers exactly the term that used to be inlined, so
//! nothing downstream changes meaning — only size.
//!
//! Two properties make this safe to do blindly:
//!
//! - **The definitions are closed.** An *index* type is unparameterized by
//!   `inductive.rs`'s own rule (a parameterized index is rejected at the
//!   declaration), so a tag predicate and a child projection are closed for
//!   every family that can exist. `μ` is closed exactly when the forded
//!   declaration itself has no type parameters — see [`Elaborator::mu_def`]
//!   and the boundary note there.
//! - **Registration is best-effort.** If any piece fails to build or fails
//!   the kernel gate here, nothing is pushed and the emission site falls back
//!   to writing the term out inline, exactly as before. A definition is a
//!   *size* optimization, never a semantic one, so the fallback is the old
//!   behavior verbatim rather than an error at a span the user never wrote.

use std::collections::HashMap;
use std::sync::Arc as Rc;

use heather_kernel::layer::Layer;
use heather_kernel::level::Level;
use heather_kernel::term::{
    CtxBase, GlobalBinding, GlobalVar, LocalCtx, LocalSubst, LocalVar, SubstTail, Term, Type,
};
use heather_syntax::ast::Span;

use crate::inductive::{ConstBody, IdxTy, Inductive};
use crate::stats::decline;
use crate::{Alias, Cx, Elaborator, R, TyVar};

/// The key of a machine-named definition. Keys are **nominal**: a declaration
/// tag plus, where the device is per-constructor, its position. That is what
/// makes the recognizers of §6.3/§10.1 re-keyable — a reference to `μ_D` is
/// recognized by *being* `μ_D`, not by having `μ_D`'s shape.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub(crate) enum GenDef {
    /// `μ_D : ⟦Skel⟧ → I` for the forded declaration with this nominal tag
    /// (`docs/inductive-fording-lowering.md` §5).
    Mu(u32),
    /// `is_k : I → Type⁰`, the index type's tag predicate at constructor `k`
    /// (`docs/inductive-tier1-wf-lowering.md` §7.1). Keyed by the *index*
    /// type's tag, so every family over that index shares one.
    IdxTag(u32, usize),
    /// `proj_{k,t} : I → I → I`, the index type's `t`-th child projection at
    /// constructor `k`, abstracted over its default (§7.2). Keyed by the
    /// index type's tag, shared as above.
    IdxChild(u32, usize, usize),
    /// `I#icode : Trm_c(· ⊢ Ty l_I)` — the index type's **code**, consumed as
    /// `El (I#icode^δ)` (`docs/family-type-code-defs-design.md` §1). Keyed by
    /// the *index* type's tag, shared by every family over that index, exactly
    /// as `IdxTag`/`IdxChild`. An index type is unparameterized by
    /// `inductive.rs`'s own rule, so this has no closedness boundary at all.
    IdxCode(u32),
    /// `D#code : Trm_c(· ⊢ Ty l)` — the forded declaration's **skeleton
    /// code**, consumed as `El (D#code^δ)` (design §1). Keyed by the forded
    /// declaration's tag. Exists only for an unparameterized declaration —
    /// the same boundary as [`GenDef::Mu`], for the same reason (§14.12).
    SkelCode(u32),
    /// `D#tycode : Trm_c(· ⊢ Ty l)` — an **unparameterized, unindexed**
    /// declaration's whole lowered type `⟦D⟧`, consumed as `El (D#tycode^δ)`
    /// (`docs/family-type-code-defs-design.md` §1, dated extension of
    /// 2026-08-12). Keyed by the declaration's tag. Recursive (a `Type::Wf`)
    /// or not (a sum-of-Σs) — both are Θ(n²) and both are copied Θ(arms)
    /// times by the two `match` lowerings.
    ///
    /// The sibling of [`GenDef::SkelCode`], and deliberately a *different*
    /// key: `SkelCode` names a forded declaration's **skeleton**, this names a
    /// declaration's **own** lowering. The two boundaries differ too — see
    /// [`Elaborator::register_ty_code`].
    TyCode(u32),
    /// `D#tycode_fn : Π(A₁ : Ty l₁)…(v_m : T_m). Ty l :=
    /// λ(A₁ : Ty l₁)…(v_m : T_m). ⌜⟦D<El A₁,…>(v̄)⟧⌝` — a **parameterized or
    /// value-indexed**, unindexed declaration's lowering, abstracted over its
    /// own telescope, consumed as `El l (app(D#tycode_fn^δ; ā))`
    /// (`docs/per-instantiation-type-codes-design.md` §2). Keyed by the
    /// declaration's tag: one definition per declaration, not one per
    /// instantiation (§2.3).
    ///
    /// The complement of [`GenDef::TyCode`], which names the whole lowering of
    /// the declarations this one cannot reach. Registered at the
    /// **all-parameters-`Ty 0`** level profile and at no other (§2.1); a
    /// higher-level instantiation fails §4.1's guard and keeps the inline
    /// spelling.
    TyCodeFn(u32),
    /// `D#shape : Trm_c(· ⊢ Ty l)` — a **recursive** declaration's `Wf`
    /// **shape component** (the sum-of-Σs with the recursive fields deleted),
    /// consumed as `El (D#shape^δ)` in a `Supf`/`ElimWf`/`Type::Wf` shape slot
    /// (`docs/wf-shape-code-design.md` §2). Keyed by the declaration's tag.
    ///
    /// Deliberately *not* [`GenDef::TyCode`]: that names `⟦D⟧ = Wf(S). n`
    /// whole, and no reference to the whole can stand in a slot that holds the
    /// **component** — which is exactly why
    /// [[wf-shape-annotation-slots]] outlived the whole-type code round.
    ShapeCode(u32),
    /// `D#arity : Π(x : El (D#shape^δ)). Nat` — the same declaration's `Wf`
    /// **arity term**, λ-abstracted over the shape binder it is scoped under,
    /// consumed as `app(D#arity^δ; x₀)` in an arity slot (design §2).
    ///
    /// A *function*, not a code: the arity slot holds a `Term` in the extended
    /// context, and the only closed thing that can stand there and reduce back
    /// to `n` is an application of a definition to the binder. It is the
    /// larger of the two slots by several times, measured, which is why it is
    /// named at all rather than left as this issue's opening sentence had it.
    ArityFn(u32),
    /// `D#fam : Trm_c(· ⊢ Π(i : I). Ty l)` — a **route-1** indexed
    /// declaration's family function, consumed as `El l (D#fam^δ i)` (design
    /// §6). Keyed by the indexed declaration's tag. Route 1's family *is* a
    /// type-valued eliminator, so unlike route 2b there is one definition and
    /// not two: naming the function names the whole family. Same closedness
    /// boundary as [`GenDef::Mu`] (§5).
    Fam(u32),
    /// `D#projⱼ : Trm_c(· ⊢ Π(v : ⟦D⟧). Tⱼ)` — a **record**'s `j`-th field
    /// projection, keyed by the record's tag and the field's index
    /// (`issues/theorem-field-projection-oom.md`).
    ///
    /// Unlike its siblings this one is not only a size optimization. `π_j` is
    /// `fst(sndʲ v)`, and every `fst`/`snd` node carries the Σ components at
    /// its level as annotations, so a later field's type — which mentions the
    /// earlier fields — inlines the earlier projections *with their
    /// annotations*, once per occurrence: the term is exponential in the
    /// field index. Naming each projection makes a field's type mention
    /// `D#projᵢ^δ v` (one node) instead, so the walk, the term it produces,
    /// and everything downstream of both stay linear.
    ///
    /// Same closedness boundary as [`GenDef::Mu`] and [`GenDef::TyCode`]: only
    /// an unparameterized record, whose lowering is one closed type.
    RecProj(u32, usize),
    /// `D#tailⱼ : Trm_c(· ⊢ Π(v : ⟦D⟧). Σ…)` — the same record's Σ spine past
    /// entry `j`, the companion [`GenDef::RecProj`] is read off
    /// (`issues/theorem-field-projection-oom.md`).
    ///
    /// `π_j` is `fst` of a *tail*, and a raw `sndʲ` tail makes the kernel
    /// re-check the whole spine below it — carrying the whole remaining record
    /// type — once per level above. Naming each tail makes every one of those
    /// checks local: the pair a `fst`/`snd` is taken of has its Σ type
    /// straight out of Ψ. Registered with, and under the same boundary as,
    /// the projections.
    RecTail(u32, usize),
    /// `D#famⱼ : Trm_c(· ⊢ Π(v : ⟦D⟧). Π(x : Fⱼ). Ty l)` — the same record's
    /// Σ **tail family** at entry `j`, as a code
    /// (`issues/theorem-field-projection-oom.md`).
    ///
    /// The annotation every projection and tail node carries is `El` of this,
    /// which is what keeps their gate checks local: a code is checked, not
    /// reduced, so the earlier projections it mentions stay folded until a
    /// conversion actually needs the type behind them.
    RecFam(u32, usize),
    /// `D#payloadₖ : Trm_c(· ⊢ Ty lₖ) := ⌜⟦cₖ⟧⌝` — the `k`-th constructor's
    /// **payload type** of a **non-recursive**, unparameterized declaration
    /// with at least two constructors, consumed as `El (D#payloadₖ^δ)` in the
    /// `Inl`/`Inr` annotations of a constructor value and in a `Case`'s
    /// component slots (`issues/inductive-spelling-codes-nonrecursive.md`).
    /// Keyed by the declaration's tag and the constructor's position.
    ///
    /// The shape-code round rejected this key for **recursive** declarations
    /// on measurement (docs/wf-shape-code-design.md §5.1: their payloads'
    /// mass is embedded field types `TyCode` already names). A flat sum is
    /// different in kind: it has no `Wf` and no `D#shape`, so without these
    /// the only name it has is the whole type, and every `inl`/`inr` level
    /// below the whole writes its suffix sum out — Θ(n²) per literal.
    PayloadCode(u32, usize),
    /// `D#suffixₖ : Trm_c(· ⊢ Ty l) := D#payload_{k+1}^δ + D#suffix_{k+1}^δ`
    /// — the same declaration's **suffix sum** past constructor `k`, the
    /// right operand of the `k`-th `+` (`Spine::tails[k]`), spelled over the
    /// names of its own components so that each level of an injection costs
    /// the kernel one δ and a syntactic comparison. Registered for
    /// `k < n - 2` only: the last tail *is* the last payload, and takes
    /// [`GenDef::PayloadCode`]`(tag, n - 1)`.
    SuffixCode(u32, usize),
}

impl GenDef {
    /// The machine name, for diagnostics only — `#` is unwritable at the
    /// surface, the same convention `skeleton_of` uses.
    pub(crate) fn name(&self, owner: &str) -> String {
        match self {
            GenDef::Mu(_) => format!("{owner}#mu"),
            GenDef::IdxTag(_, k) => format!("{owner}#tag{k}"),
            GenDef::IdxChild(_, k, t) => format!("{owner}#child{k}.{t}"),
            GenDef::IdxCode(_) => format!("{owner}#icode"),
            GenDef::SkelCode(_) => format!("{owner}#code"),
            GenDef::TyCode(_) => format!("{owner}#tycode"),
            GenDef::TyCodeFn(_) => format!("{owner}#tycode_fn"),
            GenDef::ShapeCode(_) => format!("{owner}#shape"),
            GenDef::ArityFn(_) => format!("{owner}#arity"),
            GenDef::Fam(_) => format!("{owner}#fam"),
            GenDef::RecProj(_, j) => format!("{owner}#proj{j}"),
            GenDef::RecTail(_, j) => format!("{owner}#tail{j}"),
            GenDef::RecFam(_, j) => format!("{owner}#fam{j}"),
            GenDef::PayloadCode(_, k) => format!("{owner}#payload{k}"),
            GenDef::SuffixCode(_, k) => format!("{owner}#suffix{k}"),
        }
    }
}

/// The guard copies of one declaration's `Wf` slot pair
/// (`docs/wf-shape-code-design.md` §2.3).
#[derive(Clone)]
pub(crate) struct WfSlots {
    /// The shape as `lower_instance` writes it: the raw sum-of-Σs.
    pub(crate) shape: Rc<Type>,
    /// The shape as a *decode* of the whole-type code writes it —
    /// `El ⌜S⌝`, the lazy reduct of `El (D#tycode^δ)`
    /// (`reduce.rs`'s `TmWf` rule). A value built at a **respelled expected
    /// type** arrives with this spelling and no other, which is why the guard
    /// takes two copies and not one: with only the inline copy the whole
    /// constructor-value site — the one the measurement put first — declines
    /// silently. Measured: statements did not move at all until this was
    /// added.
    pub(crate) shape_decoded: Rc<Type>,
    /// The arity term, identical under both spellings (`code_of` keeps a
    /// term slot verbatim, and the decode hands it back unchanged).
    pub(crate) arity: Rc<Term>,
    /// The declaration's level, which is also its shape's.
    pub(crate) level: Level,
}

/// The guard copy of one parameterized or value-indexed declaration's code
/// function (`docs/per-instantiation-type-codes-design.md` §2.2): the **open
/// template** the body was quoted from, and the definition's own statement.
///
/// The template is what §4.1 hole-matches an inline instantiation against, and
/// the statement is what a use site walks to build the application spine — its
/// `Π` domains are the arguments' types (dependent in general: a value
/// parameter's type may mention an earlier parameter), so one entry answers
/// both "is this that declaration's lowering" and "what does the spine
/// annotate with".
#[derive(Clone)]
pub(crate) struct TyCodeFn {
    /// `⟦D<El A₁,…>(v̄)⟧` under the definition's own binders.
    pub(crate) template: Rc<Type>,
    /// `Π(A₁ : Ty l₁)…(v_m : T_m). Ty l`, closed.
    pub(crate) stmt: Rc<Type>,
    /// The parameter level profile the definition was registered at — all
    /// `Ty 0` today (§2.1), kept explicit so widening is a data change.
    pub(crate) param_levels: Vec<Level>,
    /// The instantiation's own level.
    pub(crate) level: Level,
}

/// The state of §4.1's positional hole-match: which argument each template
/// hole recovered, and the scoping the subject's own position imposes on it.
///
/// Positional, never a scan, which is `issues/tag-types-collide-with-lowerings.md`
/// answered by construction — a declaration's tag Σ is compared for *equality*
/// against the template's own tag Σ at the position the template puts it, so
/// no payload can be mistaken for a tag digit and no tag digit for a payload.
/// A type parameter and a value parameter may be spelled with the same index
/// at their own depths and are never confused, because they are matched by
/// position in the template and live in different sorts of slot.
struct Holes<'a> {
    /// The registry, for [`Holes::see_through`], and the scratch anchor the
    /// references inside the subject are numbered at
    /// ([`Elaborator::unspell_here_in`]). The anchor is carried rather than
    /// assumed because a reference read at the wrong one names a *different*
    /// definition rather than none.
    el: &'a Elaborator,
    g: u32,
    /// Whether a global's substitution tail counts. The **match**'s two sides
    /// are read in different frames and the tail records a frame's length and
    /// nothing about the constant (see [`Holes::tm`]'s global arm); step 2's
    /// two sides are read in *one* frame and catching a wrongly-framed copy is
    /// that walk's whole job (§3 of
    /// `docs/closed-argument-and-parameter-domain-spelling-design.md`).
    strict: bool,
    /// The subject's context base and length, for [`strengthened_ty`]: a hole
    /// hit `md` binders inside the subject is scoped `md` deeper than the
    /// reference that will carry it.
    base: CtxBase,
    outer: u32,
    /// The definition's whole telescope, and how much of it is type
    /// parameters — the template spells parameter `i` as `Var(total - 1 - i)`
    /// at its own base depth.
    total: u32,
    np: u32,
    /// A type parameter's recovered argument, **as a code** and never as a
    /// `Type` (`docs/telescoped-record-projections-design.md` §2.3). The same
    /// parameter is hit in a type slot (`El (Var i)` against the subject's
    /// `El c`, or against a literal former) and in a term slot (`Var i`
    /// against the subject's `c`, which is what a lowering inherited from
    /// another declaration's spine spells it as), and `Nat` and `El ⌜Nat⌝`
    /// disagree syntactically. Recovering the code makes the two slots one by
    /// construction; the *type* the emission of the argument needs is
    /// `decode_deep (El l c)` and is derived once, in [`Elaborator::instance_match`].
    types: Vec<Option<Rc<Term>>>,
    values: Vec<Option<Rc<Term>>>,
    /// The **first** shape the walk stopped on, as a `template/subject` former
    /// pair, for the decline listing.
    ///
    /// A decline here is silent and looks exactly like a device that fired and
    /// lost (§13.10), and "hole-match" on its own says only that; what a
    /// reader needs is *which former* the matcher does not descend into,
    /// because that is the next line of §2.2's list. Two `&'static str`s and a
    /// write on the first failure — no formatting, no allocation, and nothing
    /// at all unless the listing asked.
    why: Option<(&'static str, &'static str)>,
}

/// The former name of a type, for [`Holes::why`].
fn ty_former(t: &Type) -> &'static str {
    match t {
        Type::Nat => "Nat",
        Type::Ty(_) => "Ty",
        Type::El { .. } => "El",
        Type::Pi { .. } => "Pi",
        Type::Sigma { .. } => "Sigma",
        Type::Sum { .. } => "Sum",
        Type::Unit { .. } => "Unit",
        Type::Empty { .. } => "Empty",
        Type::Vec { .. } => "Vec",
        Type::Wf { .. } => "Wf",
        Type::Id { .. } => "Id",
        Type::SEq { .. } => "SEq",
        _ => "other-ty",
    }
}

/// The former name of a term, for [`Holes::why`].
fn tm_former(t: &Term) -> &'static str {
    match t {
        Term::Var(_) => "Var",
        Term::GlobalTm { .. } => "Global",
        Term::App { .. } => "App",
        Term::Lam { .. } => "Lam",
        Term::Fst { .. } => "Fst",
        Term::Snd { .. } => "Snd",
        Term::Pair { .. } => "Pair",
        Term::Zero | Term::Succ(_) => "Num",
        Term::TmTy(_) => "TmTy",
        Term::TmNat => "TmNat",
        Term::TmPi { .. } => "TmPi",
        Term::TmSigma { .. } => "TmSigma",
        Term::TmSum { .. } => "TmSum",
        Term::TmId { .. } => "TmId",
        Term::TmVec { .. } => "TmVec",
        Term::TmWf { .. } => "TmWf",
        _ => "other-tm",
    }
}

impl Holes<'_> {
    /// The registry's **inline** copy behind `El (D#tycode^δ)` or
    /// `El (app(D#tycode_fn^δ; ā))`, and `None` for everything else — the
    /// recognizer seeing through a *name*
    /// (`docs/closed-argument-and-parameter-domain-spelling-design.md` §3).
    ///
    /// Reached only where the two sides already differ at a node, so the fast
    /// path never pays for it, and what it materializes is the copy step 2 was
    /// going to build anyway. Seeing through a **quote** is not the same
    /// sentence and is not here: §5.2 built it and measured a stack overflow,
    /// because a quote can be a multi-megabyte literal while a reference
    /// unspells to the copy the walk was already comparing.
    fn see_through(&self, ty: &Type) -> Option<Type> {
        self.el.unspell_here_in(ty, self.g)
    }

    /// [`Self::see_through`] at a **code**: the inline copy a code reference
    /// names, quoted again. [`Elaborator::unspell_here_in`] reads the `El`'s
    /// code and never its level, so the level here is scaffolding for that
    /// call and not a claim about the code's sort.
    fn see_through_code(&self, t: &Term) -> Option<Term> {
        let el = Type::El {
            level: Level::Zero,
            tm: Rc::new(t.clone()),
        };
        crate::code::code_of(&self.see_through(&el)?)
    }

    /// Whether two codes recovered for one hole are two spellings of one type,
    /// and which of them to keep.
    ///
    /// The **reference** is kept: that is what the reference carries, what the
    /// emitted argument becomes anyway (`instance_match` re-derives it as
    /// `code_of(emit_ty(decode_deep(El l c)))`, which gives the reference from
    /// either input), and what step 2's copy is then spelled with. When
    /// neither side is a reference the two codes are equal and the choice does
    /// not arise.
    fn agree_as_codes(&self, a: &Rc<Term>, b: &Rc<Term>) -> Option<Rc<Term>> {
        let ia = self.see_through_code(a);
        let ib = self.see_through_code(b);
        (ia.as_ref().unwrap_or(&**a) == ib.as_ref().unwrap_or(&**b))
            .then(|| if ia.is_some() { Rc::clone(a) } else { Rc::clone(b) })
    }

    /// Which parameter, if any, a template variable at walk depth `md` is.
    fn hole(&self, v: u32, md: u32) -> Option<u32> {
        (v >= md && v - md < self.total).then(|| self.total - 1 - (v - md))
    }

    /// Record the first decline and answer `None`, which is what every
    /// caller does with it.
    fn stop(&mut self, t: &'static str, s: &'static str) -> Option<()> {
        if self.why.is_none() {
            self.why = Some((t, s));
        }
        None
    }

    /// Place type parameter `i`'s code, or check it against what an earlier
    /// occurrence placed. One entry point for both slots, which is the whole
    /// content of §2.3.
    fn place_ty(&mut self, i: u32, code: Term) -> Option<()> {
        let code = Rc::new(code);
        if let Some(prev) = &self.types[i as usize] {
            if *prev == code {
                return Some(());
            }
            // A **closed** argument is spelled two ways inside one lowering: a
            // binder's type is a structural read and keeps the inline
            // lowering, while the same type as an application's type argument
            // went through the emission chokepoint and is a reference (§2 of
            // `docs/closed-argument-and-parameter-domain-spelling-design.md`).
            // Two codes for one hole agree when their inline copies do.
            if let Some(keep) = self.agree_as_codes(prev, &code) {
                self.types[i as usize] = Some(keep);
                return Some(());
            }
            return self.stop("type-hole", "two-occurrences-disagree");
        }
        self.types[i as usize] = Some(code);
        Some(())
    }

    /// `template` against `subject`, both `md` binders inside their own
    /// scopes. Every occurrence of a hole must agree, and everything outside
    /// a hole must be syntactically identical, levels included.
    fn ty(&mut self, template: &Type, subject: &Type, md: u32) -> Option<()> {
        if let Type::El { tm, .. } = template
            && let Term::Var(LocalVar(v)) = &**tm
            && let Some(i) = self.hole(*v, md)
            && i < self.np
        {
            let Some(here) = strengthened_ty(subject, self.base, self.outer, md) else {
                return self.stop("hole", "escapes-binder");
            };
            let Some(code) = crate::code::code_of(&here) else {
                return self.stop("hole", "not-quotable");
            };
            return self.place_ty(i, code);
        }
        match (template, subject) {
            (
                Type::Sum { lhs: a1, rhs: b1, lhs_level: l1, rhs_level: r1 },
                Type::Sum { lhs: a2, rhs: b2, lhs_level: l2, rhs_level: r2 },
            ) => {
                (l1 == l2 && r1 == r2).then_some(())?;
                self.ty(a1, a2, md)?;
                self.ty(b1, b2, md)
            }
            (
                Type::Sigma { fst: a1, snd: b1, fst_level: l1, snd_level: r1 },
                Type::Sigma { fst: a2, snd: b2, fst_level: l2, snd_level: r2 },
            ) => {
                (l1 == l2 && r1 == r2).then_some(())?;
                self.ty(a1, a2, md)?;
                self.ty(b1, b2, md + 1)
            }
            (
                Type::Pi { dom: a1, cod: b1, dom_level: l1, cod_level: r1 },
                Type::Pi { dom: a2, cod: b2, dom_level: l2, cod_level: r2 },
            ) => {
                (l1 == l2 && r1 == r2).then_some(())?;
                self.ty(a1, a2, md)?;
                self.ty(b1, b2, md + 1)
            }
            (
                Type::Wf { shape: s1, arity: _, level: v1 },
                Type::Wf { shape: s2, arity: _, level: v2 },
            ) => {
                // The arity is a term under the shape's binder and a function
                // of the shape; the re-lowering derives it, so declining to
                // descend costs nothing and matching it would be a second
                // syntax to keep in step (§4.1).
                (v1 == v2).then_some(())?;
                self.ty(s1, s2, md)
            }
            (
                Type::Vec { elem: e1, len: n1, level: v1 },
                Type::Vec { elem: e2, len: n2, level: v2 },
            ) => {
                (v1 == v2).then_some(())?;
                self.tm(n1, n2, md)?;
                self.ty(e1, e2, md)
            }
            (
                Type::Id { ty: t1, lhs: a1, rhs: b1, level: v1 },
                Type::Id { ty: t2, lhs: a2, rhs: b2, level: v2 },
            )
            | (
                Type::SEq { ty: t1, lhs: a1, rhs: b1, level: v1 },
                Type::SEq { ty: t2, lhs: a2, rhs: b2, level: v2 },
            ) if std::mem::discriminant(template) == std::mem::discriminant(subject) => {
                (v1 == v2).then_some(())?;
                self.ty(t1, t2, md)?;
                self.tm(a1, a2, md)?;
                self.tm(b1, b2, md)
            }
            (Type::El { tm: c1, level: v1 }, Type::El { tm: c2, level: v2 }) => {
                (v1 == v2).then_some(())?;
                self.tm(c1, c2, md)
            }
            (a, b) => {
                if a == b {
                    return Some(());
                }
                // The former-mismatch arm, and the only place §3's relation is
                // consulted: the subject first, then the template. Every arm
                // above is untouched, so nothing that matches today matches
                // differently. `hole-match-Wf/El`, `Sigma/El` and `Sum/El` are
                // one relation seen at three formers and leave together (§3.1).
                if let Some(seen) = self.see_through(b) {
                    return self.ty(a, &seen, md);
                }
                if let Some(seen) = self.see_through(a) {
                    return self.ty(&seen, b, md);
                }
                self.stop(ty_former(a), ty_former(b))
            }
        }
    }

    /// A **term** slot of the template: a parameter's hole, the two formers a
    /// parameter hides behind, a closed global, or syntax that must match
    /// exactly.
    ///
    /// The matcher may be as incomplete as convenient and can never be wrong
    /// — [`Elaborator::instance_match`]'s step 2 requires the template *at the
    /// recovered arguments* to be the subject syntactically — so each arm
    /// below is a decline turned into a match and never an answer that has to
    /// be argued for. What is *not* free is leaving one out: the decline is
    /// today's inline spelling, and a device that names some declarations and
    /// not others is a regression rather than a small win
    /// (`docs/telescoped-record-projections-design.md` §2.4).
    fn tm(&mut self, template: &Term, subject: &Term, md: u32) -> Option<()> {
        if let Term::Var(LocalVar(v)) = template
            && let Some(i) = self.hole(*v, md)
        {
            let Some(here) = strengthened_tm(subject, self.base, self.outer, md) else {
                return self.stop("hole", "escapes-binder");
            };
            let here = Rc::new(here);
            // A **type** parameter met in a term slot: its code (§2.3). The
            // template spells `T` as `El (Var i)` where a type stands and as
            // the bare `Var i` — its code — inside the `app(list_len; …)` and
            // `app(Le; …)` spines it inherits from another declaration, and
            // the subject carries the argument's code there.
            if i < self.np {
                return self.place_ty(i, (*here).clone());
            }
            let slot = (i - self.np) as usize;
            if let Some(prev) = &self.values[slot] {
                if *prev == here {
                    return Some(());
                }
                return self.stop("value-hole", "two-occurrences-disagree");
            }
            self.values[slot] = Some(here);
            return Some(());
        }
        match (template, subject) {
            // A **closed** global — a `GlobalTm` substituting nothing — is
            // the same constant in two frames, and its `·^k` tail records the
            // length of the frame and nothing about the constant. The
            // template's is the telescope's (`·^{|Θ|+md}`) and the subject's
            // is the use site's (`·^{outer+md}`), so comparing them
            // syntactically is comparing the two contexts' lengths, which is
            // never what the match is about: every declaration whose lowering
            // mentions a global declined at every use site but the identity
            // spine (§2.1, the tail half). The index is the whole content, and
            // [`instance_of_template`]'s composition then writes the frame's
            // own tail into the copy step 2 compares.
            (
                Term::GlobalTm { var: v1, subst: s1 },
                Term::GlobalTm { var: v2, subst: s2 },
            ) if s1.terms.is_empty()
                && s2.terms.is_empty()
                && matches!(s1.tail, SubstTail::Empty { .. })
                && matches!(s2.tail, SubstTail::Empty { .. }) =>
            {
                // …except in step 2's walk, whose two sides are in one frame
                // and whose whole job is to catch a wrongly-framed copy (§3).
                (v1 == v2 && (!self.strict || s1.tail == s2.tail)).then_some(())
            }
            // §2.2: the two formers a parameter hides behind in every
            // declaration of `lib/std` and `lib/std/parser`. `Certified`'s
            // `begin` occurs only as `begin.offset` and its `relation` only
            // applied; `Exists`'s `P` only as `P(witness)`. Neither is ever
            // bare, so without these arms neither is ever placed. Each
            // further former would be another decline, never a wrong answer,
            // so the set stays the measured one.
            (
                Term::App {
                    fun: f1,
                    dom_level: dl1,
                    cod_level: cl1,
                    dom: d1,
                    cod: c1,
                    arg: a1,
                },
                Term::App {
                    fun: f2,
                    dom_level: dl2,
                    cod_level: cl2,
                    dom: d2,
                    cod: c2,
                    arg: a2,
                },
            ) => {
                (dl1 == dl2 && cl1 == cl2).then_some(())?;
                self.tm(f1, f2, md)?;
                self.ty(d1, d2, md)?;
                // The codomain binds the argument.
                self.ty(c1, c2, md + 1)?;
                self.tm(a1, a2, md)
            }
            (
                Term::Fst {
                    fst_level: fl1,
                    snd_level: sl1,
                    fst_ty: f1,
                    snd_ty: s1,
                    pair: p1,
                },
                Term::Fst {
                    fst_level: fl2,
                    snd_level: sl2,
                    fst_ty: f2,
                    snd_ty: s2,
                    pair: p2,
                },
            )
            | (
                Term::Snd {
                    fst_level: fl1,
                    snd_level: sl1,
                    fst_ty: f1,
                    snd_ty: s1,
                    pair: p1,
                },
                Term::Snd {
                    fst_level: fl2,
                    snd_level: sl2,
                    fst_ty: f2,
                    snd_ty: s2,
                    pair: p2,
                },
            ) if std::mem::discriminant(template) == std::mem::discriminant(subject) => {
                (fl1 == fl2 && sl1 == sl2).then_some(())?;
                self.ty(f1, f2, md)?;
                // The Σ's tail binds the first component.
                self.ty(s1, s2, md + 1)?;
                self.tm(p1, p2, md)
            }
            (a, b) => {
                if a == b {
                    return Some(());
                }
                // §3 at the code layer: the same component, quoted. A type
                // argument that went through the chokepoint is `D#tycode^δ`
                // where the binder-type occurrence's code is `TmSum(…)`.
                if let Some(seen) = self.see_through_code(b) {
                    return self.tm(a, &seen, md);
                }
                if let Some(seen) = self.see_through_code(a) {
                    return self.tm(&seen, b, md);
                }
                self.stop(tm_former(a), tm_former(b))
            }
        }
    }
}

/// `t`, scoped in a context of `m + d` binders, as it is scoped in the first
/// `m` alone; `None` when it mentions any of the innermost `d`.
///
/// [`crate::unification::strengthen_ty`]'s trick, keyed by the context's
/// *length* rather than the context itself: the emission walk that produced
/// `d` crosses binders without carrying their types, and the substitution
/// only ever reads the length and the base.
fn strengthened_ty(t: &Type, base: CtxBase, m: u32, d: u32) -> Option<Type> {
    if d == 0 {
        return Some(t.clone());
    }
    let s = t.apply_local(&drop_innermost(base, m, d));
    (s.shift_local(d) == *t).then_some(s)
}

/// [`strengthened_ty`] for a term.
fn strengthened_tm(t: &Term, base: CtxBase, m: u32, d: u32) -> Option<Term> {
    if d == 0 {
        return Some(t.clone());
    }
    let s = t.apply_local(&drop_innermost(base, m, d));
    (s.shift_local(d) == *t).then_some(s)
}

fn drop_innermost(base: CtxBase, m: u32, d: u32) -> LocalSubst {
    let tail = match base {
        CtxBase::Nil => SubstTail::Empty {
            len: m,
            base: CtxBase::Nil,
        },
        CtxBase::Var(g) => SubstTail::Wk { len: m, ctx_var: g },
    };
    let terms = (0..m)
        .map(|k| Rc::new(Term::Var(LocalVar(m - 1 - k))))
        .chain((0..d).map(|_| Rc::new(Term::Zero)))
        .collect();
    LocalSubst { tail, terms }
}

/// The identity substitution of `cx` extended by `d` binders — the
/// β-substitution [`Elaborator::gen_spine`] needs to walk a dependent
/// telescope at the depth the subject sits at.
fn id_subst_at(cx: &Cx, d: u32) -> LocalSubst {
    let m = cx.gamma.entries.len() as u32 + d;
    let tail = match cx.gamma.base {
        CtxBase::Nil => SubstTail::Empty {
            len: m,
            base: CtxBase::Nil,
        },
        CtxBase::Var(g) => SubstTail::Wk { len: m, ctx_var: g },
    };
    LocalSubst {
        tail,
        terms: (0..m)
            .map(|k| Rc::new(Term::Var(LocalVar(m - 1 - k))))
            .collect(),
    }
}

/// A closed definition statement weakened into `cx` plus `d` binders.
fn weakened(stmt: &Type, cx: &Cx, d: u32) -> Type {
    // [`weaken`]'s substitution and not `shift_local`, and the difference is a
    // kernel rejection rather than a spelling: a closed statement's globals
    // carry `·^0_·`, and `shift_local` moves the *length* while keeping the
    // stored base, so read into a frame that ends in a context variable the
    // annotations `gen_spine` writes say `·^k_·` where everything around them
    // says `·^k_g` — `SubstMismatch`, not a decline. The composition rewrites
    // both.
    weaken_at(stmt, cx, d)
}

/// [`weaken`] for a slot sitting `d` binders past `cx`.
fn weaken_at(ty: &Type, cx: &Cx, d: u32) -> Type {
    ty.apply_local(&LocalSubst {
        tail: frame_tail(cx, d),
        terms: vec![],
    })
}

/// The tail a substitution **out of** a closed context into `cx` plus `d`
/// binders carries: that frame's own length and base. `Empty` and not `Wk`
/// even at a context-variable base, because the source it targets is the
/// empty context (ch. 02's `·^k_{g?}`) — `Wk` is for the identity, where the
/// context variable maps to itself ([`id_subst_at`]).
fn frame_tail(cx: &Cx, d: u32) -> SubstTail {
    SubstTail::Empty {
        len: cx.gamma.entries.len() as u32 + d,
        base: cx.gamma.base,
    }
}

/// How many arguments a code function's statement takes.
fn pi_arity(stmt: &Type) -> usize {
    let mut n = 0;
    let mut cur = stmt;
    while let Type::Pi { cod, .. } = cur {
        n += 1;
        cur = cod;
    }
    n
}

/// The template at `args` — the inline lowering behind a saturated
/// `app(D#tycode_fn^δ; ā)` (`docs/per-instantiation-type-codes-design.md`
/// §4.2). Substituting the arguments for the definition's own binders puts a
/// **code** where the template has `El (Var i)`, which is the kernel's own
/// decode spelling; `decode_deep` is what turns that back into the identity
/// every structural reader anchors on.
///
/// `frame` is the substitution's **source**: the length and base of the
/// context `args` are scoped in. It is not optional and it is not the
/// telescope's own length. The template is scoped in `Θ`, and its globals
/// carry `Θ`'s tail (`u^{·^{|Θ|+d}}`); the composition rewrites every one of
/// them to the frame's, so a template read at a use site whose context is a
/// different length comes out spelled the way the subject there is. With
/// `·^{|Θ|}` hard-coded, §4.1's identity step compared two frames and
/// declined at every use site but the identity spine — and, once §2.1's
/// rescoping made the *indices* agree, handed a wrongly-tailed term to the
/// kernel instead (`docs/telescoped-record-projections-design.md` §2.1,
/// amended 2026-09-15).
fn instance_of_template(entry: &TyCodeFn, args: &[Rc<Term>], frame: SubstTail) -> Type {
    let subst = LocalSubst {
        tail: frame,
        terms: args.to_vec(),
    };
    let at = entry.template.apply_local(&subst);
    crate::inductive::decode_deep(&at).unwrap_or(at)
}

/// The frame a `app(D#…^δ; ā)` spine is scoped in, read off its head's own
/// substitution tail.
///
/// A generated definition is closed, so [`Elaborator::gen_ref_deeper`] writes
/// the ambient `Γ`'s length and base there and nowhere else. That is exactly
/// what [`instance_of_template`] needs, and reading it here is what lets the
/// **inverse** ([`Elaborator::unspell_here`], [`Elaborator::unspell_ty_deep`])
/// be frame-correct without every caller of it having to hand one over — those
/// two are reached from goals, motives and structural reads that know their Ψ
/// anchor and not their `Γ`.
fn spine_frame(t: &Term) -> Option<SubstTail> {
    let mut cur = t;
    while let Term::App { fun, .. } = cur {
        cur = fun;
    }
    match cur {
        Term::GlobalTm { subst, .. } => Some(subst.tail),
        _ => None,
    }
}

/// The guard copies of one non-recursive declaration's spine codes
/// ([`GenDef::PayloadCode`]/[`GenDef::SuffixCode`]): the **inline** spine
/// the codes were minted from, exactly as `Elaborator::spine` reads it off
/// the registered lowering, so a reference can only ever stand for the
/// component it decodes to — the same structural guard as [`WfSlots`] and
/// [`GenDefLayer::ty_code`], at the spine's granularity.
#[derive(Clone)]
pub(crate) struct SpineCodes {
    /// `(⟦cₖ⟧, lₖ)` per constructor.
    pub(crate) ctors: Vec<(Rc<Type>, Level)>,
    /// `(R_{k+1}, its level)` per `+`; `tails[n-2]` is `ctors[n-1]`.
    pub(crate) tails: Vec<(Rc<Type>, Level)>,
}

/// One append-only generated-definition delta. Its lookup views are sealed
/// together at the semantic-image boundary.
#[derive(Clone, Default)]
struct GenDefLayer {
    /// Key → absolute Ψ index (the `GlobalInfo::abs` convention).
    by_key: HashMap<GenDef, u32>,
    /// Absolute Ψ index → key. The recognizers' half.
    by_abs: HashMap<u32, GenDef>,
    /// Per route-1 declaration tag with a registered [`GenDef::Fam`], the two
    /// levels an occurrence needs to spell `El l (D#fam^δ i)`: the family's
    /// own level `l` and the index type's `l_I`. They are a property of the
    /// declaration, not of the use site — which holds only because the
    /// definition exists solely for an unparameterized declaration, where the
    /// two-pass level computation has one answer forever (design §5).
    fam_lvl: HashMap<u32, (Level, Level)>,
    /// Per declaration tag with a registered [`GenDef::TyCode`], the
    /// **inline** `⟦D⟧` the code was minted from and its level.
    ///
    /// The inline copy is not a convenience: it is the use-site *guard*.
    /// [`Elaborator::closed_type_ref`] hands out the reference only when the type
    /// in front of it is structurally that exact lowering, so a reference can
    /// never stand for a type it does not decode to — the tag alone would be
    /// a nominal claim about a type the emission site read from somewhere
    /// else. (Tags are unique per declaration and codes are minted only for
    /// unparameterized declarations, so this can only ever *decline*; it costs
    /// one structural comparison per `match` and buys the property outright.)
    ty_code: HashMap<u32, (Rc<Type>, Level)>,
    /// Per declaration tag with a registered [`GenDef::TyCodeFn`], the open
    /// template and statement the definition was minted from
    /// ([`TyCodeFn`]) — the use-site guard, exactly as
    /// [`GenDefLayer::ty_code`]'s inline copy is, with the hole-matching and
    /// re-lowering of `docs/per-instantiation-type-codes-design.md` §4.1 in
    /// place of one structural comparison.
    ty_code_fn: HashMap<u32, TyCodeFn>,
    /// Per declaration tag with a registered [`GenDef::ShapeCode`] **and**
    /// [`GenDef::ArityFn`], the **inline** `Wf` slot pair the two were minted
    /// from and the declaration's level.
    ///
    /// The pair is the use-site guard, exactly as [`GenDefs::ty_code`]'s copy
    /// is: [`Elaborator::wf_slot_refs`] hands out the references only when the
    /// slots in front of it are structurally *those* slots, so a reference can
    /// never stand for a shape it does not decode to. Both entries are written
    /// together or not at all — a spelled shape with an inline arity would be
    /// correct but is never useful, and the pairing is what lets every use
    /// site ask one question (design §2.3).
    wf_slots: HashMap<u32, WfSlots>,
    /// Per non-recursive declaration tag whose whole spine registered
    /// ([`Elaborator::register_spine_codes`]), the inline spine the codes
    /// were minted from — the use-site guard, written all-or-nothing.
    spine_codes: HashMap<u32, SpineCodes>,
}

/// The registry: immutable image layers plus one suffix delta. The two
/// directions remain in the same layer and are kept in step by
/// [`Elaborator::push_gen_def`].
#[derive(Clone, Default)]
pub(crate) struct GenDefs {
    sealed: Rc<Vec<Rc<GenDefLayer>>>,
    current: Rc<GenDefLayer>,
}

impl GenDefs {
    pub(crate) fn semantic_snapshot(&self) -> Self {
        let mut defs = self.clone();
        if !defs.current.by_key.is_empty() {
            Rc::make_mut(&mut defs.sealed).push(Rc::clone(&defs.current));
            defs.current = Rc::new(GenDefLayer::default());
        }
        defs
    }

    fn layers(&self) -> impl Iterator<Item = &GenDefLayer> {
        std::iter::once(self.current.as_ref()).chain(self.sealed.iter().rev().map(Rc::as_ref))
    }

    fn contains_key(&self, key: &GenDef) -> bool {
        self.layers().any(|layer| layer.by_key.contains_key(key))
    }

    pub(crate) fn abs_for(&self, key: &GenDef) -> Option<&u32> {
        self.layers().find_map(|layer| layer.by_key.get(key))
    }

    fn key_for_abs(&self, abs: &u32) -> Option<&GenDef> {
        self.layers().find_map(|layer| layer.by_abs.get(abs))
    }

    fn fam_levels(&self, tag: &u32) -> Option<&(Level, Level)> {
        self.layers().find_map(|layer| layer.fam_lvl.get(tag))
    }

    fn ty_code(&self, tag: &u32) -> Option<&(Rc<Type>, Level)> {
        self.layers().find_map(|layer| layer.ty_code.get(tag))
    }

    fn has_ty_codes(&self) -> bool {
        self.layers().any(|layer| !layer.ty_code.is_empty())
    }

    fn ty_code_fn(&self, tag: &u32) -> Option<&TyCodeFn> {
        self.layers().find_map(|layer| layer.ty_code_fn.get(tag))
    }

    fn has_ty_code_fns(&self) -> bool {
        self.layers().any(|layer| !layer.ty_code_fn.is_empty())
    }

    pub(crate) fn has_ty_code_fn(&self, tag: u32) -> bool {
        self.ty_code_fn(&tag).is_some()
    }

    pub(crate) fn insert_ty_code_fn(&mut self, tag: u32, value: TyCodeFn) {
        Rc::make_mut(&mut self.current).ty_code_fn.insert(tag, value);
    }

    fn wf_slots(&self, tag: &u32) -> Option<&WfSlots> {
        self.layers().find_map(|layer| layer.wf_slots.get(tag))
    }

    pub(crate) fn has_binding(&self, key: &GenDef, abs: u32) -> bool {
        self.contains_key(key) || self.key_for_abs(&abs).is_some()
    }

    pub(crate) fn has_ty_code(&self, tag: u32) -> bool {
        self.ty_code(&tag).is_some()
    }

    pub(crate) fn has_wf_slot_entry(&self, tag: u32) -> bool {
        self.wf_slots(&tag).is_some()
    }

    pub(crate) fn has_fam_level_entry(&self, tag: u32) -> bool {
        self.fam_levels(&tag).is_some()
    }

    fn has_wf_slots(&self) -> bool {
        self.layers().any(|layer| !layer.wf_slots.is_empty())
    }

    fn spine_codes(&self, tag: &u32) -> Option<&SpineCodes> {
        self.layers().find_map(|layer| layer.spine_codes.get(tag))
    }

    fn has_spine_codes(&self) -> bool {
        self.layers().any(|layer| !layer.spine_codes.is_empty())
    }

    pub(crate) fn has_spine_code_entry(&self, tag: u32) -> bool {
        self.spine_codes(&tag).is_some()
    }

    pub(crate) fn insert_spine_codes(&mut self, tag: u32, value: SpineCodes) {
        Rc::make_mut(&mut self.current).spine_codes.insert(tag, value);
    }

    pub(crate) fn insert_ty_code(&mut self, tag: u32, value: (Rc<Type>, Level)) {
        Rc::make_mut(&mut self.current).ty_code.insert(tag, value);
    }

    pub(crate) fn insert_wf_slots(&mut self, tag: u32, value: WfSlots) {
        Rc::make_mut(&mut self.current).wf_slots.insert(tag, value);
    }

    pub(crate) fn insert_fam_levels(&mut self, tag: u32, value: (Level, Level)) {
        Rc::make_mut(&mut self.current).fam_lvl.insert(tag, value);
    }

    pub(crate) fn insert_binding(&mut self, key: GenDef, abs: u32) {
        let layer = Rc::make_mut(&mut self.current);
        layer.by_key.insert(key, abs);
        layer.by_abs.insert(abs, key);
    }

    #[cfg(test)]
    pub(crate) fn shares_sealed_with(&self, other: &Self) -> bool {
        Rc::ptr_eq(&self.sealed, &other.sealed)
    }
}

impl Elaborator {
    // -- registration -------------------------------------------------------

    /// Register everything `ind` owes, at its declaration. Errors are
    /// swallowed by design (see the module header): the emission sites all
    /// fall back to inlining.
    pub(crate) fn register_gen_defs(&mut self, ind: &Rc<Inductive>, span: Span) {
        if ind.skel.is_none() {
            // Route 1 (design §6): the family function, and the index type's
            // code for the `Π`'s domain. The index type's *devices* are route
            // 2b's inversion machinery and route 1 emits none of them, so
            // they are not registered here.
            if ind.index.is_some() {
                if let Some(IdxTy::Decl(iind)) = ind.index_ty.as_ref() {
                    let iind = Rc::clone(iind);
                    self.register_idx_code(&iind, span);
                }
                self.register_fam(ind, span);
                return;
            }
            // Unindexed, tier 1 or tier 0: the declaration's own lowered type
            // gets a code, so that the `match` lowerings can *name* `⟦D⟧`
            // instead of writing it out ~21 times per arm
            // ([[wf-field-conversion-cost]], design §10).
            self.register_ty_code(ind, span);
            // …and, for exactly the declarations that one returns from, the
            // code *function* over the declaration's own telescope
            // (`docs/per-instantiation-type-codes-design.md` §2).
            self.register_ty_code_fn(ind, span);
            // …and a record's fields get their projections, which is the one
            // device here that a *user-written* term reaches directly.
            self.register_rec_projs(ind, span);
            return;
        }
        // The index type's devices first: they are closed for every family,
        // and shared across all families over the same index. The **code**
        // comes before the rest so that a later device's statement may
        // reference it (Ψ is a telescope — design §1.4, retro-spelling
        // deferred but the order is kept ready for it).
        if let Some(IdxTy::Decl(iind)) = ind.index_ty.as_ref() {
            let iind = Rc::clone(iind);
            self.register_idx_code(&iind, span);
            self.register_index_devices(&iind, span);
        }
        // The skeleton's code before `μ`, for the same telescope reason.
        self.register_skel_code(ind, span);
        let _ = self.register_mu(ind, span);
    }

    /// `I#icode := ⌜⟦I⟧⌝`, the index type's code (design §1.1). Best-effort:
    /// a `None` from `code_of` or a gate failure skips registration and every
    /// occurrence stays inline, exactly as before.
    fn register_idx_code(&mut self, iind: &Rc<Inductive>, span: Span) {
        let key = GenDef::IdxCode(iind.tag);
        if self.types.gdefs().contains_key(&key) {
            return;
        }
        let cx = Cx::empty();
        let Ok((ity, ilvl)) = self.lower_instance(&cx, iind, &[], &[], span) else {
            return;
        };
        let Some(body) = crate::code::code_of(&ity) else {
            return;
        };
        let ty = Type::Ty(ilvl.clone());
        // A term of type `Ty l` lives at `1 + l` (the Tarski formation rule).
        let _ = self.push_gen_def(key, &iind.name, ty, Level::succ(ilvl), body, span);
    }

    /// `D#code := ⌜⟦Skel⟧⌝`, the forded declaration's skeleton code (design
    /// §1.1). Only an **unparameterized** declaration gets one — the same
    /// boundary as [`Elaborator::mu_def`], because `⟦Skel⟧` of a parameterized
    /// family is monomorphized per instantiation and a definition must be
    /// closed at declaration time (§14.12).
    fn register_skel_code(&mut self, ind: &Rc<Inductive>, span: Span) {
        if !ind.params.is_empty() || !ind.valparams.is_empty() {
            return;
        }
        let key = GenDef::SkelCode(ind.tag);
        if self.types.gdefs().contains_key(&key) {
            return;
        }
        let Some(skel) = ind.skel.as_ref() else {
            return;
        };
        let cx = Cx::empty();
        let Ok((skel_ty, l)) = self.lower_instance(&cx, skel, &[], &[], span) else {
            return;
        };
        let Some(body) = crate::code::code_of(&skel_ty) else {
            return;
        };
        let ty = Type::Ty(l.clone());
        let _ = self.push_gen_def(key, &ind.name, ty, Level::succ(l), body, span);
    }

    /// `D#tycode := ⌜⟦D⟧⌝`, a declaration's own whole lowered type
    /// (design §1.1, §10.2 — the 2026-08-12 extension). Best-effort like every
    /// other piece here: no code means every occurrence stays inline, exactly
    /// as before.
    ///
    /// **Boundary — two conditions, each for its own reason.**
    ///
    /// - *Unparameterized* ([`Elaborator::mu_def`]'s reason, §14.12): `⟦D⟧` of
    ///   a parameterized declaration is monomorphized per instantiation
    ///   (`Cx::tyvars`), so it is not one closed type but one per
    ///   instantiation, and a definition is registered where the
    ///   instantiations are not yet known.
    /// - *Unindexed*: an indexed family's use-site type mentions the index, so
    ///   there is no single type to name (that is route 1's
    ///   [`GenDef::Fam`], which names the *function*). This function is
    ///   reached only off `register_gen_defs`'s unindexed branch.
    ///
    /// A **non-recursive** declaration gets one too, and that is deliberate
    /// rather than incidental: its lowering is a bare sum-of-Σs, which is
    /// exactly as large as a `Wf`'s and grows by the same quadratic law, and
    /// it is very often the *motive* of a `match` on something else
    /// (`cert_body : Ir -> CertOut` — the container is recursive, the answer
    /// is not). Restricting to recursive declarations left the single largest
    /// occurrence site in the round's own fixture untouched; measured.
    fn register_ty_code(&mut self, ind: &Rc<Inductive>, span: Span) {
        if !ind.params.is_empty() || !ind.valparams.is_empty() {
            return;
        }
        let key = GenDef::TyCode(ind.tag);
        if self.types.gdefs().contains_key(&key) {
            return;
        }
        let cx = Cx::empty();
        let Ok((d_ty, l)) = self.lower_instance(&cx, ind, &[], &[], span) else {
            return;
        };
        // The recognizer's own precondition, checked here rather than assumed:
        // `respell_ty` finds this code by running `tag_of` over a type and
        // looking the answer up, so a lowering `tag_of` does not route back to
        // *this* declaration must not be registered — the reference would be
        // unreachable at best and, if some other declaration's `tag_of` landed
        // here, wrong. (`tag_of` also rejects the shapes with no tag at all,
        // which is the same set this used to exclude by hand.)
        if self.tag_of(&d_ty).map(|i| i.tag) != Some(ind.tag) {
            return;
        }
        let Some(inline_body) = crate::code::code_of(&d_ty) else {
            return;
        };
        // A flat declaration names its spine *first*, and its whole-type code
        // is then spelled over those names rather than as the inline literal
        // (`issues/inductive-spelling-codes-nonrecursive.md`): `El (D#tycode^δ)`
        // meets the injection spellings at every constructor label the
        // kernel checks, and with the literal body that comparison decoded
        // and walked the whole sum-of-Σs in the value domain, once per
        // label — measured as the largest single bucket of the five-node
        // FunctionIR/x86 module. With the named body, one δ exposes the same
        // `Sum(El (D#payload₀^δ), El (D#suffix₀^δ))` the label carries.
        // The guard copy is the inline lowering either way.
        let body = if ind.recursive {
            inline_body
        } else {
            self.register_spine_codes(ind, &d_ty, &l, span)
                .unwrap_or(inline_body)
        };
        let ty = Type::Ty(l.clone());
        if self
            .push_gen_def(key, &ind.name, ty, Level::succ(l.clone()), body, span)
            .is_ok()
        {
            self.semantic_commit_gen_ty_code(ind.tag, Rc::new(d_ty.clone()), l.clone());
        }
        self.register_wf_slots(ind, &d_ty, &l, span);
    }

    /// `D#tycode_fn := λ(A₁ : Ty 0)…(v_m : T_m). ⌜⟦D<El A₁,…>(v̄)⟧⌝`, a
    /// **parameterized or value-indexed** declaration's lowering abstracted
    /// over its own telescope (`docs/per-instantiation-type-codes-design.md`
    /// §2). The complement of [`Self::register_ty_code`]'s boundary: reached
    /// off the same unindexed branch, for exactly the declarations that one
    /// returns from.
    ///
    /// Registration is at the **all-parameters-`Ty 0`** profile (§2.1) — the
    /// elaborator mints no level variables, so one closed λ fixes one
    /// profile, and a higher-level instantiation declines at §4.1's guard and
    /// keeps today's inline spelling. Best-effort like every other `GenDef`.
    fn register_ty_code_fn(&mut self, ind: &Rc<Inductive>, span: Span) {
        if ind.params.is_empty() && ind.valparams.is_empty() {
            return;
        }
        let key = GenDef::TyCodeFn(ind.tag);
        if self.types.gdefs().contains_key(&key) {
            return;
        }
        let Some((cx, binders, targs, vargs)) = self.tycode_fn_telescope(ind, span) else {
            return;
        };
        let Ok((template, l)) = self.lower_instance(&cx, ind, &targs, &vargs, span) else {
            return;
        };
        // `register_ty_code`'s precondition, for the same reason (§2.2): the
        // guard finds this entry by running `tag_of` over an instantiation, so
        // a template whose own tag read does not route back here must not be
        // registered.
        if self.tag_of(&template).map(|i| i.tag) != Some(ind.tag) {
            return;
        }
        // Quote the spelling the emission chokepoint would emit — registered
        // sub-lowerings as references — not the raw inline lowering: what the
        // kernel decodes from behind the reference then matches, component
        // for component, the annotation `project_field`'s walk writes, and
        // the `Fst`/`Snd` rule's check of that annotation against the
        // receiver's reference stops paying a δ per component
        // (`docs/record-projection-reference-design.md` §9.8). The stored
        // `template` stays inline: §4's inverse re-lowers against it.
        let quoted = self.annotation_type(&cx, &template, 0);
        let Some(code) = crate::code::code_of(&quoted) else {
            return;
        };
        let mut ty = Type::Ty(l.clone());
        let mut ty_level = Level::succ(l.clone());
        let mut body = code;
        // The statement's domains — which are also the `App.dom` annotations
        // `gen_spine` writes at every use site — take the emission spelling
        // ([`Self::emitted_tel`]). The λ's domains must be the same terms, so
        // both loops read this one list.
        let binders = self.emitted_tel(&binders);
        for (dom, dom_level) in binders.iter().rev() {
            body = Term::Lam {
                dom_level: dom_level.clone(),
                cod_level: ty_level.clone(),
                dom: Rc::new(dom.clone()),
                body: Rc::new(body),
            };
            ty = Type::Pi {
                dom_level: dom_level.clone(),
                cod_level: ty_level.clone(),
                dom: Rc::new(dom.clone()),
                cod: Rc::new(ty),
            };
            ty_level = Level::max(dom_level.clone(), ty_level).normalize().canonical();
        }
        if self
            .push_gen_def(key, &ind.name, ty.clone(), ty_level, body, span)
            .is_ok()
        {
            self.semantic_commit_gen_ty_code_fn(
                ind.tag,
                TyCodeFn {
                    template: Rc::new(template),
                    stmt: Rc::new(ty),
                    param_levels: targs.iter().map(|(_, l)| l.clone()).collect(),
                    level: l,
                },
            );
        }
    }

    /// A declaration's telescope with every domain in the **emission**
    /// spelling (`docs/annotation-component-respell-design.md` §2.5/§2.6).
    ///
    /// A `Π` domain is an annotation slot like any other, and this one is
    /// written into more `App` nodes than most: [`Self::gen_spine`] reads it
    /// off `TyCodeFn::stmt` for every argument of a code-function spine, and
    /// [`saturate`] reads it off `D#projⱼ`'s statement for every field read at
    /// an instantiation. Left inline it meets, at each of them, the
    /// *reference* the argument's own type carries — which is the `El(?)`
    /// against `Wf` row `docs/telescoped-record-projections-design.md` §3.2
    /// predicted and the emission walker reports as `App.dom`/`App.cod` on a
    /// telescoped record's field read. So it takes the chokepoint, and the two
    /// sides are one term instead of a conversion.
    ///
    /// Each domain is scoped under the ones before it, so the context grows
    /// with the walk; the names are the walk's own, since emission reads
    /// nothing but `Γ`'s length and base.
    ///
    /// **Only the domains.** `tycode_fn_telescope`'s own `cx`, `targs` and
    /// `vargs` stay structural: they are what [`Self::lower_instance`] builds
    /// the **template** from, and the template is the inline identity §4's
    /// inverse re-lowers against (`register_ty_code_fn` quotes the emitted
    /// copy for the *body* and stores the inline one).
    fn emitted_tel(&self, binders: &[(Type, Level)]) -> Vec<(Type, Level)> {
        let mut cx = Cx::empty();
        let mut out = Vec::with_capacity(binders.len());
        for (i, (dom, level)) in binders.iter().enumerate() {
            out.push((self.annotation_type(&cx, dom, 0), level.clone()));
            cx.push(format!("#t{i}"), dom.clone(), level.clone());
        }
        out
    }

    /// The code function's own telescope: the context its body is built in,
    /// each binder's `(dom, dom_level)` **scoped under the binders before it**
    /// (which is what a `Π` domain is), and the argument lists that lower the
    /// open template in the full context.
    ///
    /// The type parameters install the `Cx::tyvars` entry a `(A : Type<l>)`
    /// binder already installs (`expr.rs`'s `extend_lambda_context`); the
    /// value parameters install the binder *and* the alias, so that a later
    /// value parameter's declared type reads the earlier ones by name exactly
    /// as [`Elaborator::valparam_args`] lets a use site read them (§2). `None`
    /// when a declared value-parameter type does not elaborate here, which is
    /// this device's only decline.
    #[allow(clippy::type_complexity)]
    fn tycode_fn_telescope(
        &self,
        ind: &Rc<Inductive>,
        span: Span,
    ) -> Option<(
        Cx,
        Vec<(Type, Level)>,
        Vec<(Type, Level)>,
        Vec<(Term, Type, Level)>,
    )> {
        let _ = span;
        let np = ind.params.len();
        let nv = ind.valparams.len();
        let total = np + nv;
        let mut cx = Cx::empty();
        let mut binders: Vec<(Type, Level)> = Vec::with_capacity(total);
        for (i, p) in ind.params.iter().enumerate() {
            // §2.1: one profile, all `Ty 0`.
            let l = Level::Zero;
            binders.push((Type::Ty(l.clone()), Level::succ(l.clone())));
            cx.push(format!("#p{i}"), Type::Ty(l.clone()), Level::succ(l.clone()));
            cx.tyvars.push(TyVar {
                name: p.clone(),
                ty: Type::El {
                    level: l.clone(),
                    tm: Rc::new(Term::Var(LocalVar(0))),
                },
                level: l,
                depth: cx.names.len(),
            });
        }
        for (j, (pname, pty)) in ind.valparams.iter().enumerate() {
            let (ty, level) = {
                let _scope = self.use_inductive_scope(ind);
                self.elab_ty(&cx, pty).ok()?
            };
            binders.push((ty.clone(), level.clone()));
            cx.push(format!("#v{j}"), ty.clone(), level.clone());
            cx.aliases.push(Rc::new(Alias {
                skel: None,
                name: pname.clone(),
                depth: cx.names.len(),
                term: Rc::new(Term::Var(LocalVar(0))),
                ty,
                level,
            }));
            if let Some((sym, _)) = ind.op_symbols.iter().find(|(_, n)| n == pname) {
                cx.op_locals.push((sym.clone(), pname.clone()));
            }
        }
        let targs = (0..np)
            .map(|i| {
                (
                    Type::El {
                        level: Level::Zero,
                        tm: Rc::new(Term::Var(LocalVar((total - 1 - i) as u32))),
                    },
                    Level::Zero,
                )
            })
            .collect();
        let vargs = (0..nv)
            .map(|j| {
                let k = np + j;
                let (ty, level) = &binders[k];
                (
                    Term::Var(LocalVar((total - 1 - k) as u32)),
                    ty.shift_local((total - k) as u32),
                    level.clone(),
                )
            })
            .collect();
        Some((cx, binders, targs, vargs))
    }

    /// `D#payloadₖ := ⌜⟦cₖ⟧⌝` per constructor and `D#suffixₖ :=
    /// D#payload_{k+1}^δ + D#suffix_{k+1}^δ` per `+` of a **non-recursive**
    /// declaration's sum-of-Σs (`issues/inductive-spelling-codes-nonrecursive.md`),
    /// registered off [`Self::register_ty_code`]'s own lowering under its
    /// boundary (unparameterized, unindexed, `tag_of` routes back) and only
    /// for a declaration with at least two constructors — with one, the
    /// whole type already names the only payload there is.
    ///
    /// Returns the **named** spelling of the whole type's code,
    /// `D#payload₀^δ + D#suffix₀^δ`, for the caller to register as
    /// `D#tycode`'s body; `None` when anything declined, in which case the
    /// guard entry is not written and every use site keeps the inline spine
    /// exactly as before. Best-effort and **all-or-nothing** like the `Wf`
    /// slot pair: a definition that passed the gate before a later one
    /// failed stays in Ψ, unreferenced and harmless, but no guard entry means
    /// no reference is ever handed out.
    ///
    /// Each payload's body is the emission spelling
    /// ([`Self::respell_ty_deep`] of the inline payload): its embedded field
    /// types are `El (F#tycode^δ)` where `F` has a code, so the definition is
    /// small and decodes to what a respelled field tuple is annotated with.
    /// The suffixes reference the payloads and each other, never a literal,
    /// so every level of an `inr` chain costs one δ and an `==`.
    fn register_spine_codes(
        &mut self,
        ind: &Rc<Inductive>,
        d_ty: &Type,
        l: &Level,
        span: Span,
    ) -> Option<Term> {
        let n = ind.ctors.len();
        if n < 2 || self.types.gdefs().has_spine_code_entry(ind.tag) {
            return None;
        }
        let spine = self.spine(d_ty, l, n, span).ok()?;
        let cx = Cx::empty();
        for (k, (ctor, lk)) in spine.ctors.iter().enumerate() {
            let emit = self.respell_ty_deep(&cx, ctor, 0);
            let body = crate::code::code_of(emit.as_ref().unwrap_or(ctor))?;
            self.push_gen_def(
                GenDef::PayloadCode(ind.tag, k),
                &ind.name,
                Type::Ty(lk.clone()),
                Level::succ(lk.clone()),
                body,
                span,
            )
            .ok()?;
        }
        // `suffix_k` mentions `suffix_{k+1}`, so the walk is from the right;
        // the last tail is the last payload and gets no definition of its own.
        let suffix_ref = |me: &Self, k: usize| -> Option<Term> {
            if k + 2 == n {
                me.gen_ref(&cx, GenDef::PayloadCode(ind.tag, n - 1))
            } else {
                me.gen_ref(&cx, GenDef::SuffixCode(ind.tag, k))
            }
        };
        let sum_body = |me: &Self, k: usize| -> Option<Term> {
            Some(Term::TmSum {
                lhs_level: spine.ctors[k].1.clone(),
                rhs_level: spine.tails[k].1.clone(),
                lhs: Rc::new(me.gen_ref(&cx, GenDef::PayloadCode(ind.tag, k))?),
                rhs: Rc::new(suffix_ref(me, k)?),
            })
        };
        for k in (0..n - 2).rev() {
            let body = sum_body(self, k + 1)?;
            let lk = &spine.tails[k].1;
            self.push_gen_def(
                GenDef::SuffixCode(ind.tag, k),
                &ind.name,
                Type::Ty(lk.clone()),
                Level::succ(lk.clone()),
                body,
                span,
            )
            .ok()?;
        }
        let whole = sum_body(self, 0)?;
        self.semantic_commit_gen_spine_codes(
            ind.tag,
            SpineCodes {
                ctors: spine.ctors,
                tails: spine.tails,
            },
        );
        Some(whole)
    }

    /// `D#projⱼ := λ(v : ⟦D⟧). fst(sndʲ v)`, one per field of a **record**
    /// (`issues/theorem-field-projection-oom.md`).
    ///
    /// This is [`Elaborator::project_field`]'s spine walk, run once at the
    /// declaration instead of once per use — and, crucially, run with each
    /// field's projection replaced by a *reference* to the definition just
    /// registered for it before it is substituted into the tail. That
    /// substitution is where the blow-up lived: the payload is a `fst` node
    /// carrying the Σ components at its level, so inlining it into a later
    /// field's type copies those annotations once per occurrence, and the
    /// annotations of *that* field are then the payload one level down. With
    /// a reference standing in, every payload is one node and the walk is
    /// linear — which is also what makes the definitions themselves small
    /// enough to gate one after another.
    ///
    /// Three definitions per spine entry, each naming one thing the walk
    /// would otherwise write out again at every entry above it:
    /// [`GenDef::RecFam`] the Σ tail family (as a code — see its own note),
    /// [`GenDef::RecProj`] the field, [`GenDef::RecTail`] the pair the entry
    /// above is taken of.
    ///
    /// **Boundaries (§13 of
    /// `docs/per-instantiation-type-codes-design.md` widened them).** A record
    /// only. A *parameterized or value-indexed* one is registered over its own
    /// telescope, with the record binder typed by the instantiation's
    /// **reference** — `Π(A₁ : Ty l₁)…(v : El l (app(D#tycode_fn^δ; ā))). Fⱼ`
    /// — so that the domain instantiated at a use site's `ā` *is* the
    /// receiver's own type and the kernel's `App` rule matches it
    /// syntactically. That needs the code function, so a declaration whose
    /// `register_ty_code_fn` declined keeps the inline walk.
    ///
    /// The **dependency** gate ([`Elaborator::record_spine_is_dependent`])
    /// applies to a *closed* record only. There it is the whole precondition:
    /// the inline walk's exponent comes from substituting a payload into the
    /// tails, so a non-dependent spine is linear already and the definitions
    /// would be all cost. At a telescope the reason to name is a different
    /// one — the receiver's type is a reference, and every `Fst`/`Snd` the
    /// inline walk builds makes the kernel reconstitute `Σ(fst). snd` and
    /// convert the reference against it (§10's regression, and by measurement
    /// its dominant payers — `MachineState<M>`, `StackAccess<M>`, `And<P, Q>`
    /// — are exactly the *non*-dependent ones). So a telescope registers
    /// whatever its spine does.
    ///
    /// Best-effort, like everything here: a failure at field `j` stops the
    /// walk, leaves fields `< j` registered (they are correct and useful on
    /// their own), and every later field's projection is inlined as before.
    fn register_rec_projs(&mut self, ind: &Rc<Inductive>, span: Span) {
        if !ind.is_record {
            return;
        }
        let nfields = ind.ctors[0].fields.len();
        if nfields == 0
            || self
                .types
                .gdefs()
                .contains_key(&GenDef::RecProj(ind.tag, 0))
        {
            return;
        }
        let telescoped = !ind.params.is_empty() || !ind.valparams.is_empty();
        // The declaration's own telescope and the context it lowers in —
        // `register_ty_code_fn`'s, verbatim, which is what makes the two
        // definitions' arguments the same `ā` at every use site.
        let (mut tel, cx, targs, vargs) = if telescoped {
            let Some((cx, binders, targs, vargs)) = self.tycode_fn_telescope(ind, span) else {
                decline!("register_rec_projs", &ind.name, "telescope");
                return;
            };
            // The same emitted domains `register_ty_code_fn` gives
            // `D#tycode_fn`'s own statement, for the same reason and so that
            // the two definitions' `Π`s over `Θ` are one spelling: `saturate`
            // reads these back at every field read.
            (self.emitted_tel(&binders), cx, targs, vargs)
        } else {
            (Vec::new(), Cx::empty(), Vec::new(), Vec::new())
        };
        let Ok((template, l)) = self.lower_instance(&cx, ind, &targs, &vargs, span) else {
            decline!("register_rec_projs", &ind.name, "lowering");
            return;
        };
        // The use site finds these by the tag it read off the receiver's type,
        // exactly as `register_ty_code`'s reference does; a lowering whose tag
        // does not route back here must not be named.
        if self.tag_of(&template).map(|i| i.tag) != Some(ind.tag) {
            decline!("register_rec_projs", &ind.name, "tag-route");
            return;
        }
        // The record binder's type. At a telescope it is the reference and
        // nothing else will do: the domain a use site's argument is checked
        // against is this type at `ā`, and the receiver's own type is the
        // reference at `ā`. `respell_ty` recovers the telescope's binders as
        // its arguments — the identity spine — and proves the reference means
        // the template, so a decline here is exactly the case with no name to
        // use.
        let mut d_ty = Rc::new(if telescoped {
            let Some(r) = self.respell_ty(&cx, &template) else {
                decline!("register_rec_projs", &ind.name, "binder-reference");
                return;
            };
            r
        } else {
            template.clone()
        });
        // The definitions' own context: `·, θ̄, v : R`, which is where the
        // whole walk lives — the field types come out of it scoped exactly as
        // a Π's codomain needs them.
        let mut vcx = cx;
        vcx.push("v".to_string(), (*d_ty).clone(), l.clone());
        // `cur` stays the **inline** spine: it is what the Σ components are
        // read off, and reading them off the reference would only mean
        // decoding it again at every entry.
        let mut cur = template.shift_local(1);
        // Two devices, two shapes, and one gate that points opposite ways on
        // them (§13.3 and §13.6 of
        // `docs/per-instantiation-type-codes-design.md`).
        //
        // **Closed, dependent.** The named tail family: the reason to name is
        // the inline walk's *exponent*, which comes from substituting a
        // payload into the tails, so a non-dependent closed spine is linear
        // already and the definitions would be all cost.
        //
        // **Telescoped, non-dependent.** The simple shape: the reason to name
        // is keeping the receiver's own reference off the kernel's `Fst`/`Snd`
        // rule, which any spine pays and whose measured payers
        // (`MachineState<M>`, `StackAccess<M>`, `And<P, Q>`) are the
        // non-dependent ones. Its bodies write the tail out, and one
        // `fst(sndʲ v)` is what the kernel walks in `j + 1` steps with no δ at
        // evaluation — which is what `reused_callee`'s certificate needs
        // (§13.6).
        //
        // **Telescoped, dependent** (`docs/telescoped-record-projections-
        // design.md` §3). The *closed* triple with the declaration's own `Θ`
        // in front. The simple shape's written-out tail **is** the exponent
        // here — the tail at entry `j` is the whole rest of the record with
        // the earlier projections substituted in — and §13.6's argument
        // against the named tails at a telescope was made on non-dependent
        // spines, where nothing is substituted into a tail and the code costs
        // δ per entry per read for nothing. On a dependent spine that trade
        // reverses: `probes/t_pc1..4` are zero misses and zero evaluator steps
        // at every depth and abort on emitted-term *size*.
        //
        // So the **dependency** test chooses the shape and the **telescope**
        // chooses whether there is a `Θ` in front — four combinations, three
        // devices — and the one declined cell is the closed non-dependent
        // record, §13.6's own deliberate omission, whose walk is linear
        // already and whose definitions would be all cost.
        let dependent = self.record_spine_is_dependent(&vcx, &cur, nfields, span);
        if !telescoped && !dependent {
            decline!(
                "register_rec_projs",
                &ind.name,
                "dependency-gate-nondependent-closed"
            );
            return;
        }
        let simple = telescoped && !dependent;
        let mut pair: Rc<Term> = Rc::new(Term::Var(LocalVar(0)));
        // Entry 0 of the Σ spine is the nominal tag (docs/surface-records.md
        // §3.3), so field `j` is entry `j + 1`.
        for step in 0..=nfields {
            let Ok(Type::Sigma {
                fst_level,
                snd_level,
                fst,
                snd,
            }) = self.whnf(&vcx, &cur, span)
            else {
                decline!("register_rec_projs", &ind.name, "spine-entry-{step}");
                return;
            };
            // The field type the *definitions* carry takes the emission
            // spelling, exactly as `project_field`'s fallback walk respells
            // the ones its `Fst`/`Snd` nodes carry: `Fⱼ` is read back out of
            // the projection's own statement at every use site, so a
            // monomorphized one here is a monomorphized `App.cod` at every
            // field read (the emission walker's residue rose 260 → 328
            // before this line, §13.7 item 3).
            //
            // The **tail** is deliberately not respelled with it. It is the
            // whole rest of the record at every entry, and `emit_ty` tries
            // the instance guard at every node it walks: on the eleven-field
            // cross-referencing record of
            // `crates/elab/tests/record_projection_size.rs` that walk is
            // itself the blow-up the device exists to prevent (§13.10). The
            // tail only ever reaches a use site through `D#recfamⱼ`'s code,
            // which the use site does not read annotations off.
            let fst = self.emit_ty(&vcx, &fst, 0).map_or(fst, Rc::new);
            let structural = Rc::clone(&snd);
            // The Σ's *tail family* — the whole rest of the record, as a type
            // family over this entry — named as a code, and the annotation
            // every node below carries is the decode of it. That is what keeps
            // the gate checks local: a type spelled `El (D#fam^δ v x)` is
            // checked by looking one binding up in Ψ, where the spelled-out
            // one is checked by walking the rest of the record and reducing
            // every reference it meets, once per entry of the spine.
            //
            // **Not at a telescope** (§13.6, amended by the fix pass). There
            // the definitions are the *simple* ones: the tail is written out
            // and no `D#recfam`/`D#tail` is registered, so the body of
            // `D#projⱼ` is one `fst(sndʲ v)` the kernel walks in `j + 1`
            // steps. The named tail's whole point is to bound what a
            // **dependent** spine copies, and a telescope registers only
            // non-dependent spines; what the chain costs instead is δ per
            // entry per read *at evaluation*, which is what a certificate
            // that computes through a field read pays. It is 510 exhausted
            // 2²⁰-step evaluator budgets on `reused_callee`'s certificate —
            // see §13.6.
            let tail_ann = if simple {
                Rc::clone(&snd)
            } else {
                let Some(tf) = self.push_tail_fam(
                    ind, step, &tel, &d_ty, &l, &fst, &fst_level, &snd, &snd_level, &vcx, span,
                ) else {
                    decline!("register_rec_projs", &ind.name, "tail-family-{step}");
                    return;
                };
                d_ty = Rc::new(d_ty.shift_global(1));
                shift_tel(&mut tel);
                tf
            };
            let (fst, mut structural, pair_g) = if simple {
                (fst, structural, Rc::clone(&pair))
            } else {
                (
                    Rc::new(fst.shift_global(1)),
                    Rc::new(structural.shift_global(1)),
                    Rc::new(pair.shift_global(1)),
                )
            };
            let proj = Rc::new(Term::Fst {
                fst_level: fst_level.clone(),
                snd_level: snd_level.clone(),
                fst_ty: Rc::clone(&fst),
                snd_ty: Rc::clone(&tail_ann),
                pair: Rc::clone(&pair_g),
            });
            let rest = Rc::new(Term::Snd {
                fst_level: fst_level.clone(),
                snd_level: snd_level.clone(),
                fst_ty: Rc::clone(&fst),
                snd_ty: Rc::clone(&tail_ann),
                pair: pair_g,
            });
            // The field's own projection. The tag (entry 0) is nobody's field
            // and gets none: it is a closed numeral, and nothing later refers
            // to it.
            let (payload, rest, tail_ann) = if step == 0 {
                (proj, rest, tail_ann)
            } else {
                let key = GenDef::RecProj(ind.tag, step - 1);
                let Some(payload) = self.push_proj_def(
                    key, ind, &tel, &d_ty, &l, &fst, &fst_level, &proj, &vcx, span,
                ) else {
                    decline!("register_rec_projs", &ind.name, "projection-{}", step - 1);
                    return;
                };
                // Ψ just grew by one, so everything carried past the push is
                // one binding further out (`Defs::body`'s convention). The
                // walk is the only thing here that keeps terms across a push,
                // and this is what keeps the references inside them — the
                // families, projections and tails already registered —
                // pointing at what they did.
                d_ty = Rc::new(d_ty.shift_global(1));
                shift_tel(&mut tel);
                structural = Rc::new(structural.shift_global(1));
                (
                    payload,
                    Rc::new(rest.shift_global(1)),
                    Rc::new(tail_ann.shift_global(1)),
                )
            };
            if step == nfields {
                return;
            }
            if simple {
                // No tail definition: the chain is the `Snd` node itself, and
                // the walk's own copy of the tail advances by substitution as
                // it always did. Ψ did not grow past the projection, so
                // nothing shifts here.
                cur = structural.apply_local(&LocalSubst::id(&vcx.gamma).extended(payload));
                pair = rest;
                continue;
            }
            // The tail past this entry. Its statement is the family applied to
            // this entry's projection — one node, where the kernel's own `snd`
            // rule would produce the family's whole body with the projection
            // substituted through it.
            let cod = instantiate_fam(&tail_ann, &payload, &vcx.gamma);
            let key = GenDef::RecTail(ind.tag, step);
            let Some(next) = self.push_proj_def(
                key, ind, &tel, &d_ty, &l, &cod, &snd_level, &rest, &vcx, span,
            ) else {
                decline!("register_rec_projs", &ind.name, "tail-{step}");
                return;
            };
            d_ty = Rc::new(d_ty.shift_global(1));
            shift_tel(&mut tel);
            // The walk itself keeps the spelled-out tail: it is what the next
            // entry's components are read off, and reading them off the code
            // would only mean decoding it again.
            cur = structural
                .apply_local(&LocalSubst::id(&vcx.gamma).extended(payload))
                .shift_global(1);
            pair = next;
        }
    }

    /// Does any entry of the record's Σ spine occur in the entries after it?
    ///
    /// This is the whole precondition of the device. The inline walk in
    /// [`Elaborator::project_field`] duplicates its payload once per
    /// occurrence of the entry it substitutes, so a record whose later field
    /// types never mention the earlier fields has a walk that is already
    /// linear and gains nothing from a name — while every record pays the
    /// gate checks that registering the definitions costs. A plain data
    /// record is therefore left exactly as it was.
    ///
    /// Occurrence is decided by *doing* the substitution twice with two
    /// different payloads and comparing: the traversal rewrites a
    /// substitution's tails whatever it does with the variable, so comparing
    /// against the un-substituted tail would report every global reference as
    /// a use. The two payloads are closed and differ, so the results differ
    /// exactly where the binder occurs. Nothing here is type-checked — this
    /// is a syntactic question and both probes are thrown away.
    ///
    /// A wrong answer is only ever a wrong *choice*: `false` keeps the walk
    /// that has always been there, and `true` registers definitions that face
    /// the gate like everything else. That is what makes probing with terms
    /// of the wrong type acceptable here and nowhere else.
    fn record_spine_is_dependent(
        &self,
        vcx: &Cx,
        record_ty: &Type,
        nfields: usize,
        span: Span,
    ) -> bool {
        let mut cur = record_ty.clone();
        let probe =
            |t: &Rc<Type>, x: Term| t.apply_local(&LocalSubst::id(&vcx.gamma).extended(Rc::new(x)));
        for _ in 0..=nfields {
            let Ok(Type::Sigma { snd, .. }) = self.whnf(vcx, &cur, span) else {
                // Not a spine this walk understands: leave it to the walk that
                // will meet the same wall at the use site and report there.
                return false;
            };
            let one = probe(&snd, Term::Zero);
            if one != probe(&snd, Term::TmNat) {
                return true;
            }
            cur = one;
        }
        false
    }

    /// `D#famⱼ := λ(v : ⟦D⟧). λ(x : Fⱼ). ⌜Sⱼ⌝`, the Σ tail family at spine
    /// entry `j`, and the annotation that stands for `Sⱼ` afterwards:
    /// `El (D#famⱼ^δ v x)`, scoped in `·, v, x` exactly as `Sⱼ` was.
    ///
    /// A code and not a type, because a code is *checked* rather than
    /// *reduced*: `Sⱼ` mentions the earlier projections, and every kernel
    /// visit to a spelled-out `Sⱼ` reduces those references — down a chain as
    /// long as the spine, copying the annotations at every link. Behind a code
    /// they are terms in a body nobody unfolds until a conversion actually
    /// needs the type.
    ///
    /// **At a telescope (§13).** `tel` is the declaration's own
    /// `(A₁ : Ty l₁)…(v_m : T_m)`, empty for a closed record; the statement is
    /// `Π tel. Π(v : R). Π(x : Fⱼ). Ty l'` and the occurrence applies the
    /// definition to the telescope's binders before `v` and `x`. `R` is the
    /// record's binder type — the *reference* `El (app(D#tycode_fn^δ; θ̄))`
    /// for a parameterized declaration, which is the whole point of §13.
    #[allow(clippy::too_many_arguments)]
    fn push_tail_fam(
        &mut self,
        ind: &Rc<Inductive>,
        step: usize,
        tel: &[(Type, Level)],
        d_ty: &Rc<Type>,
        l: &Level,
        fst: &Rc<Type>,
        fst_level: &Level,
        snd: &Rc<Type>,
        snd_level: &Level,
        vcx: &Cx,
        span: Span,
    ) -> Option<Rc<Type>> {
        let key = GenDef::RecFam(ind.tag, step);
        let code_ty = Type::Ty(snd_level.clone());
        let code_level = Level::succ(snd_level.clone());
        let inner_level = Level::max(fst_level.clone(), code_level.clone());
        // `Π(x : Fⱼ). Ty l'` — scoped in `·, θ̄, v`, where `Fⱼ` is.
        let inner = Type::Pi {
            dom_level: fst_level.clone(),
            cod_level: code_level.clone(),
            dom: Rc::clone(fst),
            cod: Rc::new(code_ty.clone()),
        };
        let (ty, level) = wrap_tel(
            tel,
            Type::Pi {
                dom_level: l.clone(),
                cod_level: inner_level.clone(),
                dom: Rc::clone(d_ty),
                cod: Rc::new(inner),
            },
            Level::max(l.clone(), inner_level.clone()),
        );
        let body = wrap_tel_lam(
            tel,
            Term::Lam {
                dom_level: l.clone(),
                cod_level: inner_level.clone(),
                dom: Rc::clone(d_ty),
                body: Rc::new(Term::Lam {
                    dom_level: fst_level.clone(),
                    cod_level: code_level.clone(),
                    dom: Rc::clone(fst),
                    body: Rc::new(crate::code::code_of(snd)?),
                }),
            },
            Level::max(l.clone(), inner_level),
        );
        self.push_gen_def(key, &ind.name, ty.clone(), level, body, span)
            .ok()?;
        // The occurrence, scoped in `·, θ̄, v, x` — one binder past `vcx`,
        // which is where the Σ's tail lives.
        let mut xcx = vcx.clone();
        xcx.push("x".to_string(), (**fst).clone(), fst_level.clone());
        let fun = self.gen_ref(&xcx, key)?;
        let (tm, _, _) = saturate(
            &xcx.gamma,
            fun,
            &ty.shift_global(1),
            &tel_self_args(tel.len(), 2),
        )?;
        Some(Rc::new(Type::El {
            level: snd_level.clone(),
            tm: Rc::new(tm),
        }))
    }

    /// Push one `Π(v : ⟦D⟧). cod` definition whose body is `λ(v : ⟦D⟧). node`,
    /// and answer with `key^δ v` — the reference that stands for `node` in
    /// everything built afterwards. `None` if the gate refused it, which is
    /// [`Elaborator::register_rec_projs`]'s cue to stop and leave the rest
    /// inline.
    ///
    /// Everything handed in is scoped in `·, v` (or, for `dom`, in `·`) and in
    /// the Ψ *before* the push; the reference that comes back is scoped in the
    /// Ψ after it, so a caller that keeps anything else across the call has to
    /// [`shift_global`](Type::shift_global) it by one.
    #[allow(clippy::too_many_arguments)]
    fn push_proj_def(
        &mut self,
        key: GenDef,
        ind: &Rc<Inductive>,
        tel: &[(Type, Level)],
        dom: &Rc<Type>,
        dom_level: &Level,
        cod: &Type,
        cod_level: &Level,
        node: &Rc<Term>,
        vcx: &Cx,
        span: Span,
    ) -> Option<Rc<Term>> {
        let (ty, level) = wrap_tel(
            tel,
            Type::Pi {
                dom_level: dom_level.clone(),
                cod_level: cod_level.clone(),
                dom: Rc::clone(dom),
                cod: Rc::new(cod.clone()),
            },
            Level::max(dom_level.clone(), cod_level.clone()),
        );
        let body = wrap_tel_lam(
            tel,
            Term::Lam {
                dom_level: dom_level.clone(),
                cod_level: cod_level.clone(),
                dom: Rc::clone(dom),
                body: Rc::clone(node),
            },
            Level::max(dom_level.clone(), cod_level.clone()),
        );
        self.push_gen_def(key, &ind.name, ty.clone(), level, body, span)
            .ok()?;
        let fun = self.gen_ref(vcx, key)?;
        let (tm, _, _) = saturate(
            &vcx.gamma,
            fun,
            &ty.shift_global(1),
            &tel_self_args(tel.len(), 1),
        )?;
        Some(Rc::new(tm))
    }

    /// `app(D#projⱼ^δ; ā, v)` and its type, for a projection of field `idx`
    /// off `value` at the instantiation `ā`
    /// (`issues/theorem-field-projection-oom.md`;
    /// `docs/per-instantiation-type-codes-design.md` §13). `ā` is empty for a
    /// closed record, and `None` comes back whenever the record has no
    /// registered projection or the arguments do not saturate its telescope —
    /// every such site keeps the inline walk.
    /// Did this declaration's projections register under the **dependent**
    /// shape — the closed triple, tail family and all?
    ///
    /// The tail family is the discriminator and is the only one there is: the
    /// simple telescoped device writes its tails out and registers no
    /// [`GenDef::RecFam`], so one Ψ lookup separates the two cells without a
    /// second record of what [`Self::register_rec_projs`] decided.
    /// [`crate::inductive::project_field`]'s receiver gate asks, because the
    /// dependent device is exempt from it at every receiver exactly as the
    /// closed one is (`docs/telescoped-record-projections-design.md` §4).
    pub(crate) fn rec_projs_are_dependent(&self, tag: u32) -> bool {
        self.types
            .gdefs()
            .abs_for(&GenDef::RecFam(tag, 0))
            .is_some()
    }

    pub(crate) fn rec_proj_ref_at(
        &self,
        cx: &Cx,
        tag: u32,
        idx: usize,
        args: &[Rc<Term>],
        value: &Rc<Term>,
    ) -> Option<(Term, Type, Level)> {
        let key = GenDef::RecProj(tag, idx);
        let fun = self.gen_ref(cx, key)?;
        // The Π is read back out of Ψ rather than remembered from the
        // registration: a stored copy would carry the global indices of the
        // Ψ it was built in, and every declaration since has moved them. The
        // reference's own variable gives the rescoping, exactly as it does for
        // a binding's type in `typing.rs` (`shift_global(v + 1)`).
        let Term::GlobalTm { var, .. } = &fun else {
            return None;
        };
        let abs = *self.types.gdefs().abs_for(&key)? as usize;
        let GlobalBinding::Tm { ty, .. } = self.psi.bindings.get(abs)? else {
            return None;
        };
        let stmt = ty.shift_global(var.0 + 1);
        let mut spine: Vec<Rc<Term>> = args.to_vec();
        spine.push(Rc::clone(value));
        saturate(&cx.gamma, fun, &stmt, &spine)
    }

    /// The arguments a use site must apply `D`'s telescoped definitions to,
    /// for a receiver whose type is `D` at an instantiation (§13). Two routes,
    /// and both hand back the *emitted* spelling — the same `ā` the type's own
    /// reference carries, so the definition's domain at `ā` and the receiver's
    /// type are one term:
    ///
    /// - the type is already `El (app(D#tycode_fn^δ; ā))`, and its own spine
    ///   is the answer;
    /// - the type is the inline instantiation, and §4.1's hole-match (with
    ///   its proof) recovers them — the arguments [`Self::instance_ref`] would
    ///   build the reference from, exposed rather than re-matched.
    ///
    /// `Some(vec![])` for an unparameterized declaration, which takes no
    /// arguments and needs no recovery.
    pub(crate) fn instance_args(&self, cx: &Cx, ind: &Inductive, ty: &Type) -> Option<Vec<Rc<Term>>> {
        if ind.params.is_empty() && ind.valparams.is_empty() {
            return Some(Vec::new());
        }
        if let Type::El { tm, .. } = ty
            && let Some((GenDef::TyCodeFn(tag), args)) = self.gen_app_of(tm)
            && tag == ind.tag
        {
            return Some(args);
        }
        let (_, args) = self.instance_match(cx, ind, ty, 0, 0)?;
        Some(args)
    }

    /// `D#shape := ⌜S⌝` and `D#arity := λ(x : El (D#shape^δ)). n`, for a
    /// **recursive** declaration whose lowering is `Wf(x : S). n`
    /// (`docs/wf-shape-code-design.md` §2.1). Runs off `register_ty_code`'s own
    /// lowering, so it inherits that function's boundary verbatim
    /// (unparameterized, unindexed, `tag_of`-routes-back) and the two
    /// registrations always agree about what `⟦D⟧` is.
    ///
    /// Best-effort like every other piece here, and **all-or-nothing**: the
    /// guard entry is written only when both definitions passed the gate, so a
    /// half-registered pair can never hand out half a spelling.
    fn register_wf_slots(&mut self, ind: &Rc<Inductive>, d_ty: &Type, l: &Level, span: Span) {
        let Type::Wf { shape, arity, .. } = d_ty else {
            // Non-recursive: a sum-of-Σs has no slots to name. `TyCode` is the
            // whole story there.
            return;
        };
        let skey = GenDef::ShapeCode(ind.tag);
        let akey = GenDef::ArityFn(ind.tag);
        if self.types.gdefs().contains_key(&skey)
            || self.types.gdefs().contains_key(&akey)
        {
            return;
        }
        let Some(scode) = crate::code::code_of(shape) else {
            return;
        };
        if self
            .push_gen_def(
                skey,
                &ind.name,
                Type::Ty(l.clone()),
                Level::succ(l.clone()),
                scode.clone(),
                span,
            )
            .is_err()
        {
            return;
        }
        // The λ's domain is the shape *reference* just registered: the arity
        // definition is the one place where writing the shape out again would
        // undo half of what this pair buys.
        let cx = Cx::empty();
        let Some(sref) = self.gen_type_ref(&cx, skey, l) else {
            return;
        };
        let ty = Type::Pi {
            dom_level: l.clone(),
            cod_level: Level::Zero,
            dom: Rc::new(sref.clone()),
            cod: Rc::new(Type::Nat),
        };
        let body = Term::Lam {
            dom_level: l.clone(),
            cod_level: Level::Zero,
            dom: Rc::new(sref),
            body: Rc::clone(arity),
        };
        if self
            .push_gen_def(akey, &ind.name, ty, l.clone(), body, span)
            .is_ok()
        {
            let shape_decoded = Rc::new(Type::El {
                level: l.clone(),
                tm: Rc::new(scode),
            });
            self.semantic_commit_gen_wf_slots(
                ind.tag,
                WfSlots {
                    shape: Rc::clone(shape),
                    shape_decoded,
                    arity: Rc::clone(arity),
                    level: l.clone(),
                },
            );
        }
    }

    /// `El (D#shape^δ)` and `app(D#arity^δ; x₀)` for a `Wf`'s slot pair, if and
    /// only if the pair in front of us **is** the one the two definitions were
    /// minted from (design §2.3's guard). `None` is every emission site's cue
    /// to keep the slots inline, exactly as before.
    ///
    /// The shape reference is scoped in `cx`; the arity reference is scoped one
    /// binder deeper, because an arity slot is always read under the shape's
    /// own binder (`x : S`) — that asymmetry is the whole of the bookkeeping
    /// here, and getting it wrong is a kernel `SubstMismatch`, not a wrong
    /// answer.
    pub(crate) fn wf_slot_refs(&self, cx: &Cx, shape: &Type, arity: &Term) -> Option<(Type, Term)> {
        if !self.types.gdefs().has_wf_slots() {
            return None;
        }
        let ind = self.tag_of(shape)?;
        let slots = self.types.gdefs().wf_slots(&ind.tag)?;
        let l = &slots.level;
        if (*slots.shape != *shape && *slots.shape_decoded != *shape) || *slots.arity != *arity {
            return None;
        }
        let sref = self.gen_type_ref(cx, GenDef::ShapeCode(ind.tag), l)?;
        let fun = self.gen_ref_deeper(cx, GenDef::ArityFn(ind.tag), 1)?;
        let aref = Term::App {
            fun: Rc::new(fun),
            dom_level: l.clone(),
            cod_level: Level::Zero,
            dom: Rc::new(sref.shift_local(1)),
            // `Nat` binds nothing, so the `App`'s codomain needs no shift.
            cod: Rc::new(Type::Nat),
            arg: Rc::new(Term::Var(LocalVar(0))),
        };
        Some((sref, aref))
    }

    /// Closed-registration lookup, not the default API for annotations.
    /// Parameterized declarations have a TyCodeFn and deliberately decline
    /// here; emission callers should use [`Self::annotation_type`].
    ///
    /// `El l (D#tycode^δ)` for `inline`, if and only if `inline` **is** the
    /// lowering `D#tycode` was minted from (design §1.3 + the guard note on
    /// [`GenDefs::ty_code`]). `None` means no closed registration matched;
    /// parameterized or component naming may still apply.
    pub(crate) fn closed_type_ref(&self, cx: &Cx, tag: u32, inline: &Type) -> Option<Type> {
        let (registered, level) = self.types.gdefs().ty_code(&tag)?;
        if **registered != *inline {
            return None;
        }
        self.gen_type_ref(cx, GenDef::TyCode(tag), level)
    }

    /// [`Self::closed_type_ref`] with the tag read out of the type instead of
    /// supplied: `Some(El (D#tycode^δ))` when `ty` **is** some declaration's
    /// registered lowering, `None` otherwise.
    ///
    /// Two filters, both needed. `tag_of` is a *structural* read and will walk
    /// into a `Sum`/`Σ` to find a tag, so it can name a declaration whose
    /// `⟦D⟧` is not `ty` at all; the structural comparison inside
    /// `closed_type_ref` is what turns that into a decline rather than a wrong
    /// reference. And `tag_of` goes through `decoded`, which leaves an `El` of
    /// a neutral code exactly as it is — so an already-reference-spelled type
    /// declines here too, and this is idempotent.
    /// A second route follows it when it declines
    /// (`docs/per-instantiation-type-codes-design.md` §4.1): the same tag read
    /// naming a declaration with a code *function*, whose instantiation is
    /// recovered by positional hole-matching and **proved** by re-lowering.
    pub(crate) fn respell_ty(&self, cx: &Cx, ty: &Type) -> Option<Type> {
        self.respell_ty_at(cx, ty, 0, 0)
    }

    /// [`Self::respell_ty`] for an occurrence sitting `d` binders past `cx` in
    /// a world with `g` scratch globals. The closed route mints against `cx`
    /// and shifts (a type equal to the registry's closed copy is itself
    /// closed, so only the substitution tail's length moves); the instance
    /// route mints **at depth**, because an open instance's recovered
    /// arguments mention the binders the walk has crossed and must be carried
    /// verbatim (§4.1's depth paragraph).
    pub(crate) fn respell_ty_at(&self, cx: &Cx, ty: &Type, d: u32, g: u32) -> Option<Type> {
        let ind = self.tag_of(ty)?;
        if let Some(r) = self.closed_type_ref(cx, ind.tag, ty) {
            let r = if g == 0 { r } else { r.shift_global(g) };
            return Some(if d == 0 { r } else { r.shift_local(d) });
        }
        // The one decline this site can report that the instance route cannot:
        // an *unparameterized* declaration whose tag routed back here and whose
        // registered lowering is not this type — `closed_type_ref`'s structural
        // guard turning a `tag_of` walk into a decline — or one that never
        // registered a whole-type code. The parameterized declines below all
        // print their own reason.
        if ind.params.is_empty() && ind.valparams.is_empty() {
            decline!("respell_ty_at", &ind.name, "no-closed-code");
            return None;
        }
        self.instance_ref(cx, &ind, ty, d, g)
    }

    /// `El l (app(D#tycode_fn^δ; ā))` for an inline instantiation of a
    /// parameterized or value-indexed declaration (§4.1). Two steps, and the
    /// second is what makes the first sound: the arguments are **guessed** by
    /// positional hole-matching against the registered open template, and the
    /// template at that guess is then required to be the subject
    /// syntactically.
    /// The matcher may be as incomplete as convenient and can never be wrong,
    /// so every shape it cannot place — an unfamiliar former, a value
    /// parameter at a slot the type walk does not pass, a level profile other
    /// than the registered one — is today's inline spelling.
    ///
    /// The recovered arguments are themselves emitted before the spine is
    /// built, so a nested instantiation composes references at every level
    /// and no literal is left anywhere.
    fn instance_ref(&self, cx: &Cx, ind: &Inductive, ty: &Type, d: u32, g: u32) -> Option<Type> {
        let (level, args) = self.instance_match(cx, ind, ty, d, g)?;
        let Some(spine) = self.gen_spine(cx, ind.tag, &args, d, g) else {
            decline!("instance_ref", &ind.name, "spine");
            return None;
        };
        Some(Type::El {
            level,
            tm: Rc::new(spine),
        })
    }

    /// A registered [`TyCodeFn`] **read into the world its reader compares it
    /// in**, which is never the world it was stored in.
    ///
    /// [`Self::register_ty_code_fn`] computes the template and the statement,
    /// pushes `D#tycode_fn`, and commits them as computed — so both sit in the
    /// Ψ prefix *before* the definition's own binding, exactly where a
    /// binding's declared type sits. `GlobalVar`s number from the end of Ψ, so
    /// from that push on every declaration moves the indices inside them, and a
    /// reader comparing the stored copy against a type built now is comparing
    /// two frames: the subject spells every global `len_at - abs` higher. For a
    /// declaration whose lowering mentions no global that is a difference of
    /// nothing, which is why the device looked like it had a dependency
    /// boundary; for every other one it is the whole match, and §4.1's identity
    /// step declined silently at every use site
    /// (`docs/telescoped-record-projections-design.md` §2.1).
    ///
    /// The rescoping is on the **read**, off the reference's own variable —
    /// [`Self::rec_proj_ref_at`]'s discipline for a projection's `Π`, for the
    /// same reason it gives — and never a shift at commit time, which is right
    /// for one instant and wrong after the next push. Nothing about the stored
    /// entry or the image codec changes, so a replayed image self-corrects.
    ///
    /// `len_at` is the Ψ length the reader's own globals count from: the
    /// reflection boundary's explicit anchor ([`Self::unspell_ty_deep`], which
    /// deliberately assumes no padding), or [`Self::ty_code_fn_now`]'s
    /// committed world.
    pub(crate) fn ty_code_fn_at(&self, tag: u32, len_at: u32) -> Option<TyCodeFn> {
        let entry = self.types.gdefs().ty_code_fn(&tag)?;
        let abs = *self.types.gdefs().abs_for(&GenDef::TyCodeFn(tag))?;
        let by = len_at.checked_sub(abs)?;
        if by == 0 {
            return Some(entry.clone());
        }
        Some(TyCodeFn {
            template: Rc::new(entry.template.shift_global(by)),
            stmt: Rc::new(entry.stmt.shift_global(by)),
            param_levels: entry.param_levels.clone(),
            level: entry.level.clone(),
        })
    }

    /// [`Self::ty_code_fn_at`] in the committed world, `g` scratch globals
    /// deep. This is [`Self::gen_ref`]'s own numbering — goal arena and `meta
    /// fn` padding included — so the shift it computes is exactly the
    /// `var.0 + 1` of the reference the caller is about to mint or has just
    /// read, which is what makes the entry and the reference agree whatever
    /// pushed in between.
    pub(crate) fn ty_code_fn_now(&self, tag: u32, g: u32) -> Option<TyCodeFn> {
        self.ty_code_fn_at(tag, self.gen_ref_len(g))
    }

    /// The Ψ length a reference minted `g` scratch globals deep counts from —
    /// [`Self::gen_ref`]'s own numbering, goal arena and `meta fn` padding
    /// included.
    fn gen_ref_len(&self, g: u32) -> u32 {
        self.psi.bindings.len() as u32 + self.attempt.goal_arena.base() + self.meta_offset() + g
    }

    /// [`Self::instance_ref`]'s two steps without the spine: the recovered
    /// arguments, **emitted**, and the instantiation's level. Split out so
    /// that a use site which needs the same `ā` for a *different* definition
    /// over the same telescope — a record's projections (§13) — asks the one
    /// question rather than re-matching.
    fn instance_match(
        &self,
        cx: &Cx,
        ind: &Inductive,
        ty: &Type,
        d: u32,
        g: u32,
    ) -> Option<(Level, Vec<Rc<Term>>)> {
        let Some(entry) = self.ty_code_fn_now(ind.tag, g) else {
            decline!("instance_match", &ind.name, "no-tycode-fn");
            return None;
        };
        let np = entry.param_levels.len();
        let arity = pi_arity(&entry.stmt);
        if arity != np + ind.valparams.len() {
            decline!("instance_match", &ind.name, "arity-profile");
            return None;
        }
        let mut holes = Holes {
            el: self,
            g,
            strict: false,
            base: cx.gamma.base,
            outer: cx.gamma.entries.len() as u32 + d,
            total: arity as u32,
            np: np as u32,
            types: vec![None; np],
            values: vec![None; arity - np],
            why: None,
        };
        if holes.ty(&entry.template, ty, 0).is_none() {
            // The former pair the walk stopped on, not just "hole-match":
            // that is the next line of §2.2's list, and without it a reader
            // has to re-derive it from the source every time.
            let (t, s) = holes.why.unwrap_or(("?", "level-profile"));
            decline!("instance_match", &ind.name, "hole-match-{t}/{s}");
            return None;
        }
        let Holes { types, values, .. } = holes;
        let Some(codes) = types.into_iter().collect::<Option<Vec<Rc<Term>>>>() else {
            decline!("instance_match", &ind.name, "unplaced-type-param");
            return None;
        };
        let Some(values) = values.into_iter().collect::<Option<Vec<Rc<Term>>>>() else {
            decline!("instance_match", &ind.name, "unplaced-value-param");
            return None;
        };
        // Step 2, the proof. What has to be true is that the reference's own
        // meaning is this type, and the reference's meaning is exactly the
        // template at the recovered arguments — so that is what is compared,
        // rather than a second lowering that would have to agree with the
        // template anyway (§4.1, amended 2026-09-10). The arity slot the
        // matcher declined to walk is compared here with everything else.
        //
        // The type arguments are already **codes** (§2.3), which is what the
        // template's `El (Var i)` slots want substituted into them and what
        // the quoting step used to produce; the frame is the subject's own,
        // so the copy compared here is spelled in the context `ty` is.
        let mut inline: Vec<Rc<Term>> = Vec::with_capacity(codes.len() + values.len());
        inline.extend(codes.iter().map(Rc::clone));
        inline.extend(values.iter().map(Rc::clone));
        // The comparison is `Holes::ty` again with **no holes** — an empty
        // telescope, so no hole arm can fire — rather than a syntactic `!=`
        // or a second congruence kept in step with the first: the see-through
        // arms the match needed are exactly the ones the proof is allowed, and
        // one walk cannot drift from the other. `strict` restores the one
        // reading the match gives up, a global's substitution tail (§3 of
        // `docs/closed-argument-and-parameter-domain-spelling-design.md`).
        let copy = instance_of_template(&entry, &inline, frame_tail(cx, d));
        let mut proof = Holes {
            el: self,
            g,
            strict: true,
            base: cx.gamma.base,
            outer: cx.gamma.entries.len() as u32 + d,
            total: 0,
            np: 0,
            types: Vec::new(),
            values: Vec::new(),
            why: None,
        };
        if proof.ty(&copy, ty, 0).is_none() {
            let (t, s) = proof.why.unwrap_or(("?", "level-profile"));
            decline!("instance_match", &ind.name, "identity-match-{t}/{s}");
            return None;
        }
        // The arguments the reference will carry: a type argument goes
        // through `emit_ty_in` and `code_of` first (§4.1), so
        // `List<BitVec(8)>` becomes `app(List#tycode_fn^δ;
        // app(BitVec#tycode_fn^δ; 8))` with no literal at any level.
        //
        // The *type* a recovered code stands for is `decode_deep (El l c)`
        // (§2.3) — derived here, where the emission needs it, rather than
        // carried alongside the code and kept in step with it. A declined
        // emission keeps the recovered code itself, which is already the
        // spelling the subject wrote.
        let mut args: Vec<Rc<Term>> = Vec::with_capacity(codes.len() + values.len());
        for (c, level) in codes.iter().zip(&entry.param_levels) {
            let el = Type::El {
                level: level.clone(),
                tm: Rc::clone(c),
            };
            let t = crate::inductive::decode_deep(&el).unwrap_or(el);
            match self.emit_ty_in(cx, &t, d, g) {
                Some(emitted) => {
                    let Some(code) = crate::code::code_of(&emitted) else {
                        decline!("instance_match", &ind.name, "emitted-argument-not-quotable");
                        return None;
                    };
                    args.push(Rc::new(code));
                }
                None => args.push(Rc::clone(c)),
            }
        }
        args.extend(values.iter().map(Rc::clone));
        Some((entry.level.clone(), args))
    }

    /// The application spine of a code function at recovered arguments, with
    /// each `App`'s annotations read off the definition's own `Π` as it is
    /// walked — which is where a dependent telescope's later domains come
    /// from.
    fn gen_spine(&self, cx: &Cx, tag: u32, args: &[Rc<Term>], d: u32, g: u32) -> Option<Term> {
        let entry = self.ty_code_fn_now(tag, g)?;
        let mut head = self.gen_ref_deeper(cx, GenDef::TyCodeFn(tag), d)?;
        if g != 0 {
            head = head.shift_global(g);
        }
        let mut cur = weakened(&entry.stmt, cx, d);
        for arg in args {
            let Type::Pi {
                dom_level,
                cod_level,
                dom,
                cod,
            } = cur
            else {
                return None;
            };
            head = Term::App {
                fun: Rc::new(head),
                dom_level,
                cod_level,
                dom,
                cod: Rc::clone(&cod),
                arg: Rc::clone(arg),
            };
            cur = cod.apply_local(&id_subst_at(cx, d).extended(Rc::clone(arg)));
        }
        matches!(cur, Type::Ty(_)).then_some(head)
    }

    /// `El (D#payloadₖ^δ)` or `El (D#suffixₖ^δ)` for `ty`, if and only if
    /// `ty` **is** the `k`-th component of the spine `D`'s codes were minted
    /// from ([`GenDefLayer::spine_codes`]'s guard) — the spine-level twin of
    /// [`Self::closed_type_ref`], found by a scan over the registered components.
    /// `None` is the cue to keep the inline spelling.
    ///
    /// **Not** a fallback of [`Self::respell_ty`], deliberately: a nullary
    /// payload of the declaration with nominal tag 0 is `Σ(Unit). Unit`, which
    /// is also the digit-1 component of every other declaration's *tag type*
    /// — so a scan reached from a deep walk spelled the tag types inside
    /// every later lowering as `El (Bool#payload₀^δ)`, convertible and
    /// unreadable (81 failures on the 2026-09-06 full suite). Only
    /// [`Self::spine_refs_by_position`] hands these out at emission, where
    /// the whole spine's tag says whose components they are.
    pub(crate) fn spine_type_ref(&self, cx: &Cx, tag: u32, ty: &Type) -> Option<Type> {
        let codes = self.types.gdefs().spine_codes(&tag)?;
        if let Some((k, (_, l))) = codes.ctors.iter().enumerate().find(|(_, (c, _))| **c == *ty) {
            return self.gen_type_ref(cx, GenDef::PayloadCode(tag, k), l);
        }
        let (k, (_, l)) = codes.tails.iter().enumerate().find(|(_, (t, _))| **t == *ty)?;
        self.spine_tail_ref(cx, tag, codes.ctors.len(), k, l)
    }

    /// The reference for `Spine::tails[k]` of a declaration with `n`
    /// constructors: the last tail is the last payload.
    fn spine_tail_ref(&self, cx: &Cx, tag: u32, n: usize, k: usize, l: &Level) -> Option<Type> {
        let key = if k + 2 == n {
            GenDef::PayloadCode(tag, n - 1)
        } else {
            GenDef::SuffixCode(tag, k)
        };
        self.gen_type_ref(cx, key, l)
    }

    /// [`Self::spine_type_ref`] **by position**, for the emission copy of a
    /// spine ([`Elaborator::respell_spine`]): component `k` of `spine` takes
    /// its reference when it is structurally the registered component `k`,
    /// so the guard is one comparison per component rather than a scan, and
    /// two constructors with identical payloads keep their own names. `None`
    /// when the declaration has no spine codes or the spines disagree in
    /// length, which is every caller's cue to fall back to the deep respell.
    pub(crate) fn spine_refs_by_position(
        &self,
        cx: &Cx,
        tag: u32,
        spine: &crate::inductive::Spine,
    ) -> Option<(Vec<Option<Type>>, Vec<Option<Type>>)> {
        if !self.types.gdefs().has_spine_codes() {
            return None;
        }
        let codes = self.types.gdefs().spine_codes(&tag)?;
        let n = codes.ctors.len();
        if spine.ctors.len() != n || spine.tails.len() != codes.tails.len() {
            return None;
        }
        let ctors = spine
            .ctors
            .iter()
            .zip(&codes.ctors)
            .enumerate()
            .map(|(k, ((c, _), (reg, l)))| {
                (*c == *reg)
                    .then(|| self.gen_type_ref(cx, GenDef::PayloadCode(tag, k), l))
                    .flatten()
            })
            .collect();
        let tails = spine
            .tails
            .iter()
            .zip(&codes.tails)
            .enumerate()
            .map(|(k, ((t, _), (reg, l)))| {
                (*t == *reg)
                    .then(|| self.spine_tail_ref(cx, tag, n, k, l))
                    .flatten()
            })
            .collect();
        Some((ctors, tails))
    }

    /// The `Wf` slot **pair** in the emission spelling: the two components
    /// respelled together or not at all.
    ///
    /// Not [`Self::emit_ty`] of the former they reconstitute: a slot holds the
    /// *component*, and since
    /// `docs/per-instantiation-type-codes-design.md` a monomorphized `Wf` has
    /// a name for the whole — which is exactly what may not stand here
    /// (`docs/wf-shape-code-design.md` §2, §8). `None` keeps both slots as
    /// they are, which is what every caller does with it.
    pub(crate) fn emit_wf_slots(
        &self,
        cx: &Cx,
        shape: &Type,
        arity: &Term,
        depth: u32,
    ) -> Option<(Rc<Type>, Rc<Term>)> {
        let shape = self.emit_ty(cx, shape, depth)?;
        let arity = self.respell_arity_at(cx, arity, depth + 1, 0).ok()??;
        Some((Rc::new(shape), Rc::new(arity)))
    }

    /// **The one emission chokepoint** for an annotation slot's spelling
    /// (`docs/annotation-component-respell-design.md` §2.5): the inline form
    /// where the decode handed back a code literal
    /// ([`crate::inductive::decode_deep`]), with registered sub-lowerings then
    /// respelled as references ([`Self::respell_ty_deep`]). `None` when both
    /// leave it alone, so the caller keeps its original and its sharing.
    ///
    /// Every constructor of a `Term`/`Type` **annotation** slot in the
    /// elaborator goes through this; a structural read keeps the inline copy
    /// (`docs/wf-shape-code-design.md` §4). `emission_walk` reports any slot
    /// this would still change.
    /// Use [`Self::annotation_type`] when writing an annotation and only use
    /// this optional form when the caller needs to distinguish a rewrite
    /// from an unchanged type (e.g. the emission walker or shared Rc slots).
    pub(crate) fn emit_ty(&self, cx: &Cx, ty: &Type, depth: u32) -> Option<Type> {
        self.emit_ty_in(cx, ty, depth, 0)
    }

    /// Default representation for an emitted annotation: closed references,
    /// parameterized instances and component respelling all go through the
    /// same policy. A declined rewrite keeps the original type, so callers
    /// cannot accidentally omit a naming route when choosing a fallback.
    ///
    /// `depth` counts binders beyond `cx`, exactly as in [`Self::emit_ty`].
    /// This is for annotations only: structural readers keep their original
    /// type, and Wf shape/arity slots use [`Self::emit_wf_slots`] together.
    pub(crate) fn annotation_type(&self, cx: &Cx, ty: &Type, depth: u32) -> Type {
        self.emit_ty(cx, ty, depth).unwrap_or_else(|| ty.clone())
    }

    /// [`Self::emit_ty`] for a slot living in an application's **scratch
    /// world** ([`Self::respell_ty_deep_in`]'s `scratch`).
    pub(crate) fn emit_ty_in(&self, cx: &Cx, ty: &Type, depth: u32, scratch: u32) -> Option<Type> {
        match crate::inductive::decode_deep(ty) {
            Some(inline) => Some(
                self.respell_ty_deep_in(cx, &inline, depth, scratch)
                    .unwrap_or(inline),
            ),
            None => self.respell_ty_deep_in(cx, ty, depth, scratch),
        }
    }

    /// [`Self::respell_ty`] applied **component-wise**
    /// (`docs/annotation-component-respell-design.md`): rebuild `ty` with
    /// every sub-type that *is* a registered declaration's lowering replaced
    /// by its `El (D#tycode^δ)` reference. `None` when nothing respelled, so
    /// callers keep their original (and its sharing) untouched.
    ///
    /// `depth` is how many binders `ty` sits under, past `cx` — the reference
    /// is minted against `cx` and shifted by `depth` plus however many binders
    /// the walk itself crosses (`Pi` cod, `Sigma` snd). Sound because a type
    /// that compares equal to the registry's **closed** copy is itself closed,
    /// so the shift only fixes the substitution tail's length, exactly as the
    /// `match`-motive respell's `shift_local(1)` does.
    ///
    /// Only **type** components are walked (`Pi`, `Sigma`, `Sum`, `Vec` elem,
    /// `Wf` shape, `Id`/`SEq` ty). Terms inside types — `Id` endpoints, `Vec`
    /// lengths, `El` codes — are not: annotations live in type slots, and the
    /// statement-side cascade (design §2.1) makes newly emitted terms small at
    /// the source. An `El`-headed reference declines at the top (`respell_ty`
    /// is idempotent) and has no walked components, so this is idempotent too.
    pub(crate) fn respell_ty_deep(&self, cx: &Cx, ty: &Type, depth: u32) -> Option<Type> {
        self.respell_ty_deep_in(cx, ty, depth, 0)
    }

    /// [`Self::respell_ty_deep`] for a type living in an application's
    /// **scratch world** (`application.rs`'s `apply_implicit`): `scratch`
    /// metavariables sit below the committed globals there, so every
    /// reference this mints is shifted past them, while the walk compares
    /// the components exactly as they are. A component that mentions a
    /// committed global compares unequal to the registry's copy in that
    /// world and simply declines — conservative, never a wrong reference.
    pub(crate) fn respell_ty_deep_in(
        &self,
        cx: &Cx,
        ty: &Type,
        depth: u32,
        scratch: u32,
    ) -> Option<Type> {
        let gdefs = self.types.gdefs();
        if !gdefs.has_ty_codes() && !gdefs.has_ty_code_fns() {
            return None;
        }
        self.respell_deep_at(cx, ty, depth, scratch)
    }

    fn respell_deep_at(&self, cx: &Cx, ty: &Type, d: u32, g: u32) -> Option<Type> {
        if let Some(r) = self.respell_ty_at(cx, ty, d, g) {
            return Some(r);
        }
        // One arm per former with type components; `or` keeps the sibling
        // untouched (sharing preserved) when only one side respells.
        let or = |orig: &Rc<Type>, new: Option<Type>| match new {
            Some(t) => Rc::new(t),
            None => Rc::clone(orig),
        };
        match ty {
            Type::Pi {
                dom_level,
                cod_level,
                dom,
                cod,
            } => {
                let ndom = self.respell_deep_at(cx, dom, d, g);
                let ncod = self.respell_deep_at(cx, cod, d + 1, g);
                if ndom.is_none() && ncod.is_none() {
                    return None;
                }
                Some(Type::Pi {
                    dom_level: dom_level.clone(),
                    cod_level: cod_level.clone(),
                    dom: or(dom, ndom),
                    cod: or(cod, ncod),
                })
            }
            Type::Sigma {
                fst_level,
                snd_level,
                fst,
                snd,
            } => {
                let nfst = self.respell_deep_at(cx, fst, d, g);
                let nsnd = self.respell_deep_at(cx, snd, d + 1, g);
                if nfst.is_none() && nsnd.is_none() {
                    return None;
                }
                Some(Type::Sigma {
                    fst_level: fst_level.clone(),
                    snd_level: snd_level.clone(),
                    fst: or(fst, nfst),
                    snd: or(snd, nsnd),
                })
            }
            Type::Sum {
                lhs_level,
                rhs_level,
                lhs,
                rhs,
            } => {
                let nl = self.respell_deep_at(cx, lhs, d, g);
                let nr = self.respell_deep_at(cx, rhs, d, g);
                if nl.is_none() && nr.is_none() {
                    return None;
                }
                Some(Type::Sum {
                    lhs_level: lhs_level.clone(),
                    rhs_level: rhs_level.clone(),
                    lhs: or(lhs, nl),
                    rhs: or(rhs, nr),
                })
            }
            Type::Vec { level, elem, len } => {
                let ne = self.respell_deep_at(cx, elem, d, g)?;
                Some(Type::Vec {
                    level: level.clone(),
                    elem: Rc::new(ne),
                    len: Rc::clone(len),
                })
            }
            Type::Wf {
                level,
                shape,
                arity,
            } => {
                // Reached only for a lowering the registry does not name
                // (parameterized, hence monomorphized — `Box<Ir>`), whose
                // *components* may still be registered lowerings.
                //
                // The arity goes with the shape, or neither goes: the arity
                // is a constant case tree whose `Case` annotations are the
                // shape's own components, and the kernel checks that tree
                // under `x : shape` at every occurrence of this `Wf` — so a
                // respelled shape over an inline arity is a *mismatch* the
                // kernel pays in the value domain, once per annotation, over
                // the whole inline component (a `List<Instruction>` value's
                // every `Wf` copy walked `⟦Instruction⟧`: 813 queries, 3.1 s
                // of the five-node FunctionIR/x86 module, measured
                // 2026-09-06; `issues/inductive-spelling-codes-nonrecursive.md`).
                // Spelled alike, the two compare syntactically. An arity of
                // any other form keeps the whole `Wf` inline, which is also
                // consistent.
                let ns = self.respell_deep_at(cx, shape, d, g)?;
                let na = self.respell_arity_at(cx, arity, d + 1, g).ok()??;
                Some(Type::Wf {
                    level: level.clone(),
                    shape: Rc::new(ns),
                    arity: Rc::new(na),
                })
            }
            Type::Id {
                level,
                ty,
                lhs,
                rhs,
            } => {
                let nt = self.respell_deep_at(cx, ty, d, g)?;
                Some(Type::Id {
                    level: level.clone(),
                    ty: Rc::new(nt),
                    lhs: Rc::clone(lhs),
                    rhs: Rc::clone(rhs),
                })
            }
            Type::SEq {
                level,
                ty,
                lhs,
                rhs,
            } => {
                let nt = self.respell_deep_at(cx, ty, d, g)?;
                Some(Type::SEq {
                    level: level.clone(),
                    ty: Rc::new(nt),
                    lhs: Rc::clone(lhs),
                    rhs: Rc::clone(rhs),
                })
            }
            _ => None,
        }
    }

    /// The arity term of a monomorphized `Wf` with the `Case` annotations of
    /// its constant case tree respelled by [`Self::respell_deep_at`] at the
    /// binder depth each sits under, so that `Wf(shape_e). arity_e` is one
    /// spelling end to end (the `Wf` arm above). `d` is the depth of the
    /// arity's own scope (the shape's binder included).
    ///
    /// `Ok(None)` when nothing respelled, `Err(())` when the term is not of
    /// the form `lower_arity` writes — a case tree over literals, `Succ`s and
    /// variables; a container's length projection is a `fst`/`snd` chain
    /// with its own Σ annotations and is declined rather than walked. Either
    /// way the caller keeps the whole `Wf` inline.
    fn respell_arity_at(&self, cx: &Cx, t: &Term, d: u32, g: u32) -> Result<Option<Term>, ()> {
        match t {
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
            } => {
                if **motive != Type::Nat {
                    return Err(());
                }
                let nl = self.respell_deep_at(cx, lhs, d, g);
                let nr = self.respell_deep_at(cx, rhs, d, g);
                let cl = self.respell_arity_at(cx, case_l, d + 1, g)?;
                let cr = self.respell_arity_at(cx, case_r, d + 1, g)?;
                if nl.is_none() && nr.is_none() && cl.is_none() && cr.is_none() {
                    return Ok(None);
                }
                Ok(Some(Term::Case {
                    lhs_level: lhs_level.clone(),
                    rhs_level: rhs_level.clone(),
                    motive_level: motive_level.clone(),
                    lhs: nl.map_or_else(|| Rc::clone(lhs), Rc::new),
                    rhs: nr.map_or_else(|| Rc::clone(rhs), Rc::new),
                    motive: Rc::clone(motive),
                    case_l: cl.map_or_else(|| Rc::clone(case_l), Rc::new),
                    case_r: cr.map_or_else(|| Rc::clone(case_r), Rc::new),
                    scrut: Rc::clone(scrut),
                }))
            }
            Term::Succ(p) => Ok(self
                .respell_arity_at(cx, p, d, g)?
                .map(|np| Term::Succ(Rc::new(np)))),
            Term::Var(_) | Term::Zero | Term::NatLit(_) => Ok(None),
            _ => Err(()),
        }
    }

    /// The inverse of [`Self::respell_arity_at`] for [`Self::unspell_ty_deep`]:
    /// every reference inside a case tree's annotations back to the registry's
    /// inline copy. `None` when nothing unspelled; a term that is not a case
    /// tree is left as it is (it carried no references in the first place).
    fn unspell_arity_deep(&self, len_at: u32, t: &Term) -> Option<Term> {
        match t {
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
            } => {
                let nl = self.unspell_ty_deep(len_at, lhs);
                let nr = self.unspell_ty_deep(len_at, rhs);
                let cl = self.unspell_arity_deep(len_at, case_l);
                let cr = self.unspell_arity_deep(len_at, case_r);
                if nl.is_none() && nr.is_none() && cl.is_none() && cr.is_none() {
                    return None;
                }
                Some(Term::Case {
                    lhs_level: lhs_level.clone(),
                    rhs_level: rhs_level.clone(),
                    motive_level: motive_level.clone(),
                    lhs: nl.map_or_else(|| Rc::clone(lhs), Rc::new),
                    rhs: nr.map_or_else(|| Rc::clone(rhs), Rc::new),
                    motive: Rc::clone(motive),
                    case_l: cl.map_or_else(|| Rc::clone(case_l), Rc::new),
                    case_r: cr.map_or_else(|| Rc::clone(case_r), Rc::new),
                    scrut: Rc::clone(scrut),
                })
            }
            Term::Succ(p) => self
                .unspell_arity_deep(len_at, p)
                .map(|np| Term::Succ(Rc::new(np))),
            _ => None,
        }
    }

    /// `El (D#tycode^δ)` back to the registry's inline `⟦D⟧`, at the head only
    /// and in the **current** Ψ world (goal and meta padding included, which is
    /// what [`Self::gen_def_of`] knows and [`Self::unspell_ty_deep`]'s explicit
    /// anchor deliberately does not assume).
    ///
    /// This is the elaborator's `whnf` of a reference
    /// (`docs/wf-shape-code-design.md` §3.3): δ+decode gives a type that is
    /// *convertible* to the registry's copy but spelled `Wf(El ⌜S⌝). n`, and
    /// the inline copy is the identity every structural reader and every
    /// use-site guard is written against. Closed by construction, so nothing
    /// is shifted.
    pub(crate) fn unspell_here(&self, ty: &Type) -> Option<Type> {
        self.unspell_here_in(ty, 0)
    }

    /// [`Self::unspell_here`] for a type living in an application's **scratch
    /// world** ([`Self::respell_ty_deep_in`]'s `scratch`), where `g`
    /// metavariables sit below the committed globals. The recognizer runs
    /// there too ([`Holes::see_through`]), and reading a reference at the
    /// wrong anchor would name a *different* definition rather than none, so
    /// the anchor is carried instead of assumed. At `g = 0` this is
    /// [`Self::gen_def_of`]'s own numbering, unchanged.
    pub(crate) fn unspell_here_in(&self, ty: &Type, g: u32) -> Option<Type> {
        let gdefs = self.types.gdefs();
        if !gdefs.has_ty_codes() && !gdefs.has_ty_code_fns() {
            return None;
        }
        let Type::El { tm, .. } = ty else { return None };
        let len = self.gen_ref_len(g);
        if let Term::GlobalTm { var, .. } = &**tm {
            return self.inline_of_code_key(self.code_key_at(len, *var)?);
        }
        // `El (app(D#tycode_fn^δ; ā))`, the applied spelling
        // (`docs/per-instantiation-type-codes-design.md` §4.2). Without this
        // arm a structural reader gets the kernel's lazy *decode* of the
        // instantiation instead of the registry's own copy, and every
        // use-site guard declines silently.
        let (GenDef::TyCodeFn(tag), args) = self.gen_app_of_at(len, tm)? else {
            return None;
        };
        let entry = self.ty_code_fn_now(tag, g)?;
        let args = self.inlined_arguments(&entry, &args, |el| self.unspell_here_in(el, g))?;
        Some(instance_of_template(&entry, &args, spine_frame(tm)?))
    }

    /// A code function's arguments with every **type** argument replaced by a
    /// code of the registry's own inline copy, so that substituting them into
    /// the template and decoding gives the inline lowering and not a spelling
    /// with a reference still inside it (§4.2). A value argument stands as it
    /// is. `None` when the spine is not saturated — a partial application
    /// names no type and this is not its inverse.
    fn inlined_arguments(
        &self,
        entry: &TyCodeFn,
        args: &[Rc<Term>],
        unspell: impl Fn(&Type) -> Option<Type>,
    ) -> Option<Vec<Rc<Term>>> {
        if args.len() != pi_arity(&entry.stmt) {
            return None;
        }
        Some(
            args.iter()
                .enumerate()
                .map(|(i, arg)| {
                    let Some(level) = entry.param_levels.get(i) else {
                        return Rc::clone(arg);
                    };
                    let el = Type::El {
                        level: level.clone(),
                        tm: Rc::clone(arg),
                    };
                    match unspell(&el).as_ref().and_then(crate::code::code_of) {
                        Some(code) => Rc::new(code),
                        None => Rc::clone(arg),
                    }
                })
                .collect(),
        )
    }

    /// Which definition a `GlobalVar` denotes in a type whose globals count
    /// from `len_at` — [`Self::unspell_ty_deep`]'s explicit anchor, which
    /// deliberately does not go through [`Self::gen_def_of`]'s padding.
    fn code_key_at(&self, len_at: u32, var: GlobalVar) -> Option<GenDef> {
        let abs = var.0.checked_add(1).and_then(|v| len_at.checked_sub(v))?;
        self.types.gdefs().key_for_abs(&abs).copied()
    }

    /// [`Self::gen_app_of`] at [`Self::unspell_ty_deep`]'s anchor.
    fn gen_app_of_at(&self, len_at: u32, t: &Term) -> Option<(GenDef, Vec<Rc<Term>>)> {
        let mut args = Vec::new();
        let mut cur = t;
        while let Term::App { fun, arg, .. } = cur {
            args.push(Rc::clone(arg));
            cur = fun;
        }
        if args.is_empty() {
            return None;
        }
        args.reverse();
        let Term::GlobalTm { var, .. } = cur else {
            return None;
        };
        Some((self.code_key_at(len_at, *var)?, args))
    }

    /// The registry's inline copy behind a code key that names a type
    /// occurrence — the whole lowering, a payload, or a suffix sum. `None`
    /// for every other key.
    fn inline_of_code_key(&self, key: GenDef) -> Option<Type> {
        let gdefs = self.types.gdefs();
        match key {
            GenDef::TyCode(tag) => gdefs.ty_code(&tag).map(|(inline, _)| (**inline).clone()),
            GenDef::PayloadCode(tag, k) => {
                gdefs.spine_codes(&tag).map(|codes| (*codes.ctors[k].0).clone())
            }
            GenDef::SuffixCode(tag, k) => {
                gdefs.spine_codes(&tag).map(|codes| (*codes.tails[k].0).clone())
            }
            _ => None,
        }
    }

    /// [`Self::unspell_here`] one level down a **sum**: the kernel's whnf of
    /// `El (D#tycode^δ)` for a flat declaration — or of any code that
    /// computes to one — stops at `Sum(El (D#payload₀^δ), El (D#suffix₀^δ))`,
    /// whose components are `El` of *neutral* codes that `decoded` rightly
    /// leaves alone, so `tag_of`/`spine` would not see the tag. Restoring the
    /// inline components at the `whnf` choke point keeps every structural
    /// reader spelling-insensitive, exactly as the top-level unspell does
    /// (docs/wf-shape-code-design.md §3.3). `None` when nothing unspelled.
    pub(crate) fn unspell_sum_components(&self, ty: &Type) -> Option<Type> {
        if !self.types.gdefs().has_spine_codes() {
            return None;
        }
        let Type::Sum {
            lhs_level,
            rhs_level,
            lhs,
            rhs,
        } = ty
        else {
            return None;
        };
        let nl = self.unspell_here(lhs);
        let nr = self.unspell_here(rhs);
        if nl.is_none() && nr.is_none() {
            return None;
        }
        Some(Type::Sum {
            lhs_level: lhs_level.clone(),
            rhs_level: rhs_level.clone(),
            lhs: nl.map_or_else(|| Rc::clone(lhs), Rc::new),
            rhs: nr.map_or_else(|| Rc::clone(rhs), Rc::new),
        })
    }

    /// `El (D#shape^δ)` back to the inline shape registered for a recursive
    /// declaration. This is the shape-slot counterpart of [`Self::unspell_here`]
    /// and exists for display only: a `Wf` annotation may carry the generated
    /// reference even though the nominal tag and constructor spine live in the
    /// inline shape (issues/display-inductive-type-arguments.md).
    pub(crate) fn unspell_shape_here(&self, ty: &Type) -> Option<Type> {
        if !self.types.gdefs().has_wf_slots() {
            return None;
        }
        let Type::El { tm, .. } = ty else { return None };
        let Term::GlobalTm { var, .. } = &**tm else {
            return None;
        };
        let GenDef::ShapeCode(tag) = self.gen_def_of(*var)? else {
            return None;
        };
        self.types
            .gdefs()
            .wf_slots(&tag)
            .map(|slots| (*slots.shape).clone())
    }

    /// [`Self::unspell_ty_deep`] anchored at the **current** world — goal and
    /// meta padding included, as [`Self::gen_def_of`] counts it — plus
    /// `scratch` metavariables.
    ///
    /// The spelling a structural reader that is *not* the `whnf` choke point
    /// needs: [`crate::unification::unify_ty`] is a syntactic congruence, so a
    /// reference standing where it expects a former hides the very structure
    /// an implicit is solved from (`docs/per-instantiation-type-codes-design.md`
    /// §4.2, amended 2026-09-10). One walk per unification attempt, `None`
    /// when nothing unspelled.
    pub(crate) fn unspell_deep_now(&self, ty: &Type, scratch: u32) -> Option<Type> {
        let gdefs = self.types.gdefs();
        if !gdefs.has_ty_codes() && !gdefs.has_ty_code_fns() {
            return None;
        }
        let len_at = self.psi.bindings.len() as u32
            + self.attempt.goal_arena.base()
            + self.meta_offset()
            + scratch;
        self.unspell_ty_deep(len_at, ty)
    }

    /// The **inverse** of [`Self::respell_ty_deep`], for the reflection
    /// boundary (`Elaborator::fn_type_code`): rebuild `ty` with every
    /// `El (D#tycode^δ)` reference replaced by the registry's inline lowering.
    /// `None` when nothing unspelled.
    ///
    /// Why it exists: a `meta` analyzer reads a fn's statement *as code*, and
    /// at layer m a global reference is syntax — `box (u^δ)` never unfolds,
    /// by design — so the reference spelling that shrinks every kernel
    /// checking of the statement makes it *opaque to analysis*. The
    /// opaque-globals round already drew the line ("unfolding-for-analysis
    /// happens at the reflection boundary"), and this is that unfolding for
    /// the generated codes: the registry's copy is exactly what δ+decode of
    /// the reference yields, so the analyzer sees the very type it saw
    /// before the respell existed. Closed types, so no depth bookkeeping.
    ///
    /// `len_at` anchors the reference resolution: the Ψ length the type's
    /// `GlobalVar`s count from — the *current* length for a type rescoped by
    /// `shift_global` (`fn_type_code`), the binding's own `abs` for a raw
    /// prefix-scoped statement (`sig_peel` over `global_body`). Goal and
    /// meta padding never applies to either, which is why this does not go
    /// through [`Self::gen_def_of`].
    pub(crate) fn unspell_ty_deep(&self, len_at: u32, ty: &Type) -> Option<Type> {
        let gdefs = self.types.gdefs();
        if !gdefs.has_ty_codes() && !gdefs.has_ty_code_fns() {
            return None;
        }
        if let Type::El { tm, .. } = ty
            && let Term::GlobalTm { var, .. } = &**tm
            && let Some(key) = self.code_key_at(len_at, *var)
            && let Some(inline) = self.inline_of_code_key(key)
        {
            return Some(inline);
        }
        // The applied spelling, at the reflection boundary (§4.2): a statement
        // carrying `El (app(D#tycode_fn^δ; ā))` hands a `meta` analyzer the
        // inline instantiation, exactly as it hands it the inline `⟦D⟧` behind
        // a closed code.
        if let Type::El { tm, .. } = ty
            && let Some((GenDef::TyCodeFn(tag), args)) = self.gen_app_of_at(len_at, tm)
            && let Some(entry) = self.ty_code_fn_at(tag, len_at)
            && let Some(args) =
                self.inlined_arguments(&entry, &args, |el| self.unspell_ty_deep(len_at, el))
            && let Some(frame) = spine_frame(tm)
        {
            return Some(instance_of_template(&entry, &args, frame));
        }
        let or = |orig: &Rc<Type>, new: Option<Type>| match new {
            Some(t) => Rc::new(t),
            None => Rc::clone(orig),
        };
        match ty {
            Type::Pi {
                dom_level,
                cod_level,
                dom,
                cod,
            } => {
                let ndom = self.unspell_ty_deep(len_at, dom);
                let ncod = self.unspell_ty_deep(len_at, cod);
                if ndom.is_none() && ncod.is_none() {
                    return None;
                }
                Some(Type::Pi {
                    dom_level: dom_level.clone(),
                    cod_level: cod_level.clone(),
                    dom: or(dom, ndom),
                    cod: or(cod, ncod),
                })
            }
            Type::Sigma {
                fst_level,
                snd_level,
                fst,
                snd,
            } => {
                let nfst = self.unspell_ty_deep(len_at, fst);
                let nsnd = self.unspell_ty_deep(len_at, snd);
                if nfst.is_none() && nsnd.is_none() {
                    return None;
                }
                Some(Type::Sigma {
                    fst_level: fst_level.clone(),
                    snd_level: snd_level.clone(),
                    fst: or(fst, nfst),
                    snd: or(snd, nsnd),
                })
            }
            Type::Sum {
                lhs_level,
                rhs_level,
                lhs,
                rhs,
            } => {
                let nl = self.unspell_ty_deep(len_at, lhs);
                let nr = self.unspell_ty_deep(len_at, rhs);
                if nl.is_none() && nr.is_none() {
                    return None;
                }
                Some(Type::Sum {
                    lhs_level: lhs_level.clone(),
                    rhs_level: rhs_level.clone(),
                    lhs: or(lhs, nl),
                    rhs: or(rhs, nr),
                })
            }
            Type::Vec { level, elem, len } => {
                let ne = self.unspell_ty_deep(len_at, elem)?;
                Some(Type::Vec {
                    level: level.clone(),
                    elem: Rc::new(ne),
                    len: Rc::clone(len),
                })
            }
            Type::Wf {
                level,
                shape,
                arity,
            } => {
                let ns = self.unspell_ty_deep(len_at, shape);
                let na = self.unspell_arity_deep(len_at, arity);
                if ns.is_none() && na.is_none() {
                    return None;
                }
                Some(Type::Wf {
                    level: level.clone(),
                    shape: ns.map_or_else(|| Rc::clone(shape), Rc::new),
                    arity: na.map_or_else(|| Rc::clone(arity), Rc::new),
                })
            }
            Type::Id {
                level,
                ty,
                lhs,
                rhs,
            } => {
                let nt = self.unspell_ty_deep(len_at, ty)?;
                Some(Type::Id {
                    level: level.clone(),
                    ty: Rc::new(nt),
                    lhs: Rc::clone(lhs),
                    rhs: Rc::clone(rhs),
                })
            }
            Type::SEq {
                level,
                ty,
                lhs,
                rhs,
            } => {
                let nt = self.unspell_ty_deep(len_at, ty)?;
                Some(Type::SEq {
                    level: level.clone(),
                    ty: Rc::new(nt),
                    lhs: Rc::clone(lhs),
                    rhs: Rc::clone(rhs),
                })
            }
            _ => None,
        }
    }

    /// `D#fam := λ(i : I). elim(…; i)`, a route-1 family function (design §6).
    /// Only an **unparameterized** declaration gets one, for
    /// [`Elaborator::mu_def`]'s reason: the family's branches mention the
    /// argument types, which are monomorphized per instantiation.
    fn register_fam(&mut self, ind: &Rc<Inductive>, span: Span) {
        if !ind.params.is_empty() || !ind.valparams.is_empty() {
            return;
        }
        let key = GenDef::Fam(ind.tag);
        if self.types.gdefs().contains_key(&key) {
            return;
        }
        let Ok((ty, level, body, l, ilvl)) = self.fam_def(ind, span) else {
            return;
        };
        if self
            .push_gen_def(key, &ind.name, ty, level, body, span)
            .is_ok()
        {
            self.semantic_commit_gen_fam_levels(ind.tag, l, ilvl);
        }
    }

    /// §7.1's tag predicates and §7.2's child projections, per index
    /// constructor. Memoized on the *index* type's tag, so the second family
    /// over one index pays nothing.
    fn register_index_devices(&mut self, iind: &Rc<Inductive>, span: Span) {
        let n = iind.ctors.len();
        for k in 0..n {
            let key = GenDef::IdxTag(iind.tag, k);
            if !self.types.gdefs().contains_key(&key) {
                if let Ok((ty, lvl, body)) = self.tag_pred_def(iind, k, span) {
                    let _ = self.push_gen_def(key, &iind.name, ty, lvl, body, span);
                }
            }
            // A child projection only exists at a recursive index type: a flat
            // index constructor has no child to project.
            if !iind.recursive {
                continue;
            }
            for t in 0..iind.ctors[k].arity() {
                let key = GenDef::IdxChild(iind.tag, k, t);
                if self.types.gdefs().contains_key(&key) {
                    continue;
                }
                if let Ok((ty, lvl, body)) = self.child_proj_def(iind, k, t, span) {
                    let _ = self.push_gen_def(key, &iind.name, ty, lvl, body, span);
                }
            }
        }
    }

    fn register_mu(&mut self, ind: &Rc<Inductive>, span: Span) -> R<()> {
        let key = GenDef::Mu(ind.tag);
        if self.types.gdefs().contains_key(&key) {
            return Ok(());
        }
        let (ty, lvl, body) = self.mu_def(ind, span)?;
        self.push_gen_def(key, &ind.name, ty, lvl, body, span)
    }

    /// Kernel-check and push. The gate is the same one a `fn` passes
    /// (`elab_decl_inner`): statement at layer p, body at layer c, both in the
    /// empty local context — so a definition is a checked term like any other
    /// bodied global and its transparency is the kernel's layer-indexed rule,
    /// not anything configured here.
    fn push_gen_def(
        &mut self,
        key: GenDef,
        owner: &str,
        ty: Type,
        level: Level,
        body: Term,
        span: Span,
    ) -> R<()> {
        let empty = LocalCtx::nil();
        let name = key.name(owner);
        // Generated-declaration emission, as its own column: a declaration's
        // row says how much of it was spent minting the definitions it needed
        // (`docs/instrumentation-design.md` §5). The kernel gate below keeps
        // its own bracket, and the exclusive rule keeps the two apart.
        crate::stats::count(crate::stats::Counter::GendefsPushed);
        let _phase = crate::stats::guard(crate::stats::Timer::Gendefs);
        {
            // A generated definition faces the same gate as a `fn` and the same
            // oracle (`gate.rs`): it is an ordinary bodied binding, so it gets
            // its own cache identity rather than riding its declaration
            // (docs/cache-v1-design.md §4).
            let item = crate::gate::GateItem {
                name: &name,
                ctx: &empty,
                ty: &ty,
                level: &level,
                body: &body,
                opaque: false,
                layer: Layer::Code,
                lands_in_psi: true,
            };
            let admitted = self
                .gate
                .as_ref()
                .is_some_and(|g| g.admits(&self.psi, &item));
            drop(item);
            if !admitted {
                // `stats::time_kernel`, as at the `elab_decl_inner` gate
                // (lib.rs) and the `Layer::Meta` one (quote.rs): the frontend
                // suite's `kernel` phase covers *every* finished declaration,
                // and a generated definition is one
                // (issues/gendef-gate-untimed.md).
                crate::stats::time_kernel(|| {
                    self.kernel_check_type(&self.psi, Layer::Prog, &empty, &ty, &level)
                })
                .map_err(|err| crate::ElabError::Kernel {
                    decl: name.clone(),
                    span,
                    err,
                    note: None,
                })?;
                if self.gate_is_inline() {
                    let item = crate::gate::GateItem {
                        name: &name,
                        ctx: &empty,
                        ty: &ty,
                        level: &level,
                        body: &body,
                        opaque: false,
                        layer: Layer::Code,
                        lands_in_psi: true,
                    };
                    // The serial replay's reused verdict, if this obligation
                    // is the one a worker of the discarded pass already
                    // answered (`docs/parallel-kernel-gate-design.md` §5.2).
                    let verdict = match self.kernel_replay.reuse(
                        self.psi.bindings.len(),
                        self.fuel,
                        &item,
                    ) {
                        Some(verdict) => verdict,
                        None => crate::stats::time_kernel(|| {
                            self.kernel_check_term(
                                &self.psi, Layer::Code, &empty, &body, &ty, &level,
                            )
                        }),
                    };
                    verdict.map_err(|err| crate::ElabError::Kernel {
                        decl: name.clone(),
                        span,
                        err,
                        note: None,
                    })?;
                    if let Some(g) = self.gate.as_ref() {
                        g.accepted(&self.psi, &item);
                    }
                } else {
                    // The body is committed to Ψ below and the proof is
                    // queued; the module joins before it is accepted
                    // (`docs/parallel-kernel-gate-design.md` §5).
                    self.defer_kernel_term(
                        &name, span, &empty, &ty, &level, &body, false, Layer::Code, true,
                    );
                }
            }
        }
        let abs = self.psi.bindings.len() as u32;
        self.psi.push(GlobalBinding::defined_tm(
            empty,
            Layer::Code,
            Rc::new(ty),
            level,
            Rc::new(body),
        ));
        self.semantic_commit_gen_def(key, abs);
        self.refresh_delta_psi();
        Ok(())
    }

    // -- reference and read-back --------------------------------------------

    /// `u^δ` for a registered definition, out of the current `Γ`. `None` when
    /// the definition was not registered, which is every emission site's cue
    /// to inline instead.
    pub(crate) fn gen_ref(&self, cx: &Cx, key: GenDef) -> Option<Term> {
        self.gen_ref_deeper(cx, key, 0)
    }

    /// [`Self::gen_ref`] for an occurrence sitting `extra` binders past `cx` —
    /// the substitution tail's length is the only thing that moves, since the
    /// definition is closed and its Ψ index is context-independent. One caller:
    /// the arity slot, which is always read under the shape's binder.
    fn gen_ref_deeper(&self, cx: &Cx, key: GenDef, extra: u32) -> Option<Term> {
        let abs = *self.types.gdefs().abs_for(&key)?;
        let len = self.psi.bindings.len() as u32;
        // Goals sit innermost, exactly as in `resolve` — and so do a
        // `meta fn`'s Ψ-extending binders (`Ctx`, `lib.rs`'s `meta_pushed`),
        // which `resolve` has always offset by and this did not. Latent until
        // 2026-08-12: nothing emitted a generated-definition reference from
        // inside a meta body before the tier-1 motive respell did, and the
        // symptom was a kernel `WrongGlobalBinding` naming the context binder
        // (`crates/elab/tests/certgen_route1_spike.rs`'s meta walk over `Ir`).
        // The two paddings never combine: goals are refused inside a `meta fn`.
        let var = GlobalVar(len - 1 - abs + self.attempt.goal_arena.base() + self.meta_offset());
        Some(Term::GlobalTm {
            var,
            subst: LocalSubst {
                tail: SubstTail::Empty {
                    len: cx.gamma.entries.len() as u32 + extra,
                    base: cx.gamma.base,
                },
                terms: vec![],
            },
        })
    }

    /// `El (code^δ)` — the **type** occurrence of a registered code
    /// definition (`docs/family-type-code-defs-design.md` §1.3): composition
    /// of the existing `Type::El` former with [`Self::gen_ref`]. `level` is
    /// the coded type's own level (`El l ν` with `ν : Ty l`). `None` when the
    /// definition was not registered — every emission site's cue to inline.
    pub(crate) fn gen_type_ref(&self, cx: &Cx, key: GenDef, level: &Level) -> Option<Type> {
        self.gen_ref(cx, key).map(|tm| Type::El {
            level: level.clone(),
            tm: Rc::new(tm),
        })
    }

    /// The inverse of [`Self::gen_ref`]'s numbering: which definition, if any,
    /// a `GlobalVar` occurring in a term denotes. This is the whole of the
    /// recognizers' new key — `forded_of` asks "is the head of this `μ`
    /// position *the* `μ_D`", not "does it have `μ`'s shape".
    pub(crate) fn gen_def_of(&self, var: GlobalVar) -> Option<GenDef> {
        let len = self.psi.bindings.len() as u32;
        // Fully checked: a `GlobalVar` reaching here can be anything the term
        // it came out of contains, including one that is out of scope.
        let abs = len
            .checked_add(self.attempt.goal_arena.base())?
            .checked_add(self.meta_offset())?
            .checked_sub(var.0.checked_add(1)?)?;
        self.types.gdefs().key_for_abs(&abs).copied()
    }

    /// How far a `meta fn`'s Ψ-extending binders push the committed bindings
    /// out, mirroring `resolve`'s `meta_off` (`lib.rs`). Zero everywhere else.
    fn meta_offset(&self) -> u32 {
        self.meta_pushed.borrow().len() as u32
    }

    /// Whether `t` is exactly `u^δ` for the definition `key` — the head test
    /// the recognizers use.
    pub(crate) fn is_gen_ref(&self, t: &Term, key: GenDef) -> bool {
        matches!(t, Term::GlobalTm { var, .. } if self.gen_def_of(*var) == Some(key))
    }

    /// The definition and arguments of an application spine `u^δ ā`, when its
    /// head is a registered definition — the application-aware sibling of
    /// [`Self::is_gen_ref`]/[`Self::gen_def_of`]
    /// (`docs/per-instantiation-type-codes-design.md` §4.2). `None` for
    /// anything whose head is not a registered global, the bare reference
    /// included (that is [`Self::gen_def_of`]'s business, and this returning
    /// `Some` with no arguments would make every caller check the length).
    pub(crate) fn gen_app_of(&self, t: &Term) -> Option<(GenDef, Vec<Rc<Term>>)> {
        let mut args = Vec::new();
        let mut cur = t;
        while let Term::App { fun, arg, .. } = cur {
            args.push(Rc::clone(arg));
            cur = fun;
        }
        if args.is_empty() {
            return None;
        }
        args.reverse();
        let Term::GlobalTm { var, .. } = cur else {
            return None;
        };
        Some((self.gen_def_of(*var)?, args))
    }

    /// A non-dependent application of a registered definition. `dom`/`cod` are
    /// the annotations the kernel's `App` carries; both are scoped where `arg`
    /// is, and `cod` is weakened under the (vacuous) binder for it.
    pub(crate) fn gen_app(
        fun: Term,
        dom_level: &Level,
        cod_level: &Level,
        dom: &Type,
        cod: &Type,
        arg: Term,
    ) -> Term {
        Term::App {
            fun: Rc::new(fun),
            dom_level: dom_level.clone(),
            cod_level: cod_level.clone(),
            dom: Rc::new(dom.clone()),
            cod: Rc::new(cod.shift_local(1)),
            arg: Rc::new(arg),
        }
    }

    // -- the bodies ---------------------------------------------------------

    /// `μ_D = λ(s : ⟦Skel⟧). μ-node[s]`, its type and level (§5).
    ///
    /// **Boundary.** Only a forded declaration with no type parameters gets
    /// one. `μ`'s body mentions the skeleton's lowering, which is
    /// monomorphized at each instantiation (`Cx::tyvars`), so a parameterized
    /// family's `μ` is not one closed term but one per instantiation — and a
    /// definition is registered at *declaration* time, where the
    /// instantiations are not yet known. Abstracting over the parameter would
    /// need a Π over `Type` in the definition's own statement and a
    /// `Type`-argument spine at every reference; that is a scheme change, not
    /// a registration detail. Parameterized forded families therefore keep
    /// today's inlined `μ` verbatim.
    fn mu_def(&self, ind: &Rc<Inductive>, span: Span) -> R<(Type, Level, Term)> {
        if !ind.params.is_empty() || !ind.valparams.is_empty() {
            return crate::err(
                "internal: a parameterized forded family keeps its inlined μ",
                span,
            );
        }
        let cx = Cx::empty();
        let skel = ind
            .skel
            .as_ref()
            .expect("a forded declaration has a skeleton");
        let (skel_ty, l) = self.lower_instance(&cx, skel, &[], &[], span)?;
        let (ity, ilvl) = self.index_type_of(&cx, ind, span)?;
        let node = self.build_mu(&cx, ind, skel, &skel_ty, &l, &ity, &ilvl, span)?;
        let body = Term::Lam {
            dom_level: l.clone(),
            cod_level: ilvl.clone(),
            dom: Rc::new(skel_ty.clone()),
            body: Rc::new(
                crate::indexed::set_scrut(&node.shift_local(1), Rc::new(Term::Var(LocalVar(0))))
                    .ok_or_else(|| crate::ElabError::Elab {
                        msg: "internal: a μ node has a scrutinee slot".into(),
                        span,
                    })?,
            ),
        };
        let ty = Type::Pi {
            dom_level: l.clone(),
            cod_level: ilvl.clone(),
            dom: Rc::new(skel_ty),
            cod: Rc::new(ity.shift_local(1)),
        };
        Ok((ty, Level::max(l, ilvl), body))
    }

    /// `D#fam = λ(i : I). elim(…; i) : Π(i : I). Ty l`, its statement, its
    /// level, and the two levels an occurrence needs (design §6).
    ///
    /// The two passes are [`Elaborator::lower_indexed_instance`]'s: the family
    /// is built once at a placeholder level to *read* `l` off its branches,
    /// then rebuilt at `l`. Both passes run at a closed placeholder index,
    /// because the λ's binder replaces the scrutinee afterwards — the same
    /// build-then-`set_scrut` motion [`Elaborator::mu_def`] uses.
    fn fam_def(&self, ind: &Inductive, span: Span) -> R<(Type, Level, Term, Level, Level)> {
        let cx = Cx::empty();
        let (ity, ilvl) = self.index_type_of(&cx, ind, span)?;
        let (_, l) = self.build_family(&cx, ind, &[], &Level::Zero, Term::Zero, span)?;
        let (fam, _) = self.build_family(&cx, ind, &[], &l, Term::Zero, span)?;
        let cod_level = Level::succ(l.clone());
        let body = Term::Lam {
            dom_level: ilvl.clone(),
            cod_level: cod_level.clone(),
            dom: Rc::new(ity.clone()),
            body: Rc::new(
                crate::indexed::set_scrut(&fam.shift_local(1), Rc::new(Term::Var(LocalVar(0))))
                    .ok_or_else(|| crate::ElabError::Elab {
                        msg: "internal: a family node has a scrutinee slot".into(),
                        span,
                    })?,
            ),
        };
        // `Ty l` binds nothing, so the codomain needs no shift under the Π.
        let ty = Type::Pi {
            dom_level: ilvl.clone(),
            cod_level: cod_level.clone(),
            dom: Rc::new(ity),
            cod: Rc::new(Type::Ty(l.clone())),
        };
        let level = Level::max(ilvl.clone(), cod_level);
        Ok((ty, level, body, l, ilvl))
    }

    /// `El l (D#fam^δ i)` — a route-1 family occurrence at `idx`, with the
    /// declaration's own level (design §6). `None` when no definition was
    /// registered, which is the emission site's cue to inline.
    pub(crate) fn fam_occurrence(
        &self,
        cx: &Cx,
        ind: &Inductive,
        idx: &Term,
        span: Span,
    ) -> Option<(Type, Level)> {
        let (l, ilvl) = self.types.gdefs().fam_levels(&ind.tag)?.clone();
        let fun = self.gen_ref(cx, GenDef::Fam(ind.tag))?;
        // The Π's domain is an annotation like any other, so it takes the
        // index type's own code reference where one exists (design §1.4).
        let dom = match ind.index_ty.as_ref() {
            Some(IdxTy::Decl(iind)) => self
                .gen_type_ref(cx, GenDef::IdxCode(iind.tag), &ilvl)
                .or_else(|| self.index_type_of(cx, ind, span).ok().map(|(t, _)| t))?,
            _ => Type::Nat,
        };
        let tm = Self::gen_app(
            fun,
            &ilvl,
            &Level::succ(l.clone()),
            &dom,
            &Type::Ty(l.clone()),
            idx.clone(),
        );
        Some((
            Type::El {
                level: l.clone(),
                tm: Rc::new(tm),
            },
            l,
        ))
    }

    /// `is_k = λ(z : I). Case-on-tag(z) { c_k ↦ ⌜Unit⌝ ; _ ↦ ⌜Empty⌝ }` (§7.1),
    /// at type `I → Type⁰`.
    fn tag_pred_def(&self, iind: &Rc<Inductive>, k: usize, span: Span) -> R<(Type, Level, Term)> {
        let cx = Cx::empty();
        let (ity, ilvl) = self.lower_instance(&cx, iind, &[], &[], span)?;
        let spine = self.spine(&ity, &ilvl, iind.ctors.len(), span)?;
        let ty0 = Type::Ty(Level::Zero);
        let l1 = Level::succ(Level::Zero);
        let mut zcx = cx.clone();
        zcx.push("#z".into(), ity.clone(), ilvl.clone());
        // `spine`/`ity` are read back in the *base* context (empty here) and
        // `d0` counts the binders pushed since — one, the λ's.
        let node = if iind.recursive {
            self.const_elim_wf(
                &zcx,
                iind,
                &ity,
                &spine,
                &ty0,
                &l1,
                Rc::new(Term::Var(LocalVar(0))),
                &ConstBody::TagCode(k),
                1,
                span,
            )?
        } else {
            self.const_case_tree(
                &zcx,
                &spine,
                iind.ctors.len(),
                &ty0,
                &l1,
                Rc::new(Term::Var(LocalVar(0))),
                &ConstBody::TagCode(k),
                0,
                1,
                span,
            )?
        };
        let body = Term::Lam {
            dom_level: ilvl.clone(),
            cod_level: l1.clone(),
            dom: Rc::new(ity.clone()),
            body: Rc::new(node),
        };
        let ty = Type::Pi {
            dom_level: ilvl.clone(),
            cod_level: l1.clone(),
            dom: Rc::new(ity),
            cod: Rc::new(ty0),
        };
        Ok((ty, Level::max(ilvl, l1), body))
    }

    /// `proj_{k,t} = λ(d : I). λ(z : I). elim_Wf(z) { c_k ↦ nth_t ; _ ↦ d }`
    /// (§7.2), at type `I → I → I`.
    ///
    /// The **default is abstracted** rather than baked in: it is the one thing
    /// that varies per use site (`forded_inv_branch` passes the bound `z`),
    /// and abstracting it is what lets one definition serve every occurrence.
    fn child_proj_def(
        &self,
        iind: &Rc<Inductive>,
        k: usize,
        t: usize,
        span: Span,
    ) -> R<(Type, Level, Term)> {
        let cx = Cx::empty();
        let (ity, ilvl) = self.lower_instance(&cx, iind, &[], &[], span)?;
        let mut zcx = cx.clone();
        zcx.push("#default".into(), ity.clone(), ilvl.clone());
        zcx.push("#z".into(), ity.clone(), ilvl.clone());
        let node = self.child_projection(
            &zcx,
            iind,
            &ity,
            &ilvl,
            k,
            t,
            Rc::new(Term::Var(LocalVar(1))),
            Term::Var(LocalVar(0)),
            span,
        )?;
        let body = Term::Lam {
            dom_level: ilvl.clone(),
            cod_level: ilvl.clone(),
            dom: Rc::new(ity.clone()),
            body: Rc::new(Term::Lam {
                dom_level: ilvl.clone(),
                cod_level: ilvl.clone(),
                dom: Rc::new(ity.clone()),
                body: Rc::new(node),
            }),
        };
        let ty = Type::Pi {
            dom_level: ilvl.clone(),
            cod_level: ilvl.clone(),
            dom: Rc::new(ity.clone()),
            cod: Rc::new(Type::Pi {
                dom_level: ilvl.clone(),
                cod_level: ilvl.clone(),
                dom: Rc::new(ity.clone()),
                cod: Rc::new(ity),
            }),
        };
        Ok((ty, ilvl, body))
    }
}

// -- scope moves for the record projections ---------------------------------
//
// A projection definition is closed and its codomain is scoped in the
// one-entry context `·, v : ⟦D⟧`, while a use site lives in some `Γ`. All
// three moves below are one `LocalSubst` into that context — written out
// rather than reached through `shift_local`, which would leave the tail's
// *base* at `·` and so cannot re-scope into a `Γ` standing on a context
// variable (`issues/theorem-field-projection-oom.md`).

/// A type scoped in `·`, seen in `Γ`.
fn weaken(ty: &Type, gamma: &LocalCtx) -> Type {
    ty.apply_local(&LocalSubst {
        tail: SubstTail::Empty {
            len: gamma.entries.len() as u32,
            base: gamma.base,
        },
        terms: vec![],
    })
}

/// `El (D#famⱼ^δ v x)` with `x` instantiated at `arg` — the tail family's
/// annotation applied, which is the type of the `snd` node at that entry.
/// Both are scoped in `Γ = ·, v`.
fn instantiate_fam(fam: &Rc<Type>, arg: &Rc<Term>, gamma: &LocalCtx) -> Type {
    fam.apply_local(&LocalSubst::id(gamma).extended(Rc::clone(arg)))
}

/// `head` applied to `args`, with every `App`'s annotations read off `stmt` —
/// the head's own **closed** `Π` — as the walk instantiates it. That is where
/// a dependent telescope's later domains come from, and it is the one place
/// the shape of a definition's statement is turned into a spine
/// (`docs/per-instantiation-type-codes-design.md` §13).
///
/// `None` unless the statement has a `Π` for **every** argument: a spine
/// short of the definition's own binders would come back as a partial
/// application, and every caller here means to hand its own caller a value.
///
/// The check is `<`, not `!=`, and the difference is a defect the fix pass
/// paid for: what a caller saturates is the definition's *telescope*, whose
/// length it knows, while `pi_arity` counts every `Π` in the statement —
/// including the ones a **function-typed field** contributes to a
/// `D#projⱼ : Π Θ. Π(v : R). Fⱼ` whose `Fⱼ` is itself an arrow. With `!=`
/// every such field declined at registration, which sent a record whose
/// fields are laws (`repr`'s `abs`, `Monoid`'s `op`) back to
/// `project_field`'s exponential walk and aborted two test binaries on the
/// allocator. The loop below already refuses a spine the statement cannot
/// take, which is the guard that was meant.
fn saturate(
    gamma: &LocalCtx,
    head: Term,
    stmt: &Type,
    args: &[Rc<Term>],
) -> Option<(Term, Type, Level)> {
    if pi_arity(stmt) < args.len() {
        return None;
    }
    let mut cur = weaken(stmt, gamma);
    let mut head = head;
    let mut level = None;
    for arg in args {
        let Type::Pi {
            dom_level,
            cod_level,
            dom,
            cod,
        } = cur
        else {
            return None;
        };
        head = Term::App {
            fun: Rc::new(head),
            dom_level,
            cod_level: cod_level.clone(),
            dom,
            cod: Rc::clone(&cod),
            arg: Rc::clone(arg),
        };
        cur = cod.apply_local(&LocalSubst::id(gamma).extended(Rc::clone(arg)));
        level = Some(cod_level);
    }
    Some((head, cur, level?))
}

/// A definition's statement wrapped in the declaration's telescope:
/// `Π(θ₀)…(θ_{t−1}). inner`, each binder scoped under the ones before it, and
/// the whole `Π`'s level with it (§13).
fn wrap_tel(tel: &[(Type, Level)], inner: Type, inner_level: Level) -> (Type, Level) {
    let mut ty = inner;
    let mut level = inner_level;
    for (dom, dom_level) in tel.iter().rev() {
        ty = Type::Pi {
            dom_level: dom_level.clone(),
            cod_level: level.clone(),
            dom: Rc::new(dom.clone()),
            cod: Rc::new(ty),
        };
        level = Level::max(dom_level.clone(), level).normalize().canonical();
    }
    (ty, level)
}

/// [`wrap_tel`] for the body: `λ(θ₀)…(θ_{t−1}). inner`, with the codomain
/// levels the `Π` it inhabits carries.
fn wrap_tel_lam(tel: &[(Type, Level)], inner: Term, inner_level: Level) -> Term {
    let mut body = inner;
    let mut level = inner_level;
    for (dom, dom_level) in tel.iter().rev() {
        body = Term::Lam {
            dom_level: dom_level.clone(),
            cod_level: level.clone(),
            dom: Rc::new(dom.clone()),
            body: Rc::new(body),
        };
        level = Level::max(dom_level.clone(), level).normalize().canonical();
    }
    body
}

/// The telescope's own binders, as the arguments a definition registered over
/// it is applied to from **inside** its own scope: in `·, θ̄, x₁…x_k` the
/// telescope entry `i` is `Var(t − 1 − i + k)` (§13).
fn tel_self_args(t: usize, extra: usize) -> Vec<Rc<Term>> {
    (0..t + extra)
        .rev()
        .map(|i| Rc::new(Term::Var(LocalVar(i as u32))))
        .collect()
}

/// Move a telescope one Ψ binding out, after a push
/// ([`Elaborator::register_rec_projs`] keeps it across every one of them).
fn shift_tel(tel: &mut [(Type, Level)]) {
    for (ty, _) in tel.iter_mut() {
        *ty = ty.shift_global(1);
    }
}

