//! Core syntax of DeLaM (docs/delam/04, §Syntax and §Meta-programming
//! Modalities), in fully explicit, de Bruijn form.
//!
//! Three independent variable namespaces, each with its own de Bruijn index
//! space (a binder in one never shifts the others):
//!
//! - [`LocalVar`]  — into the local context Γ (`x`, `y`),
//! - [`GlobalVar`] — into the global context Ψ (`g`, `U`, `u` share one
//!   index space; the binding form at the index determines the kind),
//! - [`crate::level::UnivVar`] — into the universe context L (`ℓ`).
//!
//! Types and terms are separate sorts (Tarski-style universes); term-level
//! *encodings* of types (`TmNat`, `TmPi`, `TmTy`) decode through [`Type::El`].
//! All elimination forms carry their full annotations — the verbosity is
//! deliberate (ch. 04): annotations are sub-structures so the code recursors
//! can recurse into them.

use std::hash::{Hash, Hasher};
use std::sync::Arc as Rc;

use crate::layer::Layer;
use crate::level::Level;

/// de Bruijn index into the local context Γ. 0 is the innermost binder.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct LocalVar(pub u32);

/// de Bruijn index into the global context Ψ. 0 is the innermost binding.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct GlobalVar(pub u32);

/// Types `S, T` (sort `Typ`).
#[derive(Clone, PartialEq, Eq)]
pub enum Type {
    /// `Nat`.
    Nat,
    /// `Π^{l,l'}(x : S). T`; `cod` binds one local variable.
    Pi {
        dom_level: Level,
        cod_level: Level,
        dom: Rc<Type>,
        cod: Rc<Type>,
    },
    /// `Ty l`, the universe at level `l` (lives at `1 + l`).
    Ty(Level),
    /// `ΠΠ ℓ⃗. T` — universe-polymorphic function type; binds `num_vars ≥ 1`
    /// universe variables in both `level` and `body`. Lives at `ω`; layer m
    /// only.
    UPi {
        num_vars: u32,
        level: Level,
        body: Rc<Type>,
    },
    /// `El^l t` — decode the encoding `t : Ty l` into a type.
    El { level: Level, tm: Rc<Term> },
    /// `Id^l (S; t; u)` — identity type over `S : Typ` at level `l`;
    /// `lhs`, `rhs : S`. Extension beyond DeLaM ch. 04 (see
    /// issues/kernel-v1-extensions.md).
    Id {
        level: Level,
        ty: Rc<Type>,
        lhs: Rc<Term>,
        rhs: Rc<Term>,
    },
    /// `sEq^l(I; a; b)` — strict (definitionally proof-irrelevant) equality
    /// over `I : Typ` at level `l`; `lhs`, `rhs : I`. Field-for-field the
    /// shape of [`Type::Id`], deliberately: `sEq` is `Id` minus proof
    /// relevance plus strictness. Any two terms at this type are convertible
    /// (`conv.rs` irrelevance arm); eliminated by [`Term::Transp`], whose
    /// strip rule is what makes the equality strict. Extension beyond DeLaM
    /// ch. 04 (docs/sprop-design.md §2.1). Admitted at layer c like every
    /// other former: it has its own code branches (`ty_seq`/`tm_seq`).
    SEq {
        level: Level,
        ty: Rc<Type>,
        lhs: Rc<Term>,
        rhs: Rc<Term>,
    },
    /// `sEmpty^l` — the strict (definitionally irrelevant) empty type at
    /// level `l`; no inhabitants, eliminated **anywhere** by
    /// [`Term::ElimSEmpty`]. Level-indexed for [`Type::Unit`]'s load-bearing
    /// reason. Unlike [`Type::Empty`] (whose neutrals compare structurally),
    /// any two terms at this type are convertible — vacuously sound, and it
    /// keeps absurdity proofs invisible when they ride in data
    /// (docs/sprop-design.md §2.2; the Empty-reuse alternative is §2.2's
    /// costed shed). Admitted at layer c with [`Type::SEq`].
    SEmpty {
        level: Level,
    },
    /// `Squash^l A` (`∥A∥`) — propositional truncation of `A`.  The
    /// payload type remains ordinary data, while inhabitants are
    /// definitionally irrelevant.  Elimination is restricted to a
    /// squash-headed family by [`Term::ElimSquash`].
    Squash {
        level: Level,
        ty: Rc<Type>,
    },
    /// `Σ^{l,l'}(x : S). T` — dependent pair type; `snd` binds one local
    /// variable (of type `fst`). Lives at `l ⊔ l'`. Extension beyond DeLaM
    /// ch. 04 (see issues/kernel-v1-extensions.md).
    Sigma {
        fst_level: Level,
        snd_level: Level,
        fst: Rc<Type>,
        snd: Rc<Type>,
    },
    /// `Unit^l` — the unit type at level `l`. A single inhabitant `⟨⟩^l`
    /// ([`Term::Triv`]) with definitional η (proof irrelevance), so no
    /// eliminator. Extension beyond DeLaM ch. 04 (see
    /// issues/kernel-v1-extensions.md).
    ///
    /// **Level-indexed, not level-polymorphic** — `Unit^l` and `Unit^{l'}` are
    /// distinct types, so every type still has exactly one level. That is
    /// load-bearing: see [`crate::typing`]'s `ty_check` and
    /// `docs/unit-empty-level-indexing.md`.
    Unit {
        level: Level,
    },
    /// `Empty^l` — the empty type at level `l`; no inhabitants, eliminated by
    /// [`Term::ElimEmpty`]. Extension beyond DeLaM ch. 04. Level-indexed for
    /// the same reason as [`Type::Unit`].
    Empty {
        level: Level,
    },
    /// `A +^{l,l'} B` — binary sum (coproduct); `lhs`, `rhs` are types in the
    /// ambient Γ (non-dependent — neither binds). Lives at `l ⊔ l'`.
    /// Introduced by [`Term::Inl`]/[`Term::Inr`], eliminated (dependently) by
    /// [`Term::Case`]. Extension beyond DeLaM ch. 04.
    Sum {
        lhs_level: Level,
        rhs_level: Level,
        lhs: Rc<Type>,
        rhs: Rc<Type>,
    },
    /// `W^{l,l'}(x : S). T` — well-founded tree type (labels/shapes `S`,
    /// branching positions `T`); `pos` binds one local variable (of type
    /// `shape`). Introduced by [`Term::Sup`], eliminated (dependently) by
    /// [`Term::ElimW`]; positive like [`Type::Sum`] (no η). Lives at
    /// `l ⊔ l'`. Extension beyond DeLaM ch. 04 (see
    /// issues/kernel-v1-extensions.md).
    W {
        shape_level: Level,
        pos_level: Level,
        shape: Rc<Type>,
        pos: Rc<Type>,
    },
    /// `Vec^l(T; k)` — the k-fold Σ-tuple of `T`, Unit-terminated, as a
    /// former: `Vec(T; 0) ⇝ Unit`, `Vec(T; S k) ⇝ Σ(_ : T). Vec(T; k)`;
    /// neutral at a neutral length, no η of its own (η arrives through the
    /// reductions). No introduction/elimination forms — values are pairs.
    /// Substrate for `Wf` (docs/wf-former-design.md §1.1); admitted at the
    /// code layer since phase 3 gave it `TmVec` and its rec.rs branches.
    Vec {
        level: Level,
        elem: Rc<Type>,
        len: Rc<Term>,
    },
    /// `Fin(k)` — canonical finite index types: `Fin(0) ⇝ Empty`,
    /// `Fin(S k) ⇝ Unit + Fin(k)`; neutral at a neutral length. Lives at 0.
    /// Same phase gate as [`Type::Vec`] (docs/wf-former-design.md §1.2).
    Fin { len: Rc<Term> },
    /// `Wf^l(x : S). n` — the **finitary** branching fixed point: shapes
    /// `S`, arity a `Nat` *term* with the shape free (`arity` binds one
    /// local, `x : S`). Introduced by [`Term::Supf`], eliminated by
    /// [`Term::ElimWf`]; positive like [`Type::W`] (no η). Lives at `l`
    /// alone — the arity is data, not a type.
    ///
    /// The difference from [`Type::W`] is the whole point (route C of
    /// docs/branching-inductives-choice.md): `W` stores children in a `Π`,
    /// which this kernel deliberately does not η-expand, so bridging an
    /// abstract child function to a constructor form needs funext. `Wf`
    /// stores them in a [`Type::Vec`], i.e. in `Σ`/`Unit`, whose η is
    /// already in `conv.rs` — so the same bridge is a conversion.
    /// Same phase gate as [`Type::Vec`] (docs/wf-former-design.md §1.3).
    Wf {
        level: Level,
        shape: Rc<Type>,
        arity: Rc<Term>,
    },
    /// `U^δ` — global type variable under a local substitution.
    GlobalTy { var: GlobalVar, subst: LocalSubst },
    /// `(g : Ctx) ⇒^l T` — meta-function type over context variables; binds
    /// one global (context) variable in `body`. Layer m only.
    CtxPi { level: Level, body: Rc<Type> },
    /// `(U : Typ(Δ, l)) ⇒^{l'} T` — meta-function type over layer-p types;
    /// binds one global (type, layer p) variable in `body`. Layer m only.
    TyPi {
        ctx: LocalCtx,
        arg_level: Level,
        body_level: Level,
        body: Rc<Type>,
    },
    /// `□(Δ ⊢ Ty l)` — contextual type of code of types. Universe 0.
    CodeTy { ctx: LocalCtx, level: Level },
    /// `□(Δ ⊢ T @ l)` — contextual type of code of terms. Universe 0.
    CodeTm {
        ctx: LocalCtx,
        ty: Rc<Type>,
        level: Level,
    },
}

/// Terms `s, t` (sort `Exp`).
#[derive(Clone, PartialEq, Eq)]
pub enum Term {
    /// Local variable `x`.
    Var(LocalVar),

    // ---- encodings of types (decoded via Type::El) ----
    /// `Nat : Ty 0`.
    TmNat,
    /// `Π^{l,l'}(x : s). t : Ty (l ⊔ l')` where `s : Ty l`; `cod` binds one
    /// local variable (of type `El s`).
    TmPi {
        dom_level: Level,
        cod_level: Level,
        dom: Rc<Term>,
        cod: Rc<Term>,
    },
    /// `Ty l : Ty (1 + l)`.
    TmTy(Level),
    /// `Id^l (s; t; u) : Ty l` where `s : Ty l`, `t, u : El^l s` — encoding
    /// of the identity type. Extension beyond DeLaM ch. 04.
    TmId {
        level: Level,
        ty: Rc<Term>,
        lhs: Rc<Term>,
        rhs: Rc<Term>,
    },
    /// `sEq^l(s; t; u) : Ty l` where `s : Ty l`, `t, u : El^l s` — encoding
    /// of strict equality; mirrors [`Term::TmId`]. Extension
    /// (docs/sprop-design.md §6).
    TmSEq {
        level: Level,
        ty: Rc<Term>,
        lhs: Rc<Term>,
        rhs: Rc<Term>,
    },
    /// `sEmpty^l : Ty l` — encoding of the strict empty type; mirrors
    /// [`Term::TmEmpty`], carrying its level for the same reason. Extension
    /// (docs/sprop-design.md §6).
    TmSEmpty {
        level: Level,
    },
    /// `Squash^l(s) : Ty l` where `s : Ty l` — encoding of propositional
    /// truncation.
    TmSquash {
        level: Level,
        ty: Rc<Term>,
    },
    /// `Σ^{l,l'}(x : s). t : Ty (l ⊔ l')` where `s : Ty l`; `snd` binds one
    /// local variable (of type `El s`) — encoding of the dependent pair
    /// type. Extension beyond DeLaM ch. 04.
    TmSigma {
        fst_level: Level,
        snd_level: Level,
        fst: Rc<Term>,
        snd: Rc<Term>,
    },
    /// `Unit^l : Ty l` — encoding of the unit type (decoded by
    /// `El^l (Unit^l) ⇝ Unit^l`). Extension beyond DeLaM ch. 04.
    ///
    /// Carries its level for the same reason [`Term::TmTy`] does: the code is
    /// a *term*, and its type `Ty l` must be determined by it.
    TmUnit {
        level: Level,
    },
    /// `Empty^l : Ty l` — encoding of the empty type (decoded by
    /// `El^l (Empty^l) ⇝ Empty^l`). Extension beyond DeLaM ch. 04.
    TmEmpty {
        level: Level,
    },
    /// `s +^{l,l'} t : Ty (l ⊔ l')` where `s : Ty l`, `t : Ty l'` — encoding
    /// of the binary sum (decoded by `El (s + t) ⇝ El s + El t`). Extension
    /// beyond DeLaM ch. 04.
    TmSum {
        lhs_level: Level,
        rhs_level: Level,
        lhs: Rc<Term>,
        rhs: Rc<Term>,
    },
    /// `W^{l,l'}(x : s). t : Ty (l ⊔ l')` where `s : Ty l`; `pos` binds one
    /// local variable (of type `El s`) — encoding of the W-type (decoded by
    /// `El (W (x:s). t) ⇝ W (x : El s). El t`, mirroring Π/Σ). Extension
    /// beyond DeLaM ch. 04.
    TmW {
        shape_level: Level,
        pos_level: Level,
        shape: Rc<Term>,
        pos: Rc<Term>,
    },
    /// `Vec^l(s; k) : Ty l` where `s : Ty l` and `k : Nat` — encoding of the
    /// fixed-length tuple (decoded by `El (Vec^l(s; k)) ⇝ Vec^l(El^l s; k)`).
    /// The length is an ordinary term of the *same* scope: `Vec` binds
    /// nothing. Extension (docs/wf-former-design.md §6).
    TmVec {
        level: Level,
        elem: Rc<Term>,
        len: Rc<Term>,
    },
    /// `Fin(k) : Ty 0` where `k : Nat` — encoding of the canonical finite
    /// index type (decoded by `El (Fin k) ⇝ Fin k`). Extension (§6).
    TmFin { len: Rc<Term> },
    /// `Wf^l(x : s). n : Ty l` where `s : Ty l` and `n : Nat` under
    /// `x : El^l s` — encoding of the finitary branching fixed point
    /// (decoded by `El (Wf^l(x:s). n) ⇝ Wf^l(x : El^l s). n`). The arity
    /// binds one local variable but is a *term*, so — as with the type
    /// former — it contributes no level. Extension (§6).
    TmWf {
        level: Level,
        shape: Rc<Term>,
        arity: Rc<Term>,
    },

    // ---- natural numbers ----
    Zero,
    /// A closed natural-number literal. This is observationally the same
    /// constructor spine as `Succ^value(Zero)` (and `NatLit(0)` is `Zero`),
    /// but keeps source numerals compact until evaluation can hand them to the
    /// generic context-program representation.
    NatLit(u64),
    Succ(Rc<Term>),
    /// `elim_Nat^l (x. M) s (x, y. s') t`; `motive` binds one local variable
    /// (the Nat), `step` binds two (predecessor, recursive result).
    ElimNat {
        level: Level,
        motive: Rc<Type>,
        base: Rc<Term>,
        step: Rc<Term>,
        scrut: Rc<Term>,
    },

    // ---- identity (extension beyond DeLaM ch. 04) ----
    /// `refl^l (S; t) : Id^l (S; t; t)`. Fully annotated so it synthesizes.
    Refl {
        level: Level,
        ty: Rc<Type>,
        tm: Rc<Term>,
    },
    /// `J^{l,l'} (S; a; y p. M; c; u; e)` — based path induction
    /// (Paulin-Mohring). `motive` binds two local variables
    /// (`y : S`, `p : Id^l (S; a; y)`); nothing else binds. `lhs` is the
    /// fixed left endpoint `a`, `case : M[a/y, refl/p]`, `rhs` the right
    /// endpoint `u`, and `proof : Id^l (S; a; u)` is the scrutinee.
    J {
        ty_level: Level,
        motive_level: Level,
        ty: Rc<Type>,
        lhs: Rc<Term>,
        motive: Rc<Type>,
        case: Rc<Term>,
        rhs: Rc<Term>,
        proof: Rc<Term>,
    },

    // ---- strict equality (extension; docs/sprop-design.md) ----
    /// `srefl^l(I; a) : sEq^l(I; a; a)`. Fully annotated so it synthesizes;
    /// the only canonical form at [`Type::SEq`], which is what makes
    /// β-on-`srefl` sufficient for closed computation. Mirrors
    /// [`Term::Refl`]. Admitted at layer c with [`Type::SEq`].
    SRefl {
        level: Level,
        ty: Rc<Type>,
        tm: Rc<Term>,
    },
    /// `squash^l(A; a) : ∥A∥`.  The witness is retained by syntax and
    /// code, but ignored by live conversion at the squash type.
    Squash {
        level: Level,
        ty: Rc<Type>,
        tm: Rc<Term>,
    },
    /// `transp^{l,l'}(I; x.P; a; b; e; t) : P[b/x]` — transport along a
    /// strict equality through a motive; J's non-dependent cousin. `motive`
    /// binds one local variable (`x : I`); nothing else binds. `proof :
    /// sEq^l(I; a; b)` and `tm : P[a/x]`. β fires on `srefl` only; the case
    /// β cannot see (a *neutral* proof at convertible endpoints) is handled
    /// by the conversion strip rule, and its stuckness is keyed on the
    /// endpoints, not the proof — see `conv.rs` and docs/sprop-design.md
    /// §5. Admitted at layer c with [`Type::SEq`].
    Transp {
        ty_level: Level,
        motive_level: Level,
        ty: Rc<Type>,
        motive: Rc<Type>,
        lhs: Rc<Term>,
        rhs: Rc<Term>,
        proof: Rc<Term>,
        tm: Rc<Term>,
    },
    /// `elim_sEmpty^{l,l'} (x. M; t) : M[t/x]` — ex falso from a strict
    /// absurdity; `motive` binds one local (`x : sEmpty^{l'}`),
    /// `scrut : sEmpty^{l'}`. [`Term::ElimEmpty`]'s discipline verbatim (no
    /// β — nothing canonical to fire on; neutral on a neutral scrutinee;
    /// `level` is the motive's, `scrut_level` the scrutinee's) with one
    /// deliberate difference: neutral congruence skips the scrutinees —
    /// they sit at an irrelevant type. Admitted at layer c with
    /// [`Type::SEq`].
    ElimSEmpty {
        level: Level,
        scrut_level: Level,
        motive: Rc<Type>,
        scrut: Rc<Term>,
    },
    /// Dependent elimination from `∥A∥` into a squash-headed family.
    /// `motive` binds `z : ∥A∥` and denotes the *inner* type `B(z)`;
    /// `case` binds `x : A` and has type `∥B(squash x)∥`.  The result is
    /// `∥B(scrut)∥`, and the beta rule sends a canonical `squash a` to
    /// `case[a/x]`.
    ElimSquash {
        src_level: Level,
        dst_level: Level,
        src_ty: Rc<Type>,
        motive: Rc<Type>,
        case: Rc<Term>,
        scrut: Rc<Term>,
    },

    // ---- dependent pairs (extension beyond DeLaM ch. 04) ----
    /// `pair^{l,l'}(x:S. T; a; b) : Σ^{l,l'}(x:S). T` — dependent pair
    /// introduction. Fully annotated so it synthesizes: `snd_ty` binds one
    /// local variable, `fst : S`, `snd : T[fst/x]`.
    Pair {
        fst_level: Level,
        snd_level: Level,
        fst_ty: Rc<Type>,
        snd_ty: Rc<Type>,
        fst: Rc<Term>,
        snd: Rc<Term>,
    },
    /// `fst^{l,l'}(x:S. T; p) : S` — first projection; `p : Σ^{l,l'}(x:S). T`.
    /// `snd_ty` binds one local variable. Annotated like `App` so it infers.
    Fst {
        fst_level: Level,
        snd_level: Level,
        fst_ty: Rc<Type>,
        snd_ty: Rc<Type>,
        pair: Rc<Term>,
    },
    /// `snd^{l,l'}(x:S. T; p) : T[fst p/x]` — second projection.
    /// `snd_ty` binds one local variable.
    Snd {
        fst_level: Level,
        snd_level: Level,
        fst_ty: Rc<Type>,
        snd_ty: Rc<Type>,
        pair: Rc<Term>,
    },

    // ---- unit and empty (extension beyond DeLaM ch. 04) ----
    /// `⟨⟩^l : Unit^l` — the unique inhabitant of `Unit^l`. By η every term of
    /// `Unit^l` type is convertible to it (proof irrelevance), so `Unit` has
    /// no eliminator.
    ///
    /// **The level annotation is not redundant**, even though it is always
    /// recoverable from the expected type. Without it `⟨⟩` inhabits `Unit^l`
    /// for *every* `l`, and a term with many types is exactly what ch. 04
    /// §Non-cumulativity says the code eliminator cannot survive — the
    /// failure that sank route (b) in `docs/unit-empty-level-indexing.md` §6.1.
    Triv {
        level: Level,
    },
    /// `elim_Empty^{l, l'} (x. M; t) : M[t/x]` — absurdity elimination;
    /// `motive` binds one local variable (`x : Empty^{l'} @ l'`),
    /// `scrut : Empty^{l'}`. No β rule (`Empty` has no constructors); neutral
    /// on a neutral scrutinee. Annotated like `elim_Nat` so it infers.
    ///
    /// `level` is the *motive's*; `scrut_level` is the scrutinee's `Empty`
    /// level. The two are independent — this is the one variant that carries
    /// a second level rather than a first.
    ElimEmpty {
        level: Level,
        scrut_level: Level,
        motive: Rc<Type>,
        scrut: Rc<Term>,
    },

    // ---- binary sums (extension beyond DeLaM ch. 04) ----
    /// `inl^{l,l'}(A; B; a) : A +^{l,l'} B` where `a : A`. Fully annotated
    /// (both summands and their levels) so it synthesizes.
    Inl {
        lhs_level: Level,
        rhs_level: Level,
        lhs: Rc<Type>,
        rhs: Rc<Type>,
        val: Rc<Term>,
    },
    /// `inr^{l,l'}(A; B; b) : A +^{l,l'} B` where `b : B`. Fully annotated so
    /// it synthesizes.
    Inr {
        lhs_level: Level,
        rhs_level: Level,
        lhs: Rc<Type>,
        rhs: Rc<Type>,
        val: Rc<Term>,
    },
    /// `case^{l,l',l''}(z. M; A; B; x. c_l; y. c_r; t) : M[t/z]` — dependent
    /// case analysis over `t : A +^{l,l'} B`. `motive` binds one local
    /// (`z : A + B`), `left` binds one (`x : A`), `right` binds one
    /// (`y : B`); `case_l : M[inl x/z]`, `case_r : M[inr y/z]`. β
    /// `case (inl a) ⇝ c_l[a/x]`, `case (inr b) ⇝ c_r[b/y]`; neutral on a
    /// neutral scrutinee. Annotated like `elim_Nat` so it infers.
    Case {
        lhs_level: Level,
        rhs_level: Level,
        motive_level: Level,
        lhs: Rc<Type>,
        rhs: Rc<Type>,
        motive: Rc<Type>,
        case_l: Rc<Term>,
        case_r: Rc<Term>,
        scrut: Rc<Term>,
    },

    // ---- well-founded trees (extension beyond DeLaM ch. 04) ----
    /// `sup^{l,l'}(x:S. T; a; f) : W^{l,l'}(x:S). T` where `a : S` and
    /// `f : Π^{l',l⊔l'}(y : T[a/x]). W^{l,l'}(x:S). T`. Fully annotated so
    /// it synthesizes; `pos_ty` binds one local variable.
    Sup {
        shape_level: Level,
        pos_level: Level,
        shape_ty: Rc<Type>,
        pos_ty: Rc<Type>,
        label: Rc<Term>,
        children: Rc<Term>,
    },
    /// `elim_W^{l,l',l''}(x:S. T; z. M; a f ih. s; t) : M[t/z]` — dependent
    /// W-elimination over `t : W^{l,l'}(x:S). T`. `motive` binds one local
    /// (`z : W`), `step` binds three (`a : S`,
    /// `f : Π^{l',l⊔l'}(y : T[a/x]). W`,
    /// `ih : Π^{l',l''}(y : T[a/x]). M[f y/z]`) with
    /// `s : M[sup(a, f)/z]`. β `elim_W (sup(…; a; f)) ⇝
    /// s[a, f, λy. elim_W(…; f y)]` — the recursive call is synthesized
    /// *under a λ* (the ih function), the only β rule with that shape.
    /// Neutral on a neutral scrutinee (positive, like `case`/`elim_Nat`).
    /// Annotated like `elim_Nat` so it infers.
    ElimW {
        shape_level: Level,
        pos_level: Level,
        motive_level: Level,
        shape: Rc<Type>,
        pos: Rc<Type>,
        motive: Rc<Type>,
        step: Rc<Term>,
        scrut: Rc<Term>,
    },

    // ---- finitary branching trees (extension; docs/wf-former-design.md) ----
    /// `sup_f^l(x:S. n; a; cs) : Wf^l(x:S). n` where `a : S` and
    /// `cs : Vec^l(Wf^l(x:S).n; n[a/x])` — the children are a **tuple**,
    /// not a function. Fully annotated so it synthesizes; `arity` binds one
    /// local (`x : shape`).
    Supf {
        level: Level,
        shape: Rc<Type>,
        arity: Rc<Term>,
        label: Rc<Term>,
        children: Rc<Term>,
    },
    /// `elim_Wf^{l,l'}(x:S. n; z. M; a cs ih. s; t) : M[t/z]` — dependent
    /// elimination over `t : Wf^l(x:S). n`. `motive` binds one local
    /// (`z : Wf`), `step` binds three (`a : S`,
    /// `cs : Vec^l(Wf; n[a/x])`,
    /// `ih : Π^{0,l'}(i : Fin n[a/x]). M[nth^l(Wf; n[a/x]; cs; i)/z]`) with
    /// `s : M[sup_f(a; cs)/z]`. β
    /// `elim_Wf (sup_f(…; a; cs)) ⇝ s[a, cs, λi. elim_Wf(…; nth … cs i)]` —
    /// like `elim_W`'s, the recursive call is synthesized *under a λ*, but
    /// over a `Fin` index rather than an abstract position, so the ih is
    /// **transient**: applied at literal indices (after the generated
    /// recursor cases on the tag), never stored in data and never compared.
    /// That is why the η-deficiency of functions costs nothing here — the
    /// resolution of wrinkle 6.2 in docs/branching-inductives-choice.md.
    /// Neutral on a neutral scrutinee. [`nth`] is materialized by this
    /// rule rather than being a former of its own.
    ElimWf {
        level: Level,
        motive_level: Level,
        shape: Rc<Type>,
        arity: Rc<Term>,
        motive: Rc<Type>,
        step: Rc<Term>,
        scrut: Rc<Term>,
    },

    // ---- dependent functions ----
    /// `λ^{l,l'}(x : S). t`; `body` binds one local variable.
    Lam {
        dom_level: Level,
        cod_level: Level,
        dom: Rc<Type>,
        body: Rc<Term>,
    },
    /// `app(t; l, l'; x : S. T; s)` — fully annotated application; `cod`
    /// binds one local variable. The annotations are sub-structures so the
    /// code recursor can recurse into them (ch. 04).
    App {
        fun: Rc<Term>,
        dom_level: Level,
        cod_level: Level,
        dom: Rc<Type>,
        cod: Rc<Type>,
        arg: Rc<Term>,
    },

    // ---- universe-polymorphic functions (layer m) ----
    /// `Λ ℓ⃗. t`; binds `num_vars ≥ 1` universe variables in `level`, `body`.
    ULam {
        num_vars: u32,
        level: Level,
        body: Rc<Term>,
    },
    /// `t $ l⃗`, `levels` non-empty and ω-free.
    UApp { fun: Rc<Term>, levels: Vec<Level> },

    // ---- global variables ----
    /// `u^δ` — global term variable under a local substitution.
    GlobalTm { var: GlobalVar, subst: LocalSubst },

    // ---- meta-functions (layer m) ----
    /// `Λ^l(g : Ctx). t`; binds one global (context) variable in `body`.
    CtxLam { level: Level, body: Rc<Term> },
    /// `t @ Δ` — apply to a layer-p local context.
    CtxApp { fun: Rc<Term>, ctx: LocalCtx },
    /// `Λ^{l,l'}(U : Typ(Δ, l)). t`; binds one global (type) variable.
    TyLam {
        ctx: LocalCtx,
        arg_level: Level,
        body_level: Level,
        body: Rc<Term>,
    },
    /// `t @ T` — apply to a layer-p type.
    TyApp { fun: Rc<Term>, arg: Rc<Type> },

    // ---- contextual types: introduction (layer m) ----
    /// `box T` where `Δ ⊢_c T` — code of a type.
    BoxTy(Rc<Type>),
    /// `box t` where `Δ ⊢_c t : T` — code of a term.
    BoxTm(Rc<Term>),

    // ---- contextual types: letbox elimination (layer m) ----
    /// `letbox^{l',l} Δ (x_T. M) (U. t') t` — eliminate `t : □(Δ ⊢ Ty l)`;
    /// `motive` binds one local variable (`x_T : □(Δ ⊢ Ty l)`), `body` binds
    /// one global variable (`U : Typ_c(Δ, l)`).
    LetBoxTy {
        motive_level: Level,
        code_level: Level,
        ctx: LocalCtx,
        motive: Rc<Type>,
        body: Rc<Term>,
        scrut: Rc<Term>,
    },
    /// `letbox^{l',l} Δ T (x_t. M) (u. t') t` — eliminate
    /// `t : □(Δ ⊢ T @ l)`; `motive` binds one local variable, `body` binds
    /// one global variable (`u : Trm_c(Δ ⊢ T @ l)`).
    LetBoxTm {
        motive_level: Level,
        code_level: Level,
        ctx: LocalCtx,
        ty: Rc<Type>,
        motive: Rc<Type>,
        body: Rc<Term>,
        scrut: Rc<Term>,
    },

    // ---- recursive principles over code (layer m, mutual) ----
    /// `elim^{Typ} (l₁,l₂) M⃗ b⃗ (l, Δ) t` — recursion over code of types,
    /// `scrut : □(Δ ⊢ Ty l)`.
    ElimCodeTy {
        ty_motive_level: Level,
        tm_motive_level: Level,
        motives: Rc<Motives>,
        branches: Rc<Branches>,
        code_level: Level,
        ctx: LocalCtx,
        scrut: Rc<Term>,
    },
    /// `elim^{Trm} (l₁,l₂) M⃗ b⃗ (l, Δ, T) t` — recursion over code of terms,
    /// `scrut : □(Δ ⊢ T @ l)`.
    ElimCodeTm {
        ty_motive_level: Level,
        tm_motive_level: Level,
        motives: Rc<Motives>,
        branches: Rc<Branches>,
        code_level: Level,
        ctx: LocalCtx,
        ty: Rc<Type>,
        scrut: Rc<Term>,
    },
}

/// The two mutual motives `M⃗` for the code recursors (ch. 04):
///
/// - `ty_motive` = `(ℓ, g, x_T. M_Typ)`: under 1 universe variable, 1 global
///   (context) variable, and 1 local variable `x_T : □(g ⊢ Ty ℓ)`.
/// - `tm_motive` = `(ℓ, g, U_T, x_t. M_Trm)`: under 1 universe variable, 2
///   global variables (`g : Ctx`, `U_T : Typ_p(g, ℓ)`), and 1 local variable
///   `x_t : □(g ⊢ U_T^id @ ℓ)`.
#[derive(Clone, PartialEq, Eq)]
pub struct Motives {
    pub ty_motive: Rc<Type>,
    pub tm_motive: Rc<Type>,
}

/// All branches `b⃗ = b⃗_Typ b⃗_Trm` of the mutual code recursors.
///
/// Each field is a term under the branch telescope given in ch. 04
/// (§More Typing and Equivalence Judgments): universe variables extend L,
/// global variables (`g`, `U_…`, `u_…`) extend Ψ innermost-last in the order
/// written in the paper, and recursive-call variables (`x_…`) extend Γ in the
/// order written. The comment on each field lists that telescope.
#[derive(Clone, PartialEq, Eq)]
pub struct Branches {
    // -- branches for code of types (b_Typ) --
    /// `(g. t_Nat)` — globals: g.
    pub ty_nat: Rc<Term>,
    /// `(ℓ, ℓ', g, U_S, U_T, x_S, x_T. t_Π)` — univs: ℓ, ℓ'; globals: g,
    /// `U_S : Typ_c(g, ℓ)`, `U_T : Typ_c((g, x : U_S^id @ ℓ), ℓ')`;
    /// locals: `x_S`, `x_T` (recursive calls).
    pub ty_pi: Rc<Term>,
    /// `(ℓ, g. t_Ty)` — univs: ℓ; globals: g.
    pub ty_ty: Rc<Term>,
    /// `(ℓ, g, u_t, x_t. t_El)` — univs: ℓ; globals: g,
    /// `u_t : Trm_c(g ⊢ Ty ℓ @ 1+ℓ)`; locals: `x_t` (recursive call, at the
    /// *term* motive).
    pub ty_el: Rc<Term>,
    /// `(ℓ, g, U_S, u_t, u_u, x_S, x_t, x_u. t_Id)` — univs: ℓ; globals: g,
    /// `U_S : Typ_c(g, ℓ)`, `u_t : Trm_c(g ⊢ U_S^id @ ℓ)`,
    /// `u_u : Trm_c(g ⊢ U_S^id @ ℓ)`; locals: `x_S` (type motive!), `x_t`,
    /// `x_u`. Extension beyond ch. 04 (kernel-v1-extensions).
    pub ty_id: Rc<Term>,
    /// `(ℓ, ℓ', g, U_S, U_T, x_S, x_T. t_Σ)` — univs: ℓ, ℓ'; globals: g,
    /// `U_S : Typ_c(g, ℓ)`, `U_T : Typ_c((g, x : U_S^id @ ℓ), ℓ')`;
    /// locals: `x_S`, `x_T` (recursive calls). Mirrors `ty_pi`. Extension
    /// beyond ch. 04 (kernel-v1-extensions).
    pub ty_sigma: Rc<Term>,
    /// `(ℓ, g. t_Unit)` — univs: ℓ; globals: g. Code of the type `Unit^ℓ`;
    /// mirrors `ty_nat` plus the level binder `Unit` gained in
    /// docs/unit-empty-level-indexing.md. Extension beyond ch. 04
    /// (kernel-v1-extensions).
    pub ty_unit: Rc<Term>,
    /// `(ℓ, g. t_Empty)` — univs: ℓ; globals: g. Code of the type `Empty^ℓ`;
    /// mirrors `ty_unit`. Extension beyond ch. 04 (kernel-v1-extensions).
    pub ty_empty: Rc<Term>,

    // -- branches for code of terms (b_Trm) --
    /// `(ℓ, g, U_T, u_x. t_x)` — univs: ℓ; globals: g,
    /// `U_T : Typ_p(g, ℓ)` (external index, layer p!),
    /// `u_x : Trm_v(g ⊢ U_T^id @ ℓ)` (layer v: only a variable fits).
    pub tm_var: Rc<Term>,
    /// `(g. t'_Nat)` — globals: g. Code of the encoding `Nat : Ty 0`.
    pub tm_nat: Rc<Term>,
    /// `(ℓ, ℓ', g, u_s, u_t, x_s, x_t. t'_Π)` — univs: ℓ, ℓ'; globals: g,
    /// `u_s : Trm_c(g ⊢ Ty ℓ)`, `u_t : Trm_c((g, x : El u_s) ⊢ Ty ℓ')`;
    /// locals: `x_s`, `x_t`.
    pub tm_pi: Rc<Term>,
    /// `(ℓ, g. t'_Ty)` — univs: ℓ; globals: g. Code of `Ty ℓ : Ty (1+ℓ)`.
    pub tm_ty: Rc<Term>,
    /// `(g. t_ze)` — globals: g.
    pub tm_zero: Rc<Term>,
    /// `(g, u_t, x_t. t_succ)` — globals: g, `u_t : Trm_c(g ⊢ Nat @ 0)`;
    /// locals: `x_t`.
    pub tm_succ: Rc<Term>,
    /// `(ℓ, g, U_M, u_s, u_s', u_t, x_M, x_s, x_s', x_t. t_elimN)` —
    /// univs: ℓ; globals: g, `U_M : Typ_c((g, x : Nat @ 0), ℓ)`,
    /// `u_s : Trm_c(g ⊢ U_M^{id,ze/x} @ ℓ)`,
    /// `u_s' : Trm_c((g, x : Nat, y : U_M^id) ⊢ U_M^{id,su x/x} @ ℓ)`,
    /// `u_t : Trm_c(g ⊢ Nat @ 0)`; locals: `x_M` (type motive!), `x_s`,
    /// `x_s'`, `x_t` (at level **0**, the scrutinee's — ch. 04 writes `ℓ`
    /// here, contradicting its own `t_ze`/`t_succ`; see
    /// docs/delam-extensions.md §16.1).
    pub tm_elim_nat: Rc<Term>,
    /// `(ℓ, ℓ', g, U_S, U_T, u_t, x_S, x_t. t_λ)` — univs: ℓ, ℓ'; globals: g,
    /// `U_S : Typ_c(g, ℓ)`, `U_T : Typ_p((g, x : U_S^id @ ℓ), ℓ')`
    /// (the return type is *not* a sub-structure: layer p, no recursive
    /// call), `u_t : Trm_c((g, x : U_S^id @ ℓ) ⊢ U_T^id @ ℓ')`;
    /// locals: `x_S`, `x_t`.
    pub tm_lam: Rc<Term>,
    /// `(ℓ, ℓ', g, U_S, U_T, u_t, u_s, x_S, x_T, x_t, x_s. t_app)` —
    /// univs: ℓ, ℓ'; globals: g, `U_S : Typ_c(g, ℓ)`,
    /// `U_T : Typ_c((g, x : U_S^id @ ℓ), ℓ')`,
    /// `u_t : Trm_c(g ⊢ Π(x:U_S).U_T @ ℓ⊔ℓ')`, `u_s : Trm_c(g ⊢ U_S^id @ ℓ)`;
    /// locals: `x_S`, `x_T`, `x_t`, `x_s`.
    pub tm_app: Rc<Term>,

    // -- extension branches (beyond ch. 04; kernel-v1-extensions) --
    /// `(ℓ, g, u_S, u_t, u_u, x_S, x_t, x_u. t'_Id)` — univs: ℓ; globals: g,
    /// `u_S : Trm_c(g ⊢ Ty ℓ @ 1+ℓ)`, `u_t : Trm_c(g ⊢ El ℓ u_S^id @ ℓ)`,
    /// `u_u : Trm_c(g ⊢ El ℓ u_S^id @ ℓ)`; locals: `x_S`, `x_t`, `x_u`.
    /// Code of the encoding `Id^ℓ (s; t; u) : Ty ℓ`.
    pub tm_id: Rc<Term>,
    /// `(ℓ, g, U_S, u_t, x_S, x_t. t_refl)` — univs: ℓ; globals: g,
    /// `U_S : Typ_c(g, ℓ)`, `u_t : Trm_c(g ⊢ U_S^id @ ℓ)`; locals: `x_S`
    /// (type motive!), `x_t`.
    pub tm_refl: Rc<Term>,
    /// `(ℓ, ℓ', g, U_S, u_a, U_M, u_c, u_r, u_e, x_S, x_a, x_M, x_c, x_r,
    /// x_e. t_J)` — univs: ℓ, ℓ'; globals: g, `U_S : Typ_c(g, ℓ)`,
    /// `u_a : Trm_c(g ⊢ U_S^id @ ℓ)`,
    /// `U_M : Typ_c((g, y : U_S^id @ ℓ, p : Id^ℓ(U_S^id; u_a^id; y) @ ℓ), ℓ')`,
    /// `u_c : Trm_c(g ⊢ U_M^{id, u_a/y, refl^ℓ(U_S^id; u_a^id)/p} @ ℓ')`,
    /// `u_r : Trm_c(g ⊢ U_S^id @ ℓ)`,
    /// `u_e : Trm_c(g ⊢ Id^ℓ(U_S^id; u_a^id; u_r^id) @ ℓ)`; locals: `x_S`,
    /// `x_a`, `x_M` (type motive!), `x_c`, `x_r`, `x_e`.
    pub tm_j: Rc<Term>,
    /// `(ℓ, ℓ', g, u_s, u_t, x_s, x_t. t'_Σ)` — univs: ℓ, ℓ'; globals: g,
    /// `u_s : Trm_c(g ⊢ Ty ℓ)`, `u_t : Trm_c((g, x : El u_s) ⊢ Ty ℓ')`;
    /// locals: `x_s`, `x_t`. Code of the encoding `Σ^ℓ,ℓ' (s; t) : Ty (ℓ⊔ℓ')`.
    /// Mirrors `tm_pi`. Extension beyond ch. 04 (kernel-v1-extensions).
    pub tm_sigma: Rc<Term>,
    /// `(ℓ, ℓ', g, U_S, U_T, u_a, u_b, x_S, x_T, x_a, x_b. t_pair)` —
    /// univs: ℓ, ℓ'; globals: g, `U_S : Typ_c(g, ℓ)`,
    /// `U_T : Typ_c((g, x : U_S^id @ ℓ), ℓ')`, `u_a : Trm_c(g ⊢ U_S^id @ ℓ)`,
    /// `u_b : Trm_c(g ⊢ U_T^{id, u_a/x} @ ℓ')`; locals: `x_S`, `x_T` (both
    /// type motive!), `x_a`, `x_b`. Extension (kernel-v1-extensions).
    pub tm_pair: Rc<Term>,
    /// `(ℓ, ℓ', g, U_S, U_T, u_p, x_S, x_T, x_p. t_fst)` — univs: ℓ, ℓ';
    /// globals: g, `U_S : Typ_c(g, ℓ)`, `U_T : Typ_c((g, x : U_S^id @ ℓ), ℓ')`,
    /// `u_p : Trm_c(g ⊢ Σ x:U_S^id. U_T^id @ ℓ⊔ℓ')`; locals: `x_S`, `x_T`
    /// (both type motive!), `x_p`. Extension (kernel-v1-extensions).
    pub tm_fst: Rc<Term>,
    /// `(ℓ, ℓ', g, U_S, U_T, u_p, x_S, x_T, x_p. t_snd)` — as `tm_fst`; the
    /// branch type is `U_T^{id, fst(…u_p^id)/x}` @ ℓ'. Extension.
    pub tm_snd: Rc<Term>,
    /// `(ℓ, g. t'_Unit)` — univs: ℓ; globals: g. Code of the encoding
    /// `Unit^ℓ : Ty ℓ`; mirrors `tm_nat` plus the level binder. Extension
    /// beyond ch. 04 (kernel-v1-extensions).
    pub tm_unit: Rc<Term>,
    /// `(ℓ, g. t'_Empty)` — univs: ℓ; globals: g. Code of the encoding
    /// `Empty^ℓ : Ty ℓ`; mirrors `tm_unit`. Extension beyond ch. 04
    /// (kernel-v1-extensions).
    pub tm_empty: Rc<Term>,
    /// `(ℓ, g. t_triv)` — univs: ℓ; globals: g. Code of the intro
    /// `⟨⟩^ℓ : Unit^ℓ`; mirrors `tm_zero` plus the level binder. Extension
    /// beyond ch. 04 (kernel-v1-extensions).
    pub tm_triv: Rc<Term>,
    /// `(ℓ, ℓ', g, U_M, u_t, x_M, x_t. t_elimE)` — univs: ℓ (the motive's),
    /// ℓ' (the scrutinee's); globals: g,
    /// `U_M : Typ_c((g, x : Empty^ℓ' @ ℓ'), ℓ)`,
    /// `u_t : Trm_c(g ⊢ Empty^ℓ' @ ℓ')`; locals: `x_M` (type motive!), `x_t`
    /// (term motive, at **ℓ'** — the scrutinee's level, see
    /// docs/delam-extensions.md §7.7). Code of
    /// `elim_Empty^{ℓ,ℓ'} (x. U_M^id; u_t^id)`; mirrors `tm_elim_nat` minus
    /// base/step. Extension (kernel-v1-extensions).
    pub tm_elim_empty: Rc<Term>,
    /// `(ℓ, ℓ', g, U_A, U_B, x_A, x_B. t_+)` — univs: ℓ, ℓ'; globals: g,
    /// `U_A : Typ_c(g, ℓ)`, `U_B : Typ_c(g, ℓ')` (both in g — non-dependent);
    /// locals: `x_A`, `x_B` (recursive calls). Code of the type
    /// `U_A^id +^{ℓ,ℓ'} U_B^id`; mirrors `ty_sigma` minus the binder
    /// extension. Extension beyond ch. 04 (kernel-v1-extensions).
    pub ty_sum: Rc<Term>,
    /// `(ℓ, ℓ', g, u_a, u_b, x_a, x_b. t'_+)` — univs: ℓ, ℓ'; globals: g,
    /// `u_a : Trm_c(g ⊢ Ty ℓ)`, `u_b : Trm_c(g ⊢ Ty ℓ')`; locals: `x_a`,
    /// `x_b`. Code of the encoding `u_a +^{ℓ,ℓ'} u_b : Ty (ℓ⊔ℓ')`; mirrors
    /// `tm_sigma` minus the binder extension. Extension.
    pub tm_sum: Rc<Term>,
    /// `(ℓ, ℓ', g, U_A, U_B, u_a, x_A, x_B, x_a. t_inl)` — univs: ℓ, ℓ';
    /// globals: g, `U_A : Typ_c(g, ℓ)`, `U_B : Typ_c(g, ℓ')`,
    /// `u_a : Trm_c(g ⊢ U_A^id @ ℓ)`; locals: `x_A`, `x_B` (both type
    /// motive!), `x_a`. Code of `inl(U_A^id; U_B^id; u_a^id)`. Extension.
    pub tm_inl: Rc<Term>,
    /// `(ℓ, ℓ', g, U_A, U_B, u_b, x_A, x_B, x_b. t_inr)` — as `tm_inl` but
    /// `u_b : Trm_c(g ⊢ U_B^id @ ℓ')` and the code is
    /// `inr(U_A^id; U_B^id; u_b^id)`. Extension.
    pub tm_inr: Rc<Term>,
    /// `(ℓ, ℓ', ℓ'', g, U_A, U_B, U_M, u_l, u_r, u_t, x_A, x_B, x_M, x_l,
    /// x_r, x_t. t_case)` — univs: ℓ, ℓ', ℓ''; globals: g,
    /// `U_A : Typ_c(g, ℓ)`, `U_B : Typ_c(g, ℓ')`,
    /// `U_M : Typ_c((g, z : (U_A^id + U_B^id) @ ℓ⊔ℓ'), ℓ'')`,
    /// `u_l : Trm_c((g, x : U_A^id @ ℓ) ⊢ U_M^{id, inl x/z} @ ℓ'')`,
    /// `u_r : Trm_c((g, y : U_B^id @ ℓ') ⊢ U_M^{id, inr y/z} @ ℓ'')`,
    /// `u_t : Trm_c(g ⊢ (U_A^id + U_B^id) @ ℓ⊔ℓ')`; locals: `x_A`, `x_B`,
    /// `x_M` (type motive!), `x_l`, `x_r`, `x_t`. Code of
    /// `case (z. U_M^id) (x. u_l^id) (y. u_r^id) u_t^id`; a positive
    /// dependent eliminator (mirrors `tm_elim_nat`'s shape, two branches).
    /// Extension.
    pub tm_case: Rc<Term>,
    /// `(ℓ, ℓ', g, U_S, U_T, x_S, x_T. t_W)` — univs: ℓ, ℓ'; globals: g,
    /// `U_S : Typ_c(g, ℓ)`, `U_T : Typ_c((g, x : U_S^id @ ℓ), ℓ')`;
    /// locals: `x_S`, `x_T` (recursive calls). Code of the type
    /// `W(x:U_S^id). U_T^id`; mirrors `ty_pi`/`ty_sigma`. Extension beyond
    /// ch. 04 (kernel-v1-extensions).
    pub ty_w: Rc<Term>,
    /// `(ℓ, ℓ', g, u_s, u_t, x_s, x_t. t'_W)` — univs: ℓ, ℓ'; globals: g,
    /// `u_s : Trm_c(g ⊢ Ty ℓ)`, `u_t : Trm_c((g, x : El u_s) ⊢ Ty ℓ')`;
    /// locals: `x_s`, `x_t`. Code of the encoding `W (x:u_s). u_t :
    /// Ty (ℓ⊔ℓ')`; mirrors `tm_pi`/`tm_sigma`. Extension.
    pub tm_w: Rc<Term>,
    /// `(ℓ, ℓ', g, U_S, U_T, u_a, u_f, x_S, x_T, x_a, x_f. t_sup)` —
    /// univs: ℓ, ℓ'; globals: g, `U_S : Typ_c(g, ℓ)`,
    /// `U_T : Typ_c((g, x : U_S^id @ ℓ), ℓ')`, `u_a : Trm_c(g ⊢ U_S^id @ ℓ)`,
    /// `u_f : Trm_c(g ⊢ Π^{ℓ',ℓ⊔ℓ'}(y : U_T^{id, u_a/x}). W(x:U_S^id).U_T^id
    /// @ ℓ⊔ℓ')`; locals: `x_S`, `x_T` (both type motive!), `x_a`, `x_f`.
    /// Code of `sup(x:U_S^id. U_T^id; u_a^id; u_f^id)`; dims mirror
    /// `tm_pair`. Extension.
    pub tm_sup: Rc<Term>,
    /// `(ℓ, ℓ', ℓ'', g, U_S, U_T, U_M, u_s, u_t, x_S, x_T, x_M, x_s, x_t.
    /// t_elimW)` — univs: ℓ, ℓ', ℓ''; globals: g, `U_S : Typ_c(g, ℓ)`,
    /// `U_T : Typ_c((g, x : U_S^id @ ℓ), ℓ')`,
    /// `U_M : Typ_c((g, z : W(x:U_S^id).U_T^id @ ℓ⊔ℓ'), ℓ'')`,
    /// `u_s : Trm_c((g, a : U_S^id @ ℓ,
    ///   f : Π^{ℓ',ℓ⊔ℓ'}(y : U_T^{id,a/x}). W @ ℓ⊔ℓ',
    ///   ih : Π^{ℓ',ℓ''}(y : U_T^{id,a/x}). U_M^{id, f y/z} @ ℓ'⊔ℓ'')
    ///   ⊢ U_M^{id, sup(a, f)/z} @ ℓ'')`,
    /// `u_t : Trm_c(g ⊢ W(x:U_S^id).U_T^id @ ℓ⊔ℓ')`; locals: `x_S`, `x_T`,
    /// `x_M` (type motive!), `x_s`, `x_t`. Code of
    /// `elim_W (x. U_S^id. U_T^id) (z. U_M^id) (a f ih. u_s^id) u_t^id`;
    /// positive dependent eliminator like `tm_case`/`tm_elim_nat`.
    /// Extension.
    pub tm_elim_w: Rc<Term>,

    // -- finitary branching branches (docs/wf-former-design.md §6) --
    /// `(ℓ, g, U_T, u_k, x_T, x_k. t_Vec)` — univs: ℓ; globals: g,
    /// `U_T : Typ_c(g, ℓ)`, `u_k : Trm_c(g ⊢ Nat @ 0)`; locals: `x_T` (type
    /// motive), `x_k` (*term* motive — the length is a term). Code of the
    /// type `Vec^ℓ(U_T^id; u_k^id)`.
    pub ty_vec: Rc<Term>,
    /// `(ℓ, g, u_t, u_k, x_t, x_k. t'_Vec)` — univs: ℓ; globals: g,
    /// `u_t : Trm_c(g ⊢ Ty ℓ @ 1+ℓ)`, `u_k : Trm_c(g ⊢ Nat @ 0)`; locals:
    /// `x_t`, `x_k`. Code of the encoding `Vec^ℓ(u_t^id; u_k^id) : Ty ℓ`.
    pub tm_vec: Rc<Term>,
    /// `(g, u_k, x_k. t_Fin)` — globals: g, `u_k : Trm_c(g ⊢ Nat @ 0)`;
    /// locals: `x_k` (*term* motive). Code of the type `Fin(u_k^id) @ 0`;
    /// no universe binder, since `Fin` lives at 0.
    pub ty_fin: Rc<Term>,
    /// `(g, u_k, x_k. t'_Fin)` — as `ty_fin` but for the encoding
    /// `Fin(u_k^id) : Ty 0`.
    pub tm_fin: Rc<Term>,
    /// `(ℓ, g, U_S, u_n, x_S, x_n. t_Wf)` — univs: ℓ; globals: g,
    /// `U_S : Typ_c(g, ℓ)`, `u_n : Trm_c((g, x : U_S^id @ ℓ) ⊢ Nat @ 0)`;
    /// locals: `x_S` (type motive), `x_n` (term motive). Code of the type
    /// `Wf^ℓ(x:U_S^id). u_n^id`; mirrors `ty_w` with the positions replaced
    /// by an arity *term*, which is why only one universe is bound.
    pub ty_wf: Rc<Term>,
    /// `(ℓ, g, u_s, u_n, x_s, x_n. t'_Wf)` — univs: ℓ; globals: g,
    /// `u_s : Trm_c(g ⊢ Ty ℓ @ 1+ℓ)`,
    /// `u_n : Trm_c((g, x : El ℓ u_s^id @ ℓ) ⊢ Nat @ 0)`; locals: `x_s`,
    /// `x_n`. Code of the encoding `Wf^ℓ(x:u_s^id). u_n^id : Ty ℓ`.
    pub tm_wf: Rc<Term>,
    /// `(ℓ, g, U_S, u_n, u_a, u_cs, x_S, x_n, x_a, x_cs. t_supf)` — univs: ℓ;
    /// globals: g, `U_S : Typ_c(g, ℓ)`,
    /// `u_n : Trm_c((g, x : U_S^id @ ℓ) ⊢ Nat @ 0)`,
    /// `u_a : Trm_c(g ⊢ U_S^id @ ℓ)`,
    /// `u_cs : Trm_c(g ⊢ Vec^ℓ(Wf^ℓ(x:U_S^id).u_n^id; u_n^{id, u_a/x}) @ ℓ)`;
    /// locals: `x_S` (type motive!), `x_n`, `x_a`, `x_cs`. Code of
    /// `sup_f(x:U_S^id. u_n^id; u_a^id; u_cs^id)`; the analogue of `tm_sup`
    /// with the child *function* replaced by a child *tuple*.
    pub tm_supf: Rc<Term>,
    /// `(ℓ, ℓ', g, U_S, u_n, U_M, u_s, u_t, x_S, x_n, x_M, x_s, x_t.
    /// t_elimWf)` — univs: ℓ, ℓ'; globals: g, `U_S : Typ_c(g, ℓ)`,
    /// `u_n : Trm_c((g, x : U_S^id @ ℓ) ⊢ Nat @ 0)`,
    /// `U_M : Typ_c((g, z : Wf^ℓ(x:U_S^id).u_n^id @ ℓ), ℓ')`,
    /// `u_s : Trm_c((g, a : U_S^id @ ℓ, cs : Vec^ℓ(Wf; u_n^{id,a/x}) @ ℓ,
    ///   ih : Π^{0,ℓ'}(i : Fin u_n^{id,a/x}). U_M^{id, nth(…; cs; i)/z} @ ℓ')
    ///   ⊢ U_M^{id, sup_f(a; cs)/z} @ ℓ')`,
    /// `u_t : Trm_c(g ⊢ Wf^ℓ(x:U_S^id).u_n^id @ ℓ)`; locals: `x_S`, `x_n`,
    /// `x_M` (type motive!), `x_s`, `x_t`. Code of
    /// `elim_Wf (x. U_S^id. u_n^id) (z. U_M^id) (a cs ih. u_s^id) u_t^id`;
    /// the step telescope is [`wf_step_telescope`], shared with typing.
    pub tm_elim_wf: Rc<Term>,

    // -- strict equality (extension; docs/sprop-design.md §6) --
    /// `(ℓ, g, U_S, u_t, u_u, x_S, x_t, x_u. t_sEq)` — mirrors `ty_id`
    /// field-for-field (`sEq` is `Id` minus relevance; the code recursor is
    /// structural on syntax, so irrelevance changes nothing here).
    pub ty_seq: Rc<Term>,
    /// `(ℓ, g, u_s, u_t, u_u, x_s, x_t, x_u. t'_sEq)` — mirrors `tm_id`.
    pub tm_seq: Rc<Term>,
    /// `(ℓ, g. t_sEmpty)` — mirrors `ty_empty` (level-indexed nullary).
    pub ty_sempty: Rc<Term>,
    /// `(ℓ, g. t'_sEmpty)` — mirrors `tm_empty`.
    pub tm_sempty: Rc<Term>,
    /// `(ℓ, g, U_S, u_t, x_S, x_t. t_srefl)` — mirrors `tm_refl`.
    pub tm_srefl: Rc<Term>,
    /// `(ℓ, ℓ', g, U_I : Typ_c(g, ℓ),
    ///  U_P : Typ_c((g, x : U_I^id @ ℓ), ℓ'),
    ///  u_a, u_b : Trm_c(g ⊢ U_I^id @ ℓ),
    ///  u_e : Trm_c(g ⊢ sEq^ℓ(U_I^id; u_a^id; u_b^id) @ ℓ),
    ///  u_t : Trm_c(g ⊢ U_P^{id, u_a/x} @ ℓ'),
    ///  x_I, x_P, x_a, x_b, x_e, x_t. t_transp)` — `tm_j` with the motive
    /// scoped over one binder instead of two (transp's motive does not
    /// abstract the proof); globals in `Term::Transp` field order. The
    /// proof *is* recursed (`x_e`): irrelevance is a conversion fact, and
    /// code is syntax.
    pub tm_transp: Rc<Term>,
    /// `(ℓ, ℓ', g, U_M : Typ_c((g, x : sEmpty^{ℓ'} @ ℓ'), ℓ),
    ///  u_t : Trm_c(g ⊢ sEmpty^{ℓ'} @ ℓ'), x_M, x_t. t_elim_sE)` — mirrors
    /// `tm_elim_empty`.
    pub tm_elim_sempty: Rc<Term>,

    // -- propositional truncation (issues/sprop-squash.md) --
    /// `(ℓ, g, U_A, x_A. t_Squash)` — code of the type `∥U_A^id∥`.
    pub ty_squash: Rc<Term>,
    /// `(ℓ, g, u_A, x_A. t'_Squash)` — code of the encoding
    /// `Squash^ℓ(u_A^id) : Ty ℓ`.
    pub tm_squash: Rc<Term>,
    /// `(ℓ, g, U_A, u_a, x_A, x_a. t_squash)` — code of
    /// `squash^ℓ(U_A^id; u_a^id)`.
    pub tm_squash_in: Rc<Term>,
    /// `(ℓ, ℓ', g, U_A, U_B, u_b, u_q, x_A, x_B, x_b, x_q.
    /// t_elim_Squash)` — code of dependent squash elimination. `U_B` is
    /// scoped over `z : ∥U_A∥`; `u_b` over `x : U_A` and returns
    /// `∥U_B[squash x/z]∥`; `u_q : ∥U_A∥`.
    pub tm_elim_squash: Rc<Term>,
}

/// Base of a local context: empty (`·`) or a context variable `g`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CtxBase {
    Nil,
    Var(GlobalVar),
}

/// Local contexts `Γ, Δ := · | g | Γ, x : T @ l`.
///
/// `entries[0]` is the *outermost* binding; [`LocalVar`] 0 refers to the
/// last entry. Each entry's type is scoped over the entries before it.
#[derive(Clone, PartialEq, Eq)]
pub struct LocalCtx {
    pub base: CtxBase,
    pub entries: CtxEntries,
}

impl LocalCtx {
    /// The empty context `·`.
    pub fn nil() -> LocalCtx {
        LocalCtx { base: CtxBase::Nil, entries: CtxEntries::empty() }
    }

    /// The context variable `g` with no entries of its own.
    pub fn ctx_var(g: GlobalVar) -> LocalCtx {
        LocalCtx { base: CtxBase::Var(g), entries: CtxEntries::empty() }
    }

    /// `base` extended by `entries`, given outermost-first.
    pub fn from_vec(base: CtxBase, entries: Vec<CtxEntry>) -> LocalCtx {
        LocalCtx { base, entries: entries.into() }
    }

    /// `self, x : ty @ level`, sharing `self`'s spine.
    pub fn extended(&self, ty: Rc<Type>, level: Level) -> LocalCtx {
        LocalCtx { base: self.base, entries: self.entries.pushed(CtxEntry { ty, level }) }
    }

    /// Number of entries (the context's length as a Γ; the base contributes
    /// nothing).
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    /// Whether the context has no entries — `·` and `g` both qualify.
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// `Γ` truncated to its outermost `k` entries, sharing the spine.
    pub fn prefix(&self, k: usize) -> LocalCtx {
        LocalCtx { base: self.base, entries: self.entries.prefix(k) }
    }
}

#[derive(Clone, PartialEq, Eq)]
pub struct CtxEntry {
    pub ty: Rc<Type>,
    pub level: Level,
}

/// The entries of a [`LocalCtx`], as a persistent snoc list whose *head is
/// the innermost* binding.
///
/// Binder descent extends Γ by one entry while keeping the parent Γ alive,
/// which a `Vec` can only serve by copying the whole context. That copy was
/// the #1 self line of a release `heather check lib/ir_v1.hthr`
/// (`Vec<CtxEntry>::clone` 5.3%, its drop 2.6%, essentially all of it
/// `Env::push_entry` at a binder — issues/context-representation-clones.md).
/// Here extending is one allocation shared with the context it extends, and
/// dropping a derived context frees one cell.
///
/// Positions are still quoted the paper's way: position 0 is the *outermost*
/// entry (so [`std::ops::Index`] and [`CtxEntries::iter`] run outermost-first,
/// as the `Vec` did), while [`LocalVar`] 0 is the innermost and is served by
/// [`CtxEntries::nth_inner`], which runs *with* the spine. The list's own
/// direction is therefore the variable-lookup direction; anything that wants
/// the whole context outermost-first pays one O(|Γ|) walk, which every such
/// site already paid to read it.
#[derive(Clone)]
pub struct CtxEntries(Option<Rc<CtxNode>>);

/// An owning identity token for a persistent context spine.
///
/// Equality and hashing observe allocation identity, while the retained `Rc`
/// makes that identity impossible for the allocator to reuse during the
/// token's lifetime.
pub(crate) struct CtxEntriesIdentity(Option<Rc<CtxNode>>);

impl Clone for CtxEntriesIdentity {
    fn clone(&self) -> Self {
        CtxEntriesIdentity(self.0.clone())
    }
}

impl PartialEq for CtxEntriesIdentity {
    fn eq(&self, other: &Self) -> bool {
        match (&self.0, &other.0) {
            (None, None) => true,
            (Some(lhs), Some(rhs)) => Rc::ptr_eq(lhs, rhs),
            _ => false,
        }
    }
}

impl Eq for CtxEntriesIdentity {}

impl Hash for CtxEntriesIdentity {
    fn hash<H: Hasher>(&self, state: &mut H) {
        match &self.0 {
            None => 0u8.hash(state),
            Some(node) => {
                1u8.hash(state);
                std::ptr::hash(Rc::as_ptr(node), state);
            }
        }
    }
}

struct CtxNode {
    entry: CtxEntry,
    /// Length of the context ending *at* this node — `rest.len() + 1`.
    /// Cached so `len()` (read on nearly every kernel operation over Γ) and
    /// the length half of structural equality stay O(1).
    len: u32,
    rest: CtxEntries,
}

impl CtxEntries {
    pub fn empty() -> CtxEntries {
        CtxEntries(None)
    }

    pub fn len(&self) -> usize {
        match &self.0 {
            None => 0,
            Some(n) => n.len as usize,
        }
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_none()
    }

    /// An owning identity token for this persistent context spine.
    pub(crate) fn identity(&self) -> CtxEntriesIdentity {
        CtxEntriesIdentity(self.0.clone())
    }

    /// `self, entry` — O(1), sharing `self`.
    pub fn pushed(&self, entry: CtxEntry) -> CtxEntries {
        let len = self.len() as u32 + 1;
        CtxEntries(Some(Rc::new(CtxNode { entry, len, rest: self.clone() })))
    }

    /// In-place [`CtxEntries::pushed`], for the `Vec`-shaped callers.
    pub fn push(&mut self, entry: CtxEntry) {
        *self = self.pushed(entry);
    }

    /// The entry `i` binders out from the innermost one — the lookup for
    /// `LocalVar(i)`. Walks `i` cells, i.e. with the spine.
    pub fn nth_inner(&self, i: u32) -> Option<&CtxEntry> {
        let mut cur = self;
        let mut k = i;
        loop {
            let n = cur.0.as_ref()?;
            if k == 0 {
                return Some(&n.entry);
            }
            k -= 1;
            cur = &n.rest;
        }
    }

    /// The entry at position `i` counted from the *outermost* end — what
    /// `entries[i]` meant when this was a `Vec`.
    pub fn get(&self, i: usize) -> Option<&CtxEntry> {
        let n = self.len();
        if i >= n {
            return None;
        }
        self.nth_inner((n - 1 - i) as u32)
    }

    /// The innermost entry.
    pub fn last(&self) -> Option<&CtxEntry> {
        self.nth_inner(0)
    }

    /// The outermost `k` entries — `entries[..k]`, sharing the spine (one
    /// walk, no allocation). Panics if `k > len()`, as slicing did.
    pub fn prefix(&self, k: usize) -> CtxEntries {
        let n = self.len();
        assert!(k <= n, "context prefix {k} out of range for length {n}");
        let mut cur = self.clone();
        for _ in 0..(n - k) {
            let rest = cur.0.as_ref().expect("length is cached").rest.clone();
            cur = rest;
        }
        cur
    }

    /// Outermost-first, as `Vec::iter` was. O(|Γ|) up front — the spine runs
    /// the other way.
    pub fn iter(&self) -> CtxIter<'_> {
        let mut v: Vec<&CtxEntry> = Vec::with_capacity(self.len());
        let mut cur = self;
        while let Some(n) = cur.0.as_ref() {
            v.push(&n.entry);
            cur = &n.rest;
        }
        v.reverse();
        CtxIter(v.into_iter())
    }

    /// Outermost-first, owned.
    pub fn to_vec(&self) -> Vec<CtxEntry> {
        self.iter().cloned().collect()
    }

    /// `n` copies of one entry — the filler contexts that the shared β
    /// helpers read only the *length* of (`reduce.rs` module doc). One cell
    /// per entry rather than the `Vec`'s single allocation; both callers are
    /// off the hot path (a code recursor's scope, and `Wf`'s step
    /// telescope), which is why this is a loop and not a shared spine.
    pub fn repeat(entry: CtxEntry, n: usize) -> CtxEntries {
        let mut c = CtxEntries::empty();
        for _ in 0..n {
            c.push(entry.clone());
        }
        c
    }
}

pub struct CtxIter<'a>(std::vec::IntoIter<&'a CtxEntry>);

impl<'a> Iterator for CtxIter<'a> {
    type Item = &'a CtxEntry;

    fn next(&mut self) -> Option<&'a CtxEntry> {
        self.0.next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

impl ExactSizeIterator for CtxIter<'_> {}

impl DoubleEndedIterator for CtxIter<'_> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.0.next_back()
    }
}

impl<'a> IntoIterator for &'a CtxEntries {
    type Item = &'a CtxEntry;
    type IntoIter = CtxIter<'a>;

    fn into_iter(self) -> CtxIter<'a> {
        self.iter()
    }
}

impl std::ops::Index<usize> for CtxEntries {
    type Output = CtxEntry;

    fn index(&self, i: usize) -> &CtxEntry {
        self.get(i).unwrap_or_else(|| {
            panic!("context entry {i} out of range for length {}", self.len())
        })
    }
}

impl From<Vec<CtxEntry>> for CtxEntries {
    /// From an outermost-first `Vec`.
    fn from(v: Vec<CtxEntry>) -> CtxEntries {
        v.into_iter().collect()
    }
}

impl FromIterator<CtxEntry> for CtxEntries {
    /// From an outermost-first iterator.
    fn from_iter<I: IntoIterator<Item = CtxEntry>>(it: I) -> CtxEntries {
        let mut c = CtxEntries::empty();
        for e in it {
            c.push(e);
        }
        c
    }
}

impl Extend<CtxEntry> for CtxEntries {
    fn extend<I: IntoIterator<Item = CtxEntry>>(&mut self, it: I) {
        for e in it {
            self.push(e);
        }
    }
}

impl Default for CtxEntries {
    fn default() -> CtxEntries {
        CtxEntries::empty()
    }
}

/// Structural, with a pointer-equality shortcut: two contexts that share a
/// spine (the common case when conversion compares two scopes derived from
/// one) settle in O(1), and a length mismatch settles in O(1) either way.
/// `PartialEq` on `LocalCtx` is on the conversion path — boxed types compare
/// their Γ (ch. 06).
impl PartialEq for CtxEntries {
    fn eq(&self, other: &CtxEntries) -> bool {
        let mut a = self;
        let mut b = other;
        loop {
            match (&a.0, &b.0) {
                (None, None) => return true,
                (Some(x), Some(y)) => {
                    if Rc::ptr_eq(x, y) {
                        return true;
                    }
                    if x.len != y.len || x.entry != y.entry {
                        return false;
                    }
                    a = &x.rest;
                    b = &y.rest;
                }
                _ => return false,
            }
        }
    }
}

impl Eq for CtxEntries {}

/// Local substitutions `δ := ·^k_{g?} | wk^k_g | δ, t/x`.
///
/// The tail is the paper's `·^k_{g?}` / `wk^k_g`; `terms[0]` substitutes the
/// *outermost* entry of the target context Δ. The query operations δ̂ and δ̌
/// (used by composition) read the tail's length and base.
#[derive(Clone, PartialEq, Eq)]
pub struct LocalSubst {
    pub tail: SubstTail,
    pub terms: Vec<Rc<Term>>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SubstTail {
    /// `·^k_{g?}`: targets the empty context from a source context of length
    /// `len` ending in `base` (δ̂ = len, δ̌ = base).
    Empty { len: u32, base: CtxBase },
    /// `wk^k_g`: targets `g` from a source of length `len` ending in `g`.
    Wk { len: u32, ctx_var: GlobalVar },
}

impl LocalSubst {
    /// δ̂ — length of the source context recorded in the tail.
    pub fn source_len(&self) -> u32 {
        match self.tail {
            SubstTail::Empty { len, .. } | SubstTail::Wk { len, .. } => len,
        }
    }

    /// δ̌ — base of the source context recorded in the tail.
    pub fn source_base(&self) -> CtxBase {
        match self.tail {
            SubstTail::Empty { base, .. } => base,
            SubstTail::Wk { ctx_var, .. } => CtxBase::Var(ctx_var),
        }
    }
}

/// Global bindings `B` making up the global context Ψ.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum GlobalBinding {
    /// `g : Ctx` — a context variable.
    Ctx,
    /// `U : Typ_i(Δ, l)` — a type in Δ at layer `i ∈ {c, p}`.
    Ty {
        ctx: LocalCtx,
        layer: Layer,
        level: Level,
    },
    /// `u : Trm_i(Δ ⊢ T @ l)` — a term at layer `i ∈ {v, c}` (layer v means
    /// only a variable can be substituted for it).
    ///
    /// With `body: Some(t)` this is a **definition** `u : Trm_i(Δ ⊢ T @ l) := t`
    /// (extension, issues/simulate-conversion-cost.md). A definition is a
    /// declaration that additionally knows its body: every ch. 04 rule
    /// mentioning `u : Trm_i(…)` stays valid verbatim, and only δ-reduction
    /// consults `body` — which is why this is a field on `Tm` rather than a
    /// fourth binding form. `t` is scoped in Δ over this binding's *prefix*
    /// of Ψ (the same convention as `ty`) and is checked at layer `i`, so
    /// unfolding never produces a term that is illegal where the global was
    /// legal. Transparency is **layer-indexed**: the body unfolds at the
    /// computing layers p/m and never at c, where a global is syntax
    /// (ch. 06 blocks code recursion on globals and compares boxed globals
    /// syntactically). See `crate::reduce::Defs`.
    Tm {
        ctx: LocalCtx,
        layer: Layer,
        ty: Rc<Type>,
        level: Level,
        body: Option<Rc<Term>>,
    },
}

impl GlobalBinding {
    /// The declaration `u : Trm_i(Δ ⊢ T @ l)` — no body, hence opaque.
    pub fn opaque_tm(ctx: LocalCtx, layer: Layer, ty: Rc<Type>, level: Level) -> GlobalBinding {
        GlobalBinding::Tm { ctx, layer, ty, level, body: None }
    }

    /// The definition `u : Trm_i(Δ ⊢ T @ l) := t`.
    pub fn defined_tm(
        ctx: LocalCtx,
        layer: Layer,
        ty: Rc<Type>,
        level: Level,
        body: Rc<Term>,
    ) -> GlobalBinding {
        GlobalBinding::Tm { ctx, layer, ty, level, body: Some(body) }
    }
}

/// The global context Ψ. `bindings[0]` is outermost; [`GlobalVar`] 0 refers
/// to the last binding.
///
/// The binding list is persistent and chunked so that *cloning Ψ is O(1)*.
/// Typing and conversion carry Ψ inside an environment they clone at every
/// binder descent, and a `fn` is now a bodied binding
/// (issues/simulate-conversion-cost.md), so a deep copy per descent was the
/// single largest line of a real profile
/// (issues/context-representation-clones.md). Sharing is safe here in a way
/// it is not for Γ: Ψ never appears *inside* a term, so no conversion rule
/// compares it structurally, and it is only ever extended at declaration
/// granularity. Appending to a shared context copies at most one bounded tail
/// rather than the entire prefix.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct GlobalCtx {
    pub bindings: GlobalBindings,
}

const GLOBAL_CHUNK: usize = 64;

#[derive(Debug, Clone, PartialEq, Eq)]
struct GlobalChunk {
    bindings: Rc<Vec<GlobalBinding>>,
}

/// Persistent outermost-first storage for Ψ.
#[derive(Clone)]
pub struct GlobalBindings {
    sealed: Rc<Vec<GlobalChunk>>,
    sealed_len: usize,
    tail: Rc<Vec<GlobalBinding>>,
    identity: Rc<()>,
}

impl Default for GlobalBindings {
    fn default() -> Self {
        Self::new(Vec::new())
    }
}

impl PartialEq for GlobalBindings {
    fn eq(&self, other: &Self) -> bool {
        self.len() == other.len() && self.iter().eq(other.iter())
    }
}

impl Eq for GlobalBindings {}

impl std::fmt::Debug for GlobalBindings {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}

impl GlobalBindings {
    fn new(bindings: Vec<GlobalBinding>) -> Self {
        let mut sealed = Vec::new();
        let mut tail = Vec::with_capacity(GLOBAL_CHUNK);
        let mut sealed_len = 0;
        for binding in bindings {
            tail.push(binding);
            if tail.len() == GLOBAL_CHUNK {
                sealed_len += tail.len();
                sealed.push(GlobalChunk {
                    bindings: Rc::new(std::mem::take(&mut tail)),
                });
            }
        }
        Self {
            sealed: Rc::new(sealed),
            sealed_len,
            tail: Rc::new(tail),
            identity: Rc::new(()),
        }
    }

    pub fn len(&self) -> usize {
        self.sealed_len + self.tail.len()
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn get(&self, index: usize) -> Option<&GlobalBinding> {
        if index >= self.sealed_len {
            return self.tail.get(index - self.sealed_len);
        }
        self.sealed
            .get(index / GLOBAL_CHUNK)?
            .bindings
            .get(index % GLOBAL_CHUNK)
    }

    pub fn last(&self) -> Option<&GlobalBinding> {
        self.tail
            .last()
            .or_else(|| self.sealed.last().and_then(|chunk| chunk.bindings.last()))
    }

    pub fn iter(&self) -> impl Iterator<Item = &GlobalBinding> {
        self.sealed
            .iter()
            .flat_map(|chunk| chunk.bindings.iter())
            .chain(self.tail.iter())
    }

    pub fn to_vec(&self) -> Vec<GlobalBinding> {
        self.iter().cloned().collect()
    }

    pub(crate) fn identity(&self) -> Rc<()> {
        Rc::clone(&self.identity)
    }

    pub(crate) fn same_identity(&self, other: &Self) -> bool {
        Rc::ptr_eq(&self.identity, &other.identity)
    }

    fn push(&mut self, binding: GlobalBinding) {
        if self.tail.len() == GLOBAL_CHUNK {
            self.seal_tail();
        }
        Rc::make_mut(&mut self.tail).push(binding);
        self.identity = Rc::new(());
    }

    fn seal_tail(&mut self) {
        if self.tail.is_empty() {
            return;
        }
        debug_assert_eq!(self.tail.len(), GLOBAL_CHUNK);
        self.sealed_len += self.tail.len();
        Rc::make_mut(&mut self.sealed).push(GlobalChunk {
            bindings: Rc::clone(&self.tail),
        });
        self.tail = Rc::new(Vec::new());
        self.identity = Rc::new(());
    }
}

impl GlobalCtx {
    /// Ψ from its bindings, outermost first.
    pub fn new(bindings: Vec<GlobalBinding>) -> GlobalCtx {
        GlobalCtx { bindings: GlobalBindings::new(bindings) }
    }

    /// Append one binding (copy-on-write if this Ψ is shared).
    pub fn push(&mut self, b: GlobalBinding) {
        self.bindings.push(b);
    }

    /// Append several bindings (copy-on-write if this Ψ is shared).
    pub fn extend(&mut self, bs: impl IntoIterator<Item = GlobalBinding>) {
        for binding in bs {
            self.bindings.push(binding);
        }
    }

    /// Share the bounded append tail for an immutable semantic image.
    pub fn semantic_snapshot(&self) -> GlobalCtx {
        self.clone()
    }
}

impl std::ops::Index<usize> for GlobalBindings {
    type Output = GlobalBinding;

    fn index(&self, index: usize) -> &Self::Output {
        self.get(index).expect("global binding index out of bounds")
    }
}

impl From<Vec<GlobalBinding>> for GlobalCtx {
    fn from(bindings: Vec<GlobalBinding>) -> GlobalCtx {
        GlobalCtx::new(bindings)
    }
}

// ---------------------------------------------------------------------------
// Derived constructions materialized by the `Wf` rules
//
// `Wf`'s typing and β rules mention `nth` and a three-entry step telescope.
// Neither is a former: both are fixed syntax schemas, built here once so the
// typing rule (typing.rs) and the neutral comparison (conv.rs) cannot drift
// apart — the transcription hazard flagged in docs/wf-former-design.md §6.
// ---------------------------------------------------------------------------

/// `nth^l(T; k; cs; i) : T` — project the `i`th component out of a
/// `Vec^l(T; k)`, by `elim_Nat` on the length at the motive
/// `Π(cs : Vec(T; k̂)). Π(i : Fin k̂). T`:
///
/// ```text
/// nth(T; 0;   cs; i) ⇝ elim_Empty i           (Fin 0 is Empty)
/// nth(T; S k; cs; i) ⇝ case i of inl _ ⇒ fst cs | inr j ⇒ nth(T; k; snd cs; j)
/// ```
///
/// So at a literal length it reduces to the projections *whatever the tuple
/// is* — including a neutral one, which is what makes the `Fin`-indexed
/// induction hypothesis usable (docs/wf-former-design.md §3).
///
/// All four arguments live in the ambient Γ; the result does too.
pub fn nth(level: &Level, elem: &Rc<Type>, len: &Rc<Term>, cs: Rc<Term>, idx: Rc<Term>) -> Term {
    let vec_at = |elem_shift: u32, len: Rc<Term>| Type::Vec {
        level: level.clone(),
        elem: Rc::new(elem.shift_local(elem_shift)),
        len,
    };
    let var = |i: u32| Rc::new(Term::Var(LocalVar(i)));

    // Motive in (Γ, k̂): Π(cs : Vec(T; k̂)). Π(i : Fin k̂). T.
    let motive = Type::Pi {
        dom_level: level.clone(),
        cod_level: level.clone(),
        dom: Rc::new(vec_at(1, var(0))),
        cod: Rc::new(Type::Pi {
            dom_level: Level::Zero,
            cod_level: level.clone(),
            dom: Rc::new(Type::Fin { len: var(1) }),
            cod: Rc::new(elem.shift_local(3)),
        }),
    };

    // Base in Γ: λ(cs : Vec(T; 0)). λ(i : Fin 0). elim_Empty(_. T; i).
    let base = Term::Lam {
        dom_level: level.clone(),
        cod_level: level.clone(),
        dom: Rc::new(vec_at(0, Rc::new(Term::Zero))),
        body: Rc::new(Term::Lam {
            dom_level: Level::Zero,
            cod_level: level.clone(),
            dom: Rc::new(Type::Fin { len: Rc::new(Term::Zero) }),
            body: Rc::new(Term::ElimEmpty {
                level: level.clone(),
                // `Fin(0) ⇝ Empty^0` — `Fin` is declared at level 0.
                scrut_level: Level::Zero,
                motive: Rc::new(elem.shift_local(3)),
                scrut: var(0),
            }),
        }),
    };

    // Step in (Γ, k̂, r), k̂ = 1, r = 0; under both λs (Γ, k̂=3, r=2, cs=1, i=0).
    // The Σ-typed projections out of `cs` are what `Vec (S k̂)` reduces to.
    let fst_cs = Term::Fst {
        fst_level: level.clone(),
        snd_level: level.clone(),
        fst_ty: Rc::new(elem.shift_local(5)),
        snd_ty: Rc::new(vec_at(6, var(5))),
        pair: var(2),
    };
    let snd_cs = Term::Snd {
        fst_level: level.clone(),
        snd_level: level.clone(),
        fst_ty: Rc::new(elem.shift_local(5)),
        snd_ty: Rc::new(vec_at(6, var(5))),
        pair: var(2),
    };
    // r (snd cs) j, in (Γ, k̂=4, r=3, cs=2, i=1, j=0).
    let rec_call = Term::App {
        fun: Rc::new(Term::App {
            fun: var(3),
            dom_level: level.clone(),
            cod_level: level.clone(),
            dom: Rc::new(vec_at(5, var(4))),
            cod: Rc::new(Type::Pi {
                dom_level: Level::Zero,
                cod_level: level.clone(),
                dom: Rc::new(Type::Fin { len: var(5) }),
                cod: Rc::new(elem.shift_local(7)),
            }),
            arg: Rc::new(snd_cs),
        }),
        dom_level: Level::Zero,
        cod_level: level.clone(),
        dom: Rc::new(Type::Fin { len: var(4) }),
        cod: Rc::new(elem.shift_local(6)),
        arg: var(0),
    };
    let step = Term::Lam {
        dom_level: level.clone(),
        cod_level: level.clone(),
        dom: Rc::new(vec_at(2, Rc::new(Term::Succ(var(1))))),
        body: Rc::new(Term::Lam {
            dom_level: Level::Zero,
            cod_level: level.clone(),
            dom: Rc::new(Type::Fin { len: Rc::new(Term::Succ(var(2))) }),
            body: Rc::new(Term::Case {
                lhs_level: Level::Zero,
                rhs_level: Level::Zero,
                motive_level: level.clone(),
                // `Fin(S k) ⇝ Unit^0 +^{0,0} Fin(k)`.
                lhs: Rc::new(Type::Unit { level: Level::Zero }),
                rhs: Rc::new(Type::Fin { len: var(3) }),
                motive: Rc::new(elem.shift_local(5)),
                case_l: Rc::new(fst_cs),
                case_r: Rc::new(rec_call),
                scrut: var(0),
            }),
        }),
    };

    // The recursion, then applied to the tuple and the index.
    let recursion = Term::ElimNat {
        level: level.clone(),
        motive: Rc::new(motive),
        base: Rc::new(base),
        step: Rc::new(step),
        scrut: Rc::clone(len),
    };
    let at_cs = Term::App {
        fun: Rc::new(recursion),
        dom_level: level.clone(),
        cod_level: level.clone(),
        dom: Rc::new(vec_at(0, Rc::clone(len))),
        cod: Rc::new(Type::Pi {
            dom_level: Level::Zero,
            cod_level: level.clone(),
            dom: Rc::new(Type::Fin { len: Rc::new(len.shift_local(1)) }),
            cod: Rc::new(elem.shift_local(2)),
        }),
        arg: cs,
    };
    Term::App {
        fun: Rc::new(at_cs),
        dom_level: Level::Zero,
        cod_level: level.clone(),
        dom: Rc::new(Type::Fin { len: Rc::clone(len) }),
        cod: Rc::new(elem.shift_local(1)),
        arg: idx,
    }
}

/// The `elim_Wf` step telescope. Given the former's parts in Γ, returns the
/// three binding types
///
/// ```text
/// cs : Vec^l(Wf; n[a/x])                                    in (Γ, a : S)
/// ih : Π(i : Fin n[a/x]). M[nth^l(Wf; n[a/x]; cs; i)/z]      in (Γ, a, cs)
/// s  : M[sup_f(a; cs)/z]                                    in (Γ, a, cs, ih)
/// ```
///
/// In `(Γ, a : S)` the arity *is* `n[a/x]` already — `a` sits exactly where
/// the binder `x` was — which is the same shortcut `elim_W`'s rules take
/// with `T[a/x]`.
pub fn wf_step_telescope(
    gamma: &LocalCtx,
    level: &Level,
    motive_level: &Level,
    shape: &Rc<Type>,
    arity: &Rc<Term>,
    motive: &Rc<Type>,
) -> (Type, Type, Type) {
    let wf = Type::Wf {
        level: level.clone(),
        shape: Rc::clone(shape),
        arity: Rc::clone(arity),
    };
    wf_step_telescope_at(gamma, level, motive_level, shape, arity, motive, &wf, None)
}

/// [`wf_step_telescope`] with the two `Wf`-typed *annotation* positions —
/// `cs`'s `Vec` element and `nth`'s element — spelled by the caller instead of
/// rebuilt from `shape`/`arity`.
///
/// The elaborator passes `El (D#tycode^δ)` here
/// (`docs/family-type-code-defs-design.md`, 2026-08-12 extension): those two
/// positions are ordinary type annotations, so any type convertible with
/// `Wf(shape). arity` stands in them, and naming `⟦D⟧` once is what stops the
/// `match` lowering from carrying every field type verbatim through Θ(arms)
/// copies ([[wf-field-conversion-cost]]).
///
/// What `d_ty` does **not** reach: the `Supf` the step's type is stated at,
/// whose `shape`/`arity` are the former's own slots and not a type annotation.
/// Those are `slots`' business — the elaborator passes
/// `El (D#shape^δ)`/`app(D#arity^δ; x₀)` there
/// (`docs/wf-shape-code-design.md` §3.2), and `None` keeps the caller's own
/// `shape`/`arity`, which is what every kernel caller wants: `typing.rs` and
/// `conv.rs` build the telescope *from* the slots of the term in front of
/// them, so re-spelling there would be inventing a term the checker never saw.
/// This function is therefore the only transcription of the telescope, still —
/// `wf_step_telescope` is one call to it.
#[allow(clippy::too_many_arguments)]
pub fn wf_step_telescope_at(
    gamma: &LocalCtx,
    level: &Level,
    motive_level: &Level,
    shape: &Rc<Type>,
    arity: &Rc<Term>,
    motive: &Rc<Type>,
    d_ty: &Type,
    slots: Option<(&Rc<Type>, &Rc<Term>)>,
) -> (Type, Type, Type) {
    let wf = d_ty.clone();
    // Every *arity* written below is an annotation like `d_ty` is — a `Vec`
    // length, a `Fin` length, `nth`'s length — so it takes `slots`' spelling
    // too, and for a second reason beyond size: the `elim_Wf` these types
    // surround carries `slots` in its own two positions, so the kernel
    // rebuilds this very telescope from them. Spelling the two sides alike is
    // what keeps the comparison syntactic instead of a δ-unfold per branch.
    let (s_slot, a_slot) = slots.unwrap_or((shape, arity));
    // cs : Vec(⟦D⟧; n) in (Γ, a).
    let cs_ty = Type::Vec {
        level: level.clone(),
        elem: Rc::new(wf.shift_local(1)),
        len: Rc::clone(a_slot),
    };
    // ih in (Γ, a, cs); its body is in (Γ, a, cs, i) where cs = 1, i = 0.
    let nth_at_i = nth(
        level,
        &Rc::new(wf.shift_local(3)),
        &Rc::new(a_slot.shift_local(2)),
        Rc::new(Term::Var(LocalVar(1))),
        Rc::new(Term::Var(LocalVar(0))),
    );
    let ih_ty = Type::Pi {
        dom_level: Level::Zero,
        cod_level: motive_level.clone(),
        dom: Rc::new(Type::Fin { len: Rc::new(a_slot.shift_local(1)) }),
        cod: Rc::new(
            motive.apply_local(&LocalSubst::id(gamma).shift_local(3).extended(Rc::new(nth_at_i))),
        ),
    };
    // s : M[sup_f(a; cs)/z] — the constructor built in (Γ, a, cs), then
    // weakened past `ih`. The `Supf`'s own slots are `shape`/`arity` (or
    // `slots`' spelling of them), never `d_ty`: they are the former's
    // components, not an annotation — and the shift goes through the `Wf` so
    // that `arity`, which is scoped under the shape's binder, crosses the
    // right number of them.
    let real_wf = Type::Wf {
        level: level.clone(),
        shape: Rc::clone(s_slot),
        arity: Rc::clone(a_slot),
    };
    let Type::Wf { shape: s2, arity: n2, .. } = real_wf.shift_local(2) else {
        unreachable!("shifting a Wf yields a Wf")
    };
    let sup_ac = Term::Supf {
        level: level.clone(),
        shape: s2,
        arity: n2,
        label: Rc::new(Term::Var(LocalVar(1))),
        children: Rc::new(Term::Var(LocalVar(0))),
    };
    let step_ty = motive.apply_local(
        &LocalSubst::id(gamma).shift_local(3).extended(Rc::new(sup_ac.shift_local(1))),
    );
    (cs_ty, ih_ty, step_ty)
}

#[cfg(test)]
mod global_ctx_tests {
    use std::sync::Arc as Rc;

    use super::*;

    #[test]
    fn semantic_snapshot_shares_chunks_and_bounds_suffix_detachment() {
        let mut base = GlobalCtx::new(vec![GlobalBinding::Ctx; 150]);
        for _ in 0..25 {
            base.push(GlobalBinding::Ctx);
        }
        let image = base.semantic_snapshot();
        assert_eq!(image.bindings.len(), 175);
        assert!(image.bindings.tail.len() <= GLOBAL_CHUNK);

        let mut suffix = image.clone();
        assert!(Rc::ptr_eq(&image.bindings.sealed, &suffix.bindings.sealed));
        let tail_len = image.bindings.tail.len();
        suffix.push(GlobalBinding::Ctx);
        assert_eq!(image.bindings.len(), 175);
        assert_eq!(suffix.bindings.len(), 176);
        assert!(Rc::ptr_eq(&image.bindings.sealed, &suffix.bindings.sealed));
        assert_eq!(suffix.bindings.tail.len(), tail_len + 1);
        assert!(suffix.bindings.iter().all(|b| *b == GlobalBinding::Ctx));
        assert_eq!(suffix, GlobalCtx::new(vec![GlobalBinding::Ctx; 176]));
    }
}
