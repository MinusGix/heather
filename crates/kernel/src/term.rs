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

use std::rc::Rc;

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
    /// `Σ^{l,l'}(x : S). T` — dependent pair type; `snd` binds one local
    /// variable (of type `fst`). Lives at `l ⊔ l'`. Extension beyond DeLaM
    /// ch. 04 (see issues/kernel-v1-extensions.md).
    Sigma {
        fst_level: Level,
        snd_level: Level,
        fst: Rc<Type>,
        snd: Rc<Type>,
    },
    /// `Unit` — the unit type. A single inhabitant `⟨⟩` ([`Term::Triv`]) with
    /// definitional η (proof irrelevance), so no eliminator. Lives at level 0.
    /// Extension beyond DeLaM ch. 04 (see issues/kernel-v1-extensions.md).
    Unit,
    /// `Empty` — the empty type; no inhabitants, eliminated by
    /// [`Term::ElimEmpty`]. Lives at level 0. Extension beyond DeLaM ch. 04.
    Empty,
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
    /// Substrate for `Wf` (docs/wf-former-design.md §1.1); currently gated
    /// out of the code layer until `TmVec` + rec.rs branches land
    /// (issues/wf-former.md phase 3).
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
    /// `Σ^{l,l'}(x : s). t : Ty (l ⊔ l')` where `s : Ty l`; `snd` binds one
    /// local variable (of type `El s`) — encoding of the dependent pair
    /// type. Extension beyond DeLaM ch. 04.
    TmSigma {
        fst_level: Level,
        snd_level: Level,
        fst: Rc<Term>,
        snd: Rc<Term>,
    },
    /// `Unit : Ty 0` — encoding of the unit type (decoded by
    /// `El (Unit) ⇝ Unit`). Extension beyond DeLaM ch. 04.
    TmUnit,
    /// `Empty : Ty 0` — encoding of the empty type (decoded by
    /// `El (Empty) ⇝ Empty`). Extension beyond DeLaM ch. 04.
    TmEmpty,
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
    /// `⟨⟩ : Unit` — the unique inhabitant of `Unit`. By η every term of
    /// `Unit` type is convertible to it (proof irrelevance), so `Unit` has no
    /// eliminator.
    Triv,
    /// `elim_Empty^l (x. M; t) : M[t/x]` — absurdity elimination; `motive`
    /// binds one local variable (`x : Empty`), `scrut : Empty`. No β rule
    /// (`Empty` has no constructors); neutral on a neutral scrutinee. Annotated
    /// like `elim_Nat` so it infers.
    ElimEmpty {
        level: Level,
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
    /// `(g. t_Unit)` — globals: g. Code of the type `Unit`; mirrors `ty_nat`.
    /// Extension beyond ch. 04 (kernel-v1-extensions).
    pub ty_unit: Rc<Term>,
    /// `(g. t_Empty)` — globals: g. Code of the type `Empty`; mirrors
    /// `ty_nat`. Extension beyond ch. 04 (kernel-v1-extensions).
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
    /// `x_s'`, `x_t`.
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
    /// `(g. t'_Unit)` — globals: g. Code of the encoding `Unit : Ty 0`;
    /// mirrors `tm_nat`. Extension beyond ch. 04 (kernel-v1-extensions).
    pub tm_unit: Rc<Term>,
    /// `(g. t'_Empty)` — globals: g. Code of the encoding `Empty : Ty 0`;
    /// mirrors `tm_nat`. Extension beyond ch. 04 (kernel-v1-extensions).
    pub tm_empty: Rc<Term>,
    /// `(g. t_triv)` — globals: g. Code of the intro `⟨⟩ : Unit`; mirrors
    /// `tm_zero`. Extension beyond ch. 04 (kernel-v1-extensions).
    pub tm_triv: Rc<Term>,
    /// `(ℓ, g, U_M, u_t, x_M, x_t. t_elimE)` — univs: ℓ; globals: g,
    /// `U_M : Typ_c((g, x : Empty @ 0), ℓ)`, `u_t : Trm_c(g ⊢ Empty @ 0)`;
    /// locals: `x_M` (type motive!), `x_t`. Code of `elim_Empty^ℓ (x. U_M^id;
    /// u_t^id)`; mirrors `tm_elim_nat` minus base/step. Extension
    /// (kernel-v1-extensions).
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
    pub entries: Vec<CtxEntry>,
}

#[derive(Clone, PartialEq, Eq)]
pub struct CtxEntry {
    pub ty: Rc<Type>,
    pub level: Level,
}

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
    Tm {
        ctx: LocalCtx,
        layer: Layer,
        ty: Rc<Type>,
        level: Level,
    },
}

/// The global context Ψ. `bindings[0]` is outermost; [`GlobalVar`] 0 refers
/// to the last binding.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct GlobalCtx {
    pub bindings: Vec<GlobalBinding>,
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
                lhs: Rc::new(Type::Unit),
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
    // cs : Vec(Wf; n) in (Γ, a).
    let cs_ty = Type::Vec {
        level: level.clone(),
        elem: Rc::new(wf.shift_local(1)),
        len: Rc::clone(arity),
    };
    // ih in (Γ, a, cs); its body is in (Γ, a, cs, i) where cs = 1, i = 0.
    let nth_at_i = nth(
        level,
        &Rc::new(wf.shift_local(3)),
        &Rc::new(arity.shift_local(2)),
        Rc::new(Term::Var(LocalVar(1))),
        Rc::new(Term::Var(LocalVar(0))),
    );
    let ih_ty = Type::Pi {
        dom_level: Level::Zero,
        cod_level: motive_level.clone(),
        dom: Rc::new(Type::Fin { len: Rc::new(arity.shift_local(1)) }),
        cod: Rc::new(
            motive.apply_local(&LocalSubst::id(gamma).shift_local(3).extended(Rc::new(nth_at_i))),
        ),
    };
    // s : M[sup_f(a; cs)/z] — the constructor built in (Γ, a, cs), then
    // weakened past `ih`.
    let Type::Wf { shape: s2, arity: n2, .. } = wf.shift_local(2) else {
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
