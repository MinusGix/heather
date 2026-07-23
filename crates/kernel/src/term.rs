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
