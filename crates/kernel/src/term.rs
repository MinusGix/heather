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

pub use heather_numeral::Numeral;
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
#[derive(Clone, Eq)]
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
    /// (`conv.rs` irrelevance arm). It has no eliminator: it is inhabited
    /// exactly when its endpoints convert, with one proof up to conversion
    /// (`transp` was removed with route 2b's fording,
    /// docs/iwf-former-design.md §7). Extension beyond DeLaM ch. 04
    /// (docs/sprop-design.md §2.1). Admitted at layer c like every
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
    /// reason. As at [`Type::Empty`] (Empty η),
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
    /// `DVec^l(k; i. F)` — dependent fixed-length tuples: [`Type::Vec`] with
    /// a per-position element type. `fam` binds one local, `i : Fin k`.
    /// `DVec(0; i. F) ⇝ Unit^l`,
    /// `DVec(S k; i. F) ⇝ Σ^{l,l}(_ : F[inl ⟨⟩/i]). DVec(k; j. F[inr j/i])`
    /// (the injections annotated by `Fin(S k)`'s reduct, `Unit^0 + Fin(k)`);
    /// neutral at a neutral length, no η of its own. Lives at `l`. Children
    /// substrate of `IWf` (docs/iwf-former-design.md §1.1); its projection is
    /// the derived [`dnth`], not a former.
    ///
    /// Code since the rec.rs round (design §13 step 4): `TmDVec` and the
    /// `ty_dvec`/`tm_dvec` branches, as `Vec` became at its phase 3. A
    /// takes-a-binder former rather than a
    /// family argument because Heather has no type-valued functions. `Vec^l(T;
    /// k)` and `DVec^l(k; _. T)` agree reduct for reduct at a canonical
    /// length and are distinct neutral types at a neutral one; they are not
    /// converted into each other (design §10, option 1).
    DVec {
        level: Level,
        len: Rc<Term>,
        fam: Rc<Type>,
    },
    /// `IWf^{l,li}(I; x:S. n; x. o; x i. c)(m)` — the finitary indexed
    /// fixed point, Dybjer's finitary inductive families in [`Type::Wf`]'s
    /// shape (docs/iwf-former-design.md §1.2). `idx` is the index type `I`
    /// at `li`, `shape` the shapes `S` at `l`; `arity` (`n : Nat`) and `out`
    /// (the constructor's output index `o : I`) bind one local, `x : S`;
    /// `child` (the child index `c : I` at position `i`) binds two,
    /// `x : S, i : Fin n`; `index` is the family's index `m : I`, in Γ.
    /// Lives at `l ⊔ li`, forced by the codes (design §1.2). Introduced by
    /// [`Term::Supi`] at index `o[a/x]`, eliminated by [`Term::ElimIWf`] at
    /// any index; positive, no η, and nothing stored but the shape and the
    /// children, so there is no irrelevance arm (design §5).
    ///
    /// The signature (everything but the index) is one shared [`IWfSig`]:
    /// flat, its two levels and five components would make every `Type`
    /// a third larger, and the checker's recursion holds `Type`s in each
    /// frame (`docs/native-depth-budget-design.md`).
    ///
    /// Code since the rec.rs round (design §13 step 4), as [`Type::DVec`]:
    /// `TmIWf`, and the `ty_iwf`/`tm_iwf`/`tm_sup_i`/`tm_elim_iwf` branches.
    IWf { sig: Rc<IWfSig>, index: Rc<Term> },
    /// `M^{l,l',li}(I; i. S; i s. P; i s p. o)(j)` — the indexed final
    /// coalgebra, the dual of [`Type::W`] with [`Type::IWf`]'s index
    /// (docs/kernel-coinduction-design.md §1.1). `idx` is the index type `I`
    /// at `li`; `shape` (`S @ l`) binds `i : I`, `pos` (`P @ l'`) binds
    /// `i, s : S`, and `next` (the child's index `o : I`) binds `i, s,
    /// p : P`; `index` is `j : I`, in Γ. The shapes depend on the index and
    /// the children's indices are computed, so a value stores no equation.
    /// Lives at `l ⊔ l' ⊔ li`. **Negative**: observed only by [`Term::Out`],
    /// introduced only by [`Term::Corec`], with β under `out` and **no η**
    /// (design §2.1), so conversion stays intensional.
    ///
    /// The signature is one shared [`MSig`], as `IWf`'s is.
    ///
    /// Code since docs/kernel-m-codes-design.md: `TmM` and four branches.
    M { sig: Rc<MSig>, index: Rc<Term> },
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

/// How many local variable leaves each thread interns ([`Term::var_rc`]).
/// Indices at or above it are allocated per call, as before: Γ is rarely
/// that long, and a bound keeps a thread's table small.
const INTERNED_LOCAL_VARS: u32 = 4096;

thread_local! {
    /// This thread's shared `Var(i)` leaves, grown on demand up to
    /// [`INTERNED_LOCAL_VARS`]. Per thread so that the kernel workers do not
    /// contend on one refcount per index; a leaf is an ordinary `Rc` and may
    /// still move to another thread with the term holding it.
    static LOCAL_VAR_LEAVES: std::cell::RefCell<Vec<Rc<Term>>> = const { std::cell::RefCell::new(Vec::new()) };
}

impl Term {
    /// A shared `Var(i)` leaf (`issues/subst-per-call-allocations.md`): an
    /// interned `Rc` for an index below [`INTERNED_LOCAL_VARS`], a fresh
    /// one above it. Sharing a leaf changes no syntax, only identity, and
    /// identity is only ever read by memos that already key on the scope
    /// (typing), answer leaves before their table (bounds), or skip leaves
    /// (substitution, `subst.rs` §Keeping a shared DAG shared).
    pub fn var_rc(i: u32) -> Rc<Term> {
        if i >= INTERNED_LOCAL_VARS {
            return Rc::new(Term::Var(LocalVar(i)));
        }
        LOCAL_VAR_LEAVES.with(|leaves| {
            let mut leaves = leaves.borrow_mut();
            Self::grow_var_leaves(&mut leaves, i + 1);
            Rc::clone(&leaves[i as usize])
        })
    }

    /// `[Var(m - 1), …, Var(0)]`: the payloads of `id(Γ)` for `|Γ| = m`,
    /// one table borrow for all of them.
    pub fn var_rcs_descending(m: u32) -> Vec<Rc<Term>> {
        if m > INTERNED_LOCAL_VARS {
            return (0..m).map(|j| Term::var_rc(m - 1 - j)).collect();
        }
        LOCAL_VAR_LEAVES.with(|leaves| {
            let mut leaves = leaves.borrow_mut();
            Self::grow_var_leaves(&mut leaves, m);
            leaves[..m as usize].iter().rev().cloned().collect()
        })
    }

    fn grow_var_leaves(leaves: &mut Vec<Rc<Term>>, len: u32) {
        let have = leaves.len() as u32;
        if have < len {
            // Grow geometrically, so a context deepening one binder at a time
            // does not come back here per binder.
            let want = len.max(have * 2).max(64).min(INTERNED_LOCAL_VARS);
            leaves.extend((have..want).map(|i| Rc::new(Term::Var(LocalVar(i)))));
        }
    }

    /// `Rc::new(self)`, except that a `Var` leaf comes from the shared table
    /// ([`Term::var_rc`]) instead of a fresh allocation.
    #[inline]
    pub fn into_rc(self) -> Rc<Term> {
        match self {
            Term::Var(LocalVar(i)) => Term::var_rc(i),
            t => Rc::new(t),
        }
    }
}

/// Terms `s, t` (sort `Exp`).
#[derive(Clone, Eq)]
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
    /// `DVec^l(k; i. f) : Ty l` where `k : Nat` and `f : Ty l` under
    /// `i : Fin k` — encoding of the dependent tuple (decoded by
    /// `El (DVec^l(k; i. f)) ⇝ DVec^l(k; i. El^l f)`;
    /// docs/iwf-former-design.md §6). The length is a term of the same scope,
    /// the family binds one local, as the type former's does.
    TmDVec {
        level: Level,
        len: Rc<Term>,
        fam: Rc<Term>,
    },
    /// `IWf^{l,li}(u_I; x:u_S. n; x. o; x i. c)(m) : Ty (l ⊔ li)` — encoding
    /// of the finitary indexed fixed point applied at index `m`
    /// (docs/iwf-former-design.md §6), decoded by `El(TmIWf …) ⇝
    /// IWf(El idx; x : El shape. arity; out; child)(index)`. `arity` and
    /// `out` bind `x`, `child` binds `x, i : Fin arity`; they and `index` are
    /// terms (of `Nat` and of `El idx`), carried across the decoding
    /// unchanged. Flat, as [`Term::TmM`] is: two levels and six pointers is
    /// `Term`'s widest shape already.
    TmIWf {
        level: Level,
        idx_level: Level,
        idx: Rc<Term>,
        shape: Rc<Term>,
        arity: Rc<Term>,
        out: Rc<Term>,
        child: Rc<Term>,
        index: Rc<Term>,
    },
    /// `M^{l,l',li}(u_I; i. u_S; i s. u_P; i s p. o)(j) : Ty (l ⊔ l' ⊔ li)` —
    /// encoding of the indexed final coalgebra applied at index `j`
    /// (docs/kernel-m-codes-design.md §1), decoded by `El(TmM …) ⇝
    /// M(El idx; i. El shape; i s. El pos; i s p. next)(index)`. `shape`
    /// binds the index, `pos` the index and the shape, `next` all three; the
    /// index of the child (`next`) and `index` are terms of `El idx`, carried
    /// across the decoding unchanged.
    TmM {
        level: Level,
        pos_level: Level,
        idx_level: Level,
        idx: Rc<Term>,
        shape: Rc<Term>,
        pos: Rc<Term>,
        next: Rc<Term>,
        index: Rc<Term>,
    },

    // ---- natural numbers ----
    Zero,
    /// A closed natural-number literal, of any size
    /// (`docs/wide-numerals-design.md`). This is observationally the same
    /// constructor spine as `Succ^value(Zero)` (and `NatLit(0)` is `Zero`),
    /// but keeps source numerals compact until evaluation can hand them to the
    /// generic context-program representation.
    NatLit(Numeral),
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

    /// `[b₀, …, b_{w-1}]^l(T; zero, one)` — a closed prefix of a `Vec`
    /// whose every element is one of two terms, held as a machine word
    /// (`docs/bitvector-literal-entry-design.md` §3,
    /// `issues/packed-vector-literal-term.md`). Observationally the
    /// right-nested pair chain the `Vec` rule types, element `i` being `one`
    /// when bit `i` of `bits` is set and `zero` otherwise, ending in `⟨⟩^l`:
    /// exactly as [`Term::NatLit`] is `Succ^n(Zero)`, and with the same
    /// one-step view ([`vec_lit_unfold`]). It names nothing — no element
    /// type, no two-valued criterion — so its typing rule checks two
    /// elements and not `w`; whether the *value* packs into a word is the
    /// evaluator's question (`eval/bits.rs`), asked of the element type.
    /// `1 ≤ width ≤ 64` and no bit at or above `width` is set.
    VecLit {
        level: Level,
        elem: Rc<Type>,
        zero: Rc<Term>,
        one: Rc<Term>,
        width: u32,
        bits: u64,
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

    // ---- checked spellings (extension; docs/intro-by-type-design.md) ----
    //
    // Five forms, one per intro or projection above, carrying **the type the
    // term was checked at** in place of that type's components — and a sixth,
    // `app@`, carrying nothing, whose Π is its head's
    // (`docs/app-by-head-type-design.md`). They exist
    // because the elaborator normalizes a type to decide a match and would
    // otherwise have to write the reduct's halves into the annotation — an
    // object exponential as a tree and linear as a value graph
    // (`issues/elab-emits-normal-form-of-matched-type-argument.md`). Here the
    // annotation is the un-reduced type it already had, and whoever needs the
    // halves computes them in the evaluator, which shares.
    //
    // Each is a *checked spelling* of the form above it, related by the
    // typing-preserving translation `⌊·⌋` of the design's §2.4: erase to the
    // component form at the whnf the derivation contains. Conservativity is
    // that translation; the kernel's own guarantee is that nothing reads the
    // annotation except the rule that exposes its head.
    //
    // **Not under a `box`** (design §2.3): the restriction is a side
    // condition on the two `box` rules — the payload of a quotation contains
    // no checked spelling — and not a layer predicate, because Heather checks
    // every declaration body at `Layer::Code` and a layer predicate is
    // therefore constantly false at the emitters. What §2.2 needs is only
    // that the code recursors never meet one, and the recursors range over
    // exactly the payload of a `box`.
    //
    // **The intros' annotation is optional** and the projections carry none
    // (design §2.1, revised after stage 2's first measurement). An
    // unannotated intro is *not inferable* — the verdict `box` already gets —
    // and is checked against the expected type, which the checker holds as an
    // `ITy` and views in the value domain; that is what lets a constructor
    // value nested inside a constructor value be written with no type at all,
    // since the expected type of a field is a *description* of a component
    // and never a spelling. The annotated form exists for the one position
    // the elaborator cannot make a checking position — a constructor value at
    // the head of a projection, or a scrutinee — and it carries the
    // un-reduced type the elaborator had.
    /// `pair@(a; b)` / `pair@^{T}(a; b) : T` where `T ⇝* Σ^{l,l'}(x:S). U` —
    /// the checked spelling of [`Term::Pair`]. With an annotation it infers
    /// `T` *un-reduced*, so a consumer that compares it against another `T`
    /// pays a head comparison and one that compares it against the former
    /// pays one δ step; without one it is checking-only.
    PairAt {
        ty: Option<Rc<Type>>,
        fst: Rc<Term>,
        snd: Rc<Term>,
    },
    /// `inl@(a)` / `inl@^{T}(a) : T` where `T ⇝* A +^{l,l'} B` and `a : A` —
    /// the checked spelling of [`Term::Inl`].
    InlAt {
        ty: Option<Rc<Type>>,
        val: Rc<Term>,
    },
    /// `inr@(b)` / `inr@^{T}(b) : T` where `T ⇝* A +^{l,l'} B` and `b : B` —
    /// the checked spelling of [`Term::Inr`].
    InrAt {
        ty: Option<Rc<Type>>,
        val: Rc<Term>,
    },
    /// `fst@(p) : S` where `p` infers `T`, `T ⇝* Σ^{l,l'}(x:S). U` — the
    /// checked spelling of [`Term::Fst`]. It carries **no** annotation: the
    /// receiver infers one, and the component `S` has no spelling smaller
    /// than the reduct, which is what forces the checker to descriptions
    /// (design §3.1).
    FstAt {
        pair: Rc<Term>,
    },
    /// `snd@(p) : U[fst@(p)/x]` — the checked spelling of [`Term::Snd`],
    /// same premises as [`Term::FstAt`].
    SndAt {
        pair: Rc<Term>,
    },
    /// `app@(f; a) : T[a/x]` where `f` infers `F`, `F ⇝* Π^{l,l'}(x:S). T`
    /// and `a : S` — the checked spelling of [`Term::App`]
    /// (`docs/app-by-head-type-design.md`). No annotation and no levels: the
    /// Π is the one the head infers. When `F` is syntactically a Π the rule
    /// returns `T[a/x]` as syntax, exactly the `App` rule's result; only a
    /// head whose type needs reduction yields a description (design §3.1).
    /// A `λ` head infers only if its body does, so the elaborator keeps
    /// [`Term::App`] for a β-redex.
    AppAt {
        fun: Rc<Term>,
        arg: Rc<Term>,
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

    // ---- finitary indexed trees (extension; docs/iwf-former-design.md) ----
    /// `sup_i^{l,li}(I; x:S. n; x. o; x i. c; a; cs) : IWf(…)(o[a/x])` where
    /// `a : S` and `cs : DVec^{l⊔li}(n[a/x]; k. IWf(…)(c[a/x, k/i]))` — the
    /// constructor *is* at its output index, so it stores no equation
    /// (design §2). The signature is [`Type::IWf`]'s, with its binders; fully
    /// annotated, so it synthesizes. Same layer gate as [`Type::IWf`].
    Supi { sig: Rc<IWfSig>, label: Rc<Term>, children: Rc<Term> },
    /// `elim_IWf^{l,li,l'}(I; x:S. n; x. o; x i. c; j z. M; a cs ih. s; m; t)
    /// : M[m/j, t/z]` — dependent elimination over `t : IWf(…)(m)`. The
    /// signature is [`Type::IWf`]'s; `motive` binds two locals
    /// (`j : I`, `z : IWf(…)(j)`), `step` three (`a : S`,
    /// `cs : DVec(n[a/x]; k. IWf(…)(c[a/x, k/i]))`,
    /// `ih : Π^{0,l'}(i : Fin n[a/x]). M[c[a/x, i/i]/j, dnth(…; cs; i)/z]`),
    /// with `s : M[o[a/x]/j, sup_i(a; cs)/z]` (the telescope is
    /// [`iwf_step_telescope`]). β fires on a `sup_i` **at any index**, open
    /// data included (design §4):
    /// `elim_IWf(…; m; sup_i(…; a; cs)) ⇝ s[a, cs, λi. elim_IWf(…; c[a, i];
    /// dnth(…; cs; i))]` ([`iwf_ih`]). Neutral on a neutral scrutinee, no η,
    /// no strip. Same layer gate as [`Type::IWf`].
    ElimIWf {
        sig: Rc<IWfSig>,
        motive_level: Level,
        motive: Rc<Type>,
        step: Rc<Term>,
        index: Rc<Term>,
        scrut: Rc<Term>,
    },

    // ---- indexed final coalgebras (extension; docs/kernel-coinduction-design.md) ----
    /// `corec^{k}(sig; i. X; i x. c; j; x) : M(sig)(j)` — primitive
    /// corecursion (the apomorphism, design §1.3). `carrier` (`X @ k`) binds
    /// `i : I`; `step` binds `i, x : X` and has type
    /// `Σ(s : S). Π(p : P). X[o/i] + M(sig)(o)` ([`m_step_ty`]): each child is
    /// a new seed (`inl`) or an existing tree (`inr`). The carrier's level `k`
    /// is free, a rule per `k`. β fires only under [`Term::Out`]
    /// ([`m_out_corec`]); a `corec` is otherwise a canonical form, compared
    /// componentwise. Same layer gate as [`Type::M`].
    Corec {
        sig: Rc<MSig>,
        carrier_level: Level,
        carrier: Rc<Type>,
        step: Rc<Term>,
        index: Rc<Term>,
        seed: Rc<Term>,
    },
    /// `out(sig; j; m) : Σ^{l,f}(s : S[j/i]). Π^{l',f}(p : P[j/i]). M(sig)(o[j/i])`
    /// with `f = l ⊔ l' ⊔ li` ([`m_out_ty`]) — the only eliminator of
    /// [`Type::M`]: no dependent case analysis exists (design §1.2). Neutral
    /// on a neutral `scrut`. Same layer gate as [`Type::M`].
    Out { sig: Rc<MSig>, index: Rc<Term>, scrut: Rc<Term> },

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
#[derive(Clone, Eq)]
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
#[derive(Clone, Eq)]
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

    // -- M-types (docs/kernel-m-codes-design.md §2) --
    /// `(ℓ, ℓ', ℓi, g, U_I, U_S, U_P, u_o, u_j, x_I, x_S, x_P, x_o, x_j.
    /// t_M)` — code of the type `M(U_I; U_S; U_P; u_o)(u_j)`. `U_S` is
    /// scoped over `i : U_I`, `U_P` over `(i, s)`, `u_o : U_I` over `(i, s,
    /// p)`.
    pub ty_m: Rc<Term>,
    /// `(ℓ, ℓ', ℓi, g, u_I, u_S, u_P, u_o, u_j, x_I, …, x_j. t'_M)` — code
    /// of the encoding `TmM(u_I; u_S; u_P; u_o; u_j) : Ty(ℓ ⊔ ℓ' ⊔ ℓi)`,
    /// the pieces read through `El` as `tm_wf` reads them.
    pub tm_m: Rc<Term>,
    /// `(ℓ, ℓ', ℓi, k, g, U_I, U_S, U_P, u_o, U_X, u_c, u_j, u_x, x_I, …,
    /// x_x. t_corec)` — code of `corec^k(σ; U_X; u_c; u_j; u_x)`; `U_X` is
    /// scoped over `i : U_I`, `u_c` over `(i, x : U_X)` at the step type.
    pub tm_corec: Rc<Term>,
    /// `(ℓ, ℓ', ℓi, g, U_I, U_S, U_P, u_o, u_j, u_m, x_I, …, x_m. t_out)` —
    /// code of `out(σ; u_j; u_m)`.
    pub tm_out: Rc<Term>,

    // -- dependent tuples and indexed trees (docs/iwf-former-design.md §6) --
    //
    // heather-coq's M17c branches 55–60 (`RecSpec`'s `brDecls`/`br_calls`),
    // whose scopes were derived from the layer-C rules before these existed;
    // these are checked against them. Univs `ℓ` (the shapes'), then `ℓi` (the
    // index type's), then `ℓ'` (a motive's).
    /// `(ℓ, g, u_n, U_F, x_n, x_F. t_DVec)` — univs: ℓ; globals: g,
    /// `u_n : Trm_c(g ⊢ Nat @ 0)`, `U_F : Typ_c((g, i : Fin u_n^id @ 0), ℓ)`;
    /// locals: `x_n` (*term* motive), `x_F` (type motive). Code of the type
    /// `DVec^ℓ(u_n^id; i. U_F^id)`.
    pub ty_dvec: Rc<Term>,
    /// `(ℓ, g, u_n, u_f, x_n, x_f. t'_DVec)` — as `ty_dvec`, with
    /// `u_f : Trm_c((g, i : Fin u_n^id) ⊢ Ty ℓ @ 1+ℓ)`. Code of the encoding
    /// `DVec^ℓ(u_n^id; i. u_f^id) : Ty ℓ`.
    pub tm_dvec: Rc<Term>,
    /// `(ℓ, ℓi, g, U_X, U_A, u_N, u_O, u_C, u_m, x_X, x_A, x_N, x_O, x_C,
    /// x_m. t_IWf)` — univs: ℓ, ℓi; globals: g, `U_X : Typ_c(g, ℓi)`,
    /// `U_A : Typ_c(g, ℓ)`, `u_N : Trm_c((g, x : U_A^id) ⊢ Nat @ 0)`,
    /// `u_O : Trm_c((g, x) ⊢ U_X^↑ @ ℓi)`,
    /// `u_C : Trm_c((g, x, i : Fin u_N^id) ⊢ U_X^↑↑ @ ℓi)`,
    /// `u_m : Trm_c(g ⊢ U_X^id @ ℓi)`; locals: one recursive call per
    /// global, `x_X`/`x_A` at the type motive. Code of the type
    /// `IWf(U_X; U_A; u_N; u_O; u_C)(u_m)` @ ℓ⊔ℓi.
    pub ty_iwf: Rc<Term>,
    /// `(ℓ, ℓi, g, u_x, u_s, u_n, u_o, u_c, u_m, x_x, …, x_m. t'_IWf)` —
    /// `ty_iwf` with the index type and shapes as codes (`Trm_c(g ⊢ Ty ℓi)`,
    /// `Trm_c(g ⊢ Ty ℓ)`) read through `El`, as `tm_wf` is `ty_wf`'s. Code of
    /// the encoding `TmIWf(…)(u_m) : Ty (ℓ⊔ℓi)`.
    pub tm_iwf: Rc<Term>,
    /// `(ℓ, ℓi, g, U_X, U_A, u_N, u_O, u_C, u_a, u_cs, x_X, …, x_C, x_a,
    /// x_cs. t_supi)` — `ty_iwf`'s five signature globals, then
    /// `u_a : Trm_c(g ⊢ U_A^id @ ℓ)`,
    /// `u_cs : Trm_c(g ⊢ DVec^{ℓ⊔ℓi}(u_N^{id,u_a/x}; k. IWf(…)(u_C^{id,u_a/x,k/i})) @ ℓ⊔ℓi)`
    /// ([`iwf_children_ty`]). Code of `sup_i(…; u_a^id; u_cs^id)`.
    pub tm_sup_i: Rc<Term>,
    /// `(ℓ, ℓi, ℓ', g, U_X, U_A, u_N, u_O, u_C, U_M, u_c, u_m, u_t, x_X, …,
    /// x_t. t_elimIWf)` — the five signature globals, then
    /// `U_M : Typ_c((g, j : U_X^id, z : IWf(…)(j)), ℓ')`,
    /// `u_c : Trm_c((g, a, cs, ih) ⊢ U_M^{id, u_O[a]/j, sup_i(a; cs)/z} @ ℓ')`
    /// (the telescope is [`iwf_step_telescope`], shared with typing),
    /// `u_m : Trm_c(g ⊢ U_X^id @ ℓi)`, `u_t : Trm_c(g ⊢ IWf(…)(u_m^id) @ ℓ⊔ℓi)`;
    /// locals: one call per global, `x_M` at the type motive. Code of
    /// `elim_IWf(…; j z. U_M^id; a cs ih. u_c^id; u_m^id; u_t^id)`.
    pub tm_elim_iwf: Rc<Term>,
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
#[derive(Clone, Eq)]
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

#[derive(Clone, Eq)]
pub struct CtxEntry {
    pub ty: Rc<Type>,
    pub level: Level,
}

/// The entries of a [`LocalCtx`], as a persistent snoc list whose *head is
/// the innermost* binding.
///
/// Binder descent extends Γ by one entry while keeping the parent Γ alive,
/// which a `Vec` can only serve by copying the whole context. That copy was
/// the #1 self line of a release `heather check lib/certgen/ir_v1.hthr`
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

    /// [`CtxEntries::identity`]'s address, without the token: 0 for the
    /// empty spine. A key built from it must hold the token alongside.
    pub(crate) fn identity_addr(&self) -> usize {
        self.0.as_ref().map_or(0, |n| Rc::as_ptr(n) as usize)
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
/// their Γ (ch. 06). The entries' types compare inside the caller's
/// comparison (`crate::syntax_eq`), so a type two entries share is compared
/// once.
impl crate::syntax_eq::SharedEq for CtxEntries {
    fn shared_eq(&self, other: &CtxEntries, m: &mut crate::syntax_eq::PairMemo) -> bool {
        let mut a = self;
        let mut b = other;
        loop {
            match (&a.0, &b.0) {
                (None, None) => return true,
                (Some(x), Some(y)) => {
                    if Rc::ptr_eq(x, y) {
                        return true;
                    }
                    if x.len != y.len || !x.entry.shared_eq(&y.entry, m) {
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
#[derive(Clone, Eq)]
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
    /// Sealed proofs: the bodies of opaque bindings that may be unsealed at
    /// a stuck elimination (`issues/theorem-witness-unfolding.md`, option D;
    /// `crate::reduce::Defs::sealed_body`). Not part of any binding, so a
    /// binding's interface, its equality and its hash are what they were
    /// before the proof was kept; losing an entry only makes the theorem
    /// opaque again, never wrong.
    pub sealed: SealedProofs,
    /// The elaborator's **interface boundary**
    /// (`docs/interface-definitions-design.md` §3): definitions whose body
    /// this world withholds at open arguments. `None` everywhere but in the
    /// elaborator's own semantic worlds; the trusted check never sets it, so
    /// what the kernel accepts does not depend on it. Like
    /// [`GlobalCtx::sealed`] it is not part of any binding.
    pub withheld: Option<Rc<Withheld>>,
}

/// Definitions a world withholds, by absolute Ψ index, each with its
/// **arity**: the number of explicit term applications a call needs before
/// the body may unfold (the declaration's parameters, type parameters
/// included). A withheld definition is an opaque neutral until a call of it
/// is saturated at arguments that read no free local variable; from there it
/// unfolds as any definition does (`crate::reduce::Defs::withheld`).
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Withheld {
    arity: std::collections::BTreeMap<usize, u32>,
}

impl Withheld {
    pub fn new() -> Withheld {
        Withheld::default()
    }

    /// Withhold the definition at absolute index `at` until `arity`
    /// arguments are applied.
    pub fn insert(&mut self, at: usize, arity: u32) {
        self.arity.insert(at, arity);
    }

    /// The arity the binding at absolute index `at` is withheld at, if it is.
    pub fn arity(&self, at: usize) -> Option<u32> {
        self.arity.get(&at).copied()
    }

    pub fn is_empty(&self) -> bool {
        self.arity.is_empty()
    }

    pub fn len(&self) -> usize {
        self.arity.len()
    }

    /// Every entry, `(absolute index, arity)`, ascending: what a verdict
    /// cache keys a check made under this boundary on.
    pub fn entries(&self) -> impl Iterator<Item = (usize, u32)> + '_ {
        self.arity.iter().map(|(at, arity)| (*at, *arity))
    }

    /// The same set without the entries in `released` (absolute indices):
    /// what an `unfold f;` statement leaves withheld.
    pub fn releasing(&self, released: &[usize]) -> Withheld {
        let mut arity = self.arity.clone();
        for at in released {
            arity.remove(at);
        }
        Withheld { arity }
    }
}

const SEALED_CHUNK: usize = 64;

/// Where a lazily kept [`SealedProof`] comes from: something that can
/// produce the proof term on demand, such as its encoding in a module image
/// (`issues/sealed-proof-memory.md`). Producing it must be deterministic —
/// the same term every call — and must not fail: whoever builds the source
/// checks up front that it can.
pub trait ProofSource: Send + Sync {
    /// The proof term.
    fn load(&self) -> Term;

    /// The source as itself, for a caller that built it and compares or
    /// re-encodes sources of its own kind without loading them.
    fn as_any(&self) -> &dyn std::any::Any;
}

/// One kept proof: a term already in memory, or a [`ProofSource`] loaded the
/// first time something needs the term and kept from then on. Ψ keeps a
/// proof for every theorem whose statement carries data, and on a run that
/// replays module images almost none of them is ever opened, so a proof held
/// as a source costs its encoding until one is.
pub struct SealedProof {
    term: std::sync::OnceLock<Rc<Term>>,
    source: Option<Box<dyn ProofSource>>,
}

impl SealedProof {
    /// A proof already in memory.
    pub fn new(term: Rc<Term>) -> SealedProof {
        SealedProof { term: std::sync::OnceLock::from(term), source: None }
    }

    /// A proof loaded from `source` on first use.
    pub fn lazy(source: impl ProofSource + 'static) -> SealedProof {
        SealedProof { term: std::sync::OnceLock::new(), source: Some(Box::new(source)) }
    }

    /// A proof computed from `base`'s term on first use — `base` is loaded
    /// only then.
    pub fn derived(base: Rc<SealedProof>, f: impl Fn(&Term) -> Term + Send + Sync + 'static) -> SealedProof {
        struct Derived<F> {
            base: Rc<SealedProof>,
            f: F,
        }
        impl<F: Fn(&Term) -> Term + Send + Sync + 'static> ProofSource for Derived<F> {
            fn load(&self) -> Term {
                (self.f)(self.base.term())
            }
            fn as_any(&self) -> &dyn std::any::Any {
                self
            }
        }
        SealedProof::lazy(Derived { base, f })
    }

    /// The proof term, loading it from its source if this is the first use.
    pub fn term(&self) -> &Rc<Term> {
        self.term.get_or_init(|| {
            crate::stats::sealed_loads(1);
            Rc::new(self.source.as_ref().expect("a sealed proof has a term or a source").load())
        })
    }

    /// The proof term if it is in memory, without loading it.
    pub fn loaded(&self) -> Option<&Rc<Term>> {
        self.term.get()
    }

    /// Where the proof loads from, if it was kept lazily.
    pub fn source(&self) -> Option<&dyn ProofSource> {
        self.source.as_deref()
    }
}

impl std::fmt::Debug for SealedProof {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.loaded() {
            Some(t) => t.fmt(f),
            None => f.write_str("<sealed proof, not loaded>"),
        }
    }
}

/// Persistent, index-ordered storage for [`GlobalCtx::sealed`]: `(absolute Ψ
/// index, proof)` pairs, strictly increasing in the index, chunked the way
/// [`GlobalBindings`] is so that cloning Ψ stays O(1).
#[derive(Clone, Default)]
pub struct SealedProofs {
    chunks: Rc<Vec<Rc<Vec<(usize, Rc<SealedProof>)>>>>,
    tail: Rc<Vec<(usize, Rc<SealedProof>)>>,
}

impl SealedProofs {
    pub fn len(&self) -> usize {
        self.chunks.iter().map(|c| c.len()).sum::<usize>() + self.tail.len()
    }

    pub fn is_empty(&self) -> bool {
        self.tail.is_empty() && self.chunks.is_empty()
    }

    /// The sealed proof of the binding at absolute index `at`, as kept: a
    /// lazy one stays unloaded.
    pub fn get(&self, at: usize) -> Option<&Rc<SealedProof>> {
        let find = |entries: &'_ [(usize, Rc<SealedProof>)]| {
            entries.binary_search_by_key(&at, |(i, _)| *i).ok()
        };
        if self.tail.first().is_some_and(|(first, _)| *first <= at) {
            return find(&self.tail).map(|k| &self.tail[k].1);
        }
        let c = self.chunks.partition_point(|c| c.first().is_some_and(|(first, _)| *first <= at));
        let chunk = self.chunks.get(c.checked_sub(1)?)?;
        find(chunk).map(|k| &chunk[k].1)
    }

    pub fn iter(&self) -> impl Iterator<Item = (usize, &Rc<SealedProof>)> {
        self.chunks.iter().flat_map(|c| c.iter()).chain(self.tail.iter()).map(|(i, t)| (*i, t))
    }

    /// Record `proof` for the binding at `at`, which must be past every index
    /// already recorded.
    fn push(&mut self, at: usize, proof: Rc<SealedProof>) {
        let last = self.tail.last().or_else(|| self.chunks.last().and_then(|c| c.last()));
        assert!(last.is_none_or(|(i, _)| *i < at), "sealed proofs are recorded in Ψ order");
        if self.tail.len() == SEALED_CHUNK {
            let full = std::mem::take(&mut self.tail);
            Rc::make_mut(&mut self.chunks).push(full);
        }
        Rc::make_mut(&mut self.tail).push((at, proof));
    }

    /// The entries below absolute index `n`.
    fn prefix(&self, n: usize) -> SealedProofs {
        if self.iter().all(|(i, _)| i < n) {
            return self.clone();
        }
        let mut out = SealedProofs::default();
        for (i, t) in self.iter().take_while(|(i, _)| *i < n) {
            out.push(i, Rc::clone(t));
        }
        out
    }
}

impl PartialEq for SealedProofs {
    /// Loads whatever it compares that is not one allocation: equality of
    /// Ψ is a test-side question, not one a check asks.
    fn eq(&self, other: &Self) -> bool {
        self.len() == other.len()
            && self.iter().zip(other.iter()).all(|((i, a), (j, b))| i == j && (Rc::ptr_eq(a, b) || a.term() == b.term()))
    }
}

impl Eq for SealedProofs {}

impl std::fmt::Debug for SealedProofs {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // The indices only: a proof is a term, and Ψ's `Debug` already prints
        // every binding.
        f.debug_list().entries(self.iter().map(|(i, _)| i)).finish()
    }
}

const GLOBAL_CHUNK: usize = 64;

#[derive(Debug, Clone, PartialEq, Eq)]
struct GlobalChunk {
    bindings: Rc<Vec<GlobalBinding>>,
}

/// [`GlobalBindings::mark`]: what a Ψ held when the mark was taken.
#[derive(Clone)]
pub struct GlobalMark(GlobalBindings);

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

    /// The first `n` bindings, sharing every full chunk: a prefix copies at
    /// most one chunk's worth of bindings, not the prefix itself.
    fn prefix(&self, n: usize) -> Self {
        if n >= self.len() {
            return self.clone();
        }
        let full = n / GLOBAL_CHUNK;
        let sealed_len = full * GLOBAL_CHUNK;
        Self {
            sealed: Rc::new(self.sealed[..full].to_vec()),
            sealed_len,
            tail: Rc::new((sealed_len..n).map(|i| self[i].clone()).collect()),
            identity: Rc::new(()),
        }
    }

    pub(crate) fn identity(&self) -> Rc<()> {
        Rc::clone(&self.identity)
    }

    /// [`GlobalBindings::identity`]'s address, without the token. A key
    /// built from it must hold the token alongside.
    pub(crate) fn identity_addr(&self) -> usize {
        Rc::as_ptr(&self.identity) as usize
    }

    pub(crate) fn same_identity(&self, other: &Self) -> bool {
        Rc::ptr_eq(&self.identity, &other.identity)
    }

    /// A handle on the bindings `self` holds now, for a caller that keeps
    /// something per binding and must later learn how much of it still
    /// describes another Ψ ([`GlobalBindings::common_prefix`]): the verdict
    /// cache's interface hashes, shared by an elaborator and its forks. It
    /// holds the chunks by reference count and copies no binding; the next
    /// push onto `self` copies the open tail (at most one chunk) once.
    pub fn mark(&self) -> GlobalMark {
        GlobalMark(self.clone())
    }

    /// How many leading bindings `self` has in common with the Ψ `mark` was
    /// taken of. A sealed chunk both hold by pointer is common without a
    /// look, so a fork, which shares every chunk its parent had sealed,
    /// costs a pointer comparison per chunk and an `==` per tail binding;
    /// any other binding is compared by `==`, so the answer is exact
    /// whatever the sharing.
    pub fn common_prefix(&self, mark: &GlobalMark) -> usize {
        let other = &mark.0;
        let n = self.len().min(other.len());
        if self.same_identity(other) {
            return n;
        }
        let mut i = 0;
        for (a, b) in self.sealed.iter().zip(other.sealed.iter()) {
            if i + GLOBAL_CHUNK > n || !Rc::ptr_eq(&a.bindings, &b.bindings) {
                break;
            }
            i += GLOBAL_CHUNK;
        }
        while i < n && self.get(i) == other.get(i) {
            i += 1;
        }
        i
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
        GlobalCtx { bindings: GlobalBindings::new(bindings), sealed: SealedProofs::default(), withheld: None }
    }

    /// This world with `withheld` as its interface boundary (`None` lifts
    /// it). The bindings get a fresh identity, so no memo keyed on Ψ's
    /// identity (`typing.rs`'s scopes) answers across the two policies.
    pub fn withholding(&self, withheld: Option<Rc<Withheld>>) -> GlobalCtx {
        let mut world = self.clone();
        world.withheld = withheld.filter(|w| !w.is_empty());
        world.bindings.identity = Rc::new(());
        world
    }

    /// Append one binding (copy-on-write if this Ψ is shared).
    pub fn push(&mut self, b: GlobalBinding) {
        self.bindings.push(b);
    }

    /// Append an opaque term binding together with its sealed proof: the
    /// binding is exactly what [`GlobalCtx::push`] would add, and `proof` is
    /// kept beside it for [`crate::reduce::Defs::sealed_body`].
    pub fn push_sealed(&mut self, b: GlobalBinding, proof: Rc<Term>) {
        let at = self.bindings.len();
        self.push(b);
        self.seal(at, proof);
    }

    /// Keep `proof` as the sealed proof of the binding at absolute index
    /// `at`. Ignored unless that binding is an opaque term binding; `at` must
    /// be past every index already sealed.
    pub fn seal(&mut self, at: usize, proof: Rc<Term>) {
        self.seal_kept(at, Rc::new(SealedProof::new(proof)));
    }

    /// [`GlobalCtx::seal`] for a proof as kept, lazy or not.
    pub fn seal_kept(&mut self, at: usize, proof: Rc<SealedProof>) {
        if matches!(self.bindings.get(at), Some(GlobalBinding::Tm { body: None, .. })) {
            self.sealed.push(at, proof);
        }
    }

    /// The sealed proof of the binding at absolute index `at`, if one is
    /// kept, loaded if it was kept lazily. Only unsealing needs the term;
    /// [`GlobalCtx::sealed_kept`] asks without loading.
    pub fn sealed_proof(&self, at: usize) -> Option<&Rc<Term>> {
        self.sealed.get(at).map(|p| p.term())
    }

    /// The sealed proof of the binding at absolute index `at` as kept,
    /// without loading it.
    pub fn sealed_kept(&self, at: usize) -> Option<&Rc<SealedProof>> {
        self.sealed.get(at)
    }

    /// Append several bindings (copy-on-write if this Ψ is shared).
    pub fn extend(&mut self, bs: impl IntoIterator<Item = GlobalBinding>) {
        for binding in bs {
            self.bindings.push(binding);
        }
    }

    /// Ψ followed by `bs`, sharing Ψ's chunks. Building the extended world
    /// from `to_vec()` copies every binding of Ψ, which per goal query was
    /// most of a split's elaboration once Ψ held a generated certificate
    /// (issues/goal-world-copies-psi.md).
    pub fn extended(&self, bs: impl IntoIterator<Item = GlobalBinding>) -> GlobalCtx {
        let mut world = self.clone();
        world.extend(bs);
        world
    }

    /// The first `n` bindings of Ψ, sharing its full chunks.
    pub fn prefix(&self, n: usize) -> GlobalCtx {
        GlobalCtx { bindings: self.bindings.prefix(n), sealed: self.sealed.prefix(n), withheld: self.withheld.clone() }
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

/// Whether `t` is the literal zero: `Zero`, or a `NatLit` of zero.
pub fn is_nat_zero(t: &Term) -> bool {
    match t {
        Term::Zero => true,
        Term::NatLit(n) => n.is_zero(),
        _ => false,
    }
}

/// A nonzero literal's predecessor, in the spelling its one-step view uses:
/// `Zero` at one, a smaller literal above (`Term::NatLit`'s contract).
pub fn nat_lit_pred(n: &Numeral) -> Term {
    let pred = n.pred().expect("only a nonzero literal has a predecessor");
    if pred.is_zero() { Term::Zero } else { Term::NatLit(pred) }
}

/// The widest [`Term::VecLit`]: one machine word.
pub const VEC_LIT_WIDTH_CAP: u32 = 64;

/// Whether a [`Term::VecLit`]'s width and bits are in range: the typing
/// rule's side condition, and what [`vec_lit_unfold`] relies on.
pub fn vec_lit_in_range(width: u32, bits: u64) -> bool {
    (1..=VEC_LIT_WIDTH_CAP).contains(&width) && (width == 64 || bits >> width == 0)
}

/// A [`Term::VecLit`]'s one-step view: the pair the `Vec` rule types at a
/// successor length, `pair^{l,l}(_: T. Vec^l(T; w-1); e₀; rest)`, its tail
/// the literal one element shorter, or `⟨⟩^l` at width one. These are the
/// annotations an elaborated vector literal's chain carries
/// (`check_vec_lit`), so a literal and its chain are the same term one step
/// apart.
pub fn vec_lit_unfold(
    level: &Level,
    elem: &Rc<Type>,
    zero: &Rc<Term>,
    one: &Rc<Term>,
    width: u32,
    bits: u64,
) -> Term {
    debug_assert!(vec_lit_in_range(width, bits));
    let head = if bits & 1 == 0 { zero } else { one };
    let rest = if width == 1 {
        Term::Triv { level: level.clone() }
    } else {
        Term::VecLit {
            level: level.clone(),
            elem: Rc::clone(elem),
            zero: Rc::clone(zero),
            one: Rc::clone(one),
            width: width - 1,
            bits: bits >> 1,
        }
    };
    let rest_len = if width == 1 { Term::Zero } else { Term::NatLit(u64::from(width - 1).into()) };
    Term::Pair {
        fst_level: level.clone(),
        snd_level: level.clone(),
        fst_ty: Rc::clone(elem),
        snd_ty: Rc::new(Type::Vec {
            level: level.clone(),
            elem: Rc::new(elem.shift_local(1)),
            len: Rc::new(rest_len),
        }),
        fst: Rc::clone(head),
        snd: Rc::new(rest),
    }
}

/// A [`Term::VecLit`] spelled out: the whole pair chain, for a reader that
/// takes vectors apart by their components — a `box` payload's recursors,
/// an export target. Each node is [`vec_lit_unfold`]'s, so the chain is the
/// one the literal stands for.
pub fn vec_lit_chain(
    level: &Level,
    elem: &Rc<Type>,
    zero: &Rc<Term>,
    one: &Rc<Term>,
    width: u32,
    bits: u64,
) -> Term {
    debug_assert!(vec_lit_in_range(width, bits));
    let shifted = Rc::new(elem.shift_local(1));
    let mut acc = Term::Triv { level: level.clone() };
    for i in (0..width).rev() {
        let rest = width - 1 - i;
        let rest_len = if rest == 0 { Term::Zero } else { Term::NatLit(u64::from(rest).into()) };
        acc = Term::Pair {
            fst_level: level.clone(),
            snd_level: level.clone(),
            fst_ty: Rc::clone(elem),
            snd_ty: Rc::new(Type::Vec {
                level: level.clone(),
                elem: Rc::clone(&shifted),
                len: Rc::new(rest_len),
            }),
            fst: Rc::clone(if bits >> i & 1 == 0 { zero } else { one }),
            snd: Rc::new(acc),
        };
    }
    acc
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

// ---------------------------------------------------------------------------
// Derived constructions for `DVec` (docs/iwf-former-design.md §1.1, §3)
//
// The successor reduct and `dnth` are transcribed binder by binder from the
// Coq formalization (heather-coq `theories/Syntax/Term.v`: `dvecHd`,
// `dvecTl`, `dnthMot`, `dnthBase`, `dnthStep`, `tmDNth`), which is the
// first precise statement of them (heather-coq `M17_DESIGN.md`). Its
// `F⟨rlift ↑⟩ⁿ[lsingle t]` is [`Type::inst_top`]`(n, t)` here, `t⟨↑⟩ⁿ` is
// `shift_local(n)`, and `T⟨rlift ↑⟩ⁿ` is `shift_local_above(n, 1)`.
// ---------------------------------------------------------------------------

/// `inl^{0,0}(Unit^0; Fin(k); ⟨⟩^0) : Fin(S k)` — the first position, with
/// `Fin(S k)`'s reduct's annotations, so it is typed at the family's domain
/// without a conversion. `k` is the predecessor, in the ambient scope.
pub fn fin_first(pred: Rc<Term>) -> Term {
    Term::Inl {
        lhs_level: Level::Zero,
        rhs_level: Level::Zero,
        lhs: Rc::new(Type::Unit { level: Level::Zero }),
        rhs: Rc::new(Type::Fin { len: pred }),
        val: Rc::new(Term::Triv { level: Level::Zero }),
    }
}

/// `inr^{0,0}(Unit^0; Fin(k); j) : Fin(S k)` — position `j : Fin(k)` moved
/// one up. `k` and `j` are in the ambient scope.
pub fn fin_next(pred: Rc<Term>, j: Rc<Term>) -> Term {
    Term::Inr {
        lhs_level: Level::Zero,
        rhs_level: Level::Zero,
        lhs: Rc::new(Type::Unit { level: Level::Zero }),
        rhs: Rc::new(Type::Fin { len: pred }),
        val: j,
    }
}

/// `DVec`'s successor reduct's two components, at the predecessor `k`
/// (scoped in Γ) of the length, over the family `F` (in `Γ, i`):
///
/// ```text
/// head  F[inl ⟨⟩/i]                          in Γ
/// tail  DVec^l(k; j. F[inr j/i])             in (Γ, x)   (the Σ's binder)
/// ```
///
/// so that `DVec^l(S k; i. F) ⇝ Σ^{l,l}(_ : head). tail`. The tail's family
/// is in `(Γ, x, j)`: `F` weakened past `x` and `j` with `i` at `inr j`.
pub fn dvec_succ_parts(level: &Level, pred: &Rc<Term>, fam: &Rc<Type>) -> (Type, Type) {
    let head = fam.inst_top(0, &fin_first(Rc::clone(pred)));
    let tail_fam = fam.inst_top(
        2,
        &fin_next(Rc::new(pred.shift_local(2)), Rc::new(Term::Var(LocalVar(0)))),
    );
    let tail = Type::DVec {
        level: level.clone(),
        len: Rc::new(pred.shift_local(1)),
        fam: Rc::new(tail_fam),
    };
    (head, tail)
}

/// `DVec^l(S k; i. F)`'s reduct, `Σ^{l,l}(_ : F[inl ⟨⟩/i]). DVec^l(k; j. F[inr j/i])`.
pub fn dvec_succ_reduct(level: &Level, pred: &Rc<Term>, fam: &Rc<Type>) -> Type {
    let (head, tail) = dvec_succ_parts(level, pred, fam);
    Type::Sigma {
        fst_level: level.clone(),
        snd_level: level.clone(),
        fst: Rc::new(head),
        snd: Rc::new(tail),
    }
}

/// `dnth^l(n; i. F; cs; i) : F` — the `i`th component of a
/// `DVec^l(n; i. F)` (docs/iwf-former-design.md §3). Not a former: a fixed
/// `elim_Nat` schema on the length, whose motive quantifies over an
/// **embedding** `e : Fin k̂ → Fin n` so that the family stays `F` over the
/// full length (a motive cannot quantify over families):
///
/// ```text
/// dnth(n; F; cs; i) := elim_Nat(k̂. Π(e : Fin k̂ → Fin n). Π(cs : DVec(k̂; j. F[e j/i])).
///                                     Π(i' : Fin k̂). F[e i'/i]
///                              ; λe cs i'. elim_Empty(x. F[e x/i]; i')
///                              ; k̂ r. λe cs i'. case i' of
///                                    { inl _ ⇒ fst cs
///                                    | inr j ⇒ r (λy. e (inr y)) (snd cs) j }
///                              ; n) (λi. i) cs i
/// ```
///
/// Every application is annotated by β-normal types (the family at
/// `e (inr y)`, not at `(λy. e (inr y)) y`), so the whole is typed at `F`
/// exactly; the β steps sit in the conversions of the applications'
/// function types — the step the Coq formalization's `V_dnth` checks.
///
/// At a literal length it reduces to the projections whatever the tuple is,
/// a neutral one included: `dnth(3; F; cs; inr (inl ⟨⟩)) ⇝* fst (snd cs)`
/// (design §3; heather-coq `dnth_reds_example`).
///
/// `len`, `cs` and `idx` live in Γ, `fam` in `(Γ, i : Fin len)`; the result
/// is in Γ.
pub fn dnth(level: &Level, len: &Rc<Term>, fam: &Rc<Type>, cs: Rc<Term>, idx: Rc<Term>) -> Term {
    let l = level;
    let z = || Level::Zero;
    let var = |i: u32| Rc::new(Term::Var(LocalVar(i)));
    let fin = |t: Rc<Term>| Rc::new(Type::Fin { len: t });
    let n_up = |k: u32| Rc::new(len.shift_local(k));
    let succ = |t: Rc<Term>| Rc::new(Term::Succ(t));
    let pi = |dl: Level, cl: Level, dom: Rc<Type>, cod: Rc<Type>| {
        Rc::new(Type::Pi { dom_level: dl, cod_level: cl, dom, cod })
    };
    let lam = |dl: Level, cl: Level, dom: Rc<Type>, body: Rc<Term>| {
        Rc::new(Term::Lam { dom_level: dl, cod_level: cl, dom, body })
    };
    let app = |fun: Rc<Term>, dl: Level, cl: Level, dom: Rc<Type>, cod: Rc<Type>, arg: Rc<Term>| {
        Rc::new(Term::App { fun, dom_level: dl, cod_level: cl, dom, cod, arg })
    };
    let dvec = |len: Rc<Term>, fam: Type| {
        Rc::new(Type::DVec { level: l.clone(), len, fam: Rc::new(fam) })
    };
    // `e t : Fin n` for the embedding `e = var(e)` of domain `Fin(k)`, read
    // `up` binders below Γ (the application's codomain one more).
    let emb_at = |e: u32, k: Rc<Term>, up: u32, t: Rc<Term>| {
        app(var(e), z(), z(), fin(k), fin(n_up(up + 1)), t)
    };

    // dnthEmb, in (Γ, k̂): Π^{0,0}(Fin k̂). Fin n.
    let emb = pi(z(), z(), fin(var(0)), fin(n_up(2)));
    // dnthFam, in (Γ, k̂, e, j): F[e j/i].
    let fam_e = fam.inst_top(3, &emb_at(1, var(2), 3, var(0)));
    // dnthRes, in (Γ, k̂, e, cs, i'): F[e i'/i].
    let res = fam.inst_top(4, &emb_at(2, var(3), 4, var(0)));
    // The motive's codomain under `e`, in (Γ, k̂, e).
    let mot_cod = pi(l.clone(), l.clone(), dvec(var(1), fam_e), pi(z(), l.clone(), fin(var(2)), Rc::new(res)));
    // dnthMot, in (Γ, k̂).
    let motive = pi(z(), l.clone(), Rc::clone(&emb), Rc::clone(&mot_cod));

    // dnthBase, in Γ.
    let base = lam(
        z(),
        l.clone(),
        pi(z(), z(), fin(Rc::new(Term::Zero)), fin(n_up(1))),
        lam(
            l.clone(),
            l.clone(),
            dvec(Rc::new(Term::Zero), fam.inst_top(2, &emb_at(1, Rc::new(Term::Zero), 2, var(0)))),
            lam(
                z(),
                l.clone(),
                fin(Rc::new(Term::Zero)),
                Rc::new(Term::ElimEmpty {
                    level: l.clone(),
                    // `Fin(0) ⇝ Empty^0` — `Fin` is declared at level 0.
                    scrut_level: Level::Zero,
                    motive: Rc::new(fam.inst_top(4, &emb_at(3, Rc::new(Term::Zero), 4, var(0)))),
                    scrut: var(0),
                }),
            ),
        ),
    );

    // dnthStep, in (Γ, k̂, r); under the three λs (Γ, k̂, r, e, cs, i'), and
    // under a case arm's binder one more.
    //
    // dnthFamS, in (Γ, k̂, r, e, cs, i', x, j): the tuple's family at
    // `e j`, `e : Fin(S k̂) → Fin n` — the projections' annotations.
    let fam_s = Rc::new(fam.inst_top(7, &emb_at(4, succ(var(6)), 7, var(0))));
    let (hd, tl) = dvec_succ_parts(l, &var(5), &fam_s);
    let (hd, tl) = (Rc::new(hd), Rc::new(tl));
    let fst_cs = Rc::new(Term::Fst {
        fst_level: l.clone(),
        snd_level: l.clone(),
        fst_ty: Rc::clone(&hd),
        snd_ty: Rc::clone(&tl),
        pair: var(2),
    });
    let snd_cs = Rc::new(Term::Snd {
        fst_level: l.clone(),
        snd_level: l.clone(),
        fst_ty: hd,
        snd_ty: tl,
        pair: var(2),
    });
    // In (Γ, k̂, r, e, cs, i', y): `inr y'` for a fresh `y' : Fin k̂` one
    // binder further in, and the family at `e (inr y')`.
    let inr_y = |pred: Rc<Term>| Rc::new(fin_next(pred, var(0)));
    let shifted_emb = lam(z(), z(), fin(var(5)), emb_at(4, succ(var(6)), 7, inr_y(var(6))));
    let fam_inr = |by: u32| fam.inst_top(by, &emb_at(by - 3, succ(var(by - 1)), by, inr_y(var(by - 1))));
    let rec_call = app(
        app(
            app(
                var(4),
                z(),
                l.clone(),
                Rc::new(emb.shift_local(5)),
                Rc::new(mot_cod.shift_local_above(5, 1)),
                shifted_emb,
            ),
            l.clone(),
            l.clone(),
            dvec(var(5), fam_inr(7)),
            pi(z(), l.clone(), fin(var(6)), Rc::new(fam_inr(8))),
            snd_cs,
        ),
        z(),
        l.clone(),
        fin(var(5)),
        Rc::new(fam_inr(7)),
        var(0),
    );
    let step = lam(
        z(),
        l.clone(),
        pi(z(), z(), fin(succ(var(1))), fin(n_up(3))),
        lam(
            l.clone(),
            l.clone(),
            dvec(succ(var(2)), fam.inst_top(4, &emb_at(1, succ(var(3)), 4, var(0)))),
            lam(
                z(),
                l.clone(),
                fin(succ(var(3))),
                Rc::new(Term::Case {
                    lhs_level: Level::Zero,
                    rhs_level: Level::Zero,
                    motive_level: l.clone(),
                    // `Fin(S k̂) ⇝ Unit^0 +^{0,0} Fin(k̂)`.
                    lhs: Rc::new(Type::Unit { level: Level::Zero }),
                    rhs: fin(var(4)),
                    motive: Rc::new(fam.inst_top(6, &emb_at(3, succ(var(5)), 6, var(0)))),
                    case_l: fst_cs,
                    case_r: rec_call,
                    scrut: var(0),
                }),
            ),
        ),
    );

    // The recursion, applied to the identity embedding, the tuple and the
    // index (tmDNth).
    let recursion = Rc::new(Term::ElimNat {
        level: l.clone(),
        motive,
        base,
        step,
        scrut: Rc::clone(len),
    });
    let at_id = app(
        recursion,
        z(),
        l.clone(),
        pi(z(), z(), fin(Rc::clone(len)), fin(n_up(1))),
        pi(
            l.clone(),
            l.clone(),
            dvec(n_up(1), fam.inst_top(2, &emb_at(1, n_up(2), 2, var(0)))),
            pi(z(), l.clone(), fin(n_up(2)), Rc::new(fam.inst_top(3, &emb_at(2, n_up(3), 3, var(0))))),
        ),
        lam(z(), z(), fin(Rc::clone(len)), var(0)),
    );
    let at_cs = app(
        at_id,
        l.clone(),
        l.clone(),
        Rc::new(Type::DVec { level: l.clone(), len: Rc::clone(len), fam: Rc::clone(fam) }),
        pi(z(), l.clone(), fin(n_up(1)), Rc::new(fam.shift_local_above(1, 1))),
        cs,
    );
    Term::App {
        fun: at_cs,
        dom_level: Level::Zero,
        cod_level: l.clone(),
        dom: fin(Rc::clone(len)),
        cod: Rc::clone(fam),
        arg: idx,
    }
}

// ---------------------------------------------------------------------------
// Derived constructions for `IWf` (docs/iwf-former-design.md §1.2, §2, §4)
//
// Transcribed from the Coq formalization (heather-coq `theories/Syntax/
// Term.v`: `iwfFam`, `iwfIH`, `iwfmotty`, `iwfcsty`, `iwfihty`,
// `iwfstepty`), with the same dictionary as `dnth`'s above, plus
// `T⟨rlift ↑⟩ⁿ…[llift (lsingle t)]` as [`Type::inst_top_above`]`(n, 1, t)`.
// One transcription serves typing, both reducers and conversion.
// ---------------------------------------------------------------------------

/// The signature of an `IWf` — every component but the index: `idx` and
/// `shape` in Γ, `arity` and `out` under `x : S`, `child` under
/// `x : S, i : Fin n` (see [`Type::IWf`]). [`Type::IWf`], [`Term::Supi`] and
/// [`Term::ElimIWf`] share it behind one pointer, and the schemas below are
/// written over it. Its `Debug` is [`Type::IWf`]'s budgeted one, through
/// `fmt.rs`.
#[derive(Clone, Eq)]
pub struct IWfSig {
    pub level: Level,
    pub idx_level: Level,
    pub idx: Rc<Type>,
    pub shape: Rc<Type>,
    pub arity: Rc<Term>,
    pub out: Rc<Term>,
    pub child: Rc<Term>,
}

impl IWfSig {
    /// The family's level, `l ⊔ li` (design §1.2).
    pub fn family_level(&self) -> Level {
        Level::join(self.level.clone(), self.idx_level.clone())
    }

    /// `IWf(…)(m)`.
    pub fn at(self: &Rc<Self>, index: Rc<Term>) -> Type {
        Type::IWf { sig: Rc::clone(self), index }
    }

    /// `sup_i(…; a; cs)`, at this signature.
    pub fn supi(self: &Rc<Self>, label: Rc<Term>, children: Rc<Term>) -> Term {
        Term::Supi { sig: Rc::clone(self), label, children }
    }

    /// The signature weakened past `by` binders. The components under the
    /// shape's (and the position's) binder keep those binders fixed, which is
    /// what shifting the whole former does, so it is done that way.
    pub fn shift_local(self: &Rc<Self>, by: u32) -> Rc<IWfSig> {
        if by == 0 {
            return Rc::clone(self);
        }
        match self.at(Rc::new(Term::Zero)).shift_local(by) {
            Type::IWf { sig, .. } => sig,
            _ => unreachable!("shifting an IWf yields an IWf"),
        }
    }
}

/// `M[t_j/j, t_z/z]` for a motive `M` in `(Γ, j, z)`, read `by` binders
/// further out: the two payloads and the result are in `(Γ, Δ)` with
/// `|Δ| = by`. `elim_IWf`'s motive binds the index and the tree.
pub fn inst_motive2(motive: &Type, by: u32, tj: &Term, tz: &Term) -> Type {
    motive.inst_top_above(by, 1, tj).inst_top(0, tz)
}

/// `iwfFam a`: the children's family, `IWf(…)(c[a/x, k/i])`, in `(Γ, k)`
/// for `a` in Γ. The `k`th child of `sup_i(a; cs)` lives at it.
pub fn iwf_fam(sig: &Rc<IWfSig>, a: &Term) -> Type {
    sig.shift_local(1).at(Rc::new(sig.child.inst_top_above(0, 1, a)))
}

/// `DVec^{l⊔li}(n[a/x]; k. IWf(…)(c[a/x, k/i]))`, in Γ for `a` in Γ: the
/// type of `sup_i(a; cs)`'s children (design §2), and `cs`'s entry in the
/// step telescope at `a := x`.
pub fn iwf_children_ty(sig: &Rc<IWfSig>, a: &Term) -> Type {
    Type::DVec {
        level: sig.family_level(),
        len: Rc::new(sig.arity.inst_top(0, a)),
        fam: Rc::new(iwf_fam(sig, a)),
    }
}

/// `iwfmotty`: the motive's scrutinee type `IWf(…)(j)`, in `(Γ, j : I)`.
pub fn iwf_motive_scrut_ty(sig: &Rc<IWfSig>) -> Type {
    sig.shift_local(1).at(Rc::new(Term::Var(LocalVar(0))))
}

/// The `elim_IWf` step telescope. Given the signature and the motive in Γ
/// (the motive in `(Γ, j, z)`), returns the three binding types
///
/// ```text
/// cs : DVec^{l⊔li}(n; k. IWf(…)(c[x, k/i]))                in (Γ, a : S)
/// ih : Π^{0,l'}(i : Fin n). M[c[x, i]/j, dnth(…; cs; i)/z]  in (Γ, a, cs)
/// s  : M[o/j, sup_i(a; cs)/z]                              in (Γ, a, cs, ih)
/// ```
///
/// where, in `(Γ, a)`, the components under the shape binder are read with
/// `a` for `x` as they stand (as `wf_step_telescope`'s arity is).
/// heather-coq's `iwfcsty`, `iwfihty` and `iwfstepty`, binder for binder.
pub fn iwf_step_telescope(sig: &Rc<IWfSig>, motive_level: &Level, motive: &Type) -> (Type, Type, Type) {
    let var = |i: u32| Rc::new(Term::Var(LocalVar(i)));
    let cs_ty = iwf_children_ty(&sig.shift_local(1), &Term::Var(LocalVar(0)));
    // In (Γ, a, cs, i): the child index c[a, i] and the `i`th child, whose
    // family is in (Γ, a, cs, i, k).
    let child_at_i = sig.child.shift_local_above(1, 1);
    let fam = sig.shift_local(4).at(Rc::new(sig.child.shift_local_above(2, 1)));
    let nth_child = dnth(
        &sig.family_level(),
        &Rc::new(sig.arity.shift_local(2)),
        &Rc::new(fam),
        var(1),
        var(0),
    );
    let ih_ty = Type::Pi {
        dom_level: Level::Zero,
        cod_level: motive_level.clone(),
        dom: Rc::new(Type::Fin { len: Rc::new(sig.arity.shift_local(1)) }),
        cod: Rc::new(inst_motive2(motive, 3, &child_at_i, &nth_child)),
    };
    let sup = sig.shift_local(3).supi(var(2), var(1));
    let step_ty = inst_motive2(motive, 3, &sig.out.shift_local(2), &sup);
    (cs_ty, ih_ty, step_ty)
}

/// `iwfIH a cs`: the induction hypothesis `elim_IWf`'s β hands its step,
///
/// ```text
/// λ^{0,l'}(i : Fin n[a/x]). elim_IWf(…; c[a/x, i/i]; dnth^{l⊔li}(n[a/x]; k. iwfFam a; cs; i))
/// ```
///
/// in Γ, for `a` and `cs` in Γ (design §4). The recursive call is at the
/// child's own index, so β fires at any index, open data included.
pub fn iwf_ih(
    sig: &Rc<IWfSig>,
    motive_level: &Level,
    motive: &Rc<Type>,
    step: &Rc<Term>,
    a: &Term,
    cs: &Term,
) -> Term {
    let len = sig.arity.inst_top(0, a);
    let child = dnth(
        &sig.family_level(),
        &Rc::new(len.shift_local(1)),
        &Rc::new(iwf_fam(sig, a).shift_local_above(1, 1)),
        Rc::new(cs.shift_local(1)),
        Rc::new(Term::Var(LocalVar(0))),
    );
    let rec = Term::ElimIWf {
        sig: sig.shift_local(1),
        motive_level: motive_level.clone(),
        motive: Rc::new(motive.shift_local_above(1, 2)),
        step: Rc::new(step.shift_local_above(1, 3)),
        index: Rc::new(sig.child.inst_top_above(0, 1, a)),
        scrut: Rc::new(child),
    };
    Term::Lam {
        dom_level: Level::Zero,
        cod_level: motive_level.clone(),
        dom: Rc::new(Type::Fin { len: Rc::new(len) }),
        body: Rc::new(rec),
    }
}

// ---------------------------------------------------------------------------
// Derived constructions for `M` (docs/kernel-coinduction-design.md §1)
//
// One transcription serves typing, both reducers and conversion, as the `IWf`
// schemas above do. Scopes are named in each doc comment; `f` is the family's
// level `l ⊔ l' ⊔ li`.
// ---------------------------------------------------------------------------

/// The signature of an `M` — every component but the index: `idx` in Γ,
/// `shape` under `i : I`, `pos` under `i, s : S`, `next` under `i, s, p : P`
/// (see [`Type::M`]). [`Type::M`], [`Term::Corec`] and [`Term::Out`] share it
/// behind one pointer. Its `Debug` is [`Type::M`]'s budgeted one, through
/// `fmt.rs`.
#[derive(Clone, Eq)]
pub struct MSig {
    pub level: Level,
    pub pos_level: Level,
    pub idx_level: Level,
    pub idx: Rc<Type>,
    pub shape: Rc<Type>,
    pub pos: Rc<Type>,
    pub next: Rc<Term>,
}

impl MSig {
    /// The family's level, `l ⊔ l' ⊔ li` (design §1.1).
    pub fn family_level(&self) -> Level {
        Level::join(Level::join(self.level.clone(), self.pos_level.clone()), self.idx_level.clone())
    }

    /// `M(…)(j)`.
    pub fn at(self: &Rc<Self>, index: Rc<Term>) -> Type {
        Type::M { sig: Rc::clone(self), index }
    }

    /// The signature weakened past `by` binders, by shifting the whole former
    /// (the components under binders keep them fixed).
    pub fn shift_local(self: &Rc<Self>, by: u32) -> Rc<MSig> {
        if by == 0 {
            return Rc::clone(self);
        }
        match self.at(Rc::new(Term::Zero)).shift_local(by) {
            Type::M { sig, .. } => sig,
            _ => unreachable!("shifting an M yields an M"),
        }
    }

    /// `S[j/i]`, in Γ for `j` in Γ.
    pub fn shape_at(&self, j: &Term) -> Type {
        self.shape.inst_top(0, j)
    }

    /// `P[j/i, s]`, in `(Γ, s)` for `j` in Γ.
    pub fn pos_at(&self, j: &Term) -> Type {
        self.pos.inst_top_above(0, 1, j)
    }

    /// `o[j/i, s, p]`, in `(Γ, s, p)` for `j` in Γ.
    pub fn next_at(&self, j: &Term) -> Term {
        self.next.inst_top_above(0, 2, j)
    }
}

/// The signature a [`Term::TmIWf`] code decodes to: the index type and the
/// shapes read through `El` at their levels, the arity, output and child
/// index carried across unchanged (docs/iwf-former-design.md §6). The one
/// place the decoding is spelled, so both reducers and the typing rule agree
/// on it.
pub fn iwf_sig_of_code(
    level: &Level,
    idx_level: &Level,
    idx: &Rc<Term>,
    shape: &Rc<Term>,
    arity: &Rc<Term>,
    out: &Rc<Term>,
    child: &Rc<Term>,
) -> IWfSig {
    let el = |level: &Level, tm: &Rc<Term>| Rc::new(Type::El { level: level.clone(), tm: Rc::clone(tm) });
    IWfSig {
        level: level.clone(),
        idx_level: idx_level.clone(),
        idx: el(idx_level, idx),
        shape: el(level, shape),
        arity: Rc::clone(arity),
        out: Rc::clone(out),
        child: Rc::clone(child),
    }
}

/// The signature a [`Term::TmM`] code decodes to: each piece read through
/// `El` at its own level, `next` carried across unchanged
/// (docs/kernel-m-codes-design.md §1). The one place the decoding is
/// spelled, so both reducers and the typing rule agree on it.
pub fn m_sig_of_code(
    level: &Level,
    pos_level: &Level,
    idx_level: &Level,
    idx: &Rc<Term>,
    shape: &Rc<Term>,
    pos: &Rc<Term>,
    next: &Rc<Term>,
) -> MSig {
    let el = |level: &Level, tm: &Rc<Term>| Rc::new(Type::El { level: level.clone(), tm: Rc::clone(tm) });
    MSig {
        level: level.clone(),
        pos_level: pos_level.clone(),
        idx_level: idx_level.clone(),
        idx: el(idx_level, idx),
        shape: el(level, shape),
        pos: el(pos_level, pos),
        next: Rc::clone(next),
    }
}

/// `out`'s type at index `j` (in Γ):
///
/// ```text
/// Σ^{l,f}(s : S[j/i]). Π^{l',f}(p : P[j/i, s]). M(…)(o[j/i, s, p])
/// ```
pub fn m_out_ty(sig: &Rc<MSig>, j: &Term) -> Type {
    let f = sig.family_level();
    Type::Sigma {
        fst_level: sig.level.clone(),
        snd_level: f.clone(),
        fst: Rc::new(sig.shape_at(j)),
        snd: Rc::new(Type::Pi {
            dom_level: sig.pos_level.clone(),
            cod_level: f,
            dom: Rc::new(sig.pos_at(j)),
            cod: Rc::new(sig.shift_local(2).at(Rc::new(sig.next_at(j)))),
        }),
    }
}

/// The type of `corec`'s step, in `(Γ, i)` (the carrier `X` at `k` in
/// `(Γ, i)`); the step itself is checked in `(Γ, i, x : X)` at this type
/// weakened by one, since it does not mention the seed:
///
/// ```text
/// Σ^{l,k⊔f}(s : S). Π^{l',k⊔f}(p : P). X[o/i] +^{k,f} M(…)(o)
/// ```
pub fn m_step_ty(sig: &Rc<MSig>, carrier_level: &Level, carrier: &Type) -> Type {
    let f = sig.family_level();
    let kf = Level::join(carrier_level.clone(), f.clone());
    // In (Γ, i, s, p): the child's index, its seed's type and its tree type.
    let o = sig.next.as_ref();
    let child_seed = carrier.inst_top(3, o);
    let child_tree = sig.shift_local(3).at(Rc::new(o.clone()));
    Type::Sigma {
        fst_level: sig.level.clone(),
        snd_level: kf.clone(),
        fst: Rc::clone(&sig.shape),
        snd: Rc::new(Type::Pi {
            dom_level: sig.pos_level.clone(),
            cod_level: kf,
            dom: Rc::clone(&sig.pos),
            cod: Rc::new(Type::Sum {
                lhs_level: carrier_level.clone(),
                rhs_level: f,
                lhs: Rc::new(child_seed),
                rhs: Rc::new(child_tree),
            }),
        }),
    }
}

/// `out(corec^{k}(…; X; c; j; x))`'s reduct (design §1.4), in Γ for `j` and
/// `x` in Γ, with `r := c[j/i, x/x]`:
///
/// ```text
/// pair^{l,f}(s. Π(p : P[j, s]). M(o[j, s, p]);
///   fst r;
///   λ^{l',f}(p : P[j, fst r]).
///     case^{k,f,f}(_. M(o[j, fst r, p]); X[o[j, fst r, p]]; M(o[j, fst r, p]);
///       y. corec(…; X; c; o[j, fst r, p]; y); t. t;
///       (snd r) p))
/// ```
///
/// `r` is written twice; the rewriter duplicates it, the value machine shares
/// it through the environment (design §7).
pub fn m_out_corec(
    sig: &Rc<MSig>,
    carrier_level: &Level,
    carrier: &Rc<Type>,
    step: &Rc<Term>,
    j: &Term,
    x: &Term,
) -> Term {
    let var = |i: u32| Rc::new(Term::Var(LocalVar(i)));
    let f = sig.family_level();
    let kf = Level::join(carrier_level.clone(), f.clone());
    // The step's type at j, in Γ: Σ(s : S[j]). Π(p : P[j, s]). X[o] + M(o).
    let Type::Sigma { snd: step_snd, .. } = m_step_ty(sig, carrier_level, carrier).inst_top(0, j) else {
        unreachable!("m_step_ty builds a Σ")
    };
    let shape_j = Rc::new(sig.shape_at(j));
    let r = Rc::new(step.inst_top(0, &x.shift_local(1)).inst_top(0, j));
    let fst_r = Rc::new(Term::Fst {
        fst_level: sig.level.clone(),
        snd_level: kf.clone(),
        fst_ty: Rc::clone(&shape_j),
        snd_ty: Rc::clone(&step_snd),
        pair: Rc::clone(&r),
    });
    let snd_r = Term::Snd {
        fst_level: sig.level.clone(),
        snd_level: kf.clone(),
        fst_ty: Rc::clone(&shape_j),
        snd_ty: Rc::clone(&step_snd),
        pair: r,
    };
    // In (Γ, p): the child's index, its seed's type, its tree type.
    let pos = Rc::new(sig.pos_at(j).inst_top(0, &fst_r));
    let o_p = sig.next_at(j).inst_top_above(0, 1, &fst_r);
    let seed_ty = Rc::new(carrier.inst_top(1, &o_p));
    let tree_ty = Rc::new(sig.shift_local(1).at(Rc::new(o_p.clone())));
    let sum_ty = Type::Sum {
        lhs_level: carrier_level.clone(),
        rhs_level: f.clone(),
        lhs: Rc::clone(&seed_ty),
        rhs: Rc::clone(&tree_ty),
    };
    let child = Term::App {
        fun: Rc::new(snd_r.shift_local(1)),
        dom_level: sig.pos_level.clone(),
        cod_level: kf,
        dom: Rc::new(pos.shift_local(1)),
        cod: Rc::new(sum_ty.shift_local_above(1, 1)),
        arg: var(0),
    };
    // The new seed's branch, in (Γ, p, y).
    let again = Term::Corec {
        sig: sig.shift_local(2),
        carrier_level: carrier_level.clone(),
        carrier: Rc::new(carrier.shift_local_above(2, 1)),
        step: Rc::new(step.shift_local_above(2, 2)),
        index: Rc::new(o_p.shift_local(1)),
        seed: var(0),
    };
    let case = Term::Case {
        lhs_level: carrier_level.clone(),
        rhs_level: f.clone(),
        motive_level: f.clone(),
        lhs: seed_ty,
        rhs: Rc::clone(&tree_ty),
        motive: Rc::new(tree_ty.shift_local(1)),
        case_l: Rc::new(again),
        case_r: var(0),
        scrut: Rc::new(child),
    };
    let Type::Sigma { snd: out_snd, .. } = m_out_ty(sig, j) else { unreachable!("m_out_ty builds a Σ") };
    Term::Pair {
        fst_level: sig.level.clone(),
        snd_level: f.clone(),
        fst_ty: shape_j,
        snd_ty: out_snd,
        fst: fst_r,
        snd: Rc::new(Term::Lam { dom_level: sig.pos_level.clone(), cod_level: f, dom: pos, body: Rc::new(case) }),
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
mod size_tests {
    use super::{Term, Type};

    /// The checker's recursion holds `Type`s and `Term`s in every frame
    /// (`docs/native-depth-budget-design.md`), so a variant that outgrows the
    /// rest grows every frame of it: a flat `IWf` signature made a 1000-deep
    /// constructor value overflow the 8 MiB stack. A former with many
    /// components keeps them behind one pointer (`IWfSig`). The annotated
    /// formers carry up to three `Level`s, two words each
    /// (`issues/kernel-compact-level.md`).
    #[test]
    #[cfg(target_pointer_width = "64")]
    fn syntax_nodes_stay_their_size() {
        assert_eq!(std::mem::size_of::<Type>(), 56);
        assert_eq!(std::mem::size_of::<Term>(), 104);
    }
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

    // A prefix and an extension are the worlds `new` builds from the same
    // bindings, at and around chunk boundaries, and share the full chunks.
    #[test]
    fn prefix_and_extension_agree_with_rebuilding() {
        let binding = |i: usize| GlobalBinding::opaque_tm(LocalCtx::nil(), Layer::Code, Rc::new(Type::Nat), Level::constant(i as u64));
        let all: Vec<GlobalBinding> = (0..200).map(binding).collect();
        let psi = GlobalCtx::new(all[..150].to_vec());
        for n in [0, 1, 63, 64, 65, 128, 149, 150, 151] {
            let prefix = psi.prefix(n);
            assert_eq!(prefix, GlobalCtx::new(all[..n.min(150)].to_vec()), "prefix {n}");
            assert!(prefix.bindings.tail.len() < GLOBAL_CHUNK || n >= 150, "prefix {n}");
            assert!(prefix.bindings.sealed.iter().zip(psi.bindings.sealed.iter()).all(|(a, b)| Rc::ptr_eq(&a.bindings, &b.bindings)));
            for extra in [0, 1, 50] {
                let extended = prefix.extended(all[n.min(150)..n.min(150) + extra].iter().cloned());
                assert_eq!(extended, GlobalCtx::new(all[..n.min(150) + extra].to_vec()), "prefix {n} + {extra}");
            }
        }
        assert_eq!(psi.bindings.len(), 150);
    }
}
