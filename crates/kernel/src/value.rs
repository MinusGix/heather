//! The **value domain**: weak head normal forms with environments and
//! closures (docs/nbe-conversion-design.md §3).
//!
//! A value is a term (or type) reduced to weak head normal form, with every
//! sub-structure kept as an *environment plus syntax* rather than as a
//! substituted term. That is the whole point of the round: an eliminator's β
//! extends an environment instead of copying a branch
//! (`issues/whnf-sharing-term-growth.md`).
//!
//! The domain is shaped so that the kernel's invariants are
//! **unrepresentable**, not merely unviolated:
//!
//! - [`Type::El`] has no value: it either decodes (and the value is the
//!   decoded former) or its encoding is stuck, in which case the value is
//!   [`VNeTy::El`]. Ch. 06's normal-form grammar `V := U^δ | El^l ν`, made
//!   structural.
//! - [`VTy::Vec`] / [`VTy::Fin`] exist only over a **non-canonical** length:
//!   at a canonical one they step, so the evaluator never builds them.
//! - `box` values ([`Val::BoxTy`], [`Val::BoxTm`]) carry raw syntax with
//!   **no environment**, so there is no environment in which the payload
//!   *could* be evaluated. Ch. 06's "reduction never enters a box", made
//!   structural (design §3.5).
//! - Variables have a two-part identity ([`Head::Var`] / [`Head::BaseVar`]):
//!   a de Bruijn **level** into the concrete entries of Γ, and a **depth**
//!   into the abstract prefix `g` of a [`CtxBase::Var`] context. Both are
//!   stable under pushing binders on the right, which is the only thing
//!   conversion ever does (design §3.2).
//!
//! Three namespaces, treated differently (design §3.1): locals go through
//! the environment; universe levels and globals stay **syntax**. A global
//! variable becomes a *glued* neutral ([`VNeutral::unfold`]).
//!
//! **Forcing is fallible everywhere.** There is no `Deref`, no infallible
//! accessor, no `unwrap`: laziness introduces new places an `OutOfFuel` can
//! originate and each one must be able to propagate (design §6). All forcing
//! lives in [`crate::eval`], which owns the fuel.
//!
//! `Debug` on every recursive type here is budget-bounded through
//! [`crate::fmt`]'s `node()` gate, per `CLAUDE.md`: an accidental `{:?}` on
//! a value must not OOM the machine. Closures print their *body syntax*
//! (itself bounded) and never force anything.

use std::cell::RefCell;
use std::fmt;
use std::rc::Rc;

use crate::fmt::node;
use crate::level::Level;
use crate::term::{Branches, CtxBase, GlobalVar, LocalCtx, Motives, SubstTail, Term, Type};

pub mod shift;

// ---------------------------------------------------------------------------
// Environments
// ---------------------------------------------------------------------------

/// A local environment: one entry per **concrete** binder in scope,
/// innermost first, as a persistent list so that pushing a binder is one
/// allocation and capturing it in a closure is a refcount bump.
///
/// De Bruijn *indices* resolve against it from the inside; anything past the
/// end is a variable of the abstract prefix `g` (see [`Lookup`]). Because
/// the list only ever grows on the right, the *level* `len - 1 - i` assigned
/// to an entry never changes — which is exactly why closures need no
/// shifting.
#[derive(Clone)]
pub struct Env {
    node: Option<Rc<EnvNode>>,
    len: u32,
}

struct EnvNode {
    val: Rc<TmClo>,
    rest: Env,
}

/// The result of resolving a de Bruijn index against an [`Env`].
pub enum Lookup {
    /// A concrete entry.
    Bound(Rc<TmClo>),
    /// A variable of the abstract prefix, at `depth` counted from the
    /// prefix's inner end.
    Base(u32),
}

impl Default for Env {
    fn default() -> Env {
        Env::empty()
    }
}

impl Env {
    pub fn empty() -> Env {
        Env { node: None, len: 0 }
    }

    /// The number of concrete entries.
    pub fn len(&self) -> u32 {
        self.len
    }

    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// `ρ, v` — one more binder, innermost.
    pub fn push(&self, val: Rc<TmClo>) -> Env {
        Env {
            node: Some(Rc::new(EnvNode { val, rest: self.clone() })),
            len: self.len + 1,
        }
    }

    /// Push several binders, `vals[0]` outermost (the order the branch
    /// telescopes and the β-rules write them).
    pub fn extend(&self, vals: &[Rc<TmClo>]) -> Env {
        let mut e = self.clone();
        for v in vals {
            e = e.push(Rc::clone(v));
        }
        e
    }

    /// Resolve a de Bruijn index (0 = innermost).
    pub fn lookup(&self, i: u32) -> Lookup {
        if i >= self.len {
            return Lookup::Base(i - self.len);
        }
        let mut cur = self;
        let mut k = i;
        loop {
            // Safe by the length invariant: `k < cur.len` at every step.
            let Some(n) = cur.node.as_ref() else {
                return Lookup::Base(k);
            };
            if k == 0 {
                return Lookup::Bound(Rc::clone(&n.val));
            }
            k -= 1;
            cur = &n.rest;
        }
    }

    /// The identity environment of a Γ with `n` concrete entries: entry `j`
    /// (counted from the *outer* end) is the neutral variable at level `j`.
    /// This is the environment at the root of a conversion.
    pub fn identity(n: u32) -> Env {
        let mut e = Env::empty();
        for j in 0..n {
            e = e.push(Rc::new(TmClo::val(Rc::new(Val::var(j)))));
        }
        e
    }

    /// The entries, **outermost first** — the order [`Env::extend`] wants.
    /// Used by the outer-namespace maps, which have to rebuild the list.
    pub fn to_vec(&self) -> Vec<Rc<TmClo>> {
        let mut out = Vec::with_capacity(self.len as usize);
        let mut cur = self;
        while let Some(n) = cur.node.as_ref() {
            out.push(Rc::clone(&n.val));
            cur = &n.rest;
        }
        out.reverse();
        out
    }
}

// ---------------------------------------------------------------------------
// Closures and lazy values
// ---------------------------------------------------------------------------

/// A term sub-structure of a value: an environment plus unevaluated syntax,
/// with a memo for its weak head value.
///
/// With `k > 0` pending binders it is a **closure** (applied by
/// [`crate::eval::Eval::apply`]); with none it is a **lazy value** (forced by
/// [`crate::eval::Eval::force`]). The two are the same object because the
/// binder count is determined by the position, exactly as in the syntax.
///
/// [`TmClo::Val`] is an already-computed value (a β payload, a δ payload) and
/// [`TmClo::Elim`] is a pending elimination — the shape the *glued* unfold of
/// a neutral takes as its spine grows (design §5).
///
/// **A thunk never memoizes a failure**: the memo is written only on `Ok`, so
/// a value graph forced under an insufficient budget and re-forced under a
/// larger one still succeeds (design §6).
pub enum TmClo {
    Syn {
        env: Env,
        body: Rc<Term>,
        memo: RefCell<Option<Rc<Val>>>,
    },
    Val(Rc<Val>),
    Elim {
        head: Rc<TmClo>,
        elim: Rc<Elim>,
        memo: RefCell<Option<Rc<Val>>>,
    },
}

impl TmClo {
    pub fn syn(env: Env, body: Rc<Term>) -> TmClo {
        TmClo::Syn { env, body, memo: RefCell::new(None) }
    }

    pub fn val(v: Rc<Val>) -> TmClo {
        TmClo::Val(v)
    }

    pub fn elim(head: Rc<TmClo>, elim: Rc<Elim>) -> TmClo {
        TmClo::Elim { head, elim, memo: RefCell::new(None) }
    }

    /// The environment and syntax, when this is a syntactic closure. Used
    /// where a *rule* needs the sub-structure's syntax rather than its value
    /// — the `El` decodes (which wrap the encoding's children in `El`) and
    /// the universe/global instantiations. Everything the evaluator builds
    /// from syntax is `Syn`; the fallback is a stuck value, never a panic.
    pub fn as_syn(&self) -> Option<(&Env, &Rc<Term>)> {
        match self {
            TmClo::Syn { env, body, .. } => Some((env, body)),
            _ => None,
        }
    }

    /// The memoized value, if this closure has already been forced.
    pub fn memo(&self) -> Option<Rc<Val>> {
        match self {
            TmClo::Syn { memo, .. } | TmClo::Elim { memo, .. } => memo.borrow().clone(),
            TmClo::Val(v) => Some(Rc::clone(v)),
        }
    }

    /// Record a successful force. Never called with a failure — that is the
    /// no-poisoned-thunk rule.
    pub(crate) fn set_memo(&self, v: &Rc<Val>) {
        match self {
            TmClo::Syn { memo, .. } | TmClo::Elim { memo, .. } => {
                *memo.borrow_mut() = Some(Rc::clone(v));
            }
            TmClo::Val(_) => {}
        }
    }
}

/// A type sub-structure of a value: the type mirror of [`TmClo`].
///
/// [`TyClo::Syn`] is the ordinary case — an environment plus unevaluated
/// syntax, with a memo. The other two exist because *conversion* builds
/// types the evaluator never does (docs/nbe-conversion-design.md §13, stage
/// 2b): the comparison rules synthesize `Π`, `Vec`, `El` … whose children are
/// **domain objects** rather than syntax, and there is no environment in
/// which a domain object could be written down.
///
/// - [`TyClo::Val`] is an already-computed type. As a *closure* it is
///   constant: applying it to arguments ignores them, which is exactly what
///   the rules that weaken a type into a binder position mean.
/// - [`TyClo::Vec`] is `Vec^l(T; k)` held **unforced**, so that the Σ-tail of
///   a vector at a canonical length stays lazy even when the element type is
///   a value with no syntax. Forcing it is `Eval::vec_ty`.
pub enum TyClo {
    Syn {
        env: Env,
        body: Rc<Type>,
        memo: RefCell<Option<Rc<VTy>>>,
    },
    Val(Rc<VTy>),
    Vec {
        level: Level,
        elem: Rc<TyClo>,
        len: Rc<TmClo>,
        memo: RefCell<Option<Rc<VTy>>>,
    },
}

impl TyClo {
    pub fn new(env: Env, body: Rc<Type>) -> TyClo {
        TyClo::Syn { env, body, memo: RefCell::new(None) }
    }

    pub fn val(v: Rc<VTy>) -> TyClo {
        TyClo::Val(v)
    }

    pub fn vec(level: Level, elem: Rc<TyClo>, len: Rc<TmClo>) -> TyClo {
        TyClo::Vec { level, elem, len, memo: RefCell::new(None) }
    }

    /// The environment and syntax, when this is a syntactic closure. See
    /// [`TmClo::as_syn`]: a rule that needs the sub-structure's *syntax*
    /// falls back to a stuck value rather than panicking.
    pub fn as_syn(&self) -> Option<(&Env, &Rc<Type>)> {
        match self {
            TyClo::Syn { env, body, .. } => Some((env, body)),
            _ => None,
        }
    }

    pub fn memo(&self) -> Option<Rc<VTy>> {
        match self {
            TyClo::Syn { memo, .. } | TyClo::Vec { memo, .. } => memo.borrow().clone(),
            TyClo::Val(v) => Some(Rc::clone(v)),
        }
    }

    pub(crate) fn set_memo(&self, v: &Rc<VTy>) {
        match self {
            TyClo::Syn { memo, .. } | TyClo::Vec { memo, .. } => {
                *memo.borrow_mut() = Some(Rc::clone(v));
            }
            TyClo::Val(_) => {}
        }
    }
}

// ---------------------------------------------------------------------------
// Neutrals
// ---------------------------------------------------------------------------

/// The tail of a local substitution inside a value: `·_{g?}` or `wk_g`.
///
/// The paper's `k` — δ̂, the *source* context's length — is deliberately
/// **dropped**, and `·`'s base is normalized to the ambient Γ's. Both are
/// determined by the scope the value lives in, which is common to the two
/// sides of every comparison; and keeping them would make a value disagree
/// with its own reduct. The rewriter renormalizes them at every
/// `apply_local` (`wk^k_g ∘ δ = wk^δ̂_g`, `·^k ∘ δ = ·^δ̂_δ̌`, `subst.rs`),
/// which is a thing an environment machine — having performed no
/// substitution — has no opportunity to do.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VTail {
    /// `·^k_{g?}` at the ambient base.
    Empty(CtxBase),
    /// `wk^k_g`.
    Wk(GlobalVar),
}

/// A local substitution inside a value. The **terms are values** — evaluated
/// pointwise when the neutral is built — because a `δ` of unforced syntax is
/// the defect class reintroduced by the domain (design §3.4, the subtlest
/// correctness point in it).
#[derive(Clone)]
pub struct VSubst {
    pub tail: VTail,
    pub terms: Vec<Rc<Val>>,
}

impl VTail {
    /// The tail of a syntactic substitution, read in a scope whose base is
    /// `base`. See [`VTail`] for why `len` and `·`'s base are not carried.
    pub fn of(tail: SubstTail, base: CtxBase) -> VTail {
        match tail {
            SubstTail::Wk { ctx_var, .. } => VTail::Wk(ctx_var),
            SubstTail::Empty { .. } => VTail::Empty(base),
        }
    }
}

/// The head of a neutral.
#[derive(Clone)]
pub enum Head {
    /// A concrete local, by de Bruijn **level** from the outer end of Γ.
    Var(u32),
    /// A local of the abstract prefix `g`, by **depth** from its inner end.
    BaseVar(u32),
    /// `u^δ` — a global term variable. Glued when it is a definition
    /// ([`VNeutral::unfold`]).
    Global { var: GlobalVar, subst: VSubst },
    /// `box (U^δ)` under a code recursor: canonical, but the recursor can
    /// never fire on it (ch. 06). Naming it a head is what keeps
    /// `reduce::is_neutral_term`'s special case from being re-derived.
    BoxedGlobalTy(Rc<Type>),
    /// `box (u^δ)` under a code recursor.
    BoxedGlobalTm(Rc<Term>),
    /// An eliminator applied to a value it cannot eliminate — reachable only
    /// on ill-typed input, where `reduce.rs` is likewise stuck without being
    /// neutral. Given a home here so that no input reaches a panic.
    Stuck(Rc<Val>),
}

impl Head {
    /// Whether this head makes the spine a genuine ch. 06 neutral (as
    /// opposed to an ill-typed stuck form).
    pub fn is_neutral(&self) -> bool {
        !matches!(self, Head::Stuck(_))
    }
}

/// A **glued** neutral: a head, a spine of eliminations applied
/// outermost-last, and — when the head is a defined global — the pending
/// δ-unfolding of the whole thing (design §5).
///
/// `unfold` is `Some` exactly when the head is a `Global` that `Defs` says is
/// defined; pushing an elimination onto a glued neutral extends the unfold by
/// the same elimination, so forcing it replays the spine. The δ-lazy
/// conversion order compares spines *without* forcing and only unfolds when
/// that fails.
pub struct VNeutral {
    pub head: Head,
    pub spine: Vec<Elim>,
    pub unfold: Option<Rc<TmClo>>,
}

/// Neutral **types**: ch. 06's `V := U^δ | El^l ν`.
pub enum VNeTy {
    /// `U^δ` — a global type variable. Never glued: type-level bindings have
    /// no bodies.
    Global { var: GlobalVar, subst: VSubst },
    /// `El^l ν` at an encoding that does not decode. Forced, so the payload
    /// is a weak head value: a neutral (the ch. 06 case) or — on ill-typed
    /// input — a stuck one.
    El { level: Level, tm: Rc<Val> },
}

// ---------------------------------------------------------------------------
// Type values
// ---------------------------------------------------------------------------

/// Weak head normal **types**. Every former keeps its levels as syntax
/// (§3.1: there is no level redex); a sub-structure under the former's own
/// local binder is a [`TyClo`]/[`TmClo`] with that binder pending.
pub enum VTy {
    Nat,
    Ty(Level),
    Unit { level: Level },
    Empty { level: Level },
    SEmpty { level: Level },
    Pi {
        dom_level: Level,
        cod_level: Level,
        dom: Rc<TyClo>,
        cod: Rc<TyClo>,
    },
    Sigma {
        fst_level: Level,
        snd_level: Level,
        fst: Rc<TyClo>,
        snd: Rc<TyClo>,
    },
    W {
        shape_level: Level,
        pos_level: Level,
        shape: Rc<TyClo>,
        pos: Rc<TyClo>,
    },
    /// The arity is a `Nat` **term** under the shape binder, so it is a term
    /// closure, not a type one.
    Wf {
        level: Level,
        shape: Rc<TyClo>,
        arity: Rc<TmClo>,
    },
    /// Non-dependent: neither summand binds, so neither is a closure — both
    /// are lazy 0-binder sub-structures.
    Sum {
        lhs_level: Level,
        rhs_level: Level,
        lhs: Rc<TyClo>,
        rhs: Rc<TyClo>,
    },
    Id {
        level: Level,
        ty: Rc<TyClo>,
        lhs: Rc<TmClo>,
        rhs: Rc<TmClo>,
    },
    SEq {
        level: Level,
        ty: Rc<TyClo>,
        lhs: Rc<TmClo>,
        rhs: Rc<TmClo>,
    },
    /// **Only at a non-canonical length** — at `0`/`S k` the former steps, so
    /// the evaluator never builds this. `len` is therefore already forced.
    Vec {
        level: Level,
        elem: Rc<TyClo>,
        len: Rc<Val>,
    },
    /// See [`VTy::Vec`].
    Fin { len: Rc<Val> },
    /// Binds *universe* variables, not a local: entered by instantiating the
    /// body syntax and evaluating it in the **unchanged** environment
    /// (`inst_univ` renumbers the outer scope back down, so the captured
    /// environment is already in the post-instantiation scope).
    UPi {
        num_vars: u32,
        level: Level,
        body: Rc<TyClo>,
    },
    /// Binds a *global* (context) variable; see [`VTy::UPi`].
    CtxPi { level: Level, body: Rc<TyClo> },
    /// Binds a *global* (type) variable; `ctx` is the argument's local
    /// context Δ and stays syntax (design §3.4).
    TyPi {
        ctx: LocalCtx,
        arg_level: Level,
        body_level: Level,
        body: Rc<TyClo>,
    },
    CodeTy { ctx: LocalCtx, level: Level },
    /// `ty` is scoped in Δ — a *different* local scope — and therefore stays
    /// syntax.
    CodeTm {
        ctx: LocalCtx,
        ty: Rc<Type>,
        level: Level,
    },
    Neutral(VNeTy),
}

// ---------------------------------------------------------------------------
// Term values
// ---------------------------------------------------------------------------

/// Weak head normal **terms**.
pub enum Val {
    // -- encodings of types (decoded by `El`) --
    TmNat,
    TmTy(Level),
    TmUnit { level: Level },
    TmEmpty { level: Level },
    TmSEmpty { level: Level },
    TmPi {
        dom_level: Level,
        cod_level: Level,
        dom: Rc<TmClo>,
        cod: Rc<TmClo>,
    },
    TmSigma {
        fst_level: Level,
        snd_level: Level,
        fst: Rc<TmClo>,
        snd: Rc<TmClo>,
    },
    TmW {
        shape_level: Level,
        pos_level: Level,
        shape: Rc<TmClo>,
        pos: Rc<TmClo>,
    },
    TmWf {
        level: Level,
        shape: Rc<TmClo>,
        arity: Rc<TmClo>,
    },
    TmId {
        level: Level,
        ty: Rc<TmClo>,
        lhs: Rc<TmClo>,
        rhs: Rc<TmClo>,
    },
    TmSEq {
        level: Level,
        ty: Rc<TmClo>,
        lhs: Rc<TmClo>,
        rhs: Rc<TmClo>,
    },
    TmSum {
        lhs_level: Level,
        rhs_level: Level,
        lhs: Rc<TmClo>,
        rhs: Rc<TmClo>,
    },
    TmVec {
        level: Level,
        elem: Rc<TmClo>,
        len: Rc<TmClo>,
    },
    TmFin { len: Rc<TmClo> },

    // -- data --
    Zero,
    Succ(Rc<TmClo>),
    Refl {
        level: Level,
        ty: Rc<TyClo>,
        tm: Rc<TmClo>,
    },
    SRefl {
        level: Level,
        ty: Rc<TyClo>,
        tm: Rc<TmClo>,
    },
    Pair {
        fst_level: Level,
        snd_level: Level,
        fst_ty: Rc<TyClo>,
        snd_ty: Rc<TyClo>,
        fst: Rc<TmClo>,
        snd: Rc<TmClo>,
    },
    Triv { level: Level },
    Inl {
        lhs_level: Level,
        rhs_level: Level,
        lhs: Rc<TyClo>,
        rhs: Rc<TyClo>,
        val: Rc<TmClo>,
    },
    Inr {
        lhs_level: Level,
        rhs_level: Level,
        lhs: Rc<TyClo>,
        rhs: Rc<TyClo>,
        val: Rc<TmClo>,
    },
    Sup {
        shape_level: Level,
        pos_level: Level,
        shape_ty: Rc<TyClo>,
        pos_ty: Rc<TyClo>,
        label: Rc<TmClo>,
        children: Rc<TmClo>,
    },
    Supf {
        level: Level,
        shape: Rc<TyClo>,
        arity: Rc<TmClo>,
        label: Rc<TmClo>,
        children: Rc<TmClo>,
    },

    // -- functions --
    Lam {
        dom_level: Level,
        cod_level: Level,
        dom: Rc<TyClo>,
        body: Rc<TmClo>,
    },
    /// Binds universe variables; see [`VTy::UPi`].
    ULam {
        num_vars: u32,
        level: Level,
        body: Rc<TmClo>,
    },
    CtxLam { level: Level, body: Rc<TmClo> },
    TyLam {
        ctx: LocalCtx,
        arg_level: Level,
        body_level: Level,
        body: Rc<TmClo>,
    },

    // -- code: inert atoms carrying syntax, with NO environment (§3.5) --
    BoxTy(Rc<Type>),
    BoxTm(Rc<Term>),

    Neutral(Rc<VNeutral>),
}

impl Val {
    /// The neutral variable at concrete level `lvl`.
    pub fn var(lvl: u32) -> Val {
        Val::Neutral(Rc::new(VNeutral {
            head: Head::Var(lvl),
            spine: Vec::new(),
            unfold: None,
        }))
    }

    /// The neutral variable at abstract-prefix depth `depth`.
    pub fn base_var(depth: u32) -> Val {
        Val::Neutral(Rc::new(VNeutral {
            head: Head::BaseVar(depth),
            spine: Vec::new(),
            unfold: None,
        }))
    }

    /// Whether this value is a ch. 06 neutral (as opposed to canonical or
    /// ill-typed-stuck).
    pub fn is_neutral(&self) -> bool {
        matches!(self, Val::Neutral(n) if n.head.is_neutral())
    }
}

// ---------------------------------------------------------------------------
// Eliminations
// ---------------------------------------------------------------------------

/// One elimination of a neutral spine, with the eliminator's annotations
/// evaluated (or held as closures) exactly as the corresponding [`Term`]
/// carries them — conversion's neutral congruences compare them.
///
/// The four forms whose β needs to rebuild *syntax* (`ElimW`, `ElimWf`, and
/// the two code recursors) carry the environment they were built in; the
/// others reach everything they need through their closures.
#[derive(Clone)]
pub enum Elim {
    App {
        dom_level: Level,
        cod_level: Level,
        dom: Rc<TyClo>,
        cod: Rc<TyClo>,
        arg: Rc<TmClo>,
    },
    UApp { levels: Vec<Level> },
    /// The argument is a local context, syntax by construction.
    CtxApp { ctx: LocalCtx },
    /// The argument is a type in the binding's Δ — a *different* local scope
    /// — so it stays syntax (design §3.4).
    TyApp { arg: Rc<Type> },
    Fst {
        fst_level: Level,
        snd_level: Level,
        fst_ty: Rc<TyClo>,
        snd_ty: Rc<TyClo>,
    },
    Snd {
        fst_level: Level,
        snd_level: Level,
        fst_ty: Rc<TyClo>,
        snd_ty: Rc<TyClo>,
    },
    ElimNat {
        level: Level,
        motive: Rc<TyClo>,
        base: Rc<TmClo>,
        step: Rc<TmClo>,
    },
    ElimEmpty {
        level: Level,
        scrut_level: Level,
        motive: Rc<TyClo>,
    },
    ElimSEmpty {
        level: Level,
        scrut_level: Level,
        motive: Rc<TyClo>,
    },
    Case {
        lhs_level: Level,
        rhs_level: Level,
        motive_level: Level,
        lhs: Rc<TyClo>,
        rhs: Rc<TyClo>,
        motive: Rc<TyClo>,
        case_l: Rc<TmClo>,
        case_r: Rc<TmClo>,
    },
    ElimW {
        shape_level: Level,
        pos_level: Level,
        motive_level: Level,
        shape: Rc<TyClo>,
        pos: Rc<TyClo>,
        motive: Rc<TyClo>,
        step: Rc<TmClo>,
        env: Env,
    },
    ElimWf {
        level: Level,
        motive_level: Level,
        shape: Rc<TyClo>,
        arity: Rc<TmClo>,
        motive: Rc<TyClo>,
        step: Rc<TmClo>,
        env: Env,
    },
    J {
        ty_level: Level,
        motive_level: Level,
        ty: Rc<TyClo>,
        lhs: Rc<TmClo>,
        motive: Rc<TyClo>,
        case: Rc<TmClo>,
        rhs: Rc<TmClo>,
    },
    Transp {
        ty_level: Level,
        motive_level: Level,
        ty: Rc<TyClo>,
        motive: Rc<TyClo>,
        lhs: Rc<TmClo>,
        rhs: Rc<TmClo>,
        tm: Rc<TmClo>,
    },
    LetBoxTy {
        motive_level: Level,
        code_level: Level,
        ctx: LocalCtx,
        motive: Rc<TyClo>,
        body: Rc<TmClo>,
    },
    LetBoxTm {
        motive_level: Level,
        code_level: Level,
        ctx: LocalCtx,
        ty: Rc<Type>,
        motive: Rc<TyClo>,
        body: Rc<TmClo>,
    },
    ElimCodeTy {
        ty_motive_level: Level,
        tm_motive_level: Level,
        motives: Rc<Motives>,
        branches: Rc<Branches>,
        code_level: Level,
        ctx: LocalCtx,
        env: Env,
    },
    /// `ty` is the recursor's type annotation, **already in WHNF** and
    /// scoped in Δ (ch. 06 fixes the type-then-term reduction order).
    ElimCodeTm {
        ty_motive_level: Level,
        tm_motive_level: Level,
        motives: Rc<Motives>,
        branches: Rc<Branches>,
        code_level: Level,
        ctx: LocalCtx,
        ty: Rc<Type>,
        env: Env,
    },
}

impl Elim {
    /// A stable name for the elimination form — the head discriminant a
    /// shape comparison keys on.
    pub fn tag(&self) -> &'static str {
        match self {
            Elim::App { .. } => "app",
            Elim::UApp { .. } => "uapp",
            Elim::CtxApp { .. } => "ctxapp",
            Elim::TyApp { .. } => "tyapp",
            Elim::Fst { .. } => "fst",
            Elim::Snd { .. } => "snd",
            Elim::ElimNat { .. } => "elim_Nat",
            Elim::ElimEmpty { .. } => "elim_Empty",
            Elim::ElimSEmpty { .. } => "elim_sEmpty",
            Elim::Case { .. } => "case",
            Elim::ElimW { .. } => "elim_W",
            Elim::ElimWf { .. } => "elim_Wf",
            Elim::J { .. } => "J",
            Elim::Transp { .. } => "transp",
            Elim::LetBoxTy { .. } => "letbox_Ty",
            Elim::LetBoxTm { .. } => "letbox_Tm",
            Elim::ElimCodeTy { .. } => "elim_CodeTy",
            Elim::ElimCodeTm { .. } => "elim_CodeTm",
        }
    }
}

// ---------------------------------------------------------------------------
// Budget-bounded Debug (CLAUDE.md: never derived, always `node()`-gated)
// ---------------------------------------------------------------------------

impl fmt::Debug for Env {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        node(f, |f| write!(f, "ρ[{}]", self.len))
    }
}

impl fmt::Debug for TmClo {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        node(f, |f| match self {
            TmClo::Syn { env, body, .. } => write!(f, "⟨{env:?}⊢{body:?}⟩"),
            TmClo::Val(v) => write!(f, "{v:?}"),
            TmClo::Elim { elim, .. } => write!(f, "⟨·{}⟩", elim.tag()),
        })
    }
}

impl fmt::Debug for TyClo {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        node(f, |f| match self {
            TyClo::Syn { env, body, .. } => write!(f, "⟨{env:?}⊢{body:?}⟩"),
            TyClo::Val(v) => write!(f, "{v:?}"),
            TyClo::Vec { elem, len, .. } => write!(f, "⟨Vec({elem:?}; {len:?})⟩"),
        })
    }
}

impl fmt::Debug for VSubst {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        node(f, |f| {
            write!(f, "^{:?}[", self.tail)?;
            for (i, t) in self.terms.iter().enumerate() {
                if i > 0 {
                    f.write_str(", ")?;
                }
                write!(f, "{t:?}")?;
            }
            f.write_str("]")
        })
    }
}

impl fmt::Debug for Head {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        node(f, |f| match self {
            Head::Var(l) => write!(f, "x@{l}"),
            Head::BaseVar(d) => write!(f, "g#{d}"),
            Head::Global { var, subst } => write!(f, "u{}{:?}", var.0, subst),
            Head::BoxedGlobalTy(t) => write!(f, "□{t:?}"),
            Head::BoxedGlobalTm(t) => write!(f, "□{t:?}"),
            Head::Stuck(v) => write!(f, "stuck({v:?})"),
        })
    }
}

impl fmt::Debug for VNeutral {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        node(f, |f| {
            write!(f, "{:?}", self.head)?;
            for e in &self.spine {
                write!(f, " ·{}", e.tag())?;
            }
            if self.unfold.is_some() {
                f.write_str(" ⟨δ⟩")?;
            }
            Ok(())
        })
    }
}

impl fmt::Debug for VNeTy {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        node(f, |f| match self {
            VNeTy::Global { var, subst } => write!(f, "U{}{:?}", var.0, subst),
            VNeTy::El { level, tm } => write!(f, "El[{level:?}]({tm:?})"),
        })
    }
}

impl fmt::Debug for Elim {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        node(f, |f| match self {
            Elim::App { arg, .. } => write!(f, "app({arg:?})"),
            Elim::UApp { levels } => write!(f, "$({} levels)", levels.len()),
            Elim::TyApp { arg } => write!(f, "@({arg:?})"),
            other => f.write_str(other.tag()),
        })
    }
}

impl fmt::Debug for VTy {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        node(f, |f| match self {
            VTy::Nat => f.write_str("Nat"),
            VTy::Ty(l) => write!(f, "Ty {l:?}"),
            VTy::Unit { level } => write!(f, "Unit {level:?}"),
            VTy::Empty { level } => write!(f, "Empty {level:?}"),
            VTy::SEmpty { level } => write!(f, "sEmpty {level:?}"),
            VTy::Pi { dom, cod, .. } => write!(f, "Π({dom:?}). {cod:?}"),
            VTy::Sigma { fst, snd, .. } => write!(f, "Σ({fst:?}). {snd:?}"),
            VTy::W { shape, pos, .. } => write!(f, "W({shape:?}). {pos:?}"),
            VTy::Wf { shape, arity, .. } => write!(f, "Wf({shape:?}). {arity:?}"),
            VTy::Sum { lhs, rhs, .. } => write!(f, "({lhs:?} + {rhs:?})"),
            VTy::Id { ty, lhs, rhs, .. } => write!(f, "Id({ty:?}; {lhs:?}; {rhs:?})"),
            VTy::SEq { ty, lhs, rhs, .. } => write!(f, "sEq({ty:?}; {lhs:?}; {rhs:?})"),
            VTy::Vec { elem, len, .. } => write!(f, "Vec({elem:?}; {len:?})"),
            VTy::Fin { len } => write!(f, "Fin({len:?})"),
            VTy::UPi { num_vars, body, .. } => write!(f, "ΠΠ[{num_vars}ℓ]. {body:?}"),
            VTy::CtxPi { body, .. } => write!(f, "(g:Ctx)⇒ {body:?}"),
            VTy::TyPi { body, .. } => write!(f, "(U:Typ)⇒ {body:?}"),
            VTy::CodeTy { level, .. } => write!(f, "□(⊢ Ty {level:?})"),
            VTy::CodeTm { ty, level, .. } => write!(f, "□(⊢ {ty:?} @ {level:?})"),
            VTy::Neutral(n) => write!(f, "{n:?}"),
        })
    }
}

impl fmt::Debug for Val {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        node(f, |f| match self {
            Val::TmNat => f.write_str("`Nat"),
            Val::TmTy(l) => write!(f, "`Ty {l:?}"),
            Val::TmUnit { .. } => f.write_str("`Unit"),
            Val::TmEmpty { .. } => f.write_str("`Empty"),
            Val::TmSEmpty { .. } => f.write_str("`sEmpty"),
            Val::TmPi { dom, cod, .. } => write!(f, "`Π({dom:?}). {cod:?}"),
            Val::TmSigma { fst, snd, .. } => write!(f, "`Σ({fst:?}). {snd:?}"),
            Val::TmW { shape, pos, .. } => write!(f, "`W({shape:?}). {pos:?}"),
            Val::TmWf { shape, arity, .. } => write!(f, "`Wf({shape:?}). {arity:?}"),
            Val::TmId { ty, lhs, rhs, .. } => write!(f, "`Id({ty:?}; {lhs:?}; {rhs:?})"),
            Val::TmSEq { ty, lhs, rhs, .. } => write!(f, "`sEq({ty:?}; {lhs:?}; {rhs:?})"),
            Val::TmSum { lhs, rhs, .. } => write!(f, "`({lhs:?} + {rhs:?})"),
            Val::TmVec { elem, len, .. } => write!(f, "`Vec({elem:?}; {len:?})"),
            Val::TmFin { len } => write!(f, "`Fin({len:?})"),
            Val::Zero => f.write_str("ze"),
            Val::Succ(t) => write!(f, "su {t:?}"),
            Val::Refl { tm, .. } => write!(f, "refl({tm:?})"),
            Val::SRefl { tm, .. } => write!(f, "srefl({tm:?})"),
            Val::Pair { fst, snd, .. } => write!(f, "⟨{fst:?}, {snd:?}⟩"),
            Val::Triv { .. } => f.write_str("⟨⟩"),
            Val::Inl { val, .. } => write!(f, "inl({val:?})"),
            Val::Inr { val, .. } => write!(f, "inr({val:?})"),
            Val::Sup { label, children, .. } => write!(f, "sup({label:?}; {children:?})"),
            Val::Supf { label, children, .. } => write!(f, "sup_f({label:?}; {children:?})"),
            Val::Lam { dom, body, .. } => write!(f, "λ({dom:?}). {body:?}"),
            Val::ULam { num_vars, body, .. } => write!(f, "Λ[{num_vars}ℓ]. {body:?}"),
            Val::CtxLam { body, .. } => write!(f, "Λ(g). {body:?}"),
            Val::TyLam { body, .. } => write!(f, "Λ(U). {body:?}"),
            Val::BoxTy(t) => write!(f, "box {t:?}"),
            Val::BoxTm(t) => write!(f, "box {t:?}"),
            Val::Neutral(n) => write!(f, "{n:?}"),
        })
    }
}
