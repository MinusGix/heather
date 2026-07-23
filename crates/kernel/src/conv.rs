//! Algorithmic convertibility checking (docs/delam/06, §Convertibility
//! Checking): reduce both sides to WHNF with the untyped weak-head
//! reduction, then compare structurally, mutually across the nine
//! judgments of the chapter:
//!
//! | tex judgment                  | here            |
//! |-------------------------------|-----------------|
//! | `Γ ⊢ T ≈ T' : l`              | [`Conv::ty`]    |
//! | `Γ ⊢ W ≈ W' : l` (normal)     | [`Conv::ty_nf`] |
//! | `Γ ⊢ V ≈ V' : l` (neutral)    | [`Conv::ty_ne`] |
//! | `⊢ Γ ≈ Δ`                     | [`Conv::ctx`]   |
//! | `Γ ⊢ t ≈ t' : T @ l`          | [`Conv::tm`]    |
//! | `Γ ⊢ w ≈ w' : W @ l` (normal) | [`Conv::tm_nf`] |
//! | `Γ ⊢ ν ≈ ν' : T @ l` (neutral)| [`Conv::tm_ne`] |
//! | … with the type in WHNF       | [`Conv::tm_nee`]|
//! | `Γ ⊢ δ ≈ δ' : Δ`              | [`Conv::subst`] |
//!
//! Shape of the algorithm (ch. 06 verbatim, per DESIGN.md):
//!
//! - **Neutral comparison is inference**: `tm_ne`/`ty_ne` return the type /
//!   universe level of the left input (left-biased — sound by ch. 08); the
//!   normal-form judgments are checking and *ignore* redundant annotations
//!   that well-typedness already forces (the ch. 06 note below the
//!   application rule). The judgment-level `l` inputs are threaded for rule
//!   fidelity but never branch the algorithm — every level the rules
//!   actually check is an *annotation*, compared via [`Level::equiv`].
//! - **η-directed** comparison at all four function types (`Π`, `ΠΠ`,
//!   `(g : Ctx) ⇒`, `(U : Typ) ⇒`): compare applications to a fresh
//!   variable in the suitably extended context.
//! - **Boxed types/terms compare syntactically** (`==`; α-equality is free
//!   under de Bruijn). Code is static data — β-convertible code is *not*
//!   convertible.
//! - Neutral recursors compare motives, all 13 branches (each at its
//!   instantiated motive type, the ch. 04 `G_A` telescopes), and indices —
//!   the ch. 06 `C_A` bundle ([`Conv::rec_ca`]).
//! - The layer index restricts *types*, not terms (ch. 06 intro): layer-m
//!   type formers mismatch outside layer m, but layer-m *term* forms are
//!   compared at any layer — their rules are stated at layer m, so those
//!   arms locally bump the layer to `m` (this is what lets conversion at
//!   layer p relate layer-m terms at MLTT types).
//! - **Fuel**: a single budget shared by all reduction steps and all
//!   comparison nodes, so the checker is total by construction even on
//!   ill-typed input; exhaustion is the distinguishable
//!   [`ConvError::OutOfFuel`]. On well-typed input conversion terminates
//!   (ch. 07/08), so exhaustion there means the budget was too small.
//!
//! Two apparent typos in the tex are deliberately not followed (both are
//! contradicted by the ch. 04 typing rules): the neutral `elim^Trm`
//! conclusion is at level `l₂` (the term-motive level), not `l₁`, and the
//! `t_app` branch type substitutes `u_s^id` (the argument) for the `Π`
//! codomain variable, not `u_t^id`.

use std::rc::Rc;

use crate::layer::Layer;
use crate::level::{Level, UnivVar};
use crate::reduce::{step_term, step_type};
use crate::subst::{GlobalEntry, GlobalSubst};
use crate::term::{
    Branches, CtxBase, CtxEntry, GlobalBinding, GlobalCtx, GlobalVar, LocalCtx, LocalSubst,
    LocalVar, Motives, Term, Type,
};

/// Why a convertibility check did not succeed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ConvError {
    /// The shared fuel budget ran out before the check finished. On
    /// well-typed input this means the budget was too small; on untyped
    /// input it may be divergence.
    OutOfFuel,
    /// No rule relates the two inputs: they are not convertible.
    NotConvertible,
}

type R<T = ()> = Result<T, ConvError>;

const NC: ConvError = ConvError::NotConvertible;

/// `Ψ; Γ ⊢_i T ≈ T' : l` — convertibility of types.
pub fn conv_type(
    psi: &GlobalCtx,
    gamma: &LocalCtx,
    layer: Layer,
    a: &Type,
    b: &Type,
    level: &Level,
    fuel: u64,
) -> R {
    debug_assert!(layer.computes(), "convertibility is only invoked at computing layers");
    Conv { fuel }.ty(&Env::new(psi, gamma, layer), a, b, level)
}

/// `Ψ; Γ ⊢_i t ≈ t' : T @ l` — convertibility of terms at a type.
#[allow(clippy::too_many_arguments)]
pub fn conv_term(
    psi: &GlobalCtx,
    gamma: &LocalCtx,
    layer: Layer,
    a: &Term,
    b: &Term,
    ty: &Type,
    level: &Level,
    fuel: u64,
) -> R {
    debug_assert!(layer.computes(), "convertibility is only invoked at computing layers");
    Conv { fuel }.tm(&Env::new(psi, gamma, layer), a, b, ty, level)
}

/// `Ψ ⊢_i Γ ≈ Δ` — convertibility of local contexts.
pub fn conv_local_ctx(
    psi: &GlobalCtx,
    layer: Layer,
    a: &LocalCtx,
    b: &LocalCtx,
    fuel: u64,
) -> R {
    debug_assert!(layer.computes(), "convertibility is only invoked at computing layers");
    let env = Env::new(psi, &LocalCtx { base: CtxBase::Nil, entries: vec![] }, layer);
    Conv { fuel }.ctx(&env, layer, a, b)
}

// ---------------------------------------------------------------------------
// Environment
// ---------------------------------------------------------------------------

/// The ambient scope of a comparison: Ψ, Γ, and the layer index. The
/// universe context L participates only by shifting (its length is never
/// consulted), so it is not tracked. Extending any namespace clones — the
/// judgments extend scopes freely and correctness beats performance here.
#[derive(Clone)]
struct Env {
    psi: GlobalCtx,
    gamma: LocalCtx,
    layer: Layer,
}

impl Env {
    fn new(psi: &GlobalCtx, gamma: &LocalCtx, layer: Layer) -> Env {
        Env { psi: psi.clone(), gamma: gamma.clone(), layer }
    }

    fn with_layer(&self, layer: Layer) -> Env {
        Env { layer, ..self.clone() }
    }

    /// Replace Γ (and the layer) — used where a rule compares inside a
    /// *different* local context, e.g. `Ψ; Δ ⊢_p T ≈ T'`.
    fn in_ctx(&self, gamma: LocalCtx, layer: Layer) -> Env {
        Env { gamma, layer, ..self.clone() }
    }

    /// `Γ, x : T @ l`.
    fn push_entry(&self, ty: Rc<Type>, level: Level) -> Env {
        let mut e = self.clone();
        e.gamma.entries.push(CtxEntry { ty, level });
        e
    }

    /// Push a telescope: `tu` universe binders then the given global
    /// bindings (each already scoped over `L, ℓ⃗` and its Ψ-prefix). The
    /// ambient Ψ and Γ are weakened accordingly.
    fn push_tele(&self, tu: u32, globals: Vec<GlobalBinding>) -> Env {
        let tg = globals.len() as u32;
        let mut psi = shift_univ_psi(&self.psi, tu);
        psi.bindings.extend(globals);
        Env {
            psi,
            gamma: self.gamma.shift_univ(tu).shift_global(tg),
            layer: self.layer,
        }
    }

    fn push_univs(&self, n: u32) -> Env {
        self.push_tele(n, vec![])
    }

    fn push_global(&self, b: GlobalBinding) -> Env {
        self.push_tele(0, vec![b])
    }
}

/// Weaken every binding of Ψ by `by` universe variables (all bindings are
/// scoped in the same L).
fn shift_univ_psi(psi: &GlobalCtx, by: u32) -> GlobalCtx {
    if by == 0 {
        return psi.clone();
    }
    GlobalCtx {
        bindings: psi
            .bindings
            .iter()
            .map(|b| match b {
                GlobalBinding::Ctx => GlobalBinding::Ctx,
                GlobalBinding::Ty { ctx, layer, level } => GlobalBinding::Ty {
                    ctx: ctx.shift_univ(by),
                    layer: *layer,
                    level: level.shift(by, 0),
                },
                GlobalBinding::Tm { ctx, layer, ty, level } => GlobalBinding::Tm {
                    ctx: ctx.shift_univ(by),
                    layer: *layer,
                    ty: Rc::new(ty.shift_univ(by)),
                    level: level.shift(by, 0),
                },
            })
            .collect(),
    }
}

/// Ψ-lookup: `bindings[len - 1 - v]` (0 is innermost). The result is scoped
/// over its *prefix* of Ψ — callers shift by `v + 1`.
fn lookup(psi: &GlobalCtx, v: GlobalVar) -> Option<&GlobalBinding> {
    psi.bindings.len().checked_sub(1 + v.0 as usize).and_then(|i| psi.bindings.get(i))
}

// ---------------------------------------------------------------------------
// Small constructors (shared with the C_A tables below)
// ---------------------------------------------------------------------------

fn lvar(i: u32) -> Level {
    Level::Var(UnivVar(i))
}

/// The context `g` for the context variable at de Bruijn index `i`.
fn g_ctx(i: u32) -> LocalCtx {
    LocalCtx { base: CtxBase::Var(GlobalVar(i)), entries: vec![] }
}

/// `Δ, x : T @ l`.
fn ext_ctx(base: &LocalCtx, ty: Type, level: Level) -> LocalCtx {
    let mut c = base.clone();
    c.entries.push(CtxEntry { ty: Rc::new(ty), level });
    c
}

/// `U^{id_Δ}` for the global type variable `var` with index context `ctx`.
fn gty(var: u32, ctx: &LocalCtx) -> Type {
    Type::GlobalTy { var: GlobalVar(var), subst: LocalSubst::id(ctx) }
}

/// `u^{id_Δ}` for the global term variable `var` with index context `ctx`.
fn gtm(var: u32, ctx: &LocalCtx) -> Term {
    Term::GlobalTm { var: GlobalVar(var), subst: LocalSubst::id(ctx) }
}

// ---------------------------------------------------------------------------
// Motive instantiation (the `M[…/ℓ, …/g, …]` substitutions of ch. 04)
// ---------------------------------------------------------------------------

/// `M_Typ[lp/ℓ, gp/g, xp/x_T]`, viewed under a branch telescope that pushed
/// `tu` universe, `tg` global and `tl` local binders. `M_Typ` is scoped in
/// `(L, ℓ; Ψ, g; Γ, x_T)`; `gamma_tele` is the ambient Γ already weakened
/// into the telescope scope; the payloads are scoped in the telescope.
fn inst_ty_motive(
    m: &Type,
    (tu, tg, tl): (u32, u32, u32),
    lp: Level,
    gp: LocalCtx,
    xp: Term,
    gamma_tele: &LocalCtx,
) -> Type {
    m.shift_univ_above(tu, 1)
        .shift_global_above(tg, 1)
        .inst_univ(&[lp])
        .apply_global(&GlobalSubst::single(GlobalEntry::Ctx(gp)))
        .apply_local(&LocalSubst::id(gamma_tele).shift_local(tl).extended(Rc::new(xp)))
}

/// `M_Trm[lp/ℓ, gp/g, up/U_T, xp/x_t]`, as [`inst_ty_motive`] but for the
/// term motive's telescope `(L, ℓ; Ψ, g, U_T; Γ, x_t)`.
#[allow(clippy::too_many_arguments)]
fn inst_tm_motive(
    m: &Type,
    (tu, tg, tl): (u32, u32, u32),
    lp: Level,
    gp: LocalCtx,
    up: Type,
    xp: Term,
    gamma_tele: &LocalCtx,
) -> Type {
    m.shift_univ_above(tu, 1)
        .shift_global_above(tg, 2)
        .inst_univ(&[lp])
        .apply_global(&GlobalSubst {
            entries: vec![GlobalEntry::Ctx(gp), GlobalEntry::Ty(Rc::new(up))],
        })
        .apply_local(&LocalSubst::id(gamma_tele).shift_local(tl).extended(Rc::new(xp)))
}

// ---------------------------------------------------------------------------
// The checker
// ---------------------------------------------------------------------------

/// Left side / right side of a recursor comparison (`C_A` inputs).
struct RecSide<'a> {
    l1: &'a Level,
    l2: &'a Level,
    motives: &'a Motives,
    branches: &'a Branches,
}

struct Conv {
    fuel: u64,
}

impl Conv {
    fn spend(&mut self) -> R {
        if self.fuel == 0 {
            return Err(ConvError::OutOfFuel);
        }
        self.fuel -= 1;
        Ok(())
    }

    /// `T ⇝* W`, spending one fuel per step (shared budget, unlike
    /// [`crate::reduce::whnf_type`]'s local one).
    fn whnf_ty(&mut self, t: &Type, env: &Env) -> R<Type> {
        let mut cur = t.clone();
        while let Some(next) = step_type(&cur, &env.gamma) {
            self.spend()?;
            cur = next;
        }
        Ok(cur)
    }

    fn whnf_tm(&mut self, t: &Term, env: &Env) -> R<Term> {
        let mut cur = t.clone();
        while let Some(next) = step_term(&cur, &env.gamma) {
            self.spend()?;
            cur = next;
        }
        Ok(cur)
    }

    /// `L ⊢ l ≈ l' : Level` as a premise.
    fn lev_eq(&self, a: &Level, b: &Level) -> R {
        if a.equiv(b) { Ok(()) } else { Err(NC) }
    }

    // -- types --------------------------------------------------------------

    /// `Γ ⊢ T ≈ T' : l`: reduce both sides to WHNF, compare as normal.
    fn ty(&mut self, env: &Env, a: &Type, b: &Type, l: &Level) -> R {
        self.spend()?;
        let wa = self.whnf_ty(a, env)?;
        let wb = self.whnf_ty(b, env)?;
        self.ty_nf(env, &wa, &wb, l)
    }

    /// `Γ ⊢ W ≈ W' : l` for weak head normal types.
    fn ty_nf(&mut self, env: &Env, a: &Type, b: &Type, _l: &Level) -> R {
        match (a, b) {
            (Type::Nat, Type::Nat) => Ok(()),
            (Type::Ty(x), Type::Ty(y)) => self.lev_eq(x, y),
            (
                Type::Pi { dom_level: dl1, cod_level: cl1, dom: s1, cod: t1 },
                Type::Pi { dom_level: dl2, cod_level: cl2, dom: s2, cod: t2 },
            ) => {
                self.lev_eq(dl1, dl2)?;
                self.lev_eq(cl1, cl2)?;
                self.ty(env, s1, s2, dl1)?;
                let e = env.push_entry(Rc::clone(s1), dl1.clone());
                self.ty(&e, t1, t2, cl1)
            }
            // -- layer-m type formers: mismatch outside layer m -------------
            (
                Type::UPi { num_vars: n1, level: v1, body: b1 },
                Type::UPi { num_vars: n2, level: v2, body: b2 },
            ) => {
                if env.layer != Layer::Meta || n1 != n2 {
                    return Err(NC);
                }
                self.lev_eq(v1, v2)?;
                let e = env.push_univs(*n1);
                self.ty(&e, b1, b2, v1)
            }
            (
                Type::CtxPi { level: v1, body: b1 },
                Type::CtxPi { level: v2, body: b2 },
            ) => {
                if env.layer != Layer::Meta {
                    return Err(NC);
                }
                self.lev_eq(v1, v2)?;
                let e = env.push_global(GlobalBinding::Ctx);
                self.ty(&e, b1, b2, v1)
            }
            (
                Type::TyPi { ctx: c1, arg_level: a1, body_level: bl1, body: b1 },
                Type::TyPi { ctx: c2, arg_level: a2, body_level: bl2, body: b2 },
            ) => {
                if env.layer != Layer::Meta {
                    return Err(NC);
                }
                self.lev_eq(a1, a2)?;
                self.lev_eq(bl1, bl2)?;
                self.ctx(env, Layer::Prog, c1, c2)?;
                let e = env.push_global(GlobalBinding::Ty {
                    ctx: c1.clone(),
                    layer: Layer::Prog,
                    level: a1.clone(),
                });
                self.ty(&e, b1, b2, bl1)
            }
            (
                Type::CodeTy { ctx: c1, level: v1 },
                Type::CodeTy { ctx: c2, level: v2 },
            ) => {
                if env.layer != Layer::Meta {
                    return Err(NC);
                }
                self.lev_eq(v1, v2)?;
                self.ctx(env, Layer::Prog, c1, c2)
            }
            (
                Type::CodeTm { ctx: c1, ty: t1, level: v1 },
                Type::CodeTm { ctx: c2, ty: t2, level: v2 },
            ) => {
                if env.layer != Layer::Meta {
                    return Err(NC);
                }
                self.lev_eq(v1, v2)?;
                self.ctx(env, Layer::Prog, c1, c2)?;
                let e = env.in_ctx(c1.clone(), Layer::Prog);
                self.ty(&e, t1, t2, v1)
            }
            // -- neutrals ---------------------------------------------------
            (
                Type::El { .. } | Type::GlobalTy { .. },
                Type::El { .. } | Type::GlobalTy { .. },
            ) => self.ty_ne(env, a, b).map(drop),
            _ => Err(NC),
        }
    }

    /// `Γ ⊢ V ≈ V' : l` for neutral types; the level is *inferred*
    /// (left-biased) and returned.
    fn ty_ne(&mut self, env: &Env, a: &Type, b: &Type) -> R<Level> {
        self.spend()?;
        match (a, b) {
            (
                Type::GlobalTy { var: u1, subst: d1 },
                Type::GlobalTy { var: u2, subst: d2 },
            ) => {
                if u1 != u2 {
                    return Err(NC);
                }
                let Some(GlobalBinding::Ty { ctx, layer, level }) = lookup(&env.psi, *u1)
                else {
                    return Err(NC);
                };
                // i' ∈ {c, p} is forced by the binding form; i' ≤ i:
                if *layer > env.layer {
                    return Err(NC);
                }
                let level = level.clone();
                let ctx = ctx.shift_global(u1.0 + 1);
                self.subst(env, d1, d2, &ctx)?;
                Ok(level)
            }
            (
                Type::El { level: l1, tm: n1 },
                Type::El { level: l2, tm: n2 },
            ) => {
                self.lev_eq(l1, l2)?;
                self.tm_nee(env, n1, n2)?; // inferred `Ty l`: redundant, ignored
                Ok(l1.clone())
            }
            _ => Err(NC),
        }
    }

    // -- contexts and local substitutions -----------------------------------

    /// `⊢_i Γ ≈ Δ`, pairwise on entries (left-biased prefixes). `layer` is
    /// explicit because several rules compare index contexts at layer p.
    fn ctx(&mut self, env: &Env, layer: Layer, a: &LocalCtx, b: &LocalCtx) -> R {
        self.spend()?;
        if a.base != b.base || a.entries.len() != b.entries.len() {
            return Err(NC);
        }
        for (k, (ea, eb)) in a.entries.iter().zip(&b.entries).enumerate() {
            let prefix = LocalCtx { base: a.base, entries: a.entries[..k].to_vec() };
            let e = env.in_ctx(prefix, layer);
            self.ty(&e, &ea.ty, &eb.ty, &ea.level)?;
            self.lev_eq(&ea.level, &eb.level)?;
        }
        Ok(())
    }

    /// `Γ ⊢ δ ≈ δ' : Δ`, pairwise on the step terms over identical tails.
    fn subst(&mut self, env: &Env, d1: &LocalSubst, d2: &LocalSubst, target: &LocalCtx) -> R {
        self.spend()?;
        if d1.tail != d2.tail
            || d1.terms.len() != target.entries.len()
            || d2.terms.len() != target.entries.len()
        {
            return Err(NC);
        }
        for (k, e) in target.entries.iter().enumerate() {
            let prefix = LocalSubst { tail: d1.tail, terms: d1.terms[..k].to_vec() };
            let ty = e.ty.apply_local(&prefix);
            self.tm(env, &d1.terms[k], &d2.terms[k], &ty, &e.level)?;
        }
        Ok(())
    }

    // -- terms --------------------------------------------------------------

    /// `Γ ⊢ t ≈ t' : T @ l`: reduce the type and both terms to WHNF, then
    /// compare type-directed.
    fn tm(&mut self, env: &Env, a: &Term, b: &Term, ty: &Type, l: &Level) -> R {
        self.spend()?;
        let w = self.whnf_ty(ty, env)?;
        let wa = self.whnf_tm(a, env)?;
        let wb = self.whnf_tm(b, env)?;
        self.tm_nf(env, &wa, &wb, &w, l)
    }

    /// `Γ ⊢ w ≈ w' : W @ l` for weak head normal terms at a WHNF type,
    /// directed by the type.
    fn tm_nf(&mut self, env: &Env, a: &Term, b: &Term, w: &Type, _l: &Level) -> R {
        match w {
            // η: Γ, x : S ⊢ app(w↑; l,l'; x:S↑.T↑; x) ≈ app(w'↑; …; x) : T
            Type::Pi { dom_level, cod_level, dom, cod } => {
                // The `cod` annotation moves under the App binder: the Π
                // variable maps to the App's bound variable, Γ weakens by 2.
                let cod_ann = Rc::new(cod.apply_local(
                    &LocalSubst::id(&env.gamma)
                        .shift_local(2)
                        .extended(Rc::new(Term::Var(LocalVar(0)))),
                ));
                let app = |t: &Term| Term::App {
                    fun: Rc::new(t.shift_local(1)),
                    dom_level: dom_level.clone(),
                    cod_level: cod_level.clone(),
                    dom: Rc::new(dom.shift_local(1)),
                    cod: Rc::clone(&cod_ann),
                    arg: Rc::new(Term::Var(LocalVar(0))),
                };
                let e = env.push_entry(Rc::clone(dom), dom_level.clone());
                self.tm(&e, &app(a), &app(b), cod, cod_level)
            }
            // η: L, ℓ⃗ ⊢ w↑ $ ℓ⃗ ≈ w'↑ $ ℓ⃗ : T
            Type::UPi { num_vars, level, body } => {
                if env.layer != Layer::Meta {
                    return Err(NC);
                }
                let n = *num_vars;
                let levels: Vec<Level> = (0..n).rev().map(lvar).collect();
                let uapp = |t: &Term| Term::UApp {
                    fun: Rc::new(t.shift_univ(n)),
                    levels: levels.clone(),
                };
                let e = env.push_univs(n);
                self.tm(&e, &uapp(a), &uapp(b), body, level)
            }
            // η: Ψ, g : Ctx ⊢ w↑ @ g ≈ w'↑ @ g : T
            Type::CtxPi { level, body } => {
                if env.layer != Layer::Meta {
                    return Err(NC);
                }
                let capp = |t: &Term| Term::CtxApp {
                    fun: Rc::new(t.shift_global(1)),
                    ctx: g_ctx(0),
                };
                let e = env.push_global(GlobalBinding::Ctx);
                self.tm(&e, &capp(a), &capp(b), body, level)
            }
            // η: Ψ, U : Typ_p(Δ, l) ⊢ w↑ @ U^{id_Δ} ≈ w'↑ @ U^{id_Δ} : T
            Type::TyPi { ctx, arg_level, body_level, body } => {
                if env.layer != Layer::Meta {
                    return Err(NC);
                }
                let ctx_up = ctx.shift_global(1);
                let arg = Rc::new(gty(0, &ctx_up));
                let tapp = |t: &Term| Term::TyApp {
                    fun: Rc::new(t.shift_global(1)),
                    arg: Rc::clone(&arg),
                };
                let e = env.push_global(GlobalBinding::Ty {
                    ctx: ctx.clone(),
                    layer: Layer::Prog,
                    level: arg_level.clone(),
                });
                self.tm(&e, &tapp(a), &tapp(b), body, body_level)
            }
            // Code compares syntactically; neutrals structurally.
            Type::CodeTy { .. } => match (a, b) {
                (Term::BoxTy(t1), Term::BoxTy(t2)) => {
                    if t1 == t2 { Ok(()) } else { Err(NC) }
                }
                (Term::BoxTy(_), _) | (_, Term::BoxTy(_)) => Err(NC),
                _ => self.tm_nee(env, a, b).map(drop),
            },
            Type::CodeTm { .. } => match (a, b) {
                (Term::BoxTm(t1), Term::BoxTm(t2)) => {
                    if t1 == t2 { Ok(()) } else { Err(NC) }
                }
                (Term::BoxTm(_), _) | (_, Term::BoxTm(_)) => Err(NC),
                _ => self.tm_nee(env, a, b).map(drop),
            },
            Type::Nat => match (a, b) {
                (Term::Zero, Term::Zero) => Ok(()),
                (Term::Succ(x), Term::Succ(y)) => {
                    self.tm(env, x, y, &Type::Nat, &Level::Zero)
                }
                (Term::Zero | Term::Succ(_), _) | (_, Term::Zero | Term::Succ(_)) => {
                    Err(NC)
                }
                _ => self.tm_nee(env, a, b).map(drop),
            },
            Type::Ty(_) => match (a, b) {
                (Term::TmNat, Term::TmNat) => Ok(()),
                (Term::TmTy(x), Term::TmTy(y)) => self.lev_eq(x, y),
                (
                    Term::TmPi { dom_level: dl1, cod_level: cl1, dom: s1, cod: t1 },
                    Term::TmPi { dom_level: dl2, cod_level: cl2, dom: s2, cod: t2 },
                ) => {
                    self.lev_eq(dl1, dl2)?;
                    self.lev_eq(cl1, cl2)?;
                    self.tm(env, s1, s2, &Type::Ty(dl1.clone()), &Level::succ(dl1.clone()))?;
                    let el = Type::El { level: dl1.clone(), tm: Rc::clone(s1) };
                    let e = env.push_entry(Rc::new(el), dl1.clone());
                    self.tm(&e, t1, t2, &Type::Ty(cl1.clone()), &Level::succ(cl1.clone()))
                }
                (Term::TmNat | Term::TmTy(_) | Term::TmPi { .. }, _)
                | (_, Term::TmNat | Term::TmTy(_) | Term::TmPi { .. }) => Err(NC),
                _ => self.tm_nee(env, a, b).map(drop),
            },
            // Neutral type: only neutral terms inhabit it.
            Type::El { .. } | Type::GlobalTy { .. } => self.tm_nee(env, a, b).map(drop),
        }
    }

    /// Neutral comparison with the inferred type reduced to WHNF.
    fn tm_nee(&mut self, env: &Env, a: &Term, b: &Term) -> R<(Type, Level)> {
        let (t, l) = self.tm_ne(env, a, b)?;
        let w = self.whnf_ty(&t, env)?;
        Ok((w, l))
    }

    /// `Γ ⊢ ν ≈ ν' : T @ l` for neutral terms; the type and level are
    /// *inferred* (left-biased) and returned. Layer-m elimination forms
    /// bump the ambient layer to m — their rules are stated there, and the
    /// layer index restricts only types.
    fn tm_ne(&mut self, env: &Env, a: &Term, b: &Term) -> R<(Type, Level)> {
        self.spend()?;
        match (a, b) {
            (Term::Var(x), Term::Var(y)) => {
                if x != y {
                    return Err(NC);
                }
                let Some(i) = env.gamma.entries.len().checked_sub(1 + x.0 as usize)
                else {
                    return Err(NC);
                };
                let e = &env.gamma.entries[i];
                Ok((e.ty.shift_local(x.0 + 1), e.level.clone()))
            }
            (
                Term::GlobalTm { var: u1, subst: d1 },
                Term::GlobalTm { var: u2, subst: d2 },
            ) => {
                if u1 != u2 {
                    return Err(NC);
                }
                let Some(GlobalBinding::Tm { ctx, layer, ty, level }) = lookup(&env.psi, *u1)
                else {
                    return Err(NC);
                };
                // i' ∈ {v, c} is forced by the binding form; i' ≤ i:
                if *layer > env.layer {
                    return Err(NC);
                }
                let level = level.clone();
                let ctx = ctx.shift_global(u1.0 + 1);
                let ty = ty.shift_global(u1.0 + 1);
                self.subst(env, d1, d2, &ctx)?;
                Ok((ty.apply_local(d1), level))
            }
            (
                Term::ElimNat { level: v1, motive: m1, base: z1, step: s1, scrut: n1 },
                Term::ElimNat { level: v2, motive: m2, base: z2, step: s2, scrut: n2 },
            ) => {
                self.lev_eq(v1, v2)?;
                let e_x = env.push_entry(Rc::new(Type::Nat), Level::Zero);
                self.ty(&e_x, m1, m2, v1)?;
                let base_ty =
                    m1.apply_local(&LocalSubst::id(&env.gamma).extended(Rc::new(Term::Zero)));
                self.tm(env, z1, z2, &base_ty, v1)?;
                // M[su x/x] scoped in (Γ, x : Nat, y : M), as in reduce.rs.
                let su_x = Term::Succ(Rc::new(Term::Var(LocalVar(1))));
                let step_ty = m1.apply_local(
                    &LocalSubst::id(&env.gamma).shift_local(2).extended(Rc::new(su_x)),
                );
                let e_xy = e_x.push_entry(Rc::clone(m1), v1.clone());
                self.tm(&e_xy, s1, s2, &step_ty, v1)?;
                self.tm_nee(env, n1, n2)?; // inferred Nat: redundant, ignored
                Ok((
                    m1.apply_local(&LocalSubst::id(&env.gamma).extended(Rc::clone(n1))),
                    v1.clone(),
                ))
            }
            (
                Term::App { fun: f1, dom_level: dl1, cod_level: cl1, dom: s1, cod: t1, arg: a1 },
                Term::App { fun: f2, dom_level: dl2, cod_level: cl2, dom: s2, cod: t2, arg: a2 },
            ) => {
                self.lev_eq(dl1, dl2)?;
                self.lev_eq(cl1, cl2)?;
                self.ty(env, s1, s2, dl1)?;
                let e_x = env.push_entry(Rc::clone(s1), dl1.clone());
                self.ty(&e_x, t1, t2, cl1)?;
                // The type inferred for the heads is ignored (ch. 06: the
                // annotations of well-typed applications are already forced).
                self.tm_nee(env, f1, f2)?;
                self.tm(env, a1, a2, s1, dl1)?;
                Ok((
                    t1.apply_local(&LocalSubst::id(&env.gamma).extended(Rc::clone(a1))),
                    cl1.clone(),
                ))
            }
            (
                Term::UApp { fun: f1, levels: ls1 },
                Term::UApp { fun: f2, levels: ls2 },
            ) => {
                let env = &env.with_layer(Layer::Meta);
                let (w, _) = self.tm_nee(env, f1, f2)?;
                let Type::UPi { num_vars, level, body } = &w else {
                    return Err(NC);
                };
                if ls1.len() != ls2.len() || ls1.len() != *num_vars as usize || ls1.is_empty()
                {
                    return Err(NC);
                }
                for (x, y) in ls1.iter().zip(ls2) {
                    self.lev_eq(x, y)?;
                }
                // Written vectors are outermost-first; instantiation wants
                // innermost-first (as in reduce.rs).
                let phi: Vec<Level> = ls1.iter().rev().cloned().collect();
                Ok((body.inst_univ(&phi), level.inst_at(&phi, 0)))
            }
            (
                Term::CtxApp { fun: f1, ctx: c1 },
                Term::CtxApp { fun: f2, ctx: c2 },
            ) => {
                let env = &env.with_layer(Layer::Meta);
                let (w, _) = self.tm_nee(env, f1, f2)?;
                let Type::CtxPi { level, body } = &w else {
                    return Err(NC);
                };
                self.ctx(env, Layer::Prog, c1, c2)?;
                Ok((
                    body.apply_global(&GlobalSubst::single(GlobalEntry::Ctx(c1.clone()))),
                    level.clone(),
                ))
            }
            (Term::TyApp { fun: f1, arg: t1 }, Term::TyApp { fun: f2, arg: t2 }) => {
                let env = &env.with_layer(Layer::Meta);
                let (w, _) = self.tm_nee(env, f1, f2)?;
                let Type::TyPi { ctx, arg_level, body_level, body } = &w else {
                    return Err(NC);
                };
                let e_d = env.in_ctx(ctx.clone(), Layer::Prog);
                self.ty(&e_d, t1, t2, arg_level)?;
                Ok((
                    body.apply_global(&GlobalSubst::single(GlobalEntry::Ty(Rc::clone(t1)))),
                    body_level.clone(),
                ))
            }
            (
                Term::LetBoxTy {
                    motive_level: ml1, code_level: cl1, ctx: d1, motive: m1, body: b1, scrut: n1,
                },
                Term::LetBoxTy {
                    motive_level: ml2, code_level: cl2, ctx: d2, motive: m2, body: b2, scrut: n2,
                },
            ) => {
                let env = &env.with_layer(Layer::Meta);
                self.lev_eq(ml1, ml2)?;
                self.lev_eq(cl1, cl2)?;
                self.ctx(env, Layer::Prog, d1, d2)?;
                self.tm_nee(env, n1, n2)?; // inferred □(Δ ⊢ Ty l): ignored
                let code_ty = Type::CodeTy { ctx: d1.clone(), level: cl1.clone() };
                let e_x = env.push_entry(Rc::new(code_ty), Level::Zero);
                self.ty(&e_x, m1, m2, ml1)?;
                // Bodies under Ψ, U : Typ_c(Δ, l) at M[box U/x_T].
                let e_u = env.push_global(GlobalBinding::Ty {
                    ctx: d1.clone(),
                    layer: Layer::Code,
                    level: cl1.clone(),
                });
                let box_u = Term::BoxTy(Rc::new(gty(0, &d1.shift_global(1))));
                let body_ty = m1
                    .shift_global(1)
                    .apply_local(&LocalSubst::id(&e_u.gamma).extended(Rc::new(box_u)));
                self.tm(&e_u, b1, b2, &body_ty, ml1)?;
                Ok((
                    m1.apply_local(&LocalSubst::id(&env.gamma).extended(Rc::clone(n1))),
                    ml1.clone(),
                ))
            }
            (
                Term::LetBoxTm {
                    motive_level: ml1, code_level: cl1, ctx: d1, ty: t1, motive: m1,
                    body: b1, scrut: n1,
                },
                Term::LetBoxTm {
                    motive_level: ml2, code_level: cl2, ctx: d2, ty: t2, motive: m2,
                    body: b2, scrut: n2,
                },
            ) => {
                let env = &env.with_layer(Layer::Meta);
                self.lev_eq(ml1, ml2)?;
                self.lev_eq(cl1, cl2)?;
                self.ctx(env, Layer::Prog, d1, d2)?;
                let e_d = env.in_ctx(d1.clone(), Layer::Prog);
                self.ty(&e_d, t1, t2, cl1)?;
                self.tm_nee(env, n1, n2)?; // inferred □(Δ ⊢ T @ l): ignored
                let code_ty = Type::CodeTm {
                    ctx: d1.clone(),
                    ty: Rc::clone(t1),
                    level: cl1.clone(),
                };
                let e_x = env.push_entry(Rc::new(code_ty), Level::Zero);
                self.ty(&e_x, m1, m2, ml1)?;
                // Bodies under Ψ, u : Trm_c(Δ ⊢ T @ l) at M[box u/x_t].
                let e_u = env.push_global(GlobalBinding::Tm {
                    ctx: d1.clone(),
                    layer: Layer::Code,
                    ty: Rc::clone(t1),
                    level: cl1.clone(),
                });
                let box_u = Term::BoxTm(Rc::new(gtm(0, &d1.shift_global(1))));
                let body_ty = m1
                    .shift_global(1)
                    .apply_local(&LocalSubst::id(&e_u.gamma).extended(Rc::new(box_u)));
                self.tm(&e_u, b1, b2, &body_ty, ml1)?;
                Ok((
                    m1.apply_local(&LocalSubst::id(&env.gamma).extended(Rc::clone(n1))),
                    ml1.clone(),
                ))
            }
            (
                Term::ElimCodeTy {
                    ty_motive_level: al1, tm_motive_level: al2, motives: am, branches: ab,
                    code_level: acl, ctx: actx, scrut: an,
                },
                Term::ElimCodeTy {
                    ty_motive_level: bl1, tm_motive_level: bl2, motives: bm, branches: bb,
                    code_level: bcl, ctx: bctx, scrut: bn,
                },
            ) => {
                let env = &env.with_layer(Layer::Meta);
                self.rec_ca(
                    env,
                    &RecSide { l1: al1, l2: al2, motives: am, branches: ab },
                    &RecSide { l1: bl1, l2: bl2, motives: bm, branches: bb },
                )?;
                self.lev_eq(acl, bcl)?;
                self.ctx(env, Layer::Prog, actx, bctx)?;
                // Blocked on box (U^δ): compared syntactically. Otherwise the
                // scrutinees are neutral.
                match (&**an, &**bn) {
                    (Term::BoxTy(c1), Term::BoxTy(c2)) => {
                        match (&**c1, &**c2) {
                            (Type::GlobalTy { .. }, Type::GlobalTy { .. }) if c1 == c2 => {}
                            _ => return Err(NC),
                        }
                    }
                    (Term::BoxTy(_), _) | (_, Term::BoxTy(_)) => return Err(NC),
                    _ => {
                        self.tm_nee(env, an, bn)?; // inferred □(Δ ⊢ Ty l): ignored
                    }
                }
                Ok((
                    inst_ty_motive(
                        &am.ty_motive,
                        (0, 0, 0),
                        acl.clone(),
                        actx.clone(),
                        (**an).clone(),
                        &env.gamma,
                    ),
                    al1.clone(),
                ))
            }
            (
                Term::ElimCodeTm {
                    ty_motive_level: al1, tm_motive_level: al2, motives: am, branches: ab,
                    code_level: acl, ctx: actx, ty: aty, scrut: an,
                },
                Term::ElimCodeTm {
                    ty_motive_level: bl1, tm_motive_level: bl2, motives: bm, branches: bb,
                    code_level: bcl, ctx: bctx, ty: bty, scrut: bn,
                },
            ) => {
                let env = &env.with_layer(Layer::Meta);
                self.rec_ca(
                    env,
                    &RecSide { l1: al1, l2: al2, motives: am, branches: ab },
                    &RecSide { l1: bl1, l2: bl2, motives: bm, branches: bb },
                )?;
                self.lev_eq(acl, bcl)?;
                self.ctx(env, Layer::Prog, actx, bctx)?;
                let e_d = env.in_ctx(actx.clone(), Layer::Prog);
                self.ty(&e_d, aty, bty, &Level::succ(acl.clone()))?;
                match (&**an, &**bn) {
                    (Term::BoxTm(c1), Term::BoxTm(c2)) => {
                        match (&**c1, &**c2) {
                            (Term::GlobalTm { .. }, Term::GlobalTm { .. }) if c1 == c2 => {}
                            _ => return Err(NC),
                        }
                    }
                    (Term::BoxTm(_), _) | (_, Term::BoxTm(_)) => return Err(NC),
                    _ => {
                        self.tm_nee(env, an, bn)?; // inferred □(Δ ⊢ T @ l): ignored
                    }
                }
                // Conclusion at l₂ (the ch. 04 typing rule; the ch. 06 rule
                // writes l₁, a typo).
                Ok((
                    inst_tm_motive(
                        &am.tm_motive,
                        (0, 0, 0),
                        acl.clone(),
                        actx.clone(),
                        (**aty).clone(),
                        (**an).clone(),
                        &env.gamma,
                    ),
                    al2.clone(),
                ))
            }
            _ => Err(NC),
        }
    }

    // -- the C_A bundle for neutral recursors -------------------------------

    /// Ch. 06 `C_A`: motive levels, both motives, and all 13 branches, each
    /// branch compared at its instantiated motive type under its ch. 04
    /// telescope (`G_M G_Typ G_Trm`). Branch types and telescope entry
    /// types are built from the *left* side (left-biased, like all
    /// inference here). The telescope tables must match `Branches`'s docs,
    /// subst.rs's `map_branches`, and reduce.rs's β-instantiations.
    fn rec_ca(&mut self, env: &Env, a: &RecSide, b: &RecSide) -> R {
        let (l1, l2) = (a.l1, a.l2);
        let (m_ty, m_tm) = (&*a.motives.ty_motive, &*a.motives.tm_motive);
        self.lev_eq(l1, b.l1)?;
        self.lev_eq(l2, b.l2)?;

        // G_M: Ψ, g; Γ, x_T : □(g ⊢ Ty ℓ) @ 0; L, ℓ ⊢ M_Typ ≈ M_Typ' : l₁
        {
            let e = env
                .push_tele(1, vec![GlobalBinding::Ctx])
                .push_entry(
                    Rc::new(Type::CodeTy { ctx: g_ctx(0), level: lvar(0) }),
                    Level::Zero,
                );
            self.ty(&e, m_ty, &b.motives.ty_motive, &l1.shift(1, 0))?;
        }
        // G_M: Ψ, g, U_T : Typ_p(g, ℓ); Γ, x_t : □(g ⊢ U_T^id @ ℓ) @ 0; L, ℓ
        //      ⊢ M_Trm ≈ M_Trm' : l₂
        {
            let e = env
                .push_tele(
                    1,
                    vec![
                        GlobalBinding::Ctx,
                        GlobalBinding::Ty {
                            ctx: g_ctx(0),
                            layer: Layer::Prog,
                            level: lvar(0),
                        },
                    ],
                )
                .push_entry(
                    Rc::new(Type::CodeTm {
                        ctx: g_ctx(1),
                        ty: Rc::new(gty(0, &g_ctx(1))),
                        level: lvar(0),
                    }),
                    Level::Zero,
                );
            self.ty(&e, m_tm, &b.motives.tm_motive, &l2.shift(1, 0))?;
        }

        // G_Typ ------------------------------------------------------------
        // (g. t_Nat) : M_Typ[0/ℓ, g/g, box Nat/x_T]
        {
            let e = env.push_tele(0, vec![GlobalBinding::Ctx]);
            let bty = inst_ty_motive(
                m_ty,
                (0, 1, 0),
                Level::Zero,
                g_ctx(0),
                Term::BoxTy(Rc::new(Type::Nat)),
                &e.gamma,
            );
            self.tm(&e, &a.branches.ty_nat, &b.branches.ty_nat, &bty, l1)?;
        }
        // (ℓ, ℓ', g, U_S : Typ_c(g, ℓ), U_T : Typ_c((g, x : U_S^id @ ℓ), ℓ'),
        //  x_S, x_T. t_Π) : M_Typ[ℓ⊔ℓ'/ℓ, g/g, box (Π x:U_S^id. U_T^id)/x_T]
        {
            let mut e = env.push_tele(
                2,
                vec![
                    GlobalBinding::Ctx,
                    GlobalBinding::Ty { ctx: g_ctx(0), layer: Layer::Code, level: lvar(1) },
                    GlobalBinding::Ty {
                        ctx: ext_ctx(&g_ctx(1), gty(0, &g_ctx(1)), lvar(1)),
                        layer: Layer::Code,
                        level: lvar(0),
                    },
                ],
            );
            let gt = e.gamma.clone();
            // telescope view: g = 2, U_S = 1, U_T = 0
            let gx = ext_ctx(&g_ctx(2), gty(1, &g_ctx(2)), lvar(1));
            let x_s = inst_ty_motive(
                m_ty,
                (2, 3, 0),
                lvar(1),
                g_ctx(2),
                Term::BoxTy(Rc::new(gty(1, &g_ctx(2)))),
                &gt,
            );
            e = e.push_entry(Rc::new(x_s), l1.shift(2, 0));
            let x_t = inst_ty_motive(
                m_ty,
                (2, 3, 1),
                lvar(0),
                gx.clone(),
                Term::BoxTy(Rc::new(gty(0, &gx))),
                &gt,
            );
            e = e.push_entry(Rc::new(x_t), l1.shift(2, 0));
            let code = Type::Pi {
                dom_level: lvar(1),
                cod_level: lvar(0),
                dom: Rc::new(gty(1, &g_ctx(2))),
                cod: Rc::new(gty(0, &gx)),
            };
            let bty = inst_ty_motive(
                m_ty,
                (2, 3, 2),
                Level::max(lvar(1), lvar(0)),
                g_ctx(2),
                Term::BoxTy(Rc::new(code)),
                &gt,
            );
            self.tm(&e, &a.branches.ty_pi, &b.branches.ty_pi, &bty, &l1.shift(2, 0))?;
        }
        // (ℓ, g. t_Ty) : M_Typ[1+ℓ/ℓ, g/g, box (Ty ℓ)/x_T]
        {
            let e = env.push_tele(1, vec![GlobalBinding::Ctx]);
            let bty = inst_ty_motive(
                m_ty,
                (1, 1, 0),
                Level::succ(lvar(0)),
                g_ctx(0),
                Term::BoxTy(Rc::new(Type::Ty(lvar(0)))),
                &e.gamma,
            );
            self.tm(&e, &a.branches.ty_ty, &b.branches.ty_ty, &bty, &l1.shift(1, 0))?;
        }
        // (ℓ, g, u_t : Trm_c(g ⊢ Ty ℓ @ 1+ℓ), x_t. t_El)
        //   : M_Typ[ℓ/ℓ, g/g, box (El ℓ u_t^id)/x_T]; x_t at the *term* motive
        {
            let mut e = env.push_tele(
                1,
                vec![
                    GlobalBinding::Ctx,
                    GlobalBinding::Tm {
                        ctx: g_ctx(0),
                        layer: Layer::Code,
                        ty: Rc::new(Type::Ty(lvar(0))),
                        level: Level::succ(lvar(0)),
                    },
                ],
            );
            let gt = e.gamma.clone();
            let x_t = inst_tm_motive(
                m_tm,
                (1, 2, 0),
                Level::succ(lvar(0)),
                g_ctx(1),
                Type::Ty(lvar(0)),
                Term::BoxTm(Rc::new(gtm(0, &g_ctx(1)))),
                &gt,
            );
            e = e.push_entry(Rc::new(x_t), l2.shift(1, 0));
            let code = Type::El { level: lvar(0), tm: Rc::new(gtm(0, &g_ctx(1))) };
            let bty = inst_ty_motive(
                m_ty,
                (1, 2, 1),
                lvar(0),
                g_ctx(1),
                Term::BoxTy(Rc::new(code)),
                &gt,
            );
            self.tm(&e, &a.branches.ty_el, &b.branches.ty_el, &bty, &l1.shift(1, 0))?;
        }

        // G_Trm ------------------------------------------------------------
        // (ℓ, g, U_T : Typ_p(g, ℓ), u_x : Trm_v(g ⊢ U_T^id @ ℓ). t_x)
        //   : M_Trm[ℓ/ℓ, g/g, U_T^id/U_T, box u_x^id/x_t]
        {
            let e = env.push_tele(
                1,
                vec![
                    GlobalBinding::Ctx,
                    GlobalBinding::Ty { ctx: g_ctx(0), layer: Layer::Prog, level: lvar(0) },
                    GlobalBinding::Tm {
                        ctx: g_ctx(1),
                        layer: Layer::Var,
                        ty: Rc::new(gty(0, &g_ctx(1))),
                        level: lvar(0),
                    },
                ],
            );
            let bty = inst_tm_motive(
                m_tm,
                (1, 3, 0),
                lvar(0),
                g_ctx(2),
                gty(1, &g_ctx(2)),
                Term::BoxTm(Rc::new(gtm(0, &g_ctx(2)))),
                &e.gamma,
            );
            self.tm(&e, &a.branches.tm_var, &b.branches.tm_var, &bty, &l2.shift(1, 0))?;
        }
        // (g. t'_Nat) : M_Trm[1/ℓ, g/g, Ty 0/U_T, box Nat/x_t]
        {
            let e = env.push_tele(0, vec![GlobalBinding::Ctx]);
            let bty = inst_tm_motive(
                m_tm,
                (0, 1, 0),
                Level::constant(1),
                g_ctx(0),
                Type::Ty(Level::Zero),
                Term::BoxTm(Rc::new(Term::TmNat)),
                &e.gamma,
            );
            self.tm(&e, &a.branches.tm_nat, &b.branches.tm_nat, &bty, l2)?;
        }
        // (ℓ, ℓ', g, u_s : Trm_c(g ⊢ Ty ℓ @ 1+ℓ),
        //  u_t : Trm_c((g, x : El ℓ u_s^id @ ℓ) ⊢ Ty ℓ' @ 1+ℓ'), x_s, x_t. t'_Π)
        //   : M_Trm[1+(ℓ⊔ℓ')/ℓ, g/g, Ty (ℓ⊔ℓ')/U_T, box (Π x:u_s^id. u_t^id)/x_t]
        {
            let mut e = env.push_tele(
                2,
                vec![
                    GlobalBinding::Ctx,
                    GlobalBinding::Tm {
                        ctx: g_ctx(0),
                        layer: Layer::Code,
                        ty: Rc::new(Type::Ty(lvar(1))),
                        level: Level::succ(lvar(1)),
                    },
                    GlobalBinding::Tm {
                        ctx: ext_ctx(
                            &g_ctx(1),
                            Type::El { level: lvar(1), tm: Rc::new(gtm(0, &g_ctx(1))) },
                            lvar(1),
                        ),
                        layer: Layer::Code,
                        ty: Rc::new(Type::Ty(lvar(0))),
                        level: Level::succ(lvar(0)),
                    },
                ],
            );
            let gt = e.gamma.clone();
            // telescope view: g = 2, u_s = 1, u_t = 0
            let gx = ext_ctx(
                &g_ctx(2),
                Type::El { level: lvar(1), tm: Rc::new(gtm(1, &g_ctx(2))) },
                lvar(1),
            );
            let x_s = inst_tm_motive(
                m_tm,
                (2, 3, 0),
                Level::succ(lvar(1)),
                g_ctx(2),
                Type::Ty(lvar(1)),
                Term::BoxTm(Rc::new(gtm(1, &g_ctx(2)))),
                &gt,
            );
            e = e.push_entry(Rc::new(x_s), l2.shift(2, 0));
            let x_t = inst_tm_motive(
                m_tm,
                (2, 3, 1),
                Level::succ(lvar(0)),
                gx.clone(),
                Type::Ty(lvar(0)),
                Term::BoxTm(Rc::new(gtm(0, &gx))),
                &gt,
            );
            e = e.push_entry(Rc::new(x_t), l2.shift(2, 0));
            let lmax = Level::max(lvar(1), lvar(0));
            let code = Term::TmPi {
                dom_level: lvar(1),
                cod_level: lvar(0),
                dom: Rc::new(gtm(1, &g_ctx(2))),
                cod: Rc::new(gtm(0, &gx)),
            };
            let bty = inst_tm_motive(
                m_tm,
                (2, 3, 2),
                Level::succ(lmax.clone()),
                g_ctx(2),
                Type::Ty(lmax),
                Term::BoxTm(Rc::new(code)),
                &gt,
            );
            self.tm(&e, &a.branches.tm_pi, &b.branches.tm_pi, &bty, &l2.shift(2, 0))?;
        }
        // (ℓ, g. t'_Ty) : M_Trm[2+ℓ/ℓ, g/g, Ty (1+ℓ)/U_T, box (Ty ℓ)/x_t]
        {
            let e = env.push_tele(1, vec![GlobalBinding::Ctx]);
            let bty = inst_tm_motive(
                m_tm,
                (1, 1, 0),
                Level::succ(Level::succ(lvar(0))),
                g_ctx(0),
                Type::Ty(Level::succ(lvar(0))),
                Term::BoxTm(Rc::new(Term::TmTy(lvar(0)))),
                &e.gamma,
            );
            self.tm(&e, &a.branches.tm_ty, &b.branches.tm_ty, &bty, &l2.shift(1, 0))?;
        }
        // (g. t_ze) : M_Trm[0/ℓ, g/g, Nat/U_T, box ze/x_t]
        {
            let e = env.push_tele(0, vec![GlobalBinding::Ctx]);
            let bty = inst_tm_motive(
                m_tm,
                (0, 1, 0),
                Level::Zero,
                g_ctx(0),
                Type::Nat,
                Term::BoxTm(Rc::new(Term::Zero)),
                &e.gamma,
            );
            self.tm(&e, &a.branches.tm_zero, &b.branches.tm_zero, &bty, l2)?;
        }
        // (g, u_t : Trm_c(g ⊢ Nat @ 0), x_t. t_succ)
        //   : M_Trm[0/ℓ, g/g, Nat/U_T, box (su u_t^id)/x_t]
        {
            let mut e = env.push_tele(
                0,
                vec![
                    GlobalBinding::Ctx,
                    GlobalBinding::Tm {
                        ctx: g_ctx(0),
                        layer: Layer::Code,
                        ty: Rc::new(Type::Nat),
                        level: Level::Zero,
                    },
                ],
            );
            let gt = e.gamma.clone();
            let x_t = inst_tm_motive(
                m_tm,
                (0, 2, 0),
                Level::Zero,
                g_ctx(1),
                Type::Nat,
                Term::BoxTm(Rc::new(gtm(0, &g_ctx(1)))),
                &gt,
            );
            e = e.push_entry(Rc::new(x_t), l2.clone());
            let code = Term::Succ(Rc::new(gtm(0, &g_ctx(1))));
            let bty = inst_tm_motive(
                m_tm,
                (0, 2, 1),
                Level::Zero,
                g_ctx(1),
                Type::Nat,
                Term::BoxTm(Rc::new(code)),
                &gt,
            );
            self.tm(&e, &a.branches.tm_succ, &b.branches.tm_succ, &bty, l2)?;
        }
        // (ℓ, g, U_M : Typ_c((g, x : Nat @ 0), ℓ),
        //  u_s : Trm_c(g ⊢ U_M^{id,ze/x} @ ℓ),
        //  u_s' : Trm_c((g, x : Nat, y : U_M^id @ ℓ) ⊢ U_M^{id,su x/x} @ ℓ),
        //  u_t : Trm_c(g ⊢ Nat @ 0), x_M, x_s, x_s', x_t. t_elimN)
        //   : M_Trm[ℓ/ℓ, g/g, U_M^{id,u_t^id/x}/U_T, box (elim_Nat …)/x_t]
        {
            let mut e = env.push_tele(
                1,
                vec![
                    GlobalBinding::Ctx,
                    GlobalBinding::Ty {
                        ctx: ext_ctx(&g_ctx(0), Type::Nat, Level::Zero),
                        layer: Layer::Code,
                        level: lvar(0),
                    },
                    GlobalBinding::Tm {
                        ctx: g_ctx(1),
                        layer: Layer::Code,
                        ty: Rc::new(Type::GlobalTy {
                            var: GlobalVar(0),
                            subst: LocalSubst::id(&g_ctx(1)).extended(Rc::new(Term::Zero)),
                        }),
                        level: lvar(0),
                    },
                    GlobalBinding::Tm {
                        ctx: {
                            let gx = ext_ctx(&g_ctx(2), Type::Nat, Level::Zero);
                            let y_ty = Type::GlobalTy {
                                var: GlobalVar(1),
                                subst: LocalSubst::id(&gx),
                            };
                            ext_ctx(&gx, y_ty, lvar(0))
                        },
                        layer: Layer::Code,
                        ty: Rc::new(Type::GlobalTy {
                            var: GlobalVar(1),
                            subst: LocalSubst::id(&g_ctx(2))
                                .shift_local(2)
                                .extended(Rc::new(Term::Succ(Rc::new(Term::Var(
                                    LocalVar(1),
                                ))))),
                        }),
                        level: lvar(0),
                    },
                    GlobalBinding::Tm {
                        ctx: g_ctx(3),
                        layer: Layer::Code,
                        ty: Rc::new(Type::Nat),
                        level: Level::Zero,
                    },
                ],
            );
            let gt = e.gamma.clone();
            // telescope view: g = 4, U_M = 3, u_s = 2, u_s' = 1, u_t = 0
            let gx = ext_ctx(&g_ctx(4), Type::Nat, Level::Zero);
            let id_gx = LocalSubst::id(&gx);
            let motive_code =
                Type::GlobalTy { var: GlobalVar(3), subst: id_gx.clone() };
            let gxy = ext_ctx(&gx, motive_code.clone(), lvar(0));
            let x_m = inst_ty_motive(
                m_ty,
                (1, 5, 0),
                lvar(0),
                gx.clone(),
                Term::BoxTy(Rc::new(motive_code.clone())),
                &gt,
            );
            e = e.push_entry(Rc::new(x_m), l1.shift(1, 0));
            let u_m_at_zero = Type::GlobalTy {
                var: GlobalVar(3),
                subst: LocalSubst::id(&g_ctx(4)).extended(Rc::new(Term::Zero)),
            };
            let x_s = inst_tm_motive(
                m_tm,
                (1, 5, 1),
                lvar(0),
                g_ctx(4),
                u_m_at_zero,
                Term::BoxTm(Rc::new(gtm(2, &g_ctx(4)))),
                &gt,
            );
            e = e.push_entry(Rc::new(x_s), l2.shift(1, 0));
            let u_m_at_succ = Type::GlobalTy {
                var: GlobalVar(3),
                subst: LocalSubst::id(&g_ctx(4))
                    .shift_local(2)
                    .extended(Rc::new(Term::Succ(Rc::new(Term::Var(LocalVar(1)))))),
            };
            let x_s2 = inst_tm_motive(
                m_tm,
                (1, 5, 2),
                lvar(0),
                gxy.clone(),
                u_m_at_succ,
                Term::BoxTm(Rc::new(gtm(1, &gxy))),
                &gt,
            );
            e = e.push_entry(Rc::new(x_s2), l2.shift(1, 0));
            let x_t = inst_tm_motive(
                m_tm,
                (1, 5, 3),
                lvar(0),
                g_ctx(4),
                Type::Nat,
                Term::BoxTm(Rc::new(gtm(0, &g_ctx(4)))),
                &gt,
            );
            e = e.push_entry(Rc::new(x_t), l2.shift(1, 0));
            let code = Term::ElimNat {
                level: lvar(0),
                motive: Rc::new(motive_code),
                base: Rc::new(gtm(2, &g_ctx(4))),
                step: Rc::new(gtm(1, &gxy)),
                scrut: Rc::new(gtm(0, &g_ctx(4))),
            };
            let u_m_at_scrut = Type::GlobalTy {
                var: GlobalVar(3),
                subst: LocalSubst::id(&g_ctx(4)).extended(Rc::new(gtm(0, &g_ctx(4)))),
            };
            let bty = inst_tm_motive(
                m_tm,
                (1, 5, 4),
                lvar(0),
                g_ctx(4),
                u_m_at_scrut,
                Term::BoxTm(Rc::new(code)),
                &gt,
            );
            self.tm(
                &e,
                &a.branches.tm_elim_nat,
                &b.branches.tm_elim_nat,
                &bty,
                &l2.shift(1, 0),
            )?;
        }
        // (ℓ, ℓ', g, U_S : Typ_c(g, ℓ), U_T : Typ_p((g, x : U_S^id @ ℓ), ℓ'),
        //  u_t : Trm_c((g, x : U_S^id @ ℓ) ⊢ U_T^id @ ℓ'), x_S, x_t. t_λ)
        //   : M_Trm[ℓ⊔ℓ'/ℓ, g/g, (Π x:U_S^id. U_T^id)/U_T, box (λ x:U_S^id. u_t^id)/x_t]
        // U_T is layer p (not a sub-structure of λ) — no recursive call.
        {
            let mut e = env.push_tele(
                2,
                vec![
                    GlobalBinding::Ctx,
                    GlobalBinding::Ty { ctx: g_ctx(0), layer: Layer::Code, level: lvar(1) },
                    GlobalBinding::Ty {
                        ctx: ext_ctx(&g_ctx(1), gty(0, &g_ctx(1)), lvar(1)),
                        layer: Layer::Prog,
                        level: lvar(0),
                    },
                    GlobalBinding::Tm {
                        ctx: ext_ctx(&g_ctx(2), gty(1, &g_ctx(2)), lvar(1)),
                        layer: Layer::Code,
                        ty: Rc::new(gty(
                            0,
                            &ext_ctx(&g_ctx(2), gty(1, &g_ctx(2)), lvar(1)),
                        )),
                        level: lvar(0),
                    },
                ],
            );
            let gt = e.gamma.clone();
            // telescope view: g = 3, U_S = 2, U_T = 1, u_t = 0
            let gx = ext_ctx(&g_ctx(3), gty(2, &g_ctx(3)), lvar(1));
            let x_s = inst_ty_motive(
                m_ty,
                (2, 4, 0),
                lvar(1),
                g_ctx(3),
                Term::BoxTy(Rc::new(gty(2, &g_ctx(3)))),
                &gt,
            );
            e = e.push_entry(Rc::new(x_s), l1.shift(2, 0));
            let x_t = inst_tm_motive(
                m_tm,
                (2, 4, 1),
                lvar(0),
                gx.clone(),
                gty(1, &gx),
                Term::BoxTm(Rc::new(gtm(0, &gx))),
                &gt,
            );
            e = e.push_entry(Rc::new(x_t), l2.shift(2, 0));
            let pi = Type::Pi {
                dom_level: lvar(1),
                cod_level: lvar(0),
                dom: Rc::new(gty(2, &g_ctx(3))),
                cod: Rc::new(gty(1, &gx)),
            };
            let code = Term::Lam {
                dom_level: lvar(1),
                cod_level: lvar(0),
                dom: Rc::new(gty(2, &g_ctx(3))),
                body: Rc::new(gtm(0, &gx)),
            };
            let bty = inst_tm_motive(
                m_tm,
                (2, 4, 2),
                Level::max(lvar(1), lvar(0)),
                g_ctx(3),
                pi,
                Term::BoxTm(Rc::new(code)),
                &gt,
            );
            self.tm(&e, &a.branches.tm_lam, &b.branches.tm_lam, &bty, &l2.shift(2, 0))?;
        }
        // (ℓ, ℓ', g, U_S : Typ_c(g, ℓ), U_T : Typ_c((g, x : U_S^id @ ℓ), ℓ'),
        //  u_t : Trm_c(g ⊢ Π x:U_S^id. U_T^id @ ℓ⊔ℓ'), u_s : Trm_c(g ⊢ U_S^id @ ℓ),
        //  x_S, x_T, x_t, x_s. t_app)
        //   : M_Trm[ℓ'/ℓ, g/g, U_T^{id,u_s^id/x}/U_T, box (app(u_t^id; …; u_s^id))/x_t]
        // (the tex substitutes u_t^id for x here — a typo for u_s^id).
        {
            let u_t_pi = Type::Pi {
                dom_level: lvar(1),
                cod_level: lvar(0),
                dom: Rc::new(gty(1, &g_ctx(2))),
                cod: Rc::new(gty(0, &ext_ctx(&g_ctx(2), gty(1, &g_ctx(2)), lvar(1)))),
            };
            let mut e = env.push_tele(
                2,
                vec![
                    GlobalBinding::Ctx,
                    GlobalBinding::Ty { ctx: g_ctx(0), layer: Layer::Code, level: lvar(1) },
                    GlobalBinding::Ty {
                        ctx: ext_ctx(&g_ctx(1), gty(0, &g_ctx(1)), lvar(1)),
                        layer: Layer::Code,
                        level: lvar(0),
                    },
                    GlobalBinding::Tm {
                        ctx: g_ctx(2),
                        layer: Layer::Code,
                        ty: Rc::new(u_t_pi),
                        level: Level::max(lvar(1), lvar(0)),
                    },
                    GlobalBinding::Tm {
                        ctx: g_ctx(3),
                        layer: Layer::Code,
                        ty: Rc::new(gty(2, &g_ctx(3))),
                        level: lvar(1),
                    },
                ],
            );
            let gt = e.gamma.clone();
            // telescope view: g = 4, U_S = 3, U_T = 2, u_t = 1, u_s = 0
            let gx = ext_ctx(&g_ctx(4), gty(3, &g_ctx(4)), lvar(1));
            let x_s = inst_ty_motive(
                m_ty,
                (2, 5, 0),
                lvar(1),
                g_ctx(4),
                Term::BoxTy(Rc::new(gty(3, &g_ctx(4)))),
                &gt,
            );
            e = e.push_entry(Rc::new(x_s), l1.shift(2, 0));
            let x_t_ty = inst_ty_motive(
                m_ty,
                (2, 5, 1),
                lvar(0),
                gx.clone(),
                Term::BoxTy(Rc::new(gty(2, &gx))),
                &gt,
            );
            e = e.push_entry(Rc::new(x_t_ty), l1.shift(2, 0));
            let pi = Type::Pi {
                dom_level: lvar(1),
                cod_level: lvar(0),
                dom: Rc::new(gty(3, &g_ctx(4))),
                cod: Rc::new(gty(2, &gx)),
            };
            let x_t = inst_tm_motive(
                m_tm,
                (2, 5, 2),
                Level::max(lvar(1), lvar(0)),
                g_ctx(4),
                pi.clone(),
                Term::BoxTm(Rc::new(gtm(1, &g_ctx(4)))),
                &gt,
            );
            e = e.push_entry(Rc::new(x_t), l2.shift(2, 0));
            let x_s_tm = inst_tm_motive(
                m_tm,
                (2, 5, 3),
                lvar(1),
                g_ctx(4),
                gty(3, &g_ctx(4)),
                Term::BoxTm(Rc::new(gtm(0, &g_ctx(4)))),
                &gt,
            );
            e = e.push_entry(Rc::new(x_s_tm), l2.shift(2, 0));
            let code = Term::App {
                fun: Rc::new(gtm(1, &g_ctx(4))),
                dom_level: lvar(1),
                cod_level: lvar(0),
                dom: Rc::new(gty(3, &g_ctx(4))),
                cod: Rc::new(gty(2, &gx)),
                arg: Rc::new(gtm(0, &g_ctx(4))),
            };
            let u_t_at_arg = Type::GlobalTy {
                var: GlobalVar(2),
                subst: LocalSubst::id(&g_ctx(4)).extended(Rc::new(gtm(0, &g_ctx(4)))),
            };
            let bty = inst_tm_motive(
                m_tm,
                (2, 5, 4),
                lvar(0),
                g_ctx(4),
                u_t_at_arg,
                Term::BoxTm(Rc::new(code)),
                &gt,
            );
            self.tm(&e, &a.branches.tm_app, &b.branches.tm_app, &bty, &l2.shift(2, 0))?;
        }

        Ok(())
    }
}
