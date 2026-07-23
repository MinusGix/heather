//! Type-directed generator of **well-typed** terms, for the conversion
//! property tests (issues/kernel-conv-properties.md). Where `mod.rs`
//! generates well-scoped-only terms, this module synthesizes
//! `(term, type, level)` triples bottom-up along the ch. 04 typing rules,
//! so every output is expected to pass `check_term` — a property the tests
//! assert, making the checker the oracle for the generator.
//!
//! Design notes:
//!
//! - **Synthesis-first** ([`gen_wt_term`]): each arm mirrors an inference
//!   rule and returns the rule's canonical type/level. Checked-mode holes
//!   (application arguments, substitution steps, box bodies) go through
//!   [`gen_wt_term_at`], which does intro-directed descent on the WHNF of
//!   the target and falls back to searching Γ with `check_term` as filter.
//! - **No `ω`-level leaks**: `ULam` is the only synthesis arm whose result
//!   level is `ω`; every position that demands `⊢ l : Level` guards with
//!   [`Level::well_formed`] and degrades the sub-result to `0 : Nat @ 0`.
//! - **Recursors** use *constant* motives: for a constant motive `M` (the
//!   weakened type of a synthesized inhabitant `m`), every instantiated
//!   branch type collapses to `M` weakened by the branch telescope's
//!   `(univs, globals, locals)` — so `m` weakened the same way inhabits it,
//!   and (where the innermost recursive-call entry has the same motive)
//!   so does `Var(0)`. The depth table below is deliberately a *fourth*
//!   independent transcription of the ch. 04 telescopes: if it disagrees
//!   with `src/rec.rs`, these tests fail.
//! - [`identity_motives`]/[`identity_branches`] duplicate the identity
//!   recursor of `tests/typing.rs` (test binaries cannot share code except
//!   through `common/`): each branch re-boxes exactly the code its
//!   telescope describes, so one β-step is the identity on code — the
//!   sharpest cheap cross-check of `reduce.rs`'s `fire` against the tables.

use std::rc::Rc;

use heather_kernel::layer::Layer;
use heather_kernel::level::{Level, UnivVar};
use heather_kernel::reduce::whnf_type;
use heather_kernel::term::{
    Branches, CtxBase, CtxEntry, GlobalBinding, GlobalCtx, GlobalVar, LocalCtx, LocalSubst,
    LocalVar, Motives, SubstTail, Term, Type,
};
use heather_kernel::typing::check_term;

use super::Rng;

/// Generous fuel for the checker/reducer calls the generator and the
/// property tests make (well-typed inputs terminate; exhaustion = bug).
pub const FUEL: u64 = 1 << 20;

// -------------------------------------------------------------------------
// Small constructors (as in tests/typing.rs)
// -------------------------------------------------------------------------

fn rt(t: Term) -> Rc<Term> {
    Rc::new(t)
}

fn rty(t: Type) -> Rc<Type> {
    Rc::new(t)
}

fn lv(i: u32) -> Level {
    Level::Var(UnivVar(i))
}

fn v(i: u32) -> Term {
    Term::Var(LocalVar(i))
}

fn nil_ctx() -> LocalCtx {
    LocalCtx { base: CtxBase::Nil, entries: vec![] }
}

fn g_ctx(i: u32) -> LocalCtx {
    LocalCtx { base: CtxBase::Var(GlobalVar(i)), entries: vec![] }
}

fn ext(base: &LocalCtx, ty: Type, level: Level) -> LocalCtx {
    let mut c = base.clone();
    c.entries.push(CtxEntry { ty: rty(ty), level });
    c
}

fn gty(var: u32, ctx: &LocalCtx) -> Type {
    Type::GlobalTy { var: GlobalVar(var), subst: LocalSubst::id(ctx) }
}

fn gtm(var: u32, ctx: &LocalCtx) -> Term {
    Term::GlobalTm { var: GlobalVar(var), subst: LocalSubst::id(ctx) }
}

// -------------------------------------------------------------------------
// Environment
// -------------------------------------------------------------------------

/// The ambient scope of a synthesis: Ψ, |L|, the layer, and Γ (mirrors
/// `typing::Env`, which is private).
#[derive(Clone)]
pub struct WtEnv {
    pub psi: GlobalCtx,
    pub univs: u32,
    pub layer: Layer,
    pub gamma: LocalCtx,
}

/// `shift_univ_psi` replica (the kernel's is crate-private): weaken every
/// binding of Ψ by `by` universe variables.
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

impl WtEnv {
    pub fn in_ctx(&self, gamma: LocalCtx, layer: Layer) -> WtEnv {
        WtEnv { gamma, layer, ..self.clone() }
    }

    fn push_entry(&self, ty: Rc<Type>, level: Level) -> WtEnv {
        let mut e = self.clone();
        e.gamma.entries.push(CtxEntry { ty, level });
        e
    }

    fn push_univs(&self, n: u32) -> WtEnv {
        WtEnv {
            psi: shift_univ_psi(&self.psi, n),
            univs: self.univs + n,
            layer: self.layer,
            gamma: self.gamma.shift_univ(n),
        }
    }

    fn push_global(&self, b: GlobalBinding) -> WtEnv {
        let mut psi = self.psi.clone();
        psi.bindings.push(b);
        WtEnv { psi, univs: self.univs, layer: self.layer, gamma: self.gamma.shift_global(1) }
    }

    /// Does this term check here? (The kernel checker as generator filter.)
    fn checks(&self, t: &Term, ty: &Type, l: &Level) -> bool {
        check_term(&self.psi, self.univs, self.layer, &self.gamma, t, ty, l, FUEL).is_ok()
    }
}

// -------------------------------------------------------------------------
// Environments, levels, contexts
// -------------------------------------------------------------------------

/// A well-formed `⊢_L l : Level` (no `ω`, variables below `univs`).
pub fn gen_wf_level(univs: u32, r: &mut Rng, depth: u32) -> Level {
    match r.below(if depth == 0 { 2 } else { 4 }) {
        0 if univs > 0 => Level::Var(UnivVar(r.below(univs))),
        0 | 1 => Level::Zero,
        2 => Level::succ(gen_wf_level(univs, r, depth - 1)),
        _ => Level::max(
            gen_wf_level(univs, r, depth - 1),
            gen_wf_level(univs, r, depth - 1),
        ),
    }
}

/// A random well-formed ambient scope: one of a few known-good Ψ shapes, a
/// computing layer, and a generated well-formed Γ.
pub fn gen_wt_env(r: &mut Rng) -> WtEnv {
    let univs = r.below(3);
    let psi = match r.below(3) {
        0 => GlobalCtx::default(),
        1 => GlobalCtx { bindings: vec![GlobalBinding::Ctx] },
        // Ψ = (g : Ctx, U : Typ_c(g, 0), u : Trm_v(g ⊢ U^id @ 0)).
        _ => GlobalCtx {
            bindings: vec![
                GlobalBinding::Ctx,
                GlobalBinding::Ty { ctx: g_ctx(0), layer: Layer::Code, level: Level::Zero },
                GlobalBinding::Tm {
                    ctx: g_ctx(1),
                    layer: Layer::Var,
                    ty: rty(gty(0, &g_ctx(1))),
                    level: Level::Zero,
                },
            ],
        },
    };
    let layer = if r.below(4) == 0 { Layer::Prog } else { Layer::Meta };
    let mut env = WtEnv { psi, univs, layer, gamma: nil_ctx() };
    env.gamma = gen_wt_ctx(&env, r, 4, layer);
    env
}

/// A well-formed local context `⊢_layer Δ` over `env.psi` (base `·` or a
/// visible context binding), entries synthesized at `layer`.
pub fn gen_wt_ctx(env: &WtEnv, r: &mut Rng, b: u32, layer: Layer) -> LocalCtx {
    let ctx_vars: Vec<u32> = env
        .psi
        .bindings
        .iter()
        .enumerate()
        .filter(|(_, k)| matches!(k, GlobalBinding::Ctx))
        .map(|(i, _)| env.psi.bindings.len() as u32 - 1 - i as u32)
        .collect();
    let base = if !ctx_vars.is_empty() && r.below(2) == 0 {
        CtxBase::Var(GlobalVar(ctx_vars[r.below(ctx_vars.len() as u32) as usize]))
    } else {
        CtxBase::Nil
    };
    let mut ctx = LocalCtx { base, entries: vec![] };
    for _ in 0..r.below(3) {
        let e_env = env.in_ctx(ctx.clone(), layer);
        let (ty, level) = gen_wt_type(&e_env, r, b / 2);
        ctx.entries.push(CtxEntry { ty, level });
    }
    ctx
}

// -------------------------------------------------------------------------
// Types
// -------------------------------------------------------------------------

/// Synthesize `⊢_i T @ l`, returning `(T, l)`. Never returns an `ω`-level
/// type (no `ΠΠ` arm — `ΠΠ` types enter the tests only as inferred types of
/// `Λ ℓ⃗` terms).
pub fn gen_wt_type(env: &WtEnv, r: &mut Rng, b: u32) -> (Rc<Type>, Level) {
    assert!(env.layer != Layer::Var);
    for _ in 0..8 {
        match r.below(10) {
            0 => return (rty(Type::Nat), Level::Zero),
            1 => {
                let l = gen_wf_level(env.univs, r, 1);
                return (rty(Type::Ty(l.clone())), Level::succ(l));
            }
            2 if b > 0 => {
                let (dom, dl) = gen_wt_type(env, r, b / 2);
                let e = env.push_entry(Rc::clone(&dom), dl.clone());
                let (cod, cl) = gen_wt_type(&e, r, b / 2);
                return (
                    rty(Type::Pi { dom_level: dl.clone(), cod_level: cl.clone(), dom, cod }),
                    Level::max(dl, cl),
                );
            }
            3 if b > 0 => {
                let (tm, l) = gen_encoding(env, r, b / 2);
                return (rty(Type::El { level: l.clone(), tm }), l);
            }
            4 => {
                // U^δ for a visible Ty binding, if a δ can be built.
                let cands: Vec<u32> = (0..env.psi.bindings.len() as u32)
                    .filter(|x| {
                        let i = env.psi.bindings.len() - 1 - *x as usize;
                        matches!(&env.psi.bindings[i],
                                 GlobalBinding::Ty { layer, .. } if *layer <= env.layer)
                    })
                    .collect();
                if cands.is_empty() {
                    continue;
                }
                let x = cands[r.below(cands.len() as u32) as usize];
                let i = env.psi.bindings.len() - 1 - x as usize;
                let GlobalBinding::Ty { ctx, level, .. } = &env.psi.bindings[i] else {
                    unreachable!()
                };
                let level = level.clone();
                let ctx = ctx.shift_global(x + 1);
                let Some(subst) = gen_wt_subst(env, r, b / 2, &ctx) else { continue };
                return (rty(Type::GlobalTy { var: GlobalVar(x), subst }), level);
            }
            5 if b > 0 && env.layer == Layer::Meta => {
                let e = env.push_global(GlobalBinding::Ctx);
                let (body, bl) = gen_wt_type(&e, r, b / 2);
                return (rty(Type::CtxPi { level: bl.clone(), body }), bl);
            }
            6 if b > 0 && env.layer == Layer::Meta => {
                let ctx = gen_wt_ctx(env, r, b / 2, Layer::Prog);
                let al = gen_wf_level(env.univs, r, 1);
                let e = env.push_global(GlobalBinding::Ty {
                    ctx: ctx.clone(),
                    layer: Layer::Prog,
                    level: al.clone(),
                });
                let (body, bl) = gen_wt_type(&e, r, b / 2);
                return (
                    rty(Type::TyPi { ctx, arg_level: al, body_level: bl.clone(), body }),
                    bl,
                );
            }
            7 if env.layer == Layer::Meta => {
                let ctx = gen_wt_ctx(env, r, b / 2, Layer::Prog);
                let level = gen_wf_level(env.univs, r, 1);
                return (rty(Type::CodeTy { ctx, level }), Level::Zero);
            }
            8 if b > 0 && env.layer == Layer::Meta => {
                let ctx = gen_wt_ctx(env, r, b / 2, Layer::Prog);
                let (ty, cl) = gen_wt_type(&env.in_ctx(ctx.clone(), Layer::Prog), r, b / 2);
                return (rty(Type::CodeTm { ctx, ty, level: cl }), Level::Zero);
            }
            _ => continue,
        }
    }
    (rty(Type::Nat), Level::Zero)
}

/// Synthesize an encoding `⊢_i t : Ty l @ 1+l`, returning `(t, l)`.
fn gen_encoding(env: &WtEnv, r: &mut Rng, b: u32) -> (Rc<Term>, Level) {
    match r.below(3) {
        0 => (rt(Term::TmNat), Level::Zero),
        1 => {
            let l = gen_wf_level(env.univs, r, 1);
            (rt(Term::TmTy(l.clone())), Level::succ(l))
        }
        _ if b > 0 => {
            let (dom, dl) = gen_encoding(env, r, b / 2);
            let e = env.push_entry(
                rty(Type::El { level: dl.clone(), tm: Rc::clone(&dom) }),
                dl.clone(),
            );
            let (cod, cl) = gen_encoding(&e, r, b / 2);
            (
                rt(Term::TmPi { dom_level: dl.clone(), cod_level: cl.clone(), dom, cod }),
                Level::max(dl, cl),
            )
        }
        _ => (rt(Term::TmNat), Level::Zero),
    }
}

/// A type at an *exact* level (for `@`-application arguments and boxed-type
/// bodies), or `None`.
fn gen_wt_type_at(env: &WtEnv, r: &mut Rng, b: u32, level: &Level) -> Option<Rc<Type>> {
    if level.equiv(&Level::Zero) && r.below(2) == 0 {
        return Some(rty(Type::Nat));
    }
    for _ in 0..3 {
        let (t, l) = gen_wt_type(env, r, b);
        if l.equiv(level) {
            return Some(t);
        }
    }
    // El^level of a checked encoding at Ty level.
    let tm = gen_wt_term_at(
        env,
        r,
        b,
        &Type::Ty(level.clone()),
        &Level::succ(level.clone()),
    )?;
    Some(rty(Type::El { level: level.clone(), tm }))
}

// -------------------------------------------------------------------------
// Local substitutions
// -------------------------------------------------------------------------

/// `⊢_i δ : Δ` from `env.gamma`, or `None` when the tail is unreachable or
/// some entry type cannot be inhabited.
pub fn gen_wt_subst(env: &WtEnv, r: &mut Rng, b: u32, target: &LocalCtx) -> Option<LocalSubst> {
    let tail = match target.base {
        CtxBase::Nil => SubstTail::Empty {
            len: env.gamma.entries.len() as u32,
            base: env.gamma.base,
        },
        CtxBase::Var(g) => {
            if env.gamma.base != CtxBase::Var(g) {
                return None;
            }
            SubstTail::Wk { len: env.gamma.entries.len() as u32, ctx_var: g }
        }
    };
    let mut delta = LocalSubst { tail, terms: vec![] };
    for entry in &target.entries {
        let ty = entry.ty.apply_local(&delta);
        let t = gen_wt_term_at(env, r, b / 2, &ty, &entry.level)?;
        delta = delta.extended(t);
    }
    Some(delta)
}

// -------------------------------------------------------------------------
// Terms: checked mode
// -------------------------------------------------------------------------

/// A term of type `Nat @ 0`: a numeral or a Γ-variable.
fn gen_nat(env: &WtEnv, r: &mut Rng) -> Rc<Term> {
    if r.below(3) == 0 {
        if let Some(t) = find_var(env, r, &Type::Nat, &Level::Zero) {
            return t;
        }
    }
    let mut t = Term::Zero;
    for _ in 0..r.below(3) {
        t = Term::Succ(rt(t));
    }
    rt(t)
}

/// A Γ-variable that checks at `(ty, level)`, searched from a random start.
fn find_var(env: &WtEnv, r: &mut Rng, ty: &Type, level: &Level) -> Option<Rc<Term>> {
    let n = env.gamma.entries.len() as u32;
    if n == 0 {
        return None;
    }
    let start = r.below(n);
    for k in 0..n {
        let t = v((start + k) % n);
        if env.checks(&t, ty, level) {
            return Some(rt(t));
        }
    }
    None
}

/// Checked mode: a term of the given type and level, or `None`. Descends
/// intro-directed through the WHNF of the target, falling back to a Γ
/// search filtered by `check_term`.
pub fn gen_wt_term_at(
    env: &WtEnv,
    r: &mut Rng,
    b: u32,
    ty: &Type,
    level: &Level,
) -> Option<Rc<Term>> {
    let w = whnf_type(ty, &env.gamma, FUEL).ok()?;
    let intro: Option<Rc<Term>> = match &w {
        Type::Nat => Some(gen_nat(env, r)),
        Type::Pi { dom_level, cod_level, dom, cod } if b > 0 => {
            let e = env.push_entry(Rc::clone(dom), dom_level.clone());
            gen_wt_term_at(&e, r, b - 1, cod, cod_level).map(|body| {
                rt(Term::Lam {
                    dom_level: dom_level.clone(),
                    cod_level: cod_level.clone(),
                    dom: Rc::clone(dom),
                    body,
                })
            })
        }
        Type::Ty(l) => {
            let mut found = None;
            for _ in 0..3 {
                let (t, tl) = gen_encoding(env, r, b);
                if tl.equiv(l) {
                    found = Some(t);
                    break;
                }
            }
            found
        }
        Type::UPi { num_vars, level: bl, body } if b > 0 && env.layer == Layer::Meta => {
            let e = env.push_univs(*num_vars);
            gen_wt_term_at(&e, r, b - 1, body, bl).map(|body| {
                rt(Term::ULam { num_vars: *num_vars, level: bl.clone(), body })
            })
        }
        Type::CtxPi { level: bl, body } if b > 0 && env.layer == Layer::Meta => {
            let e = env.push_global(GlobalBinding::Ctx);
            gen_wt_term_at(&e, r, b - 1, body, bl)
                .map(|body| rt(Term::CtxLam { level: bl.clone(), body }))
        }
        Type::TyPi { ctx, arg_level, body_level, body } if b > 0 && env.layer == Layer::Meta => {
            let e = env.push_global(GlobalBinding::Ty {
                ctx: ctx.clone(),
                layer: Layer::Prog,
                level: arg_level.clone(),
            });
            gen_wt_term_at(&e, r, b - 1, body, body_level).map(|body| {
                rt(Term::TyLam {
                    ctx: ctx.clone(),
                    arg_level: arg_level.clone(),
                    body_level: body_level.clone(),
                    body,
                })
            })
        }
        Type::CodeTy { ctx, level: cl } if b > 0 && env.layer == Layer::Meta => {
            let ce = env.in_ctx(ctx.clone(), Layer::Code);
            gen_wt_type_at(&ce, r, b - 1, cl).map(|t| rt(Term::BoxTy(t)))
        }
        Type::CodeTm { ctx, ty: cty, level: cl } if b > 0 && env.layer == Layer::Meta => {
            let ce = env.in_ctx(ctx.clone(), Layer::Code);
            gen_wt_term_at(&ce, r, b - 1, cty, cl).map(|t| rt(Term::BoxTm(t)))
        }
        _ => None,
    };
    // Verify intro results (annotations copied out of the target type can
    // exceed the term layer, as in the synthesis app arm) before use.
    if let Some(t) = intro {
        if env.checks(&t, ty, level) {
            return Some(t);
        }
    }
    find_var(env, r, ty, level)
}

// -------------------------------------------------------------------------
// Terms: synthesis
// -------------------------------------------------------------------------

/// Replace an `ω`-level (or out-of-scope-level) result with `0 : Nat @ 0`,
/// for positions that demand `⊢_L l : Level`.
fn guard(univs: u32, trip: (Rc<Term>, Rc<Type>, Level)) -> (Rc<Term>, Rc<Type>, Level) {
    if trip.2.well_formed(univs) {
        trip
    } else {
        (rt(Term::Zero), rty(Type::Nat), Level::Zero)
    }
}

/// Synthesize `⊢_i t : T @ l`, returning `(t, T, l)` per the corresponding
/// inference rule's conclusion.
pub fn gen_wt_term(env: &WtEnv, r: &mut Rng, b: u32) -> (Rc<Term>, Rc<Type>, Level) {
    assert!(env.layer != Layer::Var);
    let meta = env.layer == Layer::Meta;
    for _ in 0..10 {
        match r.below(18) {
            0 | 1 if !env.gamma.entries.is_empty() => {
                let x = r.below(env.gamma.entries.len() as u32);
                let i = env.gamma.entries.len() - 1 - x as usize;
                let e = &env.gamma.entries[i];
                return (rt(v(x)), rty(e.ty.shift_local(x + 1)), e.level.clone());
            }
            2 => return (gen_nat(env, r), rty(Type::Nat), Level::Zero),
            3 => {
                let (t, l) = gen_encoding(env, r, b / 2);
                return (t, rty(Type::Ty(l.clone())), Level::succ(l));
            }
            4 if b > 0 => {
                // λ: synthesize the body, guard its level (no ω codomains).
                let (dom, dl) = gen_wt_type(env, r, b / 2);
                let e = env.push_entry(Rc::clone(&dom), dl.clone());
                let (body, cod, cl) = guard(env.univs, gen_wt_term(&e, r, b / 2));
                return (
                    rt(Term::Lam {
                        dom_level: dl.clone(),
                        cod_level: cl.clone(),
                        dom: Rc::clone(&dom),
                        body,
                    }),
                    rty(Type::Pi { dom_level: dl.clone(), cod_level: cl.clone(), dom, cod }),
                    Level::max(dl, cl),
                );
            }
            5 if b > 0 => {
                // app: a synthesized head if its WHNF type is a Π, else a
                // fresh λ head (guaranteeing β-redexes stay common).
                let (f, fty, _) = gen_wt_term(env, r, b / 2);
                let (f, w) = match whnf_type(&fty, &env.gamma, FUEL) {
                    Ok(w @ Type::Pi { .. }) => (f, w),
                    _ => {
                        let (dom, dl) = gen_wt_type(env, r, b / 2);
                        let e = env.push_entry(Rc::clone(&dom), dl.clone());
                        let (body, cod, cl) = guard(env.univs, gen_wt_term(&e, r, b / 2));
                        (
                            rt(Term::Lam {
                                dom_level: dl.clone(),
                                cod_level: cl.clone(),
                                dom: Rc::clone(&dom),
                                body,
                            }),
                            Type::Pi { dom_level: dl, cod_level: cl, dom, cod },
                        )
                    }
                };
                let Type::Pi { dom_level, cod_level, dom, cod } = w else { unreachable!() };
                let Some(arg) = gen_wt_term_at(env, r, b / 2, &dom, &dom_level) else {
                    continue;
                };
                let res = cod.apply_local(
                    &LocalSubst::id(&env.gamma).extended(Rc::clone(&arg)),
                );
                let lvl = cod_level.clone();
                let app = rt(Term::App { fun: f, dom_level, cod_level, dom, cod, arg });
                let res = rty(res);
                // The dom/cod annotations are copied from the head's Π type,
                // which may mention globals of a *higher* layer than terms
                // here may re-state (e.g. Prog-layer type bindings in
                // layer-c code) — filter through the checker.
                if !env.checks(&app, &res, &lvl) {
                    continue;
                }
                return (app, res, lvl);
            }
            6 if b > 0 => {
                // elim_Nat with a constant motive B (the synthesized base's
                // type); the step is `y` or the weakened base.
                let (base, bty, bl) = guard(env.univs, gen_wt_term(env, r, b / 2));
                let motive = rty(bty.shift_local(1));
                let step = if r.below(2) == 0 {
                    rt(v(0))
                } else {
                    rt(base.shift_local(2))
                };
                let scrut = gen_nat(env, r);
                return (
                    rt(Term::ElimNat { level: bl.clone(), motive, base, step, scrut }),
                    bty,
                    bl,
                );
            }
            7 => {
                // u^δ for a visible Tm binding.
                let cands: Vec<u32> = (0..env.psi.bindings.len() as u32)
                    .filter(|x| {
                        let i = env.psi.bindings.len() - 1 - *x as usize;
                        matches!(&env.psi.bindings[i],
                                 GlobalBinding::Tm { layer, .. } if *layer <= env.layer)
                    })
                    .collect();
                if cands.is_empty() {
                    continue;
                }
                let x = cands[r.below(cands.len() as u32) as usize];
                let i = env.psi.bindings.len() - 1 - x as usize;
                let GlobalBinding::Tm { ctx, ty, level, .. } = &env.psi.bindings[i] else {
                    unreachable!()
                };
                let level = level.clone();
                let ctx = ctx.shift_global(x + 1);
                let ty = ty.shift_global(x + 1);
                let Some(subst) = gen_wt_subst(env, r, b / 2, &ctx) else { continue };
                let res = ty.apply_local(&subst);
                return (
                    rt(Term::GlobalTm { var: GlobalVar(x), subst }),
                    rty(res),
                    level,
                );
            }
            8 if b > 0 && meta => {
                // Λ ℓ⃗: the one arm whose result level is ω.
                let n = 1 + r.below(2);
                let e = env.push_univs(n);
                let (body, bty, bl) = guard(e.univs, gen_wt_term(&e, r, b / 2));
                return (
                    rt(Term::ULam { num_vars: n, level: bl.clone(), body }),
                    rty(Type::UPi { num_vars: n, level: bl, body: bty }),
                    Level::Omega,
                );
            }
            9 if b > 0 && meta => {
                let (f, fty, fl) = gen_wt_term(env, r, b / 2);
                if !fl.equiv(&Level::Omega) {
                    continue;
                }
                let Ok(w) = whnf_type(&fty, &env.gamma, FUEL) else { continue };
                let Type::UPi { num_vars, level, body } = w else { continue };
                let levels: Vec<Level> =
                    (0..num_vars).map(|_| gen_wf_level(env.univs, r, 1)).collect();
                let phi: Vec<Level> = levels.iter().rev().cloned().collect();
                return (
                    rt(Term::UApp { fun: f, levels }),
                    rty(body.inst_univ(&phi)),
                    level.inst_at(&phi, 0),
                );
            }
            10 if b > 0 && meta => {
                let e = env.push_global(GlobalBinding::Ctx);
                let (body, bty, bl) = guard(e.univs, gen_wt_term(&e, r, b / 2));
                return (
                    rt(Term::CtxLam { level: bl.clone(), body }),
                    rty(Type::CtxPi { level: bl.clone(), body: bty }),
                    bl,
                );
            }
            11 if b > 0 && meta => {
                let (f, fty, _) = gen_wt_term(env, r, b / 2);
                let Ok(w) = whnf_type(&fty, &env.gamma, FUEL) else { continue };
                let Type::CtxPi { level, body } = w else { continue };
                let ctx = gen_wt_ctx(env, r, b / 2, Layer::Prog);
                let res = body.apply_global(&heather_kernel::subst::GlobalSubst::single(
                    heather_kernel::subst::GlobalEntry::Ctx(ctx.clone()),
                ));
                return (rt(Term::CtxApp { fun: f, ctx }), rty(res), level);
            }
            12 if b > 0 && meta => {
                let ctx = gen_wt_ctx(env, r, b / 2, Layer::Prog);
                let al = gen_wf_level(env.univs, r, 1);
                let e = env.push_global(GlobalBinding::Ty {
                    ctx: ctx.clone(),
                    layer: Layer::Prog,
                    level: al.clone(),
                });
                let (body, bty, bl) = guard(e.univs, gen_wt_term(&e, r, b / 2));
                return (
                    rt(Term::TyLam {
                        ctx: ctx.clone(),
                        arg_level: al.clone(),
                        body_level: bl.clone(),
                        body,
                    }),
                    rty(Type::TyPi {
                        ctx,
                        arg_level: al,
                        body_level: bl.clone(),
                        body: bty,
                    }),
                    bl,
                );
            }
            13 if b > 0 && meta => {
                let (f, fty, _) = gen_wt_term(env, r, b / 2);
                let Ok(w) = whnf_type(&fty, &env.gamma, FUEL) else { continue };
                let Type::TyPi { ctx, arg_level, body_level, body } = w else { continue };
                let de = env.in_ctx(ctx, Layer::Prog);
                let Some(arg) = gen_wt_type_at(&de, r, b / 2, &arg_level) else { continue };
                let res = body.apply_global(&heather_kernel::subst::GlobalSubst::single(
                    heather_kernel::subst::GlobalEntry::Ty(Rc::clone(&arg)),
                ));
                return (rt(Term::TyApp { fun: f, arg }), rty(res), body_level);
            }
            14 if b > 1 && meta => return gen_letbox_tm(env, r, b),
            15 if b > 1 && meta => return gen_letbox_ty(env, r, b),
            16 if b >= 4 && meta => return gen_const_rec(env, r, b, false),
            17 if b >= 4 && meta => return gen_const_rec(env, r, b, true),
            _ => continue,
        }
    }
    (rt(Term::Zero), rty(Type::Nat), Level::Zero)
}

/// `letbox` over freshly boxed code. Half the time the motive is constant
/// (a synthesized inhabitant's type); otherwise it is the code's own
/// contextual type and the body re-boxes the bound global — exercising
/// checking-only `box` bodies and the `M[box u^id/x]` substitution.
fn gen_letbox_tm(env: &WtEnv, r: &mut Rng, b: u32) -> (Rc<Term>, Rc<Type>, Level) {
    let delta = gen_wt_ctx(env, r, b / 2, Layer::Prog);
    let ce = env.in_ctx(delta.clone(), Layer::Code);
    let (tc, cty, cl) = gen_wt_term(&ce, r, b / 2);
    if r.below(2) == 0 {
        let (mt, mty, ml) = guard(env.univs, gen_wt_term(env, r, b / 2));
        (
            rt(Term::LetBoxTm {
                motive_level: ml.clone(),
                code_level: cl,
                ctx: delta,
                ty: cty,
                motive: rty(mty.shift_local(1)),
                body: rt(mt.shift_global(1)),
                scrut: rt(Term::BoxTm(tc)),
            }),
            mty,
            ml,
        )
    } else {
        let m = Type::CodeTm { ctx: delta.clone(), ty: Rc::clone(&cty), level: cl.clone() };
        let body = rt(Term::BoxTm(rt(gtm(0, &delta.shift_global(1)))));
        (
            rt(Term::LetBoxTm {
                motive_level: Level::Zero,
                code_level: cl,
                ctx: delta,
                ty: cty,
                motive: rty(m.shift_local(1)),
                body,
                scrut: rt(Term::BoxTm(tc)),
            }),
            rty(m),
            Level::Zero,
        )
    }
}

fn gen_letbox_ty(env: &WtEnv, r: &mut Rng, b: u32) -> (Rc<Term>, Rc<Type>, Level) {
    let delta = gen_wt_ctx(env, r, b / 2, Layer::Prog);
    let ce = env.in_ctx(delta.clone(), Layer::Code);
    let (cty, cl) = gen_wt_type(&ce, r, b / 2);
    if r.below(2) == 0 {
        let (mt, mty, ml) = guard(env.univs, gen_wt_term(env, r, b / 2));
        (
            rt(Term::LetBoxTy {
                motive_level: ml.clone(),
                code_level: cl,
                ctx: delta,
                motive: rty(mty.shift_local(1)),
                body: rt(mt.shift_global(1)),
                scrut: rt(Term::BoxTy(cty)),
            }),
            mty,
            ml,
        )
    } else {
        let m = Type::CodeTy { ctx: delta.clone(), level: cl.clone() };
        let body = rt(Term::BoxTy(rty(gty(0, &delta.shift_global(1)))));
        (
            rt(Term::LetBoxTy {
                motive_level: Level::Zero,
                code_level: cl,
                ctx: delta,
                motive: rty(m.shift_local(1)),
                body,
                scrut: rt(Term::BoxTy(cty)),
            }),
            rty(m),
            Level::Zero,
        )
    }
}

// -------------------------------------------------------------------------
// Recursors with constant motives
// -------------------------------------------------------------------------

/// Per-branch telescope depths `(univs, globals, locals)`, whether the
/// branch's motive is the *term* motive, and whether the innermost
/// recursive-call entry has that same motive (so `Var(0)` inhabits the
/// branch type). Order = `Branches` field order. Independent transcription
/// of docs/delam/04 — a disagreement with `src/rec.rs` is a test failure.
const BRANCH_DIMS: [(u32, u32, u32, bool, bool); 13] = [
    (0, 1, 0, false, false), // ty_nat
    (2, 3, 2, false, true),  // ty_pi
    (1, 1, 0, false, false), // ty_ty
    (1, 2, 1, false, false), // ty_el (innermost local is a *term*-motive call)
    (1, 3, 0, true, false),  // tm_var
    (0, 1, 0, true, false),  // tm_nat
    (2, 3, 2, true, true),   // tm_pi
    (1, 1, 0, true, false),  // tm_ty
    (0, 1, 0, true, false),  // tm_zero
    (0, 2, 1, true, true),   // tm_succ
    (1, 5, 4, true, true),   // tm_elim_nat
    (2, 4, 2, true, true),   // tm_lam
    (2, 5, 4, true, true),   // tm_app
];

/// A code recursor with constant motives `M₁ = typeof(m₁)`, `M₂ =
/// typeof(m₂)`: every branch is the matching inhabitant weakened by its
/// telescope depths (or `Var(0)` where the innermost recursive call has the
/// right motive). `tm_variant` selects `elim^Trm` over `elim^Typ`.
fn gen_const_rec(
    env: &WtEnv,
    r: &mut Rng,
    b: u32,
    tm_variant: bool,
) -> (Rc<Term>, Rc<Type>, Level) {
    let delta = gen_wt_ctx(env, r, b / 4, Layer::Prog);
    let ce = env.in_ctx(delta.clone(), Layer::Code);
    let (m1t, m1ty, l1) = guard(env.univs, gen_wt_term(env, r, b / 4));
    let (m2t, m2ty, l2) = guard(env.univs, gen_wt_term(env, r, b / 4));
    let motives = Rc::new(Motives {
        ty_motive: rty(m1ty.shift_univ(1).shift_global(1).shift_local(1)),
        tm_motive: rty(m2ty.shift_univ(1).shift_global(2).shift_local(1)),
    });
    let mut bs: Vec<Rc<Term>> = Vec::with_capacity(13);
    for &(tu, tg, tl, tm_kind, var_ok) in &BRANCH_DIMS {
        if var_ok && r.below(3) == 0 {
            bs.push(rt(v(0)));
        } else {
            let m = if tm_kind { &m2t } else { &m1t };
            bs.push(rt(m.shift_univ(tu).shift_global(tg).shift_local(tl)));
        }
    }
    let branches = Rc::new(Branches {
        ty_nat: bs[0].clone(),
        ty_pi: bs[1].clone(),
        ty_ty: bs[2].clone(),
        ty_el: bs[3].clone(),
        tm_var: bs[4].clone(),
        tm_nat: bs[5].clone(),
        tm_pi: bs[6].clone(),
        tm_ty: bs[7].clone(),
        tm_zero: bs[8].clone(),
        tm_succ: bs[9].clone(),
        tm_elim_nat: bs[10].clone(),
        tm_lam: bs[11].clone(),
        tm_app: bs[12].clone(),
    });
    if tm_variant {
        let (tc, cty, cl) = gen_wt_term(&ce, r, b / 4);
        (
            rt(Term::ElimCodeTm {
                ty_motive_level: l1,
                tm_motive_level: l2.clone(),
                motives,
                branches,
                code_level: cl,
                ctx: delta,
                ty: cty,
                scrut: rt(Term::BoxTm(tc)),
            }),
            m2ty,
            l2,
        )
    } else {
        let (cty, cl) = gen_wt_type(&ce, r, b / 4);
        (
            rt(Term::ElimCodeTy {
                ty_motive_level: l1.clone(),
                tm_motive_level: l2,
                motives,
                branches,
                code_level: cl,
                ctx: delta,
                scrut: rt(Term::BoxTy(cty)),
            }),
            m1ty,
            l1,
        )
    }
}

// -------------------------------------------------------------------------
// The identity recursor (duplicated from tests/typing.rs — test binaries
// cannot share code except through common/)
// -------------------------------------------------------------------------

/// Motives that are the contextual types themselves: `elim` should be the
/// identity on code.
pub fn identity_motives() -> Rc<Motives> {
    Rc::new(Motives {
        // (ℓ, g, x_T. □(g ⊢ Ty ℓ))
        ty_motive: rty(Type::CodeTy { ctx: g_ctx(0), level: lv(0) }),
        // (ℓ, g, U_T, x_t. □(g ⊢ U_T^id @ ℓ))
        tm_motive: rty(Type::CodeTm {
            ctx: g_ctx(1),
            ty: rty(gty(0, &g_ctx(1))),
            level: lv(0),
        }),
    })
}

/// Branches that re-box exactly the code each telescope describes.
pub fn identity_branches() -> Rc<Branches> {
    let g1 = g_ctx(1);
    let g2 = g_ctx(2);
    let g3 = g_ctx(3);
    let g4 = g_ctx(4);
    let gx_typi = ext(&g2, gty(1, &g2), lv(1));
    let gx_app = ext(&g4, gty(3, &g4), lv(1));
    let gx_tmpi = ext(&g2, Type::El { level: lv(1), tm: rt(gtm(1, &g2)) }, lv(1));
    let gx_lam = ext(&g3, gty(2, &g3), lv(1));
    let gx_nat = ext(&g4, Type::Nat, Level::Zero);
    let u_m = Type::GlobalTy { var: GlobalVar(3), subst: LocalSubst::id(&gx_nat) };
    let gxy = ext(&gx_nat, u_m.clone(), lv(0));

    Rc::new(Branches {
        ty_nat: rt(Term::BoxTy(rty(Type::Nat))),
        ty_pi: rt(Term::BoxTy(rty(Type::Pi {
            dom_level: lv(1),
            cod_level: lv(0),
            dom: rty(gty(1, &g2)),
            cod: rty(gty(0, &gx_typi)),
        }))),
        ty_ty: rt(Term::BoxTy(rty(Type::Ty(lv(0))))),
        ty_el: rt(Term::BoxTy(rty(Type::El { level: lv(0), tm: rt(gtm(0, &g1)) }))),
        tm_var: rt(Term::BoxTm(rt(gtm(0, &g2)))),
        tm_nat: rt(Term::BoxTm(rt(Term::TmNat))),
        tm_pi: rt(Term::BoxTm(rt(Term::TmPi {
            dom_level: lv(1),
            cod_level: lv(0),
            dom: rt(gtm(1, &g2)),
            cod: rt(gtm(0, &gx_tmpi)),
        }))),
        tm_ty: rt(Term::BoxTm(rt(Term::TmTy(lv(0))))),
        tm_zero: rt(Term::BoxTm(rt(Term::Zero))),
        tm_succ: rt(Term::BoxTm(rt(Term::Succ(rt(gtm(0, &g1)))))),
        tm_elim_nat: rt(Term::BoxTm(rt(Term::ElimNat {
            level: lv(0),
            motive: rty(u_m),
            base: rt(gtm(2, &g4)),
            step: rt(gtm(1, &gxy)),
            scrut: rt(gtm(0, &g4)),
        }))),
        tm_lam: rt(Term::BoxTm(rt(Term::Lam {
            dom_level: lv(1),
            cod_level: lv(0),
            dom: rty(gty(2, &g3)),
            body: rt(gtm(0, &gx_lam)),
        }))),
        tm_app: rt(Term::BoxTm(rt(Term::App {
            fun: rt(gtm(1, &g4)),
            dom_level: lv(1),
            cod_level: lv(0),
            dom: rty(gty(3, &g4)),
            cod: rty(gty(2, &gx_app)),
            arg: rt(gtm(0, &g4)),
        }))),
    })
}
