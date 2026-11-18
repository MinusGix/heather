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

use heather_kernel::rc::Rc;

use heather_kernel::layer::Layer;
use heather_kernel::level::{Level, UnivVar};
use heather_kernel::reduce::whnf_type;
use heather_kernel::term::{
    iwf_motive_scrut_ty, iwf_step_telescope, nth, Branches, CtxBase, CtxEntry, GlobalBinding,
    GlobalCtx, GlobalVar, IWfSig, MSig, LocalCtx, LocalSubst, LocalVar, Motives, SubstTail, Term,
    Type,
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
    LocalCtx::nil()
}

fn g_ctx(i: u32) -> LocalCtx {
    LocalCtx::ctx_var(GlobalVar::index(i))
}

fn ext(base: &LocalCtx, ty: Type, level: Level) -> LocalCtx {
    let mut c = base.clone();
    c.entries.push(CtxEntry { ty: rty(ty), level });
    c
}

fn gty(var: u32, ctx: &LocalCtx) -> Type {
    Type::GlobalTy { var: GlobalVar::index(var), subst: LocalSubst::id(ctx) }
}

fn gtm(var: u32, ctx: &LocalCtx) -> Term {
    Term::GlobalTm { var: GlobalVar::index(var), subst: LocalSubst::id(ctx) }
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
    /// Generate the five **checked spellings** (`pair@`/`inl@`/`inr@`/
    /// `fst@`/`snd@`, `docs/elaborator/intro-by-type-design.md` §2)? **Off by default**,
    /// and off is byte-identical to the pre-`@` generator: the arm dispatch
    /// picks its modulus from this flag (`r.below(27)` vs `r.below(32)`) and
    /// `Rng::below` draws exactly one word whatever the bound, so a stream
    /// generated with the flag off is the same stream it was before the
    /// spellings existed.
    ///
    /// That matters because two bench fixtures are built from this generator
    /// (`conv/perturbed-pairs`, `check/generated-terms`) and their baselines
    /// gate the kernel: with the spellings on, `perturbed-pairs` moved
    /// 4.5–13.5× and `generated-terms`' slope 1.04 → 2.5, a *fixture* change
    /// that would bury the next real regression. The differential and golden
    /// tests turn it on with [`gen_wt_env_at`]; the benches do not.
    pub at_forms: bool,
}

/// `shift_univ_psi` replica (the kernel's is crate-private): weaken Ψ's
/// variables by `by` universe variables. The signature is closed in them and
/// stays as it is.
fn shift_univ_psi(psi: &GlobalCtx, by: u32) -> GlobalCtx {
    let consts = psi.consts();
    if by == 0 || consts == psi.bindings.len() {
        return psi.clone();
    }
    psi.prefix(consts).extended(psi.bindings.iter().skip(consts).map(|b| match b {
        GlobalBinding::Ctx => GlobalBinding::Ctx,
        GlobalBinding::Ty { ctx, layer, level } => GlobalBinding::Ty {
            ctx: ctx.shift_univ(by),
            layer: *layer,
            level: level.shift(by, 0),
        },
        GlobalBinding::Tm { ctx, layer, ty, level, body } => GlobalBinding::Tm {
            ctx: ctx.shift_univ(by),
            layer: *layer,
            ty: Rc::new(ty.shift_univ(by)),
            level: level.shift(by, 0),
            body: body.as_ref().map(|t| Rc::new(t.shift_univ(by))),
        },
    }))
}

impl WtEnv {
    pub fn in_ctx(&self, gamma: LocalCtx, layer: Layer) -> WtEnv {
        WtEnv { gamma, layer, ..self.clone() }
    }

    pub fn push_entry(&self, ty: Rc<Type>, level: Level) -> WtEnv {
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
            at_forms: self.at_forms,
        }
    }

    fn push_global(&self, b: GlobalBinding) -> WtEnv {
        let mut psi = self.psi.clone();
        psi.push(b);
        WtEnv {
            psi,
            univs: self.univs,
            layer: self.layer,
            gamma: self.gamma.shift_global(1),
            at_forms: self.at_forms,
        }
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
        1 => GlobalCtx::new(vec![GlobalBinding::Ctx]),
        // Ψ = (g : Ctx, U : Typ_c(g, 0), u : Trm_v(g ⊢ U^id @ 0)).
        _ => GlobalCtx::new(vec![
                GlobalBinding::Ctx,
                GlobalBinding::Ty { ctx: g_ctx(0), layer: Layer::Code, level: Level::Zero },
                GlobalBinding::Tm {
                    ctx: g_ctx(1),
                    layer: Layer::Var,
                    ty: rty(gty(0, &g_ctx(1))),
                    level: Level::Zero,
                    body: None,
                },
            ]),
    };
    let layer = if r.below(4) == 0 { Layer::Prog } else { Layer::Meta };
    let mut env = WtEnv { psi, univs, layer, gamma: nil_ctx(), at_forms: false };
    env.gamma = gen_wt_ctx(&env, r, 4, layer);
    env
}

/// [`gen_wt_env`] with the checked spellings **on** — the differential and
/// golden tests' entry point. Draws exactly the same random words as
/// `gen_wt_env`; the streams diverge only at [`gen_wt_term`]'s dispatch.
pub fn gen_wt_env_at(r: &mut Rng) -> WtEnv {
    WtEnv { at_forms: true, ..gen_wt_env(r) }
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
        CtxBase::Var(GlobalVar::index(ctx_vars[r.below(ctx_vars.len() as u32) as usize]))
    } else {
        CtxBase::Nil
    };
    let mut ctx = LocalCtx { base, entries: Default::default() };
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
        match r.below(21) {
            // Unit^l / Empty^l — level-indexed, so a generated level rather
            // than 0 (docs/kernel/unit-empty-level-indexing.md). Without these the
            // property suite never sees the round at all.
            16 => {
                let l = gen_wf_level(env.univs, r, 1);
                return (rty(Type::Unit { level: l.clone() }), l);
            }
            17 => {
                let l = gen_wf_level(env.univs, r, 1);
                return (rty(Type::Empty { level: l.clone() }), l);
            }
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
                return (rty(Type::GlobalTy { var: GlobalVar::index(x), subst }), level);
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
                let ctx = gen_wt_ctx(env, r, b / 2, Layer::Code);
                let level = gen_wf_level(env.univs, r, 1);
                return (rty(Type::CodeTy { ctx, level }), Level::Zero);
            }
            8 if b > 0 && env.layer == Layer::Meta => {
                let ctx = gen_wt_ctx(env, r, b / 2, Layer::Code);
                let (ty, cl) = gen_wt_type(&env.in_ctx(ctx.clone(), Layer::Code), r, b / 2);
                return (rty(Type::CodeTm { ctx, ty, level: cl }), Level::Zero);
            }
            9 if b > 0 => {
                // Id^l (S; t; u) (extension): both endpoints checked at S.
                let (ty, l) = gen_wt_type(env, r, b / 2);
                let Some(lhs) = gen_wt_term_at(env, r, b / 2, &ty, &l) else { continue };
                let Some(rhs) = gen_wt_term_at(env, r, b / 2, &ty, &l) else { continue };
                return (rty(Type::Id { level: l.clone(), ty, lhs, rhs }), l);
            }
            10 if b > 0 => {
                // Σ^{l,l'}(x:S).T (extension): T checked in (Γ, x:S).
                let (fst, dl) = gen_wt_type(env, r, b / 2);
                let e = env.push_entry(Rc::clone(&fst), dl.clone());
                let (snd, cl) = gen_wt_type(&e, r, b / 2);
                return (
                    rty(Type::Sigma {
                        fst_level: dl.clone(),
                        snd_level: cl.clone(),
                        fst,
                        snd,
                    }),
                    Level::max(dl, cl),
                );
            }
            11 if b > 0 => {
                // A +^{l,l'} B (extension): non-dependent, both in Γ.
                let (lhs, dl) = gen_wt_type(env, r, b / 2);
                let (rhs, cl) = gen_wt_type(env, r, b / 2);
                return (
                    rty(Type::Sum {
                        lhs_level: dl.clone(),
                        rhs_level: cl.clone(),
                        lhs,
                        rhs,
                    }),
                    Level::max(dl, cl),
                );
            }
            12 if b > 0 => {
                // W^{l,l'}(x:S).T (extension): T checked in (Γ, x:S), as Σ.
                let (shape, dl) = gen_wt_type(env, r, b / 2);
                let e = env.push_entry(Rc::clone(&shape), dl.clone());
                let (pos, cl) = gen_wt_type(&e, r, b / 2);
                return (
                    rty(Type::W {
                        shape_level: dl.clone(),
                        pos_level: cl.clone(),
                        shape,
                        pos,
                    }),
                    Level::max(dl, cl),
                );
            }
            // Vec/Fin/Wf (extension; docs/kernel/wf-former-design.md §1). Lengths
            // and arities are Nat *terms*: often neutral, in which case the
            // type is stuck and inhabiting it fails — the callers all treat
            // that as a miss, and a literal length gives the Σ/Unit form.
            13 if b > 0 => {
                let (elem, l) = gen_wt_type(env, r, b / 2);
                let len = gen_wt_nat(env, r, b / 2);
                return (rty(Type::Vec { level: l.clone(), elem, len }), l);
            }
            14 if b > 0 => {
                let len = gen_wt_nat(env, r, b / 2);
                return (rty(Type::Fin { len }), Level::Zero);
            }
            15 if b > 0 => {
                let (shape, l) = gen_wt_type(env, r, b / 2);
                let e = env.push_entry(Rc::clone(&shape), l.clone());
                let arity = gen_wt_nat(&e, r, b / 2);
                return (rty(Type::Wf { level: l.clone(), shape, arity }), l);
            }
            // DVec (extension; docs/kernel/iwf-former-design.md §1.1): the family
            // in (Γ, i : Fin len). Computing layers only — it has no code
            // yet, and a code context is generated at layer c.
            18 if b > 0 && env.layer.computes() => {
                let len = gen_wt_nat(env, r, b / 2);
                let e = env.push_entry(rty(Type::Fin { len: Rc::clone(&len) }), Level::Zero);
                let (fam, l) = gen_wt_type(&e, r, b / 2);
                return (rty(Type::DVec { level: l.clone(), len, fam }), l);
            }
            // IWf (extension; docs/kernel/iwf-former-design.md §1.2): the arity and
            // output index under `x : S`, the child index under `x, i : Fin
            // n`, the index in Γ — each component a checked term of its type,
            // or the arm is a miss. Computing layers only, as DVec.
            19 if b > 0 && env.layer.computes() => {
                let (idx, li) = gen_wt_type(env, r, b / 3);
                let (shape, l) = gen_wt_type(env, r, b / 3);
                let e_x = env.push_entry(Rc::clone(&shape), l.clone());
                let arity = gen_wt_nat(&e_x, r, b / 3);
                let e_xi = e_x.push_entry(rty(Type::Fin { len: Rc::clone(&arity) }), Level::Zero);
                let (Some(out), Some(child), Some(index)) = (
                    gen_wt_term_at(&e_x, r, b / 3, &idx.shift_local(1), &li),
                    gen_wt_term_at(&e_xi, r, b / 3, &idx.shift_local(2), &li),
                    gen_wt_term_at(env, r, b / 3, &idx, &li),
                ) else {
                    continue;
                };
                let sig = IWfSig { level: l.clone(), idx_level: li.clone(), idx, shape, arity, out, child };
                let ty = Type::IWf { sig: Rc::new(sig), index };
                return (rty(ty), Level::max(l, li));
            }
            // M (extension; docs/kernel/kernel-coinduction-design.md §1.1): shapes
            // under `i : I`, positions under `i, s`, the child index a
            // checked term of `I` under `i, s, p`, the index in Γ.
            // Computing layers only, as IWf.
            20 if b > 0 && env.layer.computes() => {
                let (idx, li) = gen_wt_type(env, r, b / 4);
                let e_i = env.push_entry(Rc::clone(&idx), li.clone());
                let (shape, l) = gen_wt_type(&e_i, r, b / 4);
                let e_is = e_i.push_entry(Rc::clone(&shape), l.clone());
                let (pos, lp) = gen_wt_type(&e_is, r, b / 4);
                let e_isp = e_is.push_entry(Rc::clone(&pos), lp.clone());
                let (Some(next), Some(index)) = (
                    gen_wt_term_at(&e_isp, r, b / 4, &idx.shift_local(3), &li),
                    gen_wt_term_at(env, r, b / 4, &idx, &li),
                ) else {
                    continue;
                };
                let sig = MSig { level: l, pos_level: lp, idx_level: li, idx, shape, pos, next };
                let level = sig.family_level();
                return (rty(Type::M { sig: Rc::new(sig), index }), level);
            }
            _ => continue,
        }
    }
    (rty(Type::Nat), Level::Zero)
}

/// A well-typed `Nat` term: a small literal most of the time (so `Vec`/`Fin`
/// actually reduce), otherwise whatever the generator finds at `Nat`.
fn gen_wt_nat(env: &WtEnv, r: &mut Rng, b: u32) -> Rc<Term> {
    if b > 0 && r.below(3) == 0 {
        if let Some(t) = gen_wt_term_at(env, r, b, &Type::Nat, &Level::Zero) {
            return t;
        }
    }
    let mut t = Term::Zero;
    for _ in 0..r.below(3) {
        t = Term::Succ(rt(t));
    }
    rt(t)
}

/// Synthesize an encoding `⊢_i t : Ty l @ 1+l`, returning `(t, l)`.
pub fn gen_encoding(env: &WtEnv, r: &mut Rng, b: u32) -> (Rc<Term>, Level) {
    match r.below(15) {
        10 => {
            let l = gen_wf_level(env.univs, r, 1);
            (rt(Term::TmUnit { level: l.clone() }), l)
        }
        11 => {
            let l = gen_wf_level(env.univs, r, 1);
            (rt(Term::TmEmpty { level: l.clone() }), l)
        }
        12 => {
            let l = gen_wf_level(env.univs, r, 1);
            (rt(Term::TmSEmpty { level: l.clone() }), l)
        }
        13 if b > 0 => {
            // sEq encoding (extension; sprop-design §6): mirrors the Id arm.
            let (ty, l) = gen_encoding(env, r, b / 2);
            let el = Type::El { level: l.clone(), tm: Rc::clone(&ty) };
            let (Some(lhs), Some(rhs)) = (
                gen_wt_term_at(env, r, b / 2, &el, &l),
                gen_wt_term_at(env, r, b / 2, &el, &l),
            ) else {
                return (rt(Term::TmNat), Level::Zero);
            };
            (rt(Term::TmSEq { level: l.clone(), ty, lhs, rhs }), l)
        }
        0 => (rt(Term::TmNat), Level::Zero),
        1 => {
            let l = gen_wf_level(env.univs, r, 1);
            (rt(Term::TmTy(l.clone())), Level::succ(l))
        }
        2 if b > 0 => {
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
        3 if b > 0 => {
            // Id encoding (extension): endpoints checked at El of the
            // encoded type; fall back to Nat when uninhabitable.
            let (ty, l) = gen_encoding(env, r, b / 2);
            let el = Type::El { level: l.clone(), tm: Rc::clone(&ty) };
            let (Some(lhs), Some(rhs)) = (
                gen_wt_term_at(env, r, b / 2, &el, &l),
                gen_wt_term_at(env, r, b / 2, &el, &l),
            ) else {
                return (rt(Term::TmNat), Level::Zero);
            };
            (rt(Term::TmId { level: l.clone(), ty, lhs, rhs }), l)
        }
        4 if b > 0 => {
            // Σ encoding (extension): snd is an encoding in (Γ, x:El fst).
            let (fst, dl) = gen_encoding(env, r, b / 2);
            let e = env.push_entry(
                rty(Type::El { level: dl.clone(), tm: Rc::clone(&fst) }),
                dl.clone(),
            );
            let (snd, cl) = gen_encoding(&e, r, b / 2);
            (
                rt(Term::TmSigma { fst_level: dl.clone(), snd_level: cl.clone(), fst, snd }),
                Level::max(dl, cl),
            )
        }
        5 if b > 0 => {
            // Sum encoding (extension): non-dependent, both encodings in Γ.
            let (lhs, dl) = gen_encoding(env, r, b / 2);
            let (rhs, cl) = gen_encoding(env, r, b / 2);
            (
                rt(Term::TmSum { lhs_level: dl.clone(), rhs_level: cl.clone(), lhs, rhs }),
                Level::max(dl, cl),
            )
        }
        6 if b > 0 => {
            // W encoding (extension): pos is an encoding in (Γ, x:El shape),
            // mirroring the Σ arm.
            let (shape, dl) = gen_encoding(env, r, b / 2);
            let e = env.push_entry(
                rty(Type::El { level: dl.clone(), tm: Rc::clone(&shape) }),
                dl.clone(),
            );
            let (pos, cl) = gen_encoding(&e, r, b / 2);
            (
                rt(Term::TmW { shape_level: dl.clone(), pos_level: cl.clone(), shape, pos }),
                Level::max(dl, cl),
            )
        }
        7 if b > 0 => {
            // Vec encoding (extension, §6): element code plus a Nat length
            // in the same scope.
            let (elem, l) = gen_encoding(env, r, b / 2);
            let len = gen_wt_nat(env, r, b / 2);
            (rt(Term::TmVec { level: l.clone(), elem, len }), l)
        }
        8 => (rt(Term::TmFin { len: gen_wt_nat(env, r, b / 2) }), Level::Zero),
        9 if b > 0 => {
            // Wf encoding (extension, §6): the arity is a Nat term under
            // `x : El shape`, mirroring the W arm's positions.
            let (shape, l) = gen_encoding(env, r, b / 2);
            let e = env.push_entry(
                rty(Type::El { level: l.clone(), tm: Rc::clone(&shape) }),
                l.clone(),
            );
            let arity = gen_wt_nat(&e, r, b / 2);
            (rt(Term::TmWf { level: l.clone(), shape, arity }), l)
        }
        14 if b > 0 => {
            // M encoding (docs/kernel/kernel-m-codes-design.md §1): each piece an
            // encoding under `El` of the earlier ones; `next` is the bound
            // index `i` itself, which always fits.
            let (idx, li) = gen_encoding(env, r, b / 4);
            let el_i = rty(Type::El { level: li.clone(), tm: Rc::clone(&idx) });
            let Some(index) = gen_wt_term_at(env, r, b / 4, &el_i, &li) else {
                return (rt(Term::TmNat), Level::Zero);
            };
            let e_i = env.push_entry(Rc::clone(&el_i), li.clone());
            let (shape, l) = gen_encoding(&e_i, r, b / 4);
            let e_is = e_i.push_entry(
                rty(Type::El { level: l.clone(), tm: Rc::clone(&shape) }),
                l.clone(),
            );
            let (pos, lp) = gen_encoding(&e_is, r, b / 4);
            let family = Level::max(l.clone(), Level::max(lp.clone(), li.clone()));
            (
                rt(Term::TmM {
                    level: l,
                    pos_level: lp,
                    idx_level: li,
                    idx,
                    shape,
                    pos,
                    next: rt(v(2)),
                    index,
                }),
                family,
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
        CtxBase::Nil => SubstTail::Empty,
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
        // `⟨⟩^l : Unit^l` — the level comes from the *type*, which is the
        // whole reason the annotation exists.
        Type::Unit { level: l } => Some(rt(Term::Triv { level: l.clone() })),
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
        // refl inhabits Id when the endpoints convert — the checks() filter
        // below rejects the candidate otherwise.
        Type::Id { level: il, ty: ity, lhs, .. } => Some(rt(Term::Refl {
            level: il.clone(),
            ty: Rc::clone(ity),
            tm: Rc::clone(lhs),
        })),
        // pair@ / inl@ / inr@ inhabit the *un-reduced* target, which is
        // what makes the checked spellings **nest**: the field of a `pair@`
        // is itself checked at a `Sel { T, Fst }`, and if it is another
        // `pair@` the checker meets a description against an annotation.
        // That chain is where `docs/elaborator/intro-by-type-design.md` §3's mechanism
        // lives, and nothing in the synthesis arms produces it — they build
        // one `@` form over component-form fields.
        //
        // Off unless `at_forms`, so the bench fixtures keep measuring the
        // workload their baseline measured (the stage-1a finding).
        Type::Sigma { fst_level: dl, snd_level: cl, fst, snd }
            if b > 0 && env.at_forms && env.layer.computes() =>
        {
            let a = gen_wt_term_at(env, r, b / 2, fst, dl)?;
            let snd_at = snd.apply_local(&LocalSubst::id(&env.gamma).extended(Rc::clone(&a)));
            let bb = gen_wt_term_at(env, r, b / 2, &snd_at, cl)?;
            // Half unannotated: a checking position is exactly where the
            // elaborator writes no annotation (design §2.1).
            let ty = if r.below(2) == 0 { None } else { Some(rty(ty.clone())) };
            Some(rt(Term::PairAt { ty, fst: a, snd: bb }))
        }
        Type::Sum { lhs_level: dl, rhs_level: cl, lhs, rhs }
            if b > 0 && env.at_forms && env.layer.computes() =>
        {
            let right = r.below(2) == 1;
            let (summand, sl) = if right { (rhs, cl) } else { (lhs, dl) };
            let v = gen_wt_term_at(env, r, b / 2, summand, sl)?;
            let ty = if r.below(2) == 0 { None } else { Some(rty(ty.clone())) };
            Some(rt(if right {
                Term::InrAt { ty, val: v }
            } else {
                Term::InlAt { ty, val: v }
            }))
        }
        // pair inhabits Σ: a : S, then b : T[a/x].
        Type::Sigma { fst_level: dl, snd_level: cl, fst, snd } if b > 0 => {
            let a = gen_wt_term_at(env, r, b / 2, fst, dl)?;
            let snd_at = snd.apply_local(&LocalSubst::id(&env.gamma).extended(Rc::clone(&a)));
            let bb = gen_wt_term_at(env, r, b / 2, &snd_at, cl)?;
            Some(rt(Term::Pair {
                fst_level: dl.clone(),
                snd_level: cl.clone(),
                fst_ty: Rc::clone(fst),
                snd_ty: Rc::clone(snd),
                fst: a,
                snd: bb,
            }))
        }
        // inl/inr inhabit a sum: inject into the chosen summand (extension).
        Type::Sum { lhs_level: dl, rhs_level: cl, lhs, rhs } if b > 0 => {
            if r.below(2) == 0 {
                let v = gen_wt_term_at(env, r, b / 2, lhs, dl)?;
                Some(rt(Term::Inl {
                    lhs_level: dl.clone(),
                    rhs_level: cl.clone(),
                    lhs: Rc::clone(lhs),
                    rhs: Rc::clone(rhs),
                    val: v,
                }))
            } else {
                let v = gen_wt_term_at(env, r, b / 2, rhs, cl)?;
                Some(rt(Term::Inr {
                    lhs_level: dl.clone(),
                    rhs_level: cl.clone(),
                    lhs: Rc::clone(lhs),
                    rhs: Rc::clone(rhs),
                    val: v,
                }))
            }
        }
        // sup inhabits W: a : S, then f : Π(y : T[a/x]). W (extension).
        Type::W { shape_level: dl, pos_level: cl, shape, pos } if b > 0 => {
            let a = gen_wt_term_at(env, r, b / 2, shape, dl)?;
            let pos_at =
                pos.apply_local(&LocalSubst::id(&env.gamma).extended(Rc::clone(&a)));
            let lmax = Level::max(dl.clone(), cl.clone());
            let w = Type::W {
                shape_level: dl.clone(),
                pos_level: cl.clone(),
                shape: Rc::clone(shape),
                pos: Rc::clone(pos),
            };
            let f_ty = Type::Pi {
                dom_level: cl.clone(),
                cod_level: lmax.clone(),
                dom: rty(pos_at),
                cod: rty(w.shift_local(1)),
            };
            let f = gen_wt_term_at(env, r, b / 2, &f_ty, &Level::max(cl.clone(), lmax))?;
            Some(rt(Term::Sup {
                shape_level: dl.clone(),
                pos_level: cl.clone(),
                shape_ty: Rc::clone(shape),
                pos_ty: Rc::clone(pos),
                label: a,
                children: f,
            }))
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
        match r.below(if env.at_forms { 34 } else { 27 }) {
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
                // Half the time the checked spelling, whose Π is the one the
                // head infers (docs/elaborator/app-by-head-type-design.md). The head
                // here infers a syntactic Π or is a λ, so this is the
                // rule's fast path; arm 32 below is the reducing head.
                let app = if env.at_forms && env.layer.computes() && r.below(2) == 0 {
                    rt(Term::AppAt { fun: f, arg })
                } else {
                    rt(Term::App { fun: f, dom_level, cod_level, dom, cod, arg })
                };
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
                    rt(Term::GlobalTm { var: GlobalVar::index(x), subst }),
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
            18 if b > 0 => {
                // refl^l (S; t) : Id^l (S; t; t) (extension).
                let (ty, l) = gen_wt_type(env, r, b / 2);
                let Some(tm) = gen_wt_term_at(env, r, b / 2, &ty, &l) else { continue };
                return (
                    rt(Term::Refl {
                        level: l.clone(),
                        ty: Rc::clone(&ty),
                        tm: Rc::clone(&tm),
                    }),
                    rty(Type::Id { level: l.clone(), ty, lhs: Rc::clone(&tm), rhs: tm }),
                    l,
                );
            }
            19 if b > 0 => {
                // J with a constant motive over `refl` (extension): rhs is
                // the left endpoint, so the result type is the motive itself
                // and β stays common.
                let (ty, tl) = gen_wt_type(env, r, b / 2);
                let Some(a) = gen_wt_term_at(env, r, b / 2, &ty, &tl) else { continue };
                let (case, mty, ml) = guard(env.univs, gen_wt_term(env, r, b / 2));
                let refl = rt(Term::Refl {
                    level: tl.clone(),
                    ty: Rc::clone(&ty),
                    tm: Rc::clone(&a),
                });
                return (
                    rt(Term::J {
                        ty_level: tl,
                        motive_level: ml.clone(),
                        ty,
                        lhs: Rc::clone(&a),
                        motive: rty(mty.shift_local(2)),
                        case,
                        rhs: a,
                        proof: refl,
                    }),
                    mty,
                    ml,
                );
            }
            20 if b > 0 => {
                // pair^{l,l'}(x:S.T; a; b) : Σ^{l,l'}(x:S).T (extension).
                let (fst_ty, dl) = gen_wt_type(env, r, b / 2);
                let Some(a) = gen_wt_term_at(env, r, b / 2, &fst_ty, &dl) else { continue };
                let e = env.push_entry(Rc::clone(&fst_ty), dl.clone());
                let (snd_ty, cl) = gen_wt_type(&e, r, b / 2);
                let snd_at =
                    snd_ty.apply_local(&LocalSubst::id(&env.gamma).extended(Rc::clone(&a)));
                let Some(bb) = gen_wt_term_at(env, r, b / 2, &snd_at, &cl) else { continue };
                return (
                    rt(Term::Pair {
                        fst_level: dl.clone(),
                        snd_level: cl.clone(),
                        fst_ty: Rc::clone(&fst_ty),
                        snd_ty: Rc::clone(&snd_ty),
                        fst: a,
                        snd: bb,
                    }),
                    rty(Type::Sigma {
                        fst_level: dl.clone(),
                        snd_level: cl.clone(),
                        fst: fst_ty,
                        snd: snd_ty,
                    }),
                    Level::max(dl, cl),
                );
            }
            21 if b > 0 => {
                // fst^{l,l'}(x:S.T; p) : S (extension).
                let (fst_ty, dl) = gen_wt_type(env, r, b / 2);
                let e = env.push_entry(Rc::clone(&fst_ty), dl.clone());
                let (snd_ty, cl) = gen_wt_type(&e, r, b / 2);
                let sigma = rty(Type::Sigma {
                    fst_level: dl.clone(),
                    snd_level: cl.clone(),
                    fst: Rc::clone(&fst_ty),
                    snd: Rc::clone(&snd_ty),
                });
                let lmax = Level::max(dl.clone(), cl.clone());
                let Some(p) = gen_wt_term_at(env, r, b / 2, &sigma, &lmax) else { continue };
                return (
                    rt(Term::Fst {
                        fst_level: dl.clone(),
                        snd_level: cl.clone(),
                        fst_ty: Rc::clone(&fst_ty),
                        snd_ty,
                        pair: p,
                    }),
                    fst_ty,
                    dl,
                );
            }
            22 if b > 0 => {
                // snd^{l,l'}(x:S.T; p) : T[fst p/x] (extension).
                let (fst_ty, dl) = gen_wt_type(env, r, b / 2);
                let e = env.push_entry(Rc::clone(&fst_ty), dl.clone());
                let (snd_ty, cl) = gen_wt_type(&e, r, b / 2);
                let sigma = rty(Type::Sigma {
                    fst_level: dl.clone(),
                    snd_level: cl.clone(),
                    fst: Rc::clone(&fst_ty),
                    snd: Rc::clone(&snd_ty),
                });
                let lmax = Level::max(dl.clone(), cl.clone());
                let Some(p) = gen_wt_term_at(env, r, b / 2, &sigma, &lmax) else { continue };
                let fst_p = rt(Term::Fst {
                    fst_level: dl.clone(),
                    snd_level: cl.clone(),
                    fst_ty: Rc::clone(&fst_ty),
                    snd_ty: Rc::clone(&snd_ty),
                    pair: Rc::clone(&p),
                });
                let snd_at = snd_ty.apply_local(&LocalSubst::id(&env.gamma).extended(fst_p));
                return (
                    rt(Term::Snd {
                        fst_level: dl.clone(),
                        snd_level: cl.clone(),
                        fst_ty,
                        snd_ty,
                        pair: p,
                    }),
                    rty(snd_at),
                    cl,
                );
            }
            23 if b > 0 => {
                // inl^{l,l'}(A;B;a) : A + B (extension).
                let (lhs, dl) = gen_wt_type(env, r, b / 2);
                let (rhs, cl) = gen_wt_type(env, r, b / 2);
                let Some(a) = gen_wt_term_at(env, r, b / 2, &lhs, &dl) else { continue };
                return (
                    rt(Term::Inl {
                        lhs_level: dl.clone(),
                        rhs_level: cl.clone(),
                        lhs: Rc::clone(&lhs),
                        rhs: Rc::clone(&rhs),
                        val: a,
                    }),
                    rty(Type::Sum {
                        lhs_level: dl.clone(),
                        rhs_level: cl.clone(),
                        lhs,
                        rhs,
                    }),
                    Level::max(dl, cl),
                );
            }
            24 if b > 0 => {
                // inr^{l,l'}(A;B;b) : A + B (extension).
                let (lhs, dl) = gen_wt_type(env, r, b / 2);
                let (rhs, cl) = gen_wt_type(env, r, b / 2);
                let Some(bb) = gen_wt_term_at(env, r, b / 2, &rhs, &cl) else { continue };
                return (
                    rt(Term::Inr {
                        lhs_level: dl.clone(),
                        rhs_level: cl.clone(),
                        lhs: Rc::clone(&lhs),
                        rhs: Rc::clone(&rhs),
                        val: bb,
                    }),
                    rty(Type::Sum {
                        lhs_level: dl.clone(),
                        rhs_level: cl.clone(),
                        lhs,
                        rhs,
                    }),
                    Level::max(dl, cl),
                );
            }
            25 if b > 0 => {
                // case with a constant motive B (the synthesized value's
                // type): both branches at B, scrutinee an inhabitant of A + B.
                let (base, bty, bl) = guard(env.univs, gen_wt_term(env, r, b / 2));
                let motive = rty(bty.shift_local(1));
                let (lhs, dl) = gen_wt_type(env, r, b / 2);
                let (rhs, cl) = gen_wt_type(env, r, b / 2);
                let lmax = Level::max(dl.clone(), cl.clone());
                let sum = rty(Type::Sum {
                    lhs_level: dl.clone(),
                    rhs_level: cl.clone(),
                    lhs: Rc::clone(&lhs),
                    rhs: Rc::clone(&rhs),
                });
                let Some(scrut) = gen_wt_term_at(env, r, b / 2, &sum, &lmax) else {
                    continue;
                };
                let case_l = rt(base.shift_local(1));
                let case_r = rt(base.shift_local(1));
                return (
                    rt(Term::Case {
                        lhs_level: dl,
                        rhs_level: cl,
                        motive_level: bl.clone(),
                        lhs,
                        rhs,
                        motive,
                        case_l,
                        case_r,
                        scrut,
                    }),
                    bty,
                    bl,
                );
            }
            26 if b > 0 => {
                // elim_W with a constant motive B: the step lives at B in the
                // (a, f, ih) context, the scrutinee inhabits the W type.
                let (base, bty, bl) = guard(env.univs, gen_wt_term(env, r, b / 2));
                let motive = rty(bty.shift_local(1));
                let (shape, dl) = gen_wt_type(env, r, b / 2);
                let e = env.push_entry(Rc::clone(&shape), dl.clone());
                let (pos, cl) = gen_wt_type(&e, r, b / 2);
                let lmax = Level::max(dl.clone(), cl.clone());
                let w = rty(Type::W {
                    shape_level: dl.clone(),
                    pos_level: cl.clone(),
                    shape: Rc::clone(&shape),
                    pos: Rc::clone(&pos),
                });
                let Some(scrut) = gen_wt_term_at(env, r, b / 2, &w, &lmax) else {
                    continue;
                };
                let step = rt(base.shift_local(3));
                return (
                    rt(Term::ElimW {
                        shape_level: dl,
                        pos_level: cl,
                        motive_level: bl.clone(),
                        shape,
                        pos,
                        motive,
                        step,
                        scrut,
                    }),
                    bty,
                    bl,
                );
            }
            // -- the checked spellings (docs/elaborator/intro-by-type-design.md) -----
            //
            // Generated so the premise `T ⇝* former` is exercised in its
            // *non*-reflexive case: the annotation is `El ⌜Σ⌝` / `El ⌜+⌝`,
            // which decodes to the former rather than being it, so the rule
            // has to reduce and a consumer of the inferred type has to see
            // through one decode. A literal former as the annotation would
            // make every `@` form a rename of its component sibling and test
            // nothing the component form does not.
            //
            // Computing layers only: these forms do not exist at c
            // (design §2.3), and `gen_letbox_tm` generates under `Layer::Code`.
            27 if b > 0 && env.at_forms && env.layer.computes() => {
                // pair@(T; a; b) : T, T = El ⌜Σ(x:El A). El B⌝.
                let Some((ty, _sigma, fst_ty, snd_ty, dl, cl, lmax)) = gen_at_sigma(env, r, b)
                else {
                    continue;
                };
                let Some(a) = gen_wt_term_at(env, r, b / 2, &fst_ty, &dl) else { continue };
                let snd_at =
                    snd_ty.apply_local(&LocalSubst::id(&env.gamma).extended(Rc::clone(&a)));
                let Some(bb) = gen_wt_term_at(env, r, b / 2, &snd_at, &cl) else { continue };
                return (rt(Term::PairAt { ty: Some(Rc::clone(&ty)), fst: a, snd: bb }), ty, lmax);
            }
            28 | 29 if b > 0 && env.at_forms && env.layer.computes() => {
                // inl@/inr@(T; v) : T, T = El ⌜A + B⌝.
                let right = r.below(2) == 0;
                let (lhs_e, dl) = gen_encoding(env, r, b / 2);
                let (rhs_e, cl) = gen_encoding(env, r, b / 2);
                let lhs = rty(Type::El { level: dl.clone(), tm: Rc::clone(&lhs_e) });
                let rhs = rty(Type::El { level: cl.clone(), tm: Rc::clone(&rhs_e) });
                let lmax = Level::max(dl.clone(), cl.clone());
                let ty = rty(Type::El {
                    level: lmax.clone(),
                    tm: rt(Term::TmSum {
                        lhs_level: dl.clone(),
                        rhs_level: cl.clone(),
                        lhs: lhs_e,
                        rhs: rhs_e,
                    }),
                });
                let (summand, sl) = if right { (&rhs, &cl) } else { (&lhs, &dl) };
                let Some(v) = gen_wt_term_at(env, r, b / 2, summand, sl) else { continue };
                let t = if right {
                    Term::InrAt { ty: Some(Rc::clone(&ty)), val: v }
                } else {
                    Term::InlAt { ty: Some(Rc::clone(&ty)), val: v }
                };
                return (rt(t), ty, lmax);
            }
            30 | 31 if b > 0 && env.at_forms && env.layer.computes() => {
                // fst@/snd@(p) : S resp. U[fst@(p)/x]; the receiver infers.
                let Some((ty, sigma, fst_ty, snd_ty, dl, cl, lmax)) = gen_at_sigma(env, r, b)
                else {
                    continue;
                };
                // The pair is generated at the *decoded* Σ, so checking it
                // against `T` is a real `Sigma`-against-`El⌜Sigma⌝` query —
                // the head pair the owning issue's 2026-09-18 trace found at
                // 96 % of a record tower's misses.
                // Or it is a `pair@^{T}`, so the receiver infers `T` and the
                // Σ is viewed out of the annotation. An unannotated intro is
                // not inferable and cannot be a receiver.
                let p = if r.below(2) == 0 {
                    let Some(a) = gen_wt_term_at(env, r, b / 2, &fst_ty, &dl) else { continue };
                    let snd_at =
                        snd_ty.apply_local(&LocalSubst::id(&env.gamma).extended(Rc::clone(&a)));
                    let Some(bb) = gen_wt_term_at(env, r, b / 2, &snd_at, &cl) else { continue };
                    rt(Term::PairAt { ty: Some(ty), fst: a, snd: bb })
                } else {
                    let Some(p) = gen_wt_term_at(env, r, b / 2, &sigma, &lmax) else { continue };
                    if matches!(&*p, Term::PairAt { ty: None, .. }) {
                        continue;
                    }
                    p
                };
                if r.below(2) == 0 {
                    return (rt(Term::FstAt { pair: p }), fst_ty, dl);
                }
                let fst_p = rt(Term::FstAt { pair: Rc::clone(&p) });
                let snd_at = snd_ty.apply_local(&LocalSubst::id(&env.gamma).extended(fst_p));
                return (rt(Term::SndAt { pair: p }), rty(snd_at), cl);
            }
            32 | 33 if b > 0 && env.at_forms && env.layer.computes() => {
                // app@ over a head whose type needs *reduction* to show its
                // Π (docs/elaborator/app-by-head-type-design.md §3.1's second line): a
                // function stored as a record field, `fst@(pair@^{T}(f; c))`
                // with T = El ⌜Σ(g: El ⌜Π(x: El A). El B⌝). El C⌝. The head
                // infers `Sel{T, Fst}`, whose Π is behind two decodes and a
                // selection, so the result is a `Sel::App` description.
                let (a_e, al) = gen_encoding(env, r, b / 2);
                let a_ty = rty(Type::El { level: al.clone(), tm: Rc::clone(&a_e) });
                let ea = env.push_entry(Rc::clone(&a_ty), al.clone());
                let (b_e, bl) = gen_encoding(&ea, r, b / 2);
                let pi_l = Level::max(al.clone(), bl.clone());
                let pi_e = rt(Term::TmPi {
                    dom_level: al.clone(),
                    cod_level: bl.clone(),
                    dom: Rc::clone(&a_e),
                    cod: Rc::clone(&b_e),
                });
                let fn_ty = rty(Type::El { level: pi_l.clone(), tm: Rc::clone(&pi_e) });
                let ef = env.push_entry(Rc::clone(&fn_ty), pi_l.clone());
                let (c_e, cl) = gen_encoding(&ef, r, b / 2);
                let lmax = Level::max(pi_l.clone(), cl.clone());
                let ty = rty(Type::El {
                    level: lmax,
                    tm: rt(Term::TmSigma {
                        fst_level: pi_l.clone(),
                        snd_level: cl.clone(),
                        fst: pi_e,
                        snd: Rc::clone(&c_e),
                    }),
                });
                let Some(g) = gen_wt_term_at(env, r, b / 2, &fn_ty, &pi_l) else { continue };
                let c_at = Type::El {
                    level: cl.clone(),
                    tm: rt(c_e.apply_local(&LocalSubst::id(&env.gamma).extended(Rc::clone(&g)))),
                };
                let Some(c) = gen_wt_term_at(env, r, b / 2, &c_at, &cl) else { continue };
                let head = rt(Term::FstAt { pair: rt(Term::PairAt { ty: Some(ty), fst: g, snd: c }) });
                let Some(arg) = gen_wt_term_at(env, r, b / 2, &a_ty, &al) else { continue };
                let res = Type::El {
                    level: bl.clone(),
                    tm: rt(b_e.apply_local(&LocalSubst::id(&env.gamma).extended(Rc::clone(&arg)))),
                };
                let app = rt(Term::AppAt { fun: head, arg });
                if !env.checks(&app, &res, &bl) {
                    continue;
                }
                return (app, rty(res), bl);
            }
            _ => continue,
        }
    }
    (rt(Term::Zero), rty(Type::Nat), Level::Zero)
}

/// A Σ behind one decode, for the checked spellings' generators: the
/// annotation `El ⌜Σ(x:El A). El B⌝`, the `Type::Sigma` it decodes to, its two
/// components and their levels.
#[allow(clippy::type_complexity)]
fn gen_at_sigma(
    env: &WtEnv,
    r: &mut Rng,
    b: u32,
) -> Option<(Rc<Type>, Rc<Type>, Rc<Type>, Rc<Type>, Level, Level, Level)> {
    let (fst_e, dl) = gen_encoding(env, r, b / 2);
    let fst_ty = rty(Type::El { level: dl.clone(), tm: Rc::clone(&fst_e) });
    let e = env.push_entry(Rc::clone(&fst_ty), dl.clone());
    let (snd_e, cl) = gen_encoding(&e, r, b / 2);
    let snd_ty = rty(Type::El { level: cl.clone(), tm: Rc::clone(&snd_e) });
    let lmax = Level::max(dl.clone(), cl.clone());
    let ty = rty(Type::El {
        level: lmax.clone(),
        tm: rt(Term::TmSigma {
            fst_level: dl.clone(),
            snd_level: cl.clone(),
            fst: fst_e,
            snd: snd_e,
        }),
    });
    let sigma = rty(Type::Sigma {
        fst_level: dl.clone(),
        snd_level: cl.clone(),
        fst: Rc::clone(&fst_ty),
        snd: Rc::clone(&snd_ty),
    });
    Some((ty, sigma, fst_ty, snd_ty, dl, cl, lmax))
}

/// `letbox` over freshly boxed code. Half the time the motive is constant
/// (a synthesized inhabitant's type); otherwise it is the code's own
/// contextual type and the body re-boxes the bound global — exercising
/// checking-only `box` bodies and the `M[box u^id/x]` substitution.
fn gen_letbox_tm(env: &WtEnv, r: &mut Rng, b: u32) -> (Rc<Term>, Rc<Type>, Level) {
    let delta = gen_wt_ctx(env, r, b / 2, Layer::Code);
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
    let delta = gen_wt_ctx(env, r, b / 2, Layer::Code);
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
const BRANCH_DIMS: [(u32, u32, u32, bool, bool); 66] = [
    (0, 1, 0, false, false), // ty_nat
    (2, 3, 2, false, true),  // ty_pi
    (1, 1, 0, false, false), // ty_ty
    (1, 2, 1, false, false), // ty_el (innermost local is a *term*-motive call)
    (1, 4, 3, false, false), // ty_id (innermost local is a *term*-motive call)
    (2, 3, 2, false, true),  // ty_sigma
    (1, 1, 0, false, false), // ty_unit
    (1, 1, 0, false, false), // ty_empty
    (1, 3, 0, true, false),  // tm_var
    (0, 1, 0, true, false),  // tm_nat
    (2, 3, 2, true, true),   // tm_pi
    (1, 1, 0, true, false),  // tm_ty
    (0, 1, 0, true, false),  // tm_zero
    (0, 2, 1, true, true),   // tm_succ
    (1, 5, 4, true, true),   // tm_elim_nat
    (2, 4, 2, true, true),   // tm_lam
    (2, 5, 4, true, true),   // tm_app
    (1, 4, 3, true, true),   // tm_id
    (1, 3, 2, true, true),   // tm_refl
    (2, 7, 6, true, true),   // tm_j
    (2, 3, 2, true, true),   // tm_sigma
    (2, 5, 4, true, true),   // tm_pair
    (2, 4, 3, true, true),   // tm_fst
    (2, 4, 3, true, true),   // tm_snd
    (1, 1, 0, true, false),  // tm_unit
    (1, 1, 0, true, false),  // tm_empty
    (1, 1, 0, true, false),  // tm_triv
    (2, 3, 2, true, true),   // tm_elim_empty (ℓ motive, ℓ' scrutinee; innermost local is a term-motive call)
    (2, 3, 2, false, true),  // ty_sum
    (2, 3, 2, true, true),   // tm_sum
    (2, 4, 3, true, true),   // tm_inl
    (2, 4, 3, true, true),   // tm_inr
    (3, 7, 6, true, true),   // tm_case (innermost local is a term-motive call)
    (2, 3, 2, false, true),  // ty_w
    (2, 3, 2, true, true),   // tm_w
    (2, 5, 4, true, true),   // tm_sup
    (3, 6, 5, true, true),   // tm_elim_w (innermost local is a term-motive call)
    (1, 3, 2, false, false), // ty_vec (innermost local is a term-motive call)
    (1, 3, 2, true, true),   // tm_vec
    (0, 2, 1, false, false), // ty_fin (innermost local is a term-motive call)
    (0, 2, 1, true, true),   // tm_fin
    (1, 3, 2, false, false), // ty_wf (innermost local is a term-motive call)
    (1, 3, 2, true, true),   // tm_wf
    (1, 5, 4, true, true),   // tm_supf
    (2, 6, 5, true, true),   // tm_elim_wf (innermost local is a term-motive call)
    (1, 4, 3, false, false), // ty_seq (innermost local is a term-motive call)
    (1, 4, 3, true, true),   // tm_seq
    (1, 1, 0, false, false), // ty_sempty
    (1, 1, 0, true, false),  // tm_sempty
    (1, 3, 2, true, true),   // tm_srefl
    (2, 3, 2, true, true),   // tm_elim_sempty (innermost local is a term-motive call)
    (1, 2, 1, false, true),  // ty_squash
    (1, 2, 1, true, true),   // tm_squash
    (1, 3, 2, true, true),   // tm_squash_in
    (2, 5, 4, true, true),   // tm_elim_squash
    (1, 2, 1, true, true),   // tm_unsquash_empty
    (3, 6, 5, false, false), // ty_m (innermost local is a term-motive call)
    (3, 6, 5, true, true),   // tm_m
    (4, 9, 8, true, true),   // tm_corec
    (3, 7, 6, true, true),   // tm_out
    (1, 3, 2, false, true),  // ty_dvec
    (1, 3, 2, true, true),   // tm_dvec
    (2, 7, 6, false, false), // ty_iwf (innermost local is a term-motive call)
    (2, 7, 6, true, true),   // tm_iwf
    (2, 8, 7, true, true),   // tm_sup_i
    (3, 10, 9, true, true),  // tm_elim_iwf
];

/// A Γ-variable whose WHNF type is a contextual type matching `tm_variant`:
/// `(index, Δ, T?, l)`. Δ and T live in their own scopes (local contexts
/// never reference the ambient Γ), so they are usable as recursor header
/// fields directly.
fn find_code_var(
    env: &WtEnv,
    r: &mut Rng,
    tm_variant: bool,
) -> Option<(u32, LocalCtx, Option<Rc<Type>>, Level)> {
    let n = env.gamma.entries.len() as u32;
    if n == 0 {
        return None;
    }
    let start = r.below(n);
    for k in 0..n {
        let x = (start + k) % n;
        let i = env.gamma.entries.len() - 1 - x as usize;
        let ty = env.gamma.entries[i].ty.shift_local(x + 1);
        let Ok(w) = whnf_type(&ty, &env.gamma, FUEL) else { continue };
        match w {
            Type::CodeTy { ctx, level } if !tm_variant => {
                return Some((x, ctx, None, level));
            }
            Type::CodeTm { ctx, ty, level } if tm_variant => {
                return Some((x, ctx, Some(ty), level));
            }
            _ => {}
        }
    }
    None
}

/// A code recursor with constant motives `M₁ = typeof(m₁)`, `M₂ =
/// typeof(m₂)`: every branch is the matching inhabitant weakened by its
/// telescope depths (or `Var(0)` where the innermost recursive call has the
/// right motive). `tm_variant` selects `elim^Trm` over `elim^Typ`. When a
/// Γ-variable of matching contextual type exists, the scrutinee is sometimes
/// that variable instead of freshly boxed code — the recursor is then
/// *neutral*, so conversion's branchwise comparison path gets exercised, not
/// just β-firing.
fn gen_const_rec(
    env: &WtEnv,
    r: &mut Rng,
    b: u32,
    tm_variant: bool,
) -> (Rc<Term>, Rc<Type>, Level) {
    let neutral = if r.below(3) == 0 { find_code_var(env, r, tm_variant) } else { None };
    let (m1t, m1ty, l1) = guard(env.univs, gen_wt_term(env, r, b / 4));
    let (m2t, m2ty, l2) = guard(env.univs, gen_wt_term(env, r, b / 4));
    let motives = Rc::new(Motives {
        ty_motive: rty(m1ty.shift_univ(1).shift_global(1).shift_local(1)),
        tm_motive: rty(m2ty.shift_univ(1).shift_global(2).shift_local(1)),
    });
    let mut bs: Vec<Rc<Term>> = Vec::with_capacity(66);
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
        ty_id: bs[4].clone(),
        ty_sigma: bs[5].clone(),
        ty_unit: bs[6].clone(),
        ty_empty: bs[7].clone(),
        tm_var: bs[8].clone(),
        tm_nat: bs[9].clone(),
        tm_pi: bs[10].clone(),
        tm_ty: bs[11].clone(),
        tm_zero: bs[12].clone(),
        tm_succ: bs[13].clone(),
        tm_elim_nat: bs[14].clone(),
        tm_lam: bs[15].clone(),
        tm_app: bs[16].clone(),
        tm_id: bs[17].clone(),
        tm_refl: bs[18].clone(),
        tm_j: bs[19].clone(),
        tm_sigma: bs[20].clone(),
        tm_pair: bs[21].clone(),
        tm_fst: bs[22].clone(),
        tm_snd: bs[23].clone(),
        tm_unit: bs[24].clone(),
        tm_empty: bs[25].clone(),
        tm_triv: bs[26].clone(),
        tm_elim_empty: bs[27].clone(),
        ty_sum: bs[28].clone(),
        tm_sum: bs[29].clone(),
        tm_inl: bs[30].clone(),
        tm_inr: bs[31].clone(),
        tm_case: bs[32].clone(),
        ty_w: bs[33].clone(),
        tm_w: bs[34].clone(),
        tm_sup: bs[35].clone(),
        tm_elim_w: bs[36].clone(),
        ty_vec: bs[37].clone(),
        tm_vec: bs[38].clone(),
        ty_fin: bs[39].clone(),
        tm_fin: bs[40].clone(),
        ty_wf: bs[41].clone(),
        tm_wf: bs[42].clone(),
        tm_supf: bs[43].clone(),
        tm_elim_wf: bs[44].clone(),
        ty_seq: bs[45].clone(),
        tm_seq: bs[46].clone(),
        ty_sempty: bs[47].clone(),
        tm_sempty: bs[48].clone(),
        tm_srefl: bs[49].clone(),
        tm_elim_sempty: bs[50].clone(),
        ty_squash: bs[51].clone(),
        tm_squash: bs[52].clone(),
        tm_squash_in: bs[53].clone(),
        tm_elim_squash: bs[54].clone(),
        tm_unsquash_empty: bs[55].clone(),
        ty_m: bs[56].clone(),
        tm_m: bs[57].clone(),
        tm_corec: bs[58].clone(),
        tm_out: bs[59].clone(),
        ty_dvec: bs[60].clone(),
        tm_dvec: bs[61].clone(),
        ty_iwf: bs[62].clone(),
        tm_iwf: bs[63].clone(),
        tm_sup_i: bs[64].clone(),
        tm_elim_iwf: bs[65].clone(),
    });
    if tm_variant {
        let (scrut, delta, cty, cl) = match neutral {
            Some((x, ctx, Some(cty), cl)) => (rt(v(x)), ctx, cty, cl),
            _ => {
                let delta = gen_wt_ctx(env, r, b / 4, Layer::Code);
                let ce = env.in_ctx(delta.clone(), Layer::Code);
                let (tc, cty, cl) = gen_wt_term(&ce, r, b / 4);
                (rt(Term::BoxTm(tc)), delta, cty, cl)
            }
        };
        (
            rt(Term::ElimCodeTm {
                ty_motive_level: l1,
                tm_motive_level: l2.clone(),
                motives,
                branches,
                code_level: cl,
                ctx: delta,
                ty: cty,
                scrut,
            }),
            m2ty,
            l2,
        )
    } else {
        let (scrut, delta, cl) = match neutral {
            Some((x, ctx, None, cl)) => (rt(v(x)), ctx, cl),
            _ => {
                let delta = gen_wt_ctx(env, r, b / 4, Layer::Code);
                let ce = env.in_ctx(delta.clone(), Layer::Code);
                let (cty, cl) = gen_wt_type(&ce, r, b / 4);
                (rt(Term::BoxTy(cty)), delta, cl)
            }
        };
        (
            rt(Term::ElimCodeTy {
                ty_motive_level: l1.clone(),
                tm_motive_level: l2,
                motives,
                branches,
                code_level: cl,
                ctx: delta,
                scrut,
            }),
            m1ty,
            l1,
        )
    }
}

// -------------------------------------------------------------------------
// Convertible perturbations (issues/kernel-conv-pair-properties.md)
// -------------------------------------------------------------------------

/// A term structurally distinct from `t` but convertible to it at
/// `ty @ l`, built by a root-level expansion: a β-redex wrap, `elim_Nat` on
/// a numeral with a constant motive, `letbox` over fresh code, or
/// η-expansion at the WHNF of `ty`. Root-only on purpose: box bodies
/// compare *syntactically*, so perturbing under a `box` breaks
/// convertibility. `None` only when no strategy is applicable (an ω-level
/// term whose type is not a `ΠΠ`, which the generator never produces).
///
/// Results are not checker-filtered — callers assert `check_term` passes,
/// keeping a perturbation bug distinct from a conversion bug.
pub fn perturb_conv(
    env: &WtEnv,
    r: &mut Rng,
    t: &Rc<Term>,
    ty: &Rc<Type>,
    l: &Level,
) -> Option<Rc<Term>> {
    let w = whnf_type(ty, &env.gamma, FUEL).ok()?;
    let meta = env.layer == Layer::Meta;
    // ω-level results cannot be re-stated as λ/elim/letbox annotations.
    let finite = l.well_formed(env.univs);
    let mut arms: Vec<u32> = vec![];
    if finite {
        arms.extend([0, 1]);
        if meta {
            arms.push(2);
        }
    }
    match &w {
        Type::Pi { .. } => arms.push(3),
        Type::UPi { .. } if meta => arms.push(4),
        Type::CtxPi { .. } | Type::TyPi { .. } if meta => arms.push(5),
        _ => {}
    }
    if arms.is_empty() {
        return None;
    }
    let t2 = match arms[r.below(arms.len() as u32) as usize] {
        // β: app(λ(x : Nat). t↑; n) — one β-step from t.
        0 => Term::App {
            fun: rt(Term::Lam {
                dom_level: Level::Zero,
                cod_level: l.clone(),
                dom: rty(Type::Nat),
                body: rt(t.shift_local(1)),
            }),
            dom_level: Level::Zero,
            cod_level: l.clone(),
            dom: rty(Type::Nat),
            cod: rty(ty.shift_local(1)),
            arg: gen_nat(env, r),
        },
        // elim_Nat with the constant motive T: computes to t on a numeral.
        1 => {
            let mut scrut = Term::Zero;
            for _ in 0..r.below(3) {
                scrut = Term::Succ(rt(scrut));
            }
            let step = if r.below(2) == 0 { rt(v(0)) } else { rt(t.shift_local(2)) };
            Term::ElimNat {
                level: l.clone(),
                motive: rty(ty.shift_local(1)),
                base: Rc::clone(t),
                step,
                scrut: rt(scrut),
            }
        }
        // letbox over fresh boxed code with the constant motive T.
        2 => {
            let delta = gen_wt_ctx(env, r, 2, Layer::Code);
            let ce = env.in_ctx(delta.clone(), Layer::Code);
            let (tc, cty, cl) = gen_wt_term(&ce, r, 2);
            Term::LetBoxTm {
                motive_level: l.clone(),
                code_level: cl,
                ctx: delta,
                ty: cty,
                motive: rty(ty.shift_local(1)),
                body: rt(t.shift_global(1)),
                scrut: rt(Term::BoxTm(tc)),
            }
        }
        // η at Π: λ(x : S). app(t↑; x). The cod annotation moves under the
        // App binder exactly as in conv.rs's η rule: Π's variable ↦ Var 0,
        // Γ weakens by 2 (λ binder + App's cod binder).
        3 => {
            let Type::Pi { dom_level, cod_level, dom, cod } = &w else { unreachable!() };
            let cod_ann = rty(cod.apply_local(
                &LocalSubst::id(&env.gamma).shift_local(2).extended(rt(v(0))),
            ));
            Term::Lam {
                dom_level: dom_level.clone(),
                cod_level: cod_level.clone(),
                dom: Rc::clone(dom),
                body: rt(Term::App {
                    fun: rt(t.shift_local(1)),
                    dom_level: dom_level.clone(),
                    cod_level: cod_level.clone(),
                    dom: rty(dom.shift_local(1)),
                    cod: cod_ann,
                    arg: rt(v(0)),
                }),
            }
        }
        // η at ΠΠ: Λ ℓ⃗. t↑ $ ℓ⃗ — the only strategy for ω-level terms.
        4 => {
            let Type::UPi { num_vars, level, .. } = &w else { unreachable!() };
            let n = *num_vars;
            Term::ULam {
                num_vars: n,
                level: level.clone(),
                body: rt(Term::UApp {
                    fun: rt(t.shift_univ(n)),
                    levels: (0..n).rev().map(|i| Level::Var(UnivVar(i))).collect(),
                }),
            }
        }
        // η at ⇒: context / type meta-functions.
        _ => match &w {
            Type::CtxPi { level, .. } => Term::CtxLam {
                level: level.clone(),
                body: rt(Term::CtxApp { fun: rt(t.shift_global(1)), ctx: g_ctx(0) }),
            },
            Type::TyPi { ctx, arg_level, body_level, .. } => Term::TyLam {
                ctx: ctx.clone(),
                arg_level: arg_level.clone(),
                body_level: body_level.clone(),
                body: rt(Term::TyApp {
                    fun: rt(t.shift_global(1)),
                    arg: rty(gty(0, &ctx.shift_global(1))),
                }),
            },
            _ => unreachable!(),
        },
    };
    Some(rt(t2))
}

// -------------------------------------------------------------------------
// Neutral recursors at constant Nat motives
// -------------------------------------------------------------------------

/// A *neutral* code recursor at type `Nat @ 0`: both motives are the
/// constant `Nat` and the scrutinee is a Γ-variable (`Var 0`, pushed by
/// [`gen_nat_rec`]), so conversion cannot fire β and must compare the 13
/// branches pairwise under their telescopes (`rec_ca`). Every branch type
/// collapses to `Nat`, so *closed* `Nat` terms (numerals and wraps thereof)
/// are well-typed branch bodies under every telescope — callers build twins
/// differing in chosen branches via [`NatRec::build`].
pub struct NatRec {
    /// The ambient scope, layer m, with the scrutinee entry pushed last.
    pub env: WtEnv,
    tm_variant: bool,
    ctx: LocalCtx,
    ty: Option<Rc<Type>>,
    code_level: Level,
}

/// Extend `base` (forced to layer m) with a `□`-typed entry and describe the
/// neutral recursor over it. `tm_variant` selects `elim^Trm` over `elim^Typ`.
pub fn gen_nat_rec(base: &WtEnv, r: &mut Rng, tm_variant: bool) -> NatRec {
    let mut env = base.clone();
    env.layer = Layer::Meta;
    let ctx = gen_wt_ctx(&env, r, 2, Layer::Code);
    let (entry, ty, code_level) = if tm_variant {
        let ce = env.in_ctx(ctx.clone(), Layer::Code);
        let (cty, cl) = gen_wt_type(&ce, r, 2);
        (
            Type::CodeTm { ctx: ctx.clone(), ty: Rc::clone(&cty), level: cl.clone() },
            Some(cty),
            cl,
        )
    } else {
        let cl = gen_wf_level(env.univs, r, 1);
        (Type::CodeTy { ctx: ctx.clone(), level: cl.clone() }, None, cl)
    };
    // Contextual types live at universe 0. Δ and the code type never mention
    // Γ's locals, so pushing the entry needs no shifts in the header fields.
    let env = env.push_entry(rty(entry), Level::Zero);
    NatRec { env, tm_variant, ctx, ty, code_level }
}

impl NatRec {
    /// The recursor over `Var 0` with the given branch bodies, in
    /// [`Branches`] field order. Checks at `Nat @ 0` in `self.env`.
    pub fn build(&self, bs: &[Rc<Term>; 66]) -> Rc<Term> {
        let motives = Rc::new(Motives {
            ty_motive: rty(Type::Nat),
            tm_motive: rty(Type::Nat),
        });
        let branches = Rc::new(Branches {
            ty_nat: bs[0].clone(),
            ty_pi: bs[1].clone(),
            ty_ty: bs[2].clone(),
            ty_el: bs[3].clone(),
            ty_id: bs[4].clone(),
            ty_sigma: bs[5].clone(),
            ty_unit: bs[6].clone(),
            ty_empty: bs[7].clone(),
            tm_var: bs[8].clone(),
            tm_nat: bs[9].clone(),
            tm_pi: bs[10].clone(),
            tm_ty: bs[11].clone(),
            tm_zero: bs[12].clone(),
            tm_succ: bs[13].clone(),
            tm_elim_nat: bs[14].clone(),
            tm_lam: bs[15].clone(),
            tm_app: bs[16].clone(),
            tm_id: bs[17].clone(),
            tm_refl: bs[18].clone(),
            tm_j: bs[19].clone(),
            tm_sigma: bs[20].clone(),
            tm_pair: bs[21].clone(),
            tm_fst: bs[22].clone(),
            tm_snd: bs[23].clone(),
            tm_unit: bs[24].clone(),
            tm_empty: bs[25].clone(),
            tm_triv: bs[26].clone(),
            tm_elim_empty: bs[27].clone(),
            ty_sum: bs[28].clone(),
            tm_sum: bs[29].clone(),
            tm_inl: bs[30].clone(),
            tm_inr: bs[31].clone(),
            tm_case: bs[32].clone(),
            ty_w: bs[33].clone(),
            tm_w: bs[34].clone(),
            tm_sup: bs[35].clone(),
            tm_elim_w: bs[36].clone(),
            ty_vec: bs[37].clone(),
            tm_vec: bs[38].clone(),
            ty_fin: bs[39].clone(),
            tm_fin: bs[40].clone(),
            ty_wf: bs[41].clone(),
            tm_wf: bs[42].clone(),
            tm_supf: bs[43].clone(),
            tm_elim_wf: bs[44].clone(),
            ty_seq: bs[45].clone(),
            tm_seq: bs[46].clone(),
            ty_sempty: bs[47].clone(),
            tm_sempty: bs[48].clone(),
            tm_srefl: bs[49].clone(),
            tm_elim_sempty: bs[50].clone(),
            ty_squash: bs[51].clone(),
            tm_squash: bs[52].clone(),
            tm_squash_in: bs[53].clone(),
            tm_elim_squash: bs[54].clone(),
            tm_unsquash_empty: bs[55].clone(),
            ty_m: bs[56].clone(),
            tm_m: bs[57].clone(),
            tm_corec: bs[58].clone(),
            tm_out: bs[59].clone(),
            ty_dvec: bs[60].clone(),
            tm_dvec: bs[61].clone(),
            ty_iwf: bs[62].clone(),
            tm_iwf: bs[63].clone(),
            tm_sup_i: bs[64].clone(),
            tm_elim_iwf: bs[65].clone(),
        });
        rt(if self.tm_variant {
            Term::ElimCodeTm {
                ty_motive_level: Level::Zero,
                tm_motive_level: Level::Zero,
                motives,
                branches,
                code_level: self.code_level.clone(),
                ctx: self.ctx.clone(),
                ty: Rc::clone(self.ty.as_ref().expect("tm variant carries a code type")),
                scrut: rt(v(0)),
            }
        } else {
            Term::ElimCodeTy {
                ty_motive_level: Level::Zero,
                tm_motive_level: Level::Zero,
                motives,
                branches,
                code_level: self.code_level.clone(),
                ctx: self.ctx.clone(),
                scrut: rt(v(0)),
            }
        })
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
    let g6 = g_ctx(6);
    let gx_typi = ext(&g2, gty(1, &g2), lv(1));
    let gx_app = ext(&g4, gty(3, &g4), lv(1));
    let gx_tmpi = ext(&g2, Type::El { level: lv(1), tm: rt(gtm(1, &g2)) }, lv(1));
    let gx_lam = ext(&g3, gty(2, &g3), lv(1));
    let gx_nat = ext(&g4, Type::Nat, Level::Zero);
    let u_m = Type::GlobalTy { var: GlobalVar::index(3), subst: LocalSubst::id(&gx_nat) };
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
        // -- extension branches (kernel-v1-extensions) --
        ty_id: rt(Term::BoxTy(rty(Type::Id {
            level: lv(0),
            ty: rty(gty(2, &g3)),
            lhs: rt(gtm(1, &g3)),
            rhs: rt(gtm(0, &g3)),
        }))),
        ty_sigma: rt(Term::BoxTy(rty(Type::Sigma {
            fst_level: lv(1),
            snd_level: lv(0),
            fst: rty(gty(1, &g2)),
            snd: rty(gty(0, &gx_typi)),
        }))),
        tm_id: rt(Term::BoxTm(rt(Term::TmId {
            level: lv(0),
            ty: rt(gtm(2, &g3)),
            lhs: rt(gtm(1, &g3)),
            rhs: rt(gtm(0, &g3)),
        }))),
        tm_refl: rt(Term::BoxTm(rt(Term::Refl {
            level: lv(0),
            ty: rty(gty(1, &g2)),
            tm: rt(gtm(0, &g2)),
        }))),
        tm_j: {
            let gy = ext(&g6, gty(5, &g6), lv(1));
            let p_ty = Type::Id {
                level: lv(1),
                ty: rty(gty(5, &g6).shift_local(1)),
                lhs: rt(gtm(4, &g6).shift_local(1)),
                rhs: rt(v(0)),
            };
            let gyp = ext(&gy, p_ty, lv(1));
            rt(Term::BoxTm(rt(Term::J {
                ty_level: lv(1),
                motive_level: lv(0),
                ty: rty(gty(5, &g6)),
                lhs: rt(gtm(4, &g6)),
                motive: rty(Type::GlobalTy {
                    var: GlobalVar::index(3),
                    subst: LocalSubst::id(&gyp),
                }),
                case: rt(gtm(2, &g6)),
                rhs: rt(gtm(1, &g6)),
                proof: rt(gtm(0, &g6)),
            })))
        },
        tm_sigma: {
            let gx = ext(&g2, Type::El { level: lv(1), tm: rt(gtm(1, &g2)) }, lv(1));
            rt(Term::BoxTm(rt(Term::TmSigma {
                fst_level: lv(1),
                snd_level: lv(0),
                fst: rt(gtm(1, &g2)),
                snd: rt(gtm(0, &gx)),
            })))
        },
        tm_pair: rt(Term::BoxTm(rt(Term::Pair {
            fst_level: lv(1),
            snd_level: lv(0),
            fst_ty: rty(gty(3, &g4)),
            snd_ty: rty(gty(2, &gx_app)),
            fst: rt(gtm(1, &g4)),
            snd: rt(gtm(0, &g4)),
        }))),
        tm_fst: rt(Term::BoxTm(rt(Term::Fst {
            fst_level: lv(1),
            snd_level: lv(0),
            fst_ty: rty(gty(2, &g3)),
            snd_ty: rty(gty(1, &gx_lam)),
            pair: rt(gtm(0, &g3)),
        }))),
        tm_snd: rt(Term::BoxTm(rt(Term::Snd {
            fst_level: lv(1),
            snd_level: lv(0),
            fst_ty: rty(gty(2, &g3)),
            snd_ty: rty(gty(1, &gx_lam)),
            pair: rt(gtm(0, &g3)),
        }))),
        // Each binds ℓ now (docs/kernel/unit-empty-level-indexing.md §3), so the
        // identity arm reconstructs at `ℓ` rather than at 0.
        ty_unit: rt(Term::BoxTy(rty(Type::Unit { level: lv(0) }))),
        ty_empty: rt(Term::BoxTy(rty(Type::Empty { level: lv(0) }))),
        tm_unit: rt(Term::BoxTm(rt(Term::TmUnit { level: lv(0) }))),
        tm_empty: rt(Term::BoxTm(rt(Term::TmEmpty { level: lv(0) }))),
        tm_triv: rt(Term::BoxTm(rt(Term::Triv { level: lv(0) }))),
        // box (elim_Empty^{ℓ,ℓ'} (x. U_M^id; u_t^id)) — universes ℓ = 1
        // (motive), ℓ' = 0 (scrutinee); telescope g = 2, U_M = 1, u_t = 0.
        tm_elim_empty: {
            let gx_empty = ext(&g2, Type::Empty { level: lv(0) }, lv(0));
            let u_m_e = Type::GlobalTy { var: GlobalVar::index(1), subst: LocalSubst::id(&gx_empty) };
            rt(Term::BoxTm(rt(Term::ElimEmpty {
                level: lv(1),
                scrut_level: lv(0),
                motive: rty(u_m_e),
                scrut: rt(gtm(0, &g2)),
            })))
        },
        // box (U_A^id +^{ℓ,ℓ'} U_B^id) — telescope g = 2, U_A = 1, U_B = 0.
        ty_sum: rt(Term::BoxTy(rty(Type::Sum {
            lhs_level: lv(1),
            rhs_level: lv(0),
            lhs: rty(gty(1, &g2)),
            rhs: rty(gty(0, &g2)),
        }))),
        // box (u_a +^{ℓ,ℓ'} u_b) — telescope g = 2, u_a = 1, u_b = 0.
        tm_sum: rt(Term::BoxTm(rt(Term::TmSum {
            lhs_level: lv(1),
            rhs_level: lv(0),
            lhs: rt(gtm(1, &g2)),
            rhs: rt(gtm(0, &g2)),
        }))),
        // box (inl(U_A^id; U_B^id; u_a^id)) — g = 3, U_A = 2, U_B = 1, u_a = 0.
        tm_inl: rt(Term::BoxTm(rt(Term::Inl {
            lhs_level: lv(1),
            rhs_level: lv(0),
            lhs: rty(gty(2, &g3)),
            rhs: rty(gty(1, &g3)),
            val: rt(gtm(0, &g3)),
        }))),
        // box (inr(U_A^id; U_B^id; u_b^id)) — g = 3, U_A = 2, U_B = 1, u_b = 0.
        tm_inr: rt(Term::BoxTm(rt(Term::Inr {
            lhs_level: lv(1),
            rhs_level: lv(0),
            lhs: rty(gty(2, &g3)),
            rhs: rty(gty(1, &g3)),
            val: rt(gtm(0, &g3)),
        }))),
        // box (case (z. U_M^id) (x. u_l^id) (y. u_r^id) u_t^id) — telescope
        // g = 6, U_A = 5, U_B = 4, U_M = 3, u_l = 2, u_r = 1, u_t = 0.
        tm_case: {
            let sum = Type::Sum {
                lhs_level: lv(2),
                rhs_level: lv(1),
                lhs: rty(gty(5, &g6)),
                rhs: rty(gty(4, &g6)),
            };
            let gz = ext(&g6, sum, Level::max(lv(2), lv(1)));
            let gx_a = ext(&g6, gty(5, &g6), lv(2));
            let gx_b = ext(&g6, gty(4, &g6), lv(1));
            rt(Term::BoxTm(rt(Term::Case {
                lhs_level: lv(2),
                rhs_level: lv(1),
                motive_level: lv(0),
                lhs: rty(gty(5, &g6)),
                rhs: rty(gty(4, &g6)),
                motive: rty(gty(3, &gz)),
                case_l: rt(gtm(2, &gx_a)),
                case_r: rt(gtm(1, &gx_b)),
                scrut: rt(gtm(0, &g6)),
            })))
        },
        // box (W x:U_S^id. U_T^id) — telescope g = 2, U_S = 1, U_T = 0.
        ty_w: rt(Term::BoxTy(rty(Type::W {
            shape_level: lv(1),
            pos_level: lv(0),
            shape: rty(gty(1, &g2)),
            pos: rty(gty(0, &gx_typi)),
        }))),
        // box (W x:u_s^id. u_t^id) — telescope g = 2, u_s = 1, u_t = 0.
        tm_w: rt(Term::BoxTm(rt(Term::TmW {
            shape_level: lv(1),
            pos_level: lv(0),
            shape: rt(gtm(1, &g2)),
            pos: rt(gtm(0, &gx_tmpi)),
        }))),
        // box (sup(x:U_S^id. U_T^id; u_a^id; u_f^id)) — telescope g = 4,
        // U_S = 3, U_T = 2, u_a = 1, u_f = 0.
        tm_sup: rt(Term::BoxTm(rt(Term::Sup {
            shape_level: lv(1),
            pos_level: lv(0),
            shape_ty: rty(gty(3, &g4)),
            pos_ty: rty(gty(2, &gx_app)),
            label: rt(gtm(1, &g4)),
            children: rt(gtm(0, &g4)),
        }))),
        // box (elim_W (x:U_S^id.U_T^id) (z. U_M^id) (a f ih. u_s^id) u_t^id)
        // — telescope g = 5, U_S = 4, U_T = 3, U_M = 2, u_s = 1, u_t = 0.
        tm_elim_w: {
            let g5 = g_ctx(5);
            let gx5 = ext(&g5, gty(4, &g5), lv(2));
            let w5 = Type::W {
                shape_level: lv(2),
                pos_level: lv(1),
                shape: rty(gty(4, &g5)),
                pos: rty(gty(3, &gx5)),
            };
            let lmax = Level::max(lv(2), lv(1));
            let gz = ext(&g5, w5.clone(), lmax.clone());
            let f_ty = Type::Pi {
                dom_level: lv(1),
                cod_level: lmax.clone(),
                dom: rty(gty(3, &gx5)),
                cod: rty(w5.shift_local(2)),
            };
            let gaf = ext(&gx5, f_ty, Level::max(lv(1), lmax));
            let f_y = Term::App {
                fun: rt(v(1)),
                dom_level: lv(1),
                cod_level: Level::max(lv(2), lv(1)),
                dom: rty(gty(3, &gx5).shift_local(2)),
                cod: rty(w5.shift_local(4)),
                arg: rt(v(0)),
            };
            let u_m_at_fy = Type::GlobalTy {
                var: GlobalVar::index(2),
                subst: LocalSubst::id(&g5).shift_local(3).extended(rt(f_y)),
            };
            let ih_ty = Type::Pi {
                dom_level: lv(1),
                cod_level: lv(0),
                dom: rty(gty(3, &gx5).shift_local(1)),
                cod: rty(u_m_at_fy),
            };
            let gafi = ext(&gaf, ih_ty, Level::max(lv(1), lv(0)));
            rt(Term::BoxTm(rt(Term::ElimW {
                shape_level: lv(2),
                pos_level: lv(1),
                motive_level: lv(0),
                shape: rty(gty(4, &g5)),
                pos: rty(gty(3, &gx5)),
                motive: rty(gty(2, &gz)),
                step: rt(gtm(1, &gafi)),
                scrut: rt(gtm(0, &g5)),
            })))
        },
        // -- finitary branching branches (docs/kernel/wf-former-design.md §6) --
        // box Vec^ℓ(U_T^id; u_k^id) — telescope g = 2, U_T = 1, u_k = 0.
        ty_vec: rt(Term::BoxTy(rty(Type::Vec {
            level: lv(0),
            elem: rty(gty(1, &g2)),
            len: rt(gtm(0, &g2)),
        }))),
        // box (Vec^ℓ(u_t^id; u_k^id)) (the encoding) — g = 2, u_t = 1,
        // u_k = 0.
        tm_vec: rt(Term::BoxTm(rt(Term::TmVec {
            level: lv(0),
            elem: rt(gtm(1, &g2)),
            len: rt(gtm(0, &g2)),
        }))),
        // box Fin(u_k^id) / box (Fin u_k^id) — g = 1, u_k = 0; no universe
        // binder.
        ty_fin: rt(Term::BoxTy(rty(Type::Fin { len: rt(gtm(0, &g1)) }))),
        tm_fin: rt(Term::BoxTm(rt(Term::TmFin { len: rt(gtm(0, &g1)) }))),
        // box (Wf^ℓ(x:U_S^id). u_n^id) — g = 2, U_S = 1, u_n = 0. One
        // universe only: the arity is a Nat term.
        ty_wf: {
            let gx = ext(&g2, gty(1, &g2), lv(0));
            rt(Term::BoxTy(rty(Type::Wf {
                level: lv(0),
                shape: rty(gty(1, &g2)),
                arity: rt(gtm(0, &gx)),
            })))
        },
        // box (Wf^ℓ(x:u_s^id). u_n^id) (the encoding) — g = 2, u_s = 1,
        // u_n = 0.
        tm_wf: {
            let gx = ext(&g2, Type::El { level: lv(0), tm: rt(gtm(1, &g2)) }, lv(0));
            rt(Term::BoxTm(rt(Term::TmWf {
                level: lv(0),
                shape: rt(gtm(1, &g2)),
                arity: rt(gtm(0, &gx)),
            })))
        },
        // box (sup_f(x:U_S^id. u_n^id; u_a^id; u_cs^id)) — g = 4, U_S = 3,
        // u_n = 2, u_a = 1, u_cs = 0.
        tm_supf: {
            let gx = ext(&g4, gty(3, &g4), lv(0));
            rt(Term::BoxTm(rt(Term::Supf {
                level: lv(0),
                shape: rty(gty(3, &g4)),
                arity: rt(gtm(2, &gx)),
                label: rt(gtm(1, &g4)),
                children: rt(gtm(0, &g4)),
            })))
        },
        // box (elim_Wf (x. U_S^id. u_n^id) (z. U_M^id) (a cs ih. u_s^id)
        // u_t^id) — telescope g = 5, U_S = 4, u_n = 3, U_M = 2, u_s = 1,
        // u_t = 0. The step's context is (g, a, cs, ih); only its length and
        // base are read by u_s's identity substitution, but the entries are
        // spelled out to keep this an honest transcription of the rule.
        tm_elim_wf: {
            let g5 = g_ctx(5);
            let gx5 = ext(&g5, gty(4, &g5), lv(1));
            let wf5 = Type::Wf {
                level: lv(1),
                shape: rty(gty(4, &g5)),
                arity: rt(gtm(3, &gx5)),
            };
            let gz = ext(&g5, wf5.clone(), lv(1));
            // cs : Vec^ℓ(Wf; u_n^{id,a/x}) in (g, a) — `a` sits where the
            // binder `x` was, so the arity is `u_n^id` unchanged.
            let cs_ty = Type::Vec {
                level: lv(1),
                elem: rty(wf5.shift_local(1)),
                len: rt(gtm(3, &gx5)),
            };
            let gacs = ext(&gx5, cs_ty, lv(1));
            // ih : Π(i : Fin u_n). U_M^{id, nth(Wf; u_n; cs; i)/z}.
            let nth_at_i = nth(
                &lv(1),
                &rty(wf5.shift_local(3)),
                &rt(gtm(3, &gx5).shift_local(2)),
                rt(Term::Var(LocalVar(1))),
                rt(Term::Var(LocalVar(0))),
            );
            let ih_ty = Type::Pi {
                dom_level: Level::Zero,
                cod_level: lv(0),
                dom: rty(Type::Fin { len: rt(gtm(3, &gx5).shift_local(1)) }),
                cod: rty(Type::GlobalTy {
                    var: GlobalVar::index(2),
                    subst: LocalSubst::id(&g5).shift_local(3).extended(rt(nth_at_i)),
                }),
            };
            let gacsi = ext(&gacs, ih_ty, lv(0));
            rt(Term::BoxTm(rt(Term::ElimWf {
                level: lv(1),
                motive_level: lv(0),
                shape: rty(gty(4, &g5)),
                arity: rt(gtm(3, &gx5)),
                motive: rty(gty(2, &gz)),
                step: rt(gtm(1, &gacsi)),
                scrut: rt(gtm(0, &g5)),
            })))
        },
        // -- strict equality (extension; sprop-design §6) --
        ty_seq: rt(Term::BoxTy(rty(Type::SEq {
            level: lv(0),
            ty: rty(gty(2, &g3)),
            lhs: rt(gtm(1, &g3)),
            rhs: rt(gtm(0, &g3)),
        }))),
        tm_seq: rt(Term::BoxTm(rt(Term::TmSEq {
            level: lv(0),
            ty: rt(gtm(2, &g3)),
            lhs: rt(gtm(1, &g3)),
            rhs: rt(gtm(0, &g3)),
        }))),
        ty_sempty: rt(Term::BoxTy(rty(Type::SEmpty { level: lv(0) }))),
        tm_sempty: rt(Term::BoxTm(rt(Term::TmSEmpty { level: lv(0) }))),
        tm_srefl: rt(Term::BoxTm(rt(Term::SRefl {
            level: lv(0),
            ty: rty(gty(1, &g2)),
            tm: rt(gtm(0, &g2)),
        }))),
        tm_elim_sempty: {
            // view: g = 2, U_M = 1, u_t = 0; ℓ = lv(1), ℓ' = lv(0).
            let gxe = ext(&g2, Type::SEmpty { level: lv(0) }, lv(0));
            rt(Term::BoxTm(rt(Term::ElimSEmpty {
                level: lv(1),
                scrut_level: lv(0),
                motive: rty(Type::GlobalTy {
                    var: GlobalVar::index(1),
                    subst: LocalSubst::id(&gxe),
                }),
                scrut: rt(gtm(0, &g2)),
            })))
        },
        ty_squash: rt(Term::BoxTy(rty(Type::Squash {
            level: lv(0),
            ty: rty(gty(0, &g1)),
        }))),
        tm_squash: rt(Term::BoxTm(rt(Term::TmSquash {
            level: lv(0),
            ty: rt(gtm(0, &g1)),
        }))),
        tm_squash_in: rt(Term::BoxTm(rt(Term::Squash {
            level: lv(0),
            ty: rty(gty(1, &g2)),
            tm: rt(gtm(0, &g2)),
        }))),
        tm_elim_squash: {
            let g4s = g_ctx(4);
            let a = gty(3, &g4s);
            let gz = ext(
                &g4s,
                Type::Squash { level: lv(1), ty: rty(a.clone()) },
                lv(1),
            );
            let gx = ext(&g4s, a.clone(), lv(1));
            rt(Term::BoxTm(rt(Term::ElimSquash {
                src_level: lv(1),
                dst_level: lv(0),
                src_ty: rty(a),
                motive: rty(Type::GlobalTy {
                    var: GlobalVar::index(2),
                    subst: LocalSubst::id(&gz),
                }),
                case: rt(gtm(1, &gx)),
                scrut: rt(gtm(0, &g4s)),
            })))
        },
        tm_unsquash_empty: rt(Term::BoxTm(rt(Term::UnsquashEmpty {
            level: lv(0),
            scrut: rt(gtm(0, &g1)),
        }))),
        // box (M(U_I; U_S; U_P; u_o)(u_j)) — g = 5, U_I = 4, U_S = 3, U_P =
        // 2, u_o = 1, u_j = 0; ℓ = lv(2), ℓ' = lv(1), ℓi = lv(0).
        ty_m: {
            let (sig, g) = m_sig_at(5, false, lv(2), lv(1), lv(0));
            rt(Term::BoxTy(rty(Type::M { sig, index: rt(gtm(0, &g)) })))
        },
        // box (TmM(u_I; u_S; u_P; u_o; u_j)), the pieces read through El.
        tm_m: {
            let (sig, g) = m_sig_at(5, true, lv(2), lv(1), lv(0));
            let code = |t: &Rc<Type>| match &**t {
                Type::El { tm, .. } => Rc::clone(tm),
                _ => unreachable!("coded pieces are El"),
            };
            rt(Term::BoxTm(rt(Term::TmM {
                level: lv(2),
                pos_level: lv(1),
                idx_level: lv(0),
                idx: code(&sig.idx),
                shape: code(&sig.shape),
                pos: code(&sig.pos),
                next: Rc::clone(&sig.next),
                index: rt(gtm(0, &g)),
            })))
        },
        // box (corec^k(σ; U_X; u_c; u_j; u_x)) — g = 8, U_I = 7, U_S = 6,
        // U_P = 5, u_o = 4, U_X = 3, u_c = 2, u_j = 1, u_x = 0; ℓ = lv(3),
        // ℓ' = lv(2), ℓi = lv(1), k = lv(0).
        tm_corec: {
            let (sig, g) = m_sig_at(8, false, lv(3), lv(2), lv(1));
            let gi = ext(&g, (*sig.idx).clone(), lv(1));
            let carrier = gty(3, &gi);
            let gix = ext(&gi, carrier.clone(), lv(0));
            rt(Term::BoxTm(rt(Term::Corec {
                sig,
                carrier_level: lv(0),
                carrier: rty(carrier),
                step: rt(gtm(2, &gix)),
                index: rt(gtm(1, &g)),
                seed: rt(gtm(0, &g)),
            })))
        },
        // box (out(σ; u_j; u_m)) — g = 6, U_I = 5, …, u_o = 2, u_j = 1, u_m
        // = 0.
        tm_out: {
            let (sig, g) = m_sig_at(6, false, lv(2), lv(1), lv(0));
            rt(Term::BoxTm(rt(Term::Out {
                sig,
                index: rt(gtm(1, &g)),
                scrut: rt(gtm(0, &g)),
            })))
        },
        // -- indexed well-founded trees (docs/kernel/iwf-former-design.md §13) --
        // box DVec^ℓ(u_n; i. U_F) — g = 2, u_n = 1, U_F = 0.
        ty_dvec: {
            let len = rt(gtm(1, &g2));
            let gi = ext(&g2, Type::Fin { len: Rc::clone(&len) }, Level::Zero);
            rt(Term::BoxTy(rty(Type::DVec { level: lv(0), len, fam: rty(gty(0, &gi)) })))
        },
        tm_dvec: {
            let len = rt(gtm(1, &g2));
            let gi = ext(&g2, Type::Fin { len: Rc::clone(&len) }, Level::Zero);
            rt(Term::BoxTm(rt(Term::TmDVec { level: lv(0), len, fam: rt(gtm(0, &gi)) })))
        },
        // box IWf(U_I; U_S; u_n; u_o; u_c)(u_m) — g = 6, I = 5, S = 4, n =
        // 3, o = 2, c = 1, m = 0; ℓ = lv(1), ℓi = lv(0).
        ty_iwf: {
            let v = iwf_sig_at(1, false, lv(1), lv(0));
            rt(Term::BoxTy(rty(v.sig.at(rt(gtm(0, &v.g))))))
        },
        tm_iwf: {
            let v = iwf_sig_at(1, true, lv(1), lv(0));
            rt(Term::BoxTm(rt(Term::TmIWf {
                level: lv(1),
                idx_level: lv(0),
                idx: rt(gtm(5, &v.g)),
                shape: rt(gtm(4, &v.g)),
                arity: Rc::clone(&v.sig.arity),
                out: Rc::clone(&v.sig.out),
                child: Rc::clone(&v.sig.child),
                index: rt(gtm(0, &v.g)),
            })))
        },
        // box sup_i(…; u_a; u_cs) — g = 7, …, c = 2, a = 1, cs = 0.
        tm_sup_i: {
            let v = iwf_sig_at(2, false, lv(1), lv(0));
            rt(Term::BoxTm(rt(v.sig.supi(rt(gtm(1, &v.g)), rt(gtm(0, &v.g))))))
        },
        // box elim_IWf(…; j z. U_M; a cs ih. u_s; u_m; u_t) — g = 9, I = 8,
        // S = 7, n = 6, o = 5, c = 4, M = 3, s = 2, m = 1, t = 0; ℓ =
        // lv(2), ℓi = lv(1), ℓ' = lv(0).
        tm_elim_iwf: {
            let v = iwf_sig_at(4, false, lv(2), lv(1));
            let family = v.sig.family_level();
            let gj = ext(&v.g, (*v.sig.idx).clone(), lv(1));
            let gjz = ext(&gj, iwf_motive_scrut_ty(&v.sig), family.clone());
            let motive = gty(3, &gjz);
            let (cs_ty, ih_ty, _) = iwf_step_telescope(&v.sig, &lv(0), &motive);
            let ga = ext(&v.g, (*v.sig.shape).clone(), lv(2));
            let gacs = ext(&ga, cs_ty, family);
            let gacsi = ext(&gacs, ih_ty, lv(0));
            rt(Term::BoxTm(rt(Term::ElimIWf {
                sig: Rc::clone(&v.sig),
                motive_level: lv(0),
                motive: rty(motive),
                step: rt(gtm(2, &gacsi)),
                index: rt(gtm(1, &v.g)),
                scrut: rt(gtm(0, &v.g)),
            })))
        },
    })
}

/// The `IWf` signature `(U_I; U_S; u_n; u_o; u_c)` of a branch whose `u_c`
/// is global `k` (so `g` is `k + 5`), the index type and shapes being (or,
/// `coded`, `El` of) the globals before it — and `g`'s context. rec.rs's
/// `iwf_view`, transcribed.
struct IWfAt {
    sig: Rc<IWfSig>,
    g: LocalCtx,
}

fn iwf_sig_at(k: u32, coded: bool, l: Level, li: Level) -> IWfAt {
    let g = g_ctx(k + 5);
    let piece = |var: u32, level: &Level| {
        if coded {
            Type::El { level: level.clone(), tm: rt(gtm(var, &g)) }
        } else {
            gty(var, &g)
        }
    };
    let idx = piece(k + 4, &li);
    let shape = piece(k + 3, &l);
    let gx = ext(&g, shape.clone(), l.clone());
    let arity = gtm(k + 2, &gx);
    let gxi = ext(&gx, Type::Fin { len: rt(arity.clone()) }, Level::Zero);
    let sig = Rc::new(IWfSig {
        level: l,
        idx_level: li,
        idx: rty(idx),
        shape: rty(shape),
        arity: rt(arity),
        out: rt(gtm(k + 1, &gx)),
        child: rt(gtm(k, &gxi)),
    });
    IWfAt { sig, g }
}

/// The signature `(U_I; U_S; U_P; u_o)` of an `M` branch whose context
/// variable `g` is global `g_at`, the four pieces the next globals inward
/// (or, `coded`, `El` of code globals) — and `g`'s context.
fn m_sig_at(g_at: u32, coded: bool, l: Level, lp: Level, li: Level) -> (Rc<MSig>, LocalCtx) {
    let piece = |var: u32, ctx: &LocalCtx, level: &Level| {
        if coded {
            Type::El { level: level.clone(), tm: rt(gtm(var, ctx)) }
        } else {
            gty(var, ctx)
        }
    };
    let g = g_ctx(g_at);
    let idx = piece(g_at - 1, &g, &li);
    let gi = ext(&g, idx.clone(), li.clone());
    let shape = piece(g_at - 2, &gi, &l);
    let gis = ext(&gi, shape.clone(), l.clone());
    let pos = piece(g_at - 3, &gis, &lp);
    let gisp = ext(&gis, pos.clone(), lp.clone());
    let next = gtm(g_at - 4, &gisp);
    let sig = Rc::new(MSig {
        level: l,
        pos_level: lp,
        idx_level: li,
        idx: rty(idx),
        shape: rty(shape),
        pos: rty(pos),
        next: rt(next),
    });
    (sig, g)
}
