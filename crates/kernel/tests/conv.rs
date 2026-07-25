//! Golden tests for ch. 06 convertibility: one or more tests per rule
//! family — β/η for all four function types, level equivalence at
//! annotations, El decoding, syntactic box comparison, neutral inference
//! (variables, globals with converting substitutions, elim_Nat, letbox,
//! recursors with the C_A bundle), context conversion, and distinguishable
//! fuel exhaustion.
//!
//! No generator-based properties here: conversion presupposes well-typed
//! inputs, and on the generators' ill-typed terms a legitimate `Err` is
//! indistinguishable from a bug. (Reflexivity on well-typed terms is the
//! ch. 07/08 PER lemma, not something the generators can witness.)

use std::rc::Rc;

use heather_kernel::conv::{conv_local_ctx, conv_term, conv_type, ConvError};
use heather_kernel::layer::Layer;
use heather_kernel::level::{Level, UnivVar};
use heather_kernel::term::{
    Branches, CtxBase, CtxEntry, GlobalBinding, GlobalCtx, GlobalVar, LocalCtx, LocalSubst,
    LocalVar, Motives, SubstTail, Term, Type,
};

const FUEL: u64 = 100_000;

// -------------------------------------------------------------------------
// Construction helpers (mirroring tests/reduce.rs)
// -------------------------------------------------------------------------

fn rt(t: Term) -> Rc<Term> {
    Rc::new(t)
}

fn rty(t: Type) -> Rc<Type> {
    Rc::new(t)
}

fn c(n: u64) -> Level {
    Level::constant(n)
}

fn lv(i: u32) -> Level {
    Level::Var(UnivVar(i))
}

fn v(i: u32) -> Term {
    Term::Var(LocalVar(i))
}

fn psi(bindings: Vec<GlobalBinding>) -> GlobalCtx {
    GlobalCtx { bindings }
}

/// `(·, x₀ : Nat @ 0, …)` with `n` entries.
fn nil_ctx(n: u32) -> LocalCtx {
    LocalCtx {
        base: CtxBase::Nil,
        entries: (0..n)
            .map(|_| CtxEntry { ty: rty(Type::Nat), level: Level::Zero })
            .collect(),
    }
}

/// `Γ, x : ty @ level`.
fn extend(gamma: &LocalCtx, ty: Type, level: Level) -> LocalCtx {
    let mut g = gamma.clone();
    g.entries.push(CtxEntry { ty: rty(ty), level });
    g
}

/// `λ^{0,0}(x : Nat). body`.
fn lam(body: Term) -> Term {
    Term::Lam {
        dom_level: Level::Zero,
        cod_level: Level::Zero,
        dom: rty(Type::Nat),
        body: rt(body),
    }
}

/// `app(f; 0,0; x : Nat. Nat; a)`.
fn app(f: Term, a: Term) -> Term {
    Term::App {
        fun: rt(f),
        dom_level: Level::Zero,
        cod_level: Level::Zero,
        dom: rty(Type::Nat),
        cod: rty(Type::Nat),
        arg: rt(a),
    }
}

fn num(n: u32) -> Term {
    let mut t = Term::Zero;
    for _ in 0..n {
        t = Term::Succ(rt(t));
    }
    t
}

/// `Π^{0,0}(x : Nat). Nat`.
fn nat_to_nat() -> Type {
    Type::Pi {
        dom_level: Level::Zero,
        cod_level: Level::Zero,
        dom: rty(Type::Nat),
        cod: rty(Type::Nat),
    }
}

/// `(λx. x) 0` — β-convertible to `0` but not syntactically equal.
fn beta_zero() -> Term {
    app(lam(v(0)), Term::Zero)
}

/// The empty substitution `·⁰` out of the empty context.
fn empty_subst(terms: Vec<Term>) -> LocalSubst {
    LocalSubst {
        tail: SubstTail::Empty { len: 0, base: CtxBase::Nil },
        terms: terms.into_iter().map(rt).collect(),
    }
}

fn ok_tm(psi: &GlobalCtx, gamma: &LocalCtx, a: &Term, b: &Term, ty: &Type, l: &Level) {
    assert_eq!(conv_term(psi, gamma, Layer::Meta, a, b, ty, l, FUEL), Ok(()));
}

fn no_tm(psi: &GlobalCtx, gamma: &LocalCtx, a: &Term, b: &Term, ty: &Type, l: &Level) {
    assert_eq!(
        conv_term(psi, gamma, Layer::Meta, a, b, ty, l, FUEL),
        Err(ConvError::NotConvertible)
    );
}

// -------------------------------------------------------------------------
// β, neutrals, congruence
// -------------------------------------------------------------------------

#[test]
fn beta_redex_converts() {
    let psi = psi(vec![]);
    ok_tm(&psi, &nil_ctx(0), &beta_zero(), &Term::Zero, &Type::Nat, &c(0));
    // Also at layer p.
    assert_eq!(
        conv_term(
            &psi,
            &nil_ctx(0),
            Layer::Prog,
            &beta_zero(),
            &Term::Zero,
            &Type::Nat,
            &c(0),
            FUEL
        ),
        Ok(())
    );
}

#[test]
fn succ_congruence() {
    let psi = psi(vec![]);
    ok_tm(&psi, &nil_ctx(0), &Term::Succ(rt(beta_zero())), &num(1), &Type::Nat, &c(0));
    no_tm(&psi, &nil_ctx(0), &num(1), &num(2), &Type::Nat, &c(0));
}

#[test]
fn neutral_variables() {
    let psi = psi(vec![]);
    let gamma = nil_ctx(2);
    ok_tm(&psi, &gamma, &v(0), &v(0), &Type::Nat, &c(0));
    no_tm(&psi, &gamma, &v(0), &v(1), &Type::Nat, &c(0));
}

#[test]
fn elim_nat_neutral_congruence() {
    // Two elim_Nats blocked on the same variable, β-convertible bases.
    let psi = psi(vec![]);
    let gamma = nil_ctx(1);
    let elim = |base: Term| Term::ElimNat {
        level: Level::Zero,
        motive: rty(Type::Nat),
        base: rt(base),
        step: rt(Term::Zero),
        scrut: rt(v(0)),
    };
    ok_tm(&psi, &gamma, &elim(beta_zero()), &elim(Term::Zero), &Type::Nat, &c(0));
    no_tm(&psi, &gamma, &elim(Term::Zero), &elim(num(1)), &Type::Nat, &c(0));
}

// -------------------------------------------------------------------------
// η at the four function types
// -------------------------------------------------------------------------

#[test]
fn eta_pi() {
    // Γ = (·, f : Π(x:Nat).Nat): λx. f x ≈ f.
    let psi = psi(vec![]);
    let gamma = extend(&nil_ctx(0), nat_to_nat(), c(0));
    let expanded = lam(app(v(1), v(0)));
    ok_tm(&psi, &gamma, &expanded, &v(0), &nat_to_nat(), &c(0));
    ok_tm(&psi, &gamma, &v(0), &expanded, &nat_to_nat(), &c(0));
    no_tm(&psi, &gamma, &lam(Term::Zero), &v(0), &nat_to_nat(), &c(0));
}

#[test]
fn eta_upi() {
    // f : ΠΠ ℓ. Nat — η-expansion drives both sides to a neutral $-spine.
    let psi = psi(vec![]);
    let upi = Type::UPi { num_vars: 1, level: Level::Zero, body: rty(Type::Nat) };
    let gamma = extend(&nil_ctx(0), upi.clone(), Level::Omega);
    ok_tm(&psi, &gamma, &v(0), &v(0), &upi, &Level::Omega);
    let expanded = Term::ULam {
        num_vars: 1,
        level: Level::Zero,
        body: rt(Term::UApp { fun: rt(v(0)), levels: vec![lv(0)] }),
    };
    ok_tm(&psi, &gamma, &expanded, &v(0), &upi, &Level::Omega);
}

#[test]
fn eta_ctx_pi() {
    let psi = psi(vec![]);
    let cpi = Type::CtxPi { level: Level::Zero, body: rty(Type::Nat) };
    let gamma = extend(&nil_ctx(0), cpi.clone(), c(0));
    ok_tm(&psi, &gamma, &v(0), &v(0), &cpi, &c(0));
    let expanded = Term::CtxLam {
        level: Level::Zero,
        body: rt(Term::CtxApp {
            fun: rt(v(0)),
            ctx: LocalCtx { base: CtxBase::Var(GlobalVar(0)), entries: vec![] },
        }),
    };
    ok_tm(&psi, &gamma, &expanded, &v(0), &cpi, &c(0));
}

#[test]
fn eta_ty_pi() {
    let psi = psi(vec![]);
    let tpi = Type::TyPi {
        ctx: nil_ctx(0),
        arg_level: Level::Zero,
        body_level: Level::Zero,
        body: rty(Type::Nat),
    };
    let gamma = extend(&nil_ctx(0), tpi.clone(), c(0));
    ok_tm(&psi, &gamma, &v(0), &v(0), &tpi, &c(0));
    let expanded = Term::TyLam {
        ctx: nil_ctx(0),
        arg_level: Level::Zero,
        body_level: Level::Zero,
        body: rt(Term::TyApp {
            fun: rt(v(0)),
            arg: rty(Type::GlobalTy { var: GlobalVar(0), subst: empty_subst(vec![]) }),
        }),
    };
    ok_tm(&psi, &gamma, &expanded, &v(0), &tpi, &c(0));
}

// -------------------------------------------------------------------------
// Types: levels, El decoding, binders
// -------------------------------------------------------------------------

#[test]
fn type_levels_modulo_equiv() {
    let psi = psi(vec![]);
    let g = nil_ctx(0);
    let a = Type::Ty(Level::max(lv(0), lv(0)));
    let b = Type::Ty(lv(0));
    assert_eq!(
        conv_type(&psi, &g, Layer::Meta, &a, &b, &Level::succ(lv(0)), FUEL),
        Ok(())
    );
    let too_big = Type::Ty(Level::succ(lv(0)));
    assert_eq!(
        conv_type(&psi, &g, Layer::Meta, &too_big, &b, &Level::succ(lv(0)), FUEL),
        Err(ConvError::NotConvertible)
    );
}

#[test]
fn el_decodes_encodings() {
    let psi = psi(vec![]);
    let g = nil_ctx(0);
    let el_nat = Type::El { level: Level::Zero, tm: rt(Term::TmNat) };
    assert_eq!(conv_type(&psi, &g, Layer::Prog, &el_nat, &Type::Nat, &c(0), FUEL), Ok(()));
    // El (Π-code) ≈ Π of Els ≈ Π of the decoded types.
    let el_pi = Type::El {
        level: Level::max(Level::Zero, Level::Zero),
        tm: rt(Term::TmPi {
            dom_level: Level::Zero,
            cod_level: Level::Zero,
            dom: rt(Term::TmNat),
            cod: rt(Term::TmNat),
        }),
    };
    assert_eq!(conv_type(&psi, &g, Layer::Prog, &el_pi, &nat_to_nat(), &c(0), FUEL), Ok(()));
    assert_eq!(
        conv_type(&psi, &g, Layer::Prog, &el_nat, &Type::Ty(c(0)), &c(0), FUEL),
        Err(ConvError::NotConvertible)
    );
}

#[test]
fn pi_compares_under_binder() {
    let psi = psi(vec![]);
    let g = nil_ctx(0);
    let a = Type::Pi {
        dom_level: Level::Zero,
        cod_level: Level::Zero,
        dom: rty(Type::Nat),
        cod: rty(Type::El { level: Level::Zero, tm: rt(Term::TmNat) }),
    };
    assert_eq!(conv_type(&psi, &g, Layer::Prog, &a, &nat_to_nat(), &c(0), FUEL), Ok(()));
}

#[test]
fn tm_pi_encoding_congruence() {
    // Term-level Π-codes compare componentwise (through reduction).
    let psi = psi(vec![]);
    let g = nil_ctx(0);
    let a = Term::TmPi {
        dom_level: Level::Zero,
        cod_level: Level::Zero,
        dom: rt(Term::TmNat),
        cod: rt(Term::TmNat),
    };
    let b = Term::TmPi {
        dom_level: Level::max(Level::Zero, Level::Zero),
        cod_level: Level::Zero,
        dom: rt(app(lam(v(0)), Term::TmNat)),
        cod: rt(Term::TmNat),
    };
    ok_tm(&psi, &g, &a, &b, &Type::Ty(c(0)), &c(1));
}

#[test]
fn ctx_conversion() {
    let psi = psi(vec![]);
    let a = extend(&nil_ctx(0), Type::El { level: Level::Zero, tm: rt(Term::TmNat) }, c(0));
    let b = nil_ctx(1);
    assert_eq!(conv_local_ctx(&psi, Layer::Prog, &a, &b, FUEL), Ok(()));
    let wrong_level = extend(&nil_ctx(0), Type::Nat, c(1));
    assert_eq!(
        conv_local_ctx(&psi, Layer::Prog, &wrong_level, &b, FUEL),
        Err(ConvError::NotConvertible)
    );
}

// -------------------------------------------------------------------------
// Boxes are syntactic; globals compare substitutions componentwise
// -------------------------------------------------------------------------

#[test]
fn box_compares_syntactically() {
    let psi = psi(vec![]);
    let g = nil_ctx(0);
    let code_ty = Type::CodeTy { ctx: nil_ctx(0), level: Level::Zero };
    ok_tm(&psi, &g, &Term::BoxTy(rty(Type::Nat)), &Term::BoxTy(rty(Type::Nat)), &code_ty, &c(0));
    // β/El-convertible code is NOT convertible as code.
    let el_nat = Type::El { level: Level::Zero, tm: rt(Term::TmNat) };
    no_tm(&psi, &g, &Term::BoxTy(rty(el_nat)), &Term::BoxTy(rty(Type::Nat)), &code_ty, &c(0));

    let code_tm = Type::CodeTm { ctx: nil_ctx(0), ty: rty(Type::Nat), level: Level::Zero };
    ok_tm(&psi, &g, &Term::BoxTm(rt(Term::Zero)), &Term::BoxTm(rt(Term::Zero)), &code_tm, &c(0));
    no_tm(&psi, &g, &Term::BoxTm(rt(beta_zero())), &Term::BoxTm(rt(Term::Zero)), &code_tm, &c(0));
}

#[test]
fn global_term_substitutions_convert_componentwise() {
    // Ψ = (u : Trm_c((·, x : Nat @ 0) ⊢ Nat @ 0)); u^{·,(λx.x)0/x} ≈ u^{·,0/x}.
    let psi = psi(vec![GlobalBinding::Tm {
        ctx: nil_ctx(1),
        layer: Layer::Code,
        ty: rty(Type::Nat),
        level: Level::Zero,
    }]);
    let g = nil_ctx(0);
    let u = |t: Term| Term::GlobalTm { var: GlobalVar(0), subst: empty_subst(vec![t]) };
    ok_tm(&psi, &g, &u(beta_zero()), &u(Term::Zero), &Type::Nat, &c(0));
    no_tm(&psi, &g, &u(num(1)), &u(Term::Zero), &Type::Nat, &c(0));
}

// -------------------------------------------------------------------------
// letbox
// -------------------------------------------------------------------------

#[test]
fn letbox_ty_neutral() {
    // Γ = (·, s : □(· ⊢ Ty 0) @ 0), scrutinee neutral: bodies compare up to β.
    let psi = psi(vec![]);
    let gamma = extend(&nil_ctx(0), Type::CodeTy { ctx: nil_ctx(0), level: Level::Zero }, c(0));
    let letbox = |body: Term| Term::LetBoxTy {
        motive_level: Level::Zero,
        code_level: Level::Zero,
        ctx: nil_ctx(0),
        motive: rty(Type::Nat),
        body: rt(body),
        scrut: rt(v(0)),
    };
    ok_tm(&psi, &gamma, &letbox(beta_zero()), &letbox(Term::Zero), &Type::Nat, &c(0));
    no_tm(&psi, &gamma, &letbox(Term::Zero), &letbox(num(1)), &Type::Nat, &c(0));
    // The critical layer property: the same m-terms relate at layer p.
    assert_eq!(
        conv_term(
            &psi,
            &gamma,
            Layer::Prog,
            &letbox(beta_zero()),
            &letbox(Term::Zero),
            &Type::Nat,
            &c(0),
            FUEL
        ),
        Ok(())
    );
}

// -------------------------------------------------------------------------
// Neutral code recursors (the C_A bundle)
// -------------------------------------------------------------------------

/// Branches all equal to `t`.
fn const_branches(t: Term) -> Rc<Branches> {
    Rc::new(Branches {
        ty_nat: rt(t.clone()),
        ty_pi: rt(t.clone()),
        ty_ty: rt(t.clone()),
        ty_el: rt(t.clone()),
        tm_var: rt(t.clone()),
        tm_nat: rt(t.clone()),
        tm_pi: rt(t.clone()),
        tm_ty: rt(t.clone()),
        tm_zero: rt(t.clone()),
        tm_succ: rt(t.clone()),
        tm_elim_nat: rt(t.clone()),
        tm_lam: rt(t.clone()),
        tm_app: rt(t.clone()),
        ty_id: rt(t.clone()),
        ty_sigma: rt(t.clone()),
        tm_id: rt(t.clone()),
        tm_refl: rt(t.clone()),
        tm_j: rt(t.clone()),
        tm_sigma: rt(t.clone()),
        tm_pair: rt(t.clone()),
        tm_fst: rt(t.clone()),
        tm_snd: rt(t.clone()),
        ty_unit: rt(t.clone()),
        ty_empty: rt(t.clone()),
        tm_unit: rt(t.clone()),
        tm_empty: rt(t.clone()),
        tm_triv: rt(t.clone()),
        tm_elim_empty: rt(t.clone()),
        ty_sum: rt(t.clone()),
        tm_sum: rt(t.clone()),
        tm_inl: rt(t.clone()),
        tm_inr: rt(t.clone()),
        tm_case: rt(t.clone()),
        ty_w: rt(t.clone()),
        tm_w: rt(t.clone()),
        tm_sup: rt(t.clone()),
        tm_elim_w: rt(t.clone()),
        ty_vec: rt(t.clone()),
        tm_vec: rt(t.clone()),
        ty_fin: rt(t.clone()),
        tm_fin: rt(t.clone()),
        ty_wf: rt(t.clone()),
        tm_wf: rt(t.clone()),
        tm_supf: rt(t.clone()),
        tm_elim_wf: rt(t),
    })
}

fn nat_motives() -> Rc<Motives> {
    Rc::new(Motives { ty_motive: rty(Type::Nat), tm_motive: rty(Type::Nat) })
}

/// A recursor blocked on `box (U₀^·)`; Ψ must start with `U₀ : Typ_c(·, 0)`.
fn elim_code_ty(motives: Rc<Motives>, branches: Rc<Branches>, ty_nat: Term) -> Term {
    let mut b = (*branches).clone();
    b.ty_nat = rt(ty_nat);
    Term::ElimCodeTy {
        ty_motive_level: Level::Zero,
        tm_motive_level: Level::Zero,
        motives,
        branches: Rc::new(b),
        code_level: Level::Zero,
        ctx: nil_ctx(0),
        scrut: rt(Term::BoxTy(rty(Type::GlobalTy {
            var: GlobalVar(0),
            subst: empty_subst(vec![]),
        }))),
    }
}

fn code_psi() -> GlobalCtx {
    psi(vec![GlobalBinding::Ty { ctx: nil_ctx(0), layer: Layer::Code, level: Level::Zero }])
}

#[test]
fn recursor_neutral_trivial_motives() {
    // Constant Nat motives: every branch compares at Nat; β-convertible
    // branches are accepted, distinct values rejected.
    let psi = code_psi();
    let g = nil_ctx(0);
    let a = elim_code_ty(nat_motives(), const_branches(Term::Zero), beta_zero());
    let b = elim_code_ty(nat_motives(), const_branches(Term::Zero), Term::Zero);
    ok_tm(&psi, &g, &a, &b, &Type::Nat, &c(0));
    let bad = elim_code_ty(nat_motives(), const_branches(Term::Zero), num(1));
    no_tm(&psi, &g, &b, &bad, &Type::Nat, &c(0));
}

#[test]
fn recursor_branch_type_uses_motive() {
    // M_Typ = Π(x:Nat).Nat: the ty branches compare at a Π type, so the
    // η-pair λx. f x ≈ f is accepted — but only if the branch type really
    // is the instantiated motive. With M_Typ = Nat the same pair mismatches.
    let psi = code_psi();
    let gamma = extend(&nil_ctx(0), nat_to_nat(), c(0));
    let pi_motives =
        Rc::new(Motives { ty_motive: rty(nat_to_nat()), tm_motive: rty(Type::Nat) });
    // In every ty-branch telescope Γ only grows, so f stays in scope; the
    // branch values here are closed over the telescope binders.
    let a = elim_code_ty(
        Rc::clone(&pi_motives),
        const_branches(lam(Term::Zero)),
        lam(app(v(1), v(0))),
    );
    let mut a = a;
    let b = {
        // Right side: ty_nat = f itself; all other branches identical.
        let Term::ElimCodeTy { branches, .. } = &a else { unreachable!() };
        let mut br = (**branches).clone();
        // tm branches compare at Nat; keep them Zero on both sides.
        for f in [&mut br.tm_var, &mut br.tm_nat, &mut br.tm_pi, &mut br.tm_ty,
                  &mut br.tm_zero, &mut br.tm_succ, &mut br.tm_elim_nat,
                  &mut br.tm_lam, &mut br.tm_app, &mut br.tm_id, &mut br.tm_refl,
                  &mut br.tm_j, &mut br.tm_sigma, &mut br.tm_pair, &mut br.tm_fst,
                  &mut br.tm_snd, &mut br.tm_unit, &mut br.tm_empty, &mut br.tm_triv,
                  &mut br.tm_elim_empty, &mut br.tm_sum, &mut br.tm_inl,
                  &mut br.tm_inr, &mut br.tm_case, &mut br.tm_w, &mut br.tm_sup,
                  &mut br.tm_elim_w, &mut br.tm_vec, &mut br.tm_fin,
                  &mut br.tm_wf, &mut br.tm_supf, &mut br.tm_elim_wf] {
            *f = rt(Term::Zero);
        }
        br.ty_nat = rt(v(0));
        let Term::ElimCodeTy { motives, code_level, ctx, scrut, .. } = &a else {
            unreachable!()
        };
        Term::ElimCodeTy {
            ty_motive_level: Level::Zero,
            tm_motive_level: Level::Zero,
            motives: Rc::clone(motives),
            branches: Rc::new(br),
            code_level: code_level.clone(),
            ctx: ctx.clone(),
            scrut: rt((**scrut).clone()),
        }
    };
    // Fix up the left side's tm branches to Zero too.
    {
        let Term::ElimCodeTy { branches, .. } = &mut a else { unreachable!() };
        let mut br = (**branches).clone();
        for f in [&mut br.tm_var, &mut br.tm_nat, &mut br.tm_pi, &mut br.tm_ty,
                  &mut br.tm_zero, &mut br.tm_succ, &mut br.tm_elim_nat,
                  &mut br.tm_lam, &mut br.tm_app, &mut br.tm_id, &mut br.tm_refl,
                  &mut br.tm_j, &mut br.tm_sigma, &mut br.tm_pair, &mut br.tm_fst,
                  &mut br.tm_snd, &mut br.tm_unit, &mut br.tm_empty, &mut br.tm_triv,
                  &mut br.tm_elim_empty, &mut br.tm_sum, &mut br.tm_inl,
                  &mut br.tm_inr, &mut br.tm_case, &mut br.tm_w, &mut br.tm_sup,
                  &mut br.tm_elim_w, &mut br.tm_vec, &mut br.tm_fin,
                  &mut br.tm_wf, &mut br.tm_supf, &mut br.tm_elim_wf] {
            *f = rt(Term::Zero);
        }
        *branches = Rc::new(br);
    }
    ok_tm(&psi, &gamma, &a, &b, &nat_to_nat(), &c(0));

    // Control: with Nat motives the same η-pair is not convertible (λ vs
    // variable at Nat), proving the Π above came from the motive.
    let a_nat = elim_code_ty(nat_motives(), const_branches(Term::Zero), lam(app(v(1), v(0))));
    let b_nat = elim_code_ty(nat_motives(), const_branches(Term::Zero), v(0));
    no_tm(&psi, &gamma, &a_nat, &b_nat, &nat_to_nat(), &c(0));
}

#[test]
fn recursor_scrut_box_is_syntactic() {
    // Two Typ_c bindings; recursors blocked on box(U₀^·) vs box(U₁^·).
    let psi = psi(vec![
        GlobalBinding::Ty { ctx: nil_ctx(0), layer: Layer::Code, level: Level::Zero },
        GlobalBinding::Ty { ctx: nil_ctx(0), layer: Layer::Code, level: Level::Zero },
    ]);
    let g = nil_ctx(0);
    let elim = |var: u32| Term::ElimCodeTy {
        ty_motive_level: Level::Zero,
        tm_motive_level: Level::Zero,
        motives: nat_motives(),
        branches: const_branches(Term::Zero),
        code_level: Level::Zero,
        ctx: nil_ctx(0),
        scrut: rt(Term::BoxTy(rty(Type::GlobalTy {
            var: GlobalVar(var),
            subst: empty_subst(vec![]),
        }))),
    };
    ok_tm(&psi, &g, &elim(0), &elim(0), &Type::Nat, &c(0));
    no_tm(&psi, &g, &elim(0), &elim(1), &Type::Nat, &c(0));
}

// -------------------------------------------------------------------------
// Fuel
// -------------------------------------------------------------------------

#[test]
fn fuel_exhaustion_is_distinguishable() {
    // Ω = (λx. x x) (λx. x x) diverges under weak-head reduction.
    let psi = psi(vec![]);
    let delta = lam(app(v(0), v(0)));
    let omega = app(delta.clone(), delta);
    assert_eq!(
        conv_term(&psi, &nil_ctx(0), Layer::Prog, &omega, &Term::Zero, &Type::Nat, &c(0), 500),
        Err(ConvError::OutOfFuel)
    );
}

// -------------------------------------------------------------------------
// Identity type (extension beyond ch. 04; kernel-v1-extensions)
// -------------------------------------------------------------------------

#[test]
fn id_type_congruence() {
    let psi = psi(vec![]);
    let g0 = nil_ctx(0);
    let id = |lhs: Term, rhs: Term| Type::Id {
        level: Level::Zero,
        ty: rty(Type::Nat),
        lhs: rt(lhs),
        rhs: rt(rhs),
    };
    // Congruence through β-convertible components.
    assert_eq!(
        conv_type(&psi, &g0, Layer::Prog, &id(beta_zero(), Term::Zero),
                  &id(Term::Zero, Term::Zero), &c(0), FUEL),
        Ok(())
    );
    // Distinct endpoints are caught.
    assert_eq!(
        conv_type(&psi, &g0, Layer::Prog, &id(Term::Zero, Term::Zero),
                  &id(Term::Zero, num(1)), &c(0), FUEL),
        Err(ConvError::NotConvertible)
    );
    // El of the encoding decodes to the Id former.
    let el_id = Type::El {
        level: Level::Zero,
        tm: rt(Term::TmId {
            level: Level::Zero,
            ty: rt(Term::TmNat),
            lhs: rt(beta_zero()),
            rhs: rt(Term::Zero),
        }),
    };
    assert_eq!(
        conv_type(&psi, &g0, Layer::Prog, &el_id, &id(Term::Zero, Term::Zero), &c(0), FUEL),
        Ok(())
    );
}

#[test]
fn refl_and_j_conversion() {
    let psi = psi(vec![]);
    let id00 = Type::Id {
        level: Level::Zero,
        ty: rty(Type::Nat),
        lhs: rt(Term::Zero),
        rhs: rt(Term::Zero),
    };
    // refl ≈ refl at Id, through β-convertible points.
    let refl = |tm: Term| Term::Refl { level: Level::Zero, ty: rty(Type::Nat), tm: rt(tm) };
    ok_tm(&psi, &nil_ctx(0), &refl(beta_zero()), &refl(Term::Zero), &id00, &c(0));
    // J β-fires against its case during conversion.
    let j = |case: Term, proof: Term| Term::J {
        ty_level: Level::Zero,
        motive_level: Level::Zero,
        ty: rty(Type::Nat),
        lhs: rt(Term::Zero),
        motive: rty(Type::Nat),
        case: rt(case),
        rhs: rt(Term::Zero),
        proof: rt(proof),
    };
    ok_tm(&psi, &nil_ctx(0), &j(num(2), refl(Term::Zero)), &num(2), &Type::Nat, &c(0));
    // Neutral J (proof is a variable): annotations compared, β-convertible
    // cases accepted, differing cases rejected.
    let gamma = extend(&nil_ctx(0), id00, c(0));
    ok_tm(&psi, &gamma, &j(beta_zero(), v(0)), &j(Term::Zero, v(0)), &Type::Nat, &c(0));
    no_tm(&psi, &gamma, &j(Term::Zero, v(0)), &j(num(1), v(0)), &Type::Nat, &c(0));
}

// -------------------------------------------------------------------------
// Dependent pairs (extension beyond ch. 04; kernel-v1-extensions)
// -------------------------------------------------------------------------

#[test]
fn sigma_type_congruence() {
    let psi = psi(vec![]);
    let g0 = nil_ctx(0);
    let sig = |fst: Type, snd: Type| Type::Sigma {
        fst_level: Level::Zero,
        snd_level: Level::Zero,
        fst: rty(fst),
        snd: rty(snd),
    };
    // Congruence through a β-convertible first component:
    // El^0 ((λx. «Nat») 0) ⇝ El^0 «Nat» ⇝ Nat.
    let el_beta = Type::El { level: Level::Zero, tm: rt(app(lam(Term::TmNat), Term::Zero)) };
    assert_eq!(
        conv_type(&psi, &g0, Layer::Prog, &sig(el_beta, Type::Nat),
                  &sig(Type::Nat, Type::Nat), &c(0), FUEL),
        Ok(())
    );
    // A distinct second component is caught.
    assert_eq!(
        conv_type(&psi, &g0, Layer::Prog, &sig(Type::Nat, Type::Nat),
                  &sig(Type::Nat, sig(Type::Nat, Type::Nat)), &c(0), FUEL),
        Err(ConvError::NotConvertible)
    );
    // El of the encoding decodes to the Σ former.
    let el_sig = Type::El {
        level: Level::Zero,
        tm: rt(Term::TmSigma {
            fst_level: Level::Zero,
            snd_level: Level::Zero,
            fst: rt(Term::TmNat),
            snd: rt(Term::TmNat),
        }),
    };
    assert_eq!(
        conv_type(&psi, &g0, Layer::Prog, &el_sig, &sig(Type::Nat, Type::Nat), &c(0), FUEL),
        Ok(())
    );
}

#[test]
fn sigma_eta_surjective_pairing() {
    let psi = psi(vec![]);
    let sig = Type::Sigma {
        fst_level: Level::Zero,
        snd_level: Level::Zero,
        fst: rty(Type::Nat),
        snd: rty(Type::Nat),
    };
    let fst_of = |p: Term| Term::Fst {
        fst_level: Level::Zero,
        snd_level: Level::Zero,
        fst_ty: rty(Type::Nat),
        snd_ty: rty(Type::Nat),
        pair: rt(p),
    };
    let snd_of = |p: Term| Term::Snd {
        fst_level: Level::Zero,
        snd_level: Level::Zero,
        fst_ty: rty(Type::Nat),
        snd_ty: rty(Type::Nat),
        pair: rt(p),
    };
    let pair = |a: Term, b: Term| Term::Pair {
        fst_level: Level::Zero,
        snd_level: Level::Zero,
        fst_ty: rty(Type::Nat),
        snd_ty: rty(Type::Nat),
        fst: rt(a),
        snd: rt(b),
    };
    // η: a neutral p ≈ (fst p, snd p) definitionally, both directions.
    let gamma = extend(&nil_ctx(0), sig.clone(), c(0));
    let eta = pair(fst_of(v(0)), snd_of(v(0)));
    ok_tm(&psi, &gamma, &v(0), &eta, &sig, &c(0));
    ok_tm(&psi, &gamma, &eta, &v(0), &sig, &c(0));
    // η is not blind: two distinct neutral pairs are not convertible.
    let gamma2 = extend(&extend(&nil_ctx(0), sig.clone(), c(0)), sig.clone(), c(0));
    no_tm(&psi, &gamma2, &v(0), &v(1), &sig, &c(0));
    // Projections β-fire during conversion.
    ok_tm(&psi, &nil_ctx(0), &fst_of(pair(beta_zero(), num(1))), &Term::Zero, &Type::Nat, &c(0));
    ok_tm(&psi, &nil_ctx(0), &snd_of(pair(Term::Zero, num(2))), &num(2), &Type::Nat, &c(0));
    // A neutral fst distinguishes its scrutinee.
    no_tm(&psi, &gamma2, &fst_of(v(0)), &fst_of(v(1)), &Type::Nat, &c(0));
}

// -------------------------------------------------------------------------
// Unit and Empty (extension beyond ch. 04; kernel-v1-extensions)
// -------------------------------------------------------------------------

#[test]
fn unit_eta_proof_irrelevance() {
    let psi = psi(vec![]);
    // Two Unit-typed variables: every term at Unit is ≈ ⟨⟩ and ≈ every other,
    // including distinct neutrals (definitional proof irrelevance).
    let gamma = extend(&extend(&nil_ctx(0), Type::Unit, c(0)), Type::Unit, c(0));
    ok_tm(&psi, &gamma, &Term::Triv, &Term::Triv, &Type::Unit, &c(0));
    ok_tm(&psi, &gamma, &v(0), &Term::Triv, &Type::Unit, &c(0));
    ok_tm(&psi, &gamma, &v(0), &v(1), &Type::Unit, &c(0));
}

#[test]
fn empty_neutrals_and_encodings() {
    let psi = psi(vec![]);
    // At Empty only neutrals appear: equal vars convert, distinct ones do not.
    let gamma = extend(&extend(&nil_ctx(0), Type::Empty, c(0)), Type::Empty, c(0));
    ok_tm(&psi, &gamma, &v(0), &v(0), &Type::Empty, &c(0));
    no_tm(&psi, &gamma, &v(0), &v(1), &Type::Empty, &c(0));
    // Encodings congruence at Ty 0; «Unit» ≉ «Empty».
    ok_tm(&psi, &nil_ctx(0), &Term::TmUnit, &Term::TmUnit, &Type::Ty(c(0)), &c(1));
    no_tm(&psi, &nil_ctx(0), &Term::TmUnit, &Term::TmEmpty, &Type::Ty(c(0)), &c(1));
    // El-decode of the encodings, and Unit ≉ Empty as types.
    let el = |t: Term| Type::El { level: c(0), tm: rt(t) };
    assert_eq!(
        conv_type(&psi, &nil_ctx(0), Layer::Prog, &el(Term::TmUnit), &Type::Unit, &c(0), FUEL),
        Ok(())
    );
    assert_eq!(
        conv_type(&psi, &nil_ctx(0), Layer::Prog, &el(Term::TmEmpty), &Type::Empty, &c(0), FUEL),
        Ok(())
    );
    assert_eq!(
        conv_type(&psi, &nil_ctx(0), Layer::Prog, &Type::Unit, &Type::Empty, &c(0), FUEL),
        Err(ConvError::NotConvertible)
    );
}

#[test]
fn elim_empty_neutral_congruence() {
    let psi = psi(vec![]);
    let gamma = extend(&nil_ctx(0), Type::Empty, c(0));
    let elim = |m: Type| Term::ElimEmpty { level: c(0), motive: rty(m), scrut: rt(v(0)) };
    // Same motive: convertible at the result type.
    ok_tm(&psi, &gamma, &elim(Type::Nat), &elim(Type::Nat), &Type::Nat, &c(0));
    // β-convertible motive (El «Nat» ⇝ Nat) accepted.
    let el_nat = Type::El { level: c(0), tm: rt(Term::TmNat) };
    ok_tm(&psi, &gamma, &elim(el_nat), &elim(Type::Nat), &Type::Nat, &c(0));
    // A differing motive is caught.
    no_tm(&psi, &gamma, &elim(Type::Nat), &elim(Type::Unit), &Type::Nat, &c(0));
}

// -------------------------------------------------------------------------
// Binary sums (extension beyond ch. 04; kernel-v1-extensions)
// -------------------------------------------------------------------------

#[test]
fn sum_type_congruence() {
    let psi = psi(vec![]);
    let g0 = nil_ctx(0);
    let sum = |lhs: Type, rhs: Type| Type::Sum {
        lhs_level: Level::Zero,
        rhs_level: Level::Zero,
        lhs: rty(lhs),
        rhs: rty(rhs),
    };
    // Congruence through a β-convertible left component.
    let el_beta = Type::El { level: Level::Zero, tm: rt(app(lam(Term::TmNat), Term::Zero)) };
    assert_eq!(
        conv_type(&psi, &g0, Layer::Prog, &sum(el_beta, Type::Nat),
                  &sum(Type::Nat, Type::Nat), &c(0), FUEL),
        Ok(())
    );
    // A distinct right component is caught.
    assert_eq!(
        conv_type(&psi, &g0, Layer::Prog, &sum(Type::Nat, Type::Nat),
                  &sum(Type::Nat, Type::Unit), &c(0), FUEL),
        Err(ConvError::NotConvertible)
    );
    // El of the encoding decodes to the Sum former.
    let el_sum = Type::El {
        level: Level::Zero,
        tm: rt(Term::TmSum {
            lhs_level: Level::Zero,
            rhs_level: Level::Zero,
            lhs: rt(Term::TmNat),
            rhs: rt(Term::TmNat),
        }),
    };
    assert_eq!(
        conv_type(&psi, &g0, Layer::Prog, &el_sum, &sum(Type::Nat, Type::Nat), &c(0), FUEL),
        Ok(())
    );
}

#[test]
fn sum_positive_conversion_and_case_beta() {
    let psi = psi(vec![]);
    let sum = Type::Sum {
        lhs_level: Level::Zero,
        rhs_level: Level::Zero,
        lhs: rty(Type::Nat),
        rhs: rty(Type::Nat),
    };
    let inl = |a: Term| Term::Inl {
        lhs_level: Level::Zero,
        rhs_level: Level::Zero,
        lhs: rty(Type::Nat),
        rhs: rty(Type::Nat),
        val: rt(a),
    };
    let inr = |b: Term| Term::Inr {
        lhs_level: Level::Zero,
        rhs_level: Level::Zero,
        lhs: rty(Type::Nat),
        rhs: rty(Type::Nat),
        val: rt(b),
    };
    // Positive: same tag compares its value (β fires inside); tag mismatch and
    // a differing value are both NotConvertible.
    ok_tm(&psi, &nil_ctx(0), &inl(Term::Zero), &inl(beta_zero()), &sum, &c(0));
    no_tm(&psi, &nil_ctx(0), &inl(Term::Zero), &inl(num(1)), &sum, &c(0));
    no_tm(&psi, &nil_ctx(0), &inl(Term::Zero), &inr(Term::Zero), &sum, &c(0));
    ok_tm(&psi, &nil_ctx(0), &inr(num(2)), &inr(num(2)), &sum, &c(0));
    // A neutral scrutinee compares structurally, and never to a canonical
    // injection.
    let gamma = extend(&nil_ctx(0), sum.clone(), c(0));
    ok_tm(&psi, &gamma, &v(0), &v(0), &sum, &c(0));
    no_tm(&psi, &gamma, &v(0), &inl(Term::Zero), &sum, &c(0));
    // case β-fires during conversion (positive eliminator).
    let case = |scrut: Term| Term::Case {
        lhs_level: Level::Zero,
        rhs_level: Level::Zero,
        motive_level: Level::Zero,
        lhs: rty(Type::Nat),
        rhs: rty(Type::Nat),
        motive: rty(Type::Nat),
        case_l: rt(Term::Succ(rt(v(0)))),
        case_r: rt(v(0)),
        scrut: rt(scrut),
    };
    ok_tm(&psi, &nil_ctx(0), &case(inl(Term::Zero)), &num(1), &Type::Nat, &c(0));
    ok_tm(&psi, &nil_ctx(0), &case(inr(num(2))), &num(2), &Type::Nat, &c(0));
}

#[test]
fn case_neutral_congruence() {
    let psi = psi(vec![]);
    let sum = Type::Sum {
        lhs_level: Level::Zero,
        rhs_level: Level::Zero,
        lhs: rty(Type::Nat),
        rhs: rty(Type::Nat),
    };
    // case over a neutral variable z : Nat + Nat, constant Nat motive.
    let gamma = extend(&nil_ctx(0), sum, c(0));
    let case = |m: Type, l: Term, rr: Term| Term::Case {
        lhs_level: Level::Zero,
        rhs_level: Level::Zero,
        motive_level: Level::Zero,
        lhs: rty(Type::Nat),
        rhs: rty(Type::Nat),
        motive: rty(m),
        case_l: rt(l),
        case_r: rt(rr),
        scrut: rt(v(0)),
    };
    // Same everything: convertible at the result type.
    ok_tm(&psi, &gamma, &case(Type::Nat, v(0), v(0)),
          &case(Type::Nat, v(0), v(0)), &Type::Nat, &c(0));
    // A β-convertible motive (El «Nat» ⇝ Nat) is accepted.
    let el_nat = Type::El { level: c(0), tm: rt(Term::TmNat) };
    ok_tm(&psi, &gamma, &case(el_nat, v(0), v(0)),
          &case(Type::Nat, v(0), v(0)), &Type::Nat, &c(0));
    // A differing left branch is caught.
    no_tm(&psi, &gamma, &case(Type::Nat, v(0), v(0)),
          &case(Type::Nat, Term::Succ(rt(v(0))), v(0)), &Type::Nat, &c(0));
}

// -------------------------------------------------------------------------
// W-types (extension; kernel-v1-extensions)
// -------------------------------------------------------------------------

/// `W^{0,0}(x : Nat). Empty` — Nat-labeled leaves.
fn w_nat_empty() -> Type {
    Type::W {
        shape_level: Level::Zero,
        pos_level: Level::Zero,
        shape: rty(Type::Nat),
        pos: rty(Type::Empty),
    }
}

/// `λ^{0,0}(y : Empty). elim_Empty^0 (x. W; y)` — the childless subtree
/// function (closed).
fn no_children() -> Term {
    Term::Lam {
        dom_level: Level::Zero,
        cod_level: Level::Zero,
        dom: rty(Type::Empty),
        body: rt(Term::ElimEmpty {
            level: Level::Zero,
            motive: rty(w_nat_empty()),
            scrut: rt(v(0)),
        }),
    }
}

fn sup_leaf(label: Term) -> Term {
    Term::Sup {
        shape_level: Level::Zero,
        pos_level: Level::Zero,
        shape_ty: rty(Type::Nat),
        pos_ty: rty(Type::Empty),
        label: rt(label),
        children: rt(no_children()),
    }
}

#[test]
fn w_type_congruence() {
    let psi = psi(vec![]);
    let g0 = nil_ctx(0);
    let w = |shape: Type, pos: Type| Type::W {
        shape_level: Level::Zero,
        pos_level: Level::Zero,
        shape: rty(shape),
        pos: rty(pos),
    };
    // Congruence through a β-convertible shape.
    let el_beta = Type::El { level: Level::Zero, tm: rt(app(lam(Term::TmNat), Term::Zero)) };
    assert_eq!(
        conv_type(&psi, &g0, Layer::Prog, &w(el_beta, Type::Nat),
                  &w(Type::Nat, Type::Nat), &c(0), FUEL),
        Ok(())
    );
    // A distinct position family is caught.
    assert_eq!(
        conv_type(&psi, &g0, Layer::Prog, &w(Type::Nat, Type::Nat),
                  &w(Type::Nat, Type::Empty), &c(0), FUEL),
        Err(ConvError::NotConvertible)
    );
    // W is not Σ (same components, different former).
    let sigma = Type::Sigma {
        fst_level: Level::Zero,
        snd_level: Level::Zero,
        fst: rty(Type::Nat),
        snd: rty(Type::Nat),
    };
    assert_eq!(
        conv_type(&psi, &g0, Layer::Prog, &w(Type::Nat, Type::Nat), &sigma, &c(0), FUEL),
        Err(ConvError::NotConvertible)
    );
    // El of the encoding decodes to the W former.
    let el_w = Type::El {
        level: Level::Zero,
        tm: rt(Term::TmW {
            shape_level: Level::Zero,
            pos_level: Level::Zero,
            shape: rt(Term::TmNat),
            pos: rt(Term::TmNat),
        }),
    };
    assert_eq!(
        conv_type(&psi, &g0, Layer::Prog, &el_w, &w(Type::Nat, Type::Nat), &c(0), FUEL),
        Ok(())
    );
}

#[test]
fn w_positive_conversion_and_elim_beta() {
    let psi = psi(vec![]);
    let w = w_nat_empty();
    // Positive: sup compares the label (β fires inside) and the subtree
    // function; a differing label is NotConvertible.
    ok_tm(&psi, &nil_ctx(0), &sup_leaf(Term::Zero), &sup_leaf(beta_zero()), &w, &c(0));
    no_tm(&psi, &nil_ctx(0), &sup_leaf(Term::Zero), &sup_leaf(num(1)), &w, &c(0));
    // A neutral scrutinee compares structurally, and never to a canonical sup.
    let gamma = extend(&nil_ctx(0), w.clone(), c(0));
    ok_tm(&psi, &gamma, &v(0), &v(0), &w, &c(0));
    no_tm(&psi, &gamma, &v(0), &sup_leaf(Term::Zero), &w, &c(0));
    // elim_W β-fires during conversion: with step = a, the whole eliminator
    // converts to the label.
    let elim = |scrut: Term| Term::ElimW {
        shape_level: Level::Zero,
        pos_level: Level::Zero,
        motive_level: Level::Zero,
        shape: rty(Type::Nat),
        pos: rty(Type::Empty),
        motive: rty(Type::Nat),
        step: rt(v(2)),
        scrut: rt(scrut),
    };
    ok_tm(&psi, &nil_ctx(0), &elim(sup_leaf(num(2))), &num(2), &Type::Nat, &c(0));
}

#[test]
fn elim_w_neutral_congruence() {
    let psi = psi(vec![]);
    // elim_W over a neutral variable z : W, constant Nat motive.
    let gamma = extend(&nil_ctx(0), w_nat_empty(), c(0));
    let elim = |m: Type, step: Term| Term::ElimW {
        shape_level: Level::Zero,
        pos_level: Level::Zero,
        motive_level: Level::Zero,
        shape: rty(Type::Nat),
        pos: rty(Type::Empty),
        motive: rty(m),
        step: rt(step),
        scrut: rt(v(0)),
    };
    // Same everything: convertible at the result type.
    ok_tm(&psi, &gamma, &elim(Type::Nat, v(2)),
          &elim(Type::Nat, v(2)), &Type::Nat, &c(0));
    // A β-convertible motive (El «Nat» ⇝ Nat) is accepted.
    let el_nat = Type::El { level: c(0), tm: rt(Term::TmNat) };
    ok_tm(&psi, &gamma, &elim(el_nat, v(2)),
          &elim(Type::Nat, v(2)), &Type::Nat, &c(0));
    // A differing step is caught.
    no_tm(&psi, &gamma, &elim(Type::Nat, v(2)),
          &elim(Type::Nat, Term::Succ(rt(v(2)))), &Type::Nat, &c(0));
}
