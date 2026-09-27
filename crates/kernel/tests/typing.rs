//! Golden tests for the ch. 04 type checker: hand-elaborated instances per
//! judgment family — MLTT at layers c/p (variables, Π/λ/app with the
//! conversion rule firing, elim_Nat, encodings/El), the layer-v and ω
//! disciplines, global contexts and local substitutions, universe
//! polymorphism, contextual types (box/letbox, checking-only box under
//! binders), and the code recursors, including a full *identity recursor*
//! whose 56 branches re-box their telescopes' code — an end-to-end exercise
//! of every `G_Typ`/`G_Trm` telescope.
//!
//! No generator-based properties: the generators produce ill-typed terms,
//! where a legitimate `Err` is indistinguishable from a bug (property tests
//! against conversion are tracked in issues/kernel-conv-properties.md).

use std::sync::Arc as Rc;

use heather_kernel::layer::Layer;
use heather_kernel::level::{Level, UnivVar};
use heather_kernel::reduce::whnf_term;
use heather_kernel::term::{
    nth, Branches, CtxBase, CtxEntry, GlobalBinding, GlobalCtx, GlobalVar, LocalCtx,
    LocalSubst, LocalVar, Motives, SubstTail, Term, Type,
};
use heather_kernel::typing::{
    check_global_ctx, check_global_ctx_extension, check_local_ctx, check_local_subst, check_term,
    check_type, infer_term, infer_type, TypeError,
};

const FUEL: u64 = 100_000;

// -------------------------------------------------------------------------
// Construction helpers (mirroring tests/conv.rs; the telescope-shaped ones
// are deliberately re-derived from docs/delam/04 rather than shared with
// src/rec.rs, so the identity-recursor test cross-checks those tables)
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

fn nil_ctx() -> LocalCtx {
    LocalCtx::nil()
}

/// The context consisting of the context variable at index `i`.
fn g_ctx(i: u32) -> LocalCtx {
    LocalCtx::ctx_var(GlobalVar(i))
}

/// `Δ, x : ty @ level`.
fn ext(base: &LocalCtx, ty: Type, level: Level) -> LocalCtx {
    let mut c = base.clone();
    c.entries.push(CtxEntry { ty: rty(ty), level });
    c
}

/// `U^{id_Δ}`.
fn gty(var: u32, ctx: &LocalCtx) -> Type {
    Type::GlobalTy { var: GlobalVar(var), subst: LocalSubst::id(ctx) }
}

/// `u^{id_Δ}`.
fn gtm(var: u32, ctx: &LocalCtx) -> Term {
    Term::GlobalTm { var: GlobalVar(var), subst: LocalSubst::id(ctx) }
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

/// `Π^{0,0}(x : Nat). Nat`.
fn nat_to_nat() -> Type {
    Type::Pi {
        dom_level: Level::Zero,
        cod_level: Level::Zero,
        dom: rty(Type::Nat),
        cod: rty(Type::Nat),
    }
}

fn infer_closed(layer: Layer, t: &Term) -> Result<(Type, Level), TypeError> {
    infer_term(&GlobalCtx::default(), 0, layer, &nil_ctx(), t, FUEL)
}

fn check_closed(layer: Layer, t: &Term, ty: &Type, l: &Level) -> Result<(), TypeError> {
    check_term(&GlobalCtx::default(), 0, layer, &nil_ctx(), t, ty, l, FUEL)
}

// -------------------------------------------------------------------------
// MLTT at layers c/p
// -------------------------------------------------------------------------

#[test]
fn identity_function_infers_pi() {
    let id = lam(v(0));
    let (ty, l) = infer_closed(Layer::Prog, &id).unwrap();
    assert!(ty == nat_to_nat());
    assert!(l.equiv(&Level::Zero));
    // The same term also types at layer c (code is full MLTT syntax) …
    check_closed(Layer::Code, &id, &nat_to_nat(), &Level::Zero).unwrap();
    // … but not at layer v (variables only).
    assert_eq!(
        infer_closed(Layer::Var, &id).unwrap_err(),
        TypeError::LayerMismatch
    );
}

#[test]
fn application_and_beta_conversion() {
    // (λx. x) 0 : Nat, and also against the β/El-convertible El 0 Nat.
    let t = app(lam(v(0)), Term::Zero);
    check_closed(Layer::Prog, &t, &Type::Nat, &Level::Zero).unwrap();
    let el_nat = Type::El { level: Level::Zero, tm: rt(Term::TmNat) };
    check_closed(Layer::Prog, &t, &el_nat, &Level::Zero).unwrap();
    // Wrong type is NotConvertible, not a level problem.
    assert_eq!(
        check_closed(Layer::Prog, &t, &nat_to_nat(), &Level::Zero).unwrap_err(),
        TypeError::NotConvertible
    );
}

#[test]
fn variables_and_dependent_context() {
    // Γ = (·, A : Ty 0 @ 1, x : El 0 A @ 0) is well-formed; x infers El 0 A.
    let gamma = ext(
        &ext(&nil_ctx(), Type::Ty(Level::Zero), c(1)),
        Type::El { level: Level::Zero, tm: rt(v(0)) },
        Level::Zero,
    );
    let psi = GlobalCtx::default();
    check_local_ctx(&psi, 0, Layer::Prog, &gamma, FUEL).unwrap();
    let (ty, l) = infer_term(&psi, 0, Layer::Prog, &gamma, &v(0), FUEL).unwrap();
    // The entry's type is weakened past x itself: El 0 (Var 1).
    assert!(ty == Type::El { level: Level::Zero, tm: rt(v(1)) });
    assert!(l.equiv(&Level::Zero));
    // Var at layer v is admitted.
    infer_term(&psi, 0, Layer::Var, &gamma, &v(0), FUEL).unwrap();
    // An entry whose type lives at the wrong level is rejected.
    let bad = ext(&nil_ctx(), Type::Ty(Level::Zero), c(2));
    assert_eq!(
        check_local_ctx(&psi, 0, Layer::Prog, &bad, FUEL).unwrap_err(),
        TypeError::LevelMismatch
    );
}

#[test]
fn elim_nat() {
    // elim_Nat^0 (x. Nat) 0 (x, y. su y) (su 0) : Nat — a predecessor-ish
    // shape exercising motive/base/step/scrut premises.
    let t = Term::ElimNat {
        level: Level::Zero,
        motive: rty(Type::Nat),
        base: rt(Term::Zero),
        step: rt(Term::Succ(rt(v(0)))),
        scrut: rt(Term::Succ(rt(Term::Zero))),
    };
    let (ty, l) = infer_closed(Layer::Prog, &t).unwrap();
    assert!(ty == Type::Nat);
    assert!(l.equiv(&Level::Zero));
    // A step whose type doesn't match the motive is rejected.
    let bad = Term::ElimNat {
        level: Level::Zero,
        motive: rty(Type::Nat),
        base: rt(Term::Zero),
        step: rt(Term::TmNat),
        scrut: rt(Term::Zero),
    };
    assert!(infer_closed(Layer::Prog, &bad).is_err());
}

#[test]
fn encodings_and_non_cumulativity() {
    // Nat-the-encoding : Ty 0 @ 1, and decodes: El 0 Nat is a type @ 0.
    let (ty, l) = infer_closed(Layer::Prog, &Term::TmNat).unwrap();
    assert!(ty == Type::Ty(Level::Zero));
    assert!(l.equiv(&c(1)));
    let el = Type::El { level: Level::Zero, tm: rt(Term::TmNat) };
    let il = infer_type(&GlobalCtx::default(), 0, Layer::Prog, &nil_ctx(), &el, FUEL).unwrap();
    assert!(il.equiv(&Level::Zero));
    // Non-cumulativity: Nat : Ty 0 does not also live in Ty 1.
    assert_eq!(
        check_closed(Layer::Prog, &Term::TmNat, &Type::Ty(c(1)), &c(2)).unwrap_err(),
        TypeError::LevelMismatch
    );
}

// -------------------------------------------------------------------------
// ω and universe polymorphism
// -------------------------------------------------------------------------

#[test]
fn omega_is_rejected_in_programmer_positions() {
    let psi = GlobalCtx::default();
    assert_eq!(
        infer_type(&psi, 0, Layer::Prog, &nil_ctx(), &Type::Ty(Level::Omega), FUEL)
            .unwrap_err(),
        TypeError::IllFormedLevel
    );
    let bad_lam = Term::Lam {
        dom_level: Level::Omega,
        cod_level: Level::Zero,
        dom: rty(Type::Nat),
        body: rt(v(0)),
    };
    assert_eq!(
        infer_closed(Layer::Meta, &bad_lam).unwrap_err(),
        TypeError::IllFormedLevel
    );
    // Out-of-scope universe variable, same error.
    assert_eq!(
        infer_type(&psi, 0, Layer::Prog, &nil_ctx(), &Type::Ty(lv(0)), FUEL).unwrap_err(),
        TypeError::IllFormedLevel
    );
}

#[test]
fn universe_polymorphism() {
    // Λℓ. Ty ℓ (the encoding) : ΠΠ ℓ. Ty (1+ℓ) @ ω, layer m only.
    let ulam = Term::ULam {
        num_vars: 1,
        level: Level::succ(Level::succ(lv(0))),
        body: rt(Term::TmTy(lv(0))),
    };
    let (ty, l) = infer_closed(Layer::Meta, &ulam).unwrap();
    let expect = Type::UPi {
        num_vars: 1,
        level: Level::succ(Level::succ(lv(0))),
        body: rty(Type::Ty(Level::succ(lv(0)))),
    };
    assert!(ty == expect);
    assert!(l.equiv(&Level::Omega));
    assert_eq!(
        infer_closed(Layer::Prog, &ulam).unwrap_err(),
        TypeError::LayerMismatch
    );

    // (Λℓ. Ty ℓ) $ 1 : Ty 2 @ 3.
    let uapp = Term::UApp { fun: rt(ulam.clone()), levels: vec![c(1)] };
    let (ty, l) = infer_closed(Layer::Meta, &uapp).unwrap();
    assert!(ty == Type::Ty(Level::succ(c(1))));
    assert!(l.equiv(&c(3)));

    // Arity and ω discipline on the level vector.
    let bad_arity = Term::UApp { fun: rt(ulam.clone()), levels: vec![c(1), c(2)] };
    assert_eq!(
        infer_closed(Layer::Meta, &bad_arity).unwrap_err(),
        TypeError::UnivArityMismatch
    );
    let bad_omega = Term::UApp { fun: rt(ulam), levels: vec![Level::Omega] };
    assert_eq!(
        infer_closed(Layer::Meta, &bad_omega).unwrap_err(),
        TypeError::IllFormedLevel
    );
}

// -------------------------------------------------------------------------
// Global contexts, global variables, local substitutions
// -------------------------------------------------------------------------

/// Ψ = (g : Ctx, U : Typ_c(g, 0), u : Trm_v(g ⊢ U^id @ 0)).
fn sample_psi() -> GlobalCtx {
    GlobalCtx::new(vec![
            GlobalBinding::Ctx,
            GlobalBinding::Ty { ctx: g_ctx(0), layer: Layer::Code, level: Level::Zero },
            GlobalBinding::Tm {
                ctx: g_ctx(1),
                layer: Layer::Var,
                ty: rty(gty(0, &g_ctx(1))),
                level: Level::Zero,
                body: None,
            },
        ])
}

#[test]
fn global_context_formation() {
    check_global_ctx(&sample_psi(), 0, FUEL).unwrap();
    // A Ty binding may not live at layer m …
    let bad = GlobalCtx::new(vec![GlobalBinding::Ty {
            ctx: nil_ctx(),
            layer: Layer::Meta,
            level: Level::Zero,
        }]);
    assert_eq!(check_global_ctx(&bad, 0, FUEL).unwrap_err(), TypeError::LayerMismatch);
    // … and a binding's context must be well-formed in its prefix.
    let unbound = GlobalCtx::new(vec![GlobalBinding::Ty {
            ctx: g_ctx(0),
            layer: Layer::Code,
            level: Level::Zero,
        }]);
    assert_eq!(
        check_global_ctx(&unbound, 0, FUEL).unwrap_err(),
        TypeError::UnboundGlobalVar(0)
    );
}

#[test]
fn global_context_extension_checks_only_the_ordered_suffix() {
    let all = sample_psi();
    let bindings = all.bindings.to_vec();
    let prefix = GlobalCtx::new(bindings[..1].to_vec());
    check_global_ctx(&prefix, 0, FUEL).unwrap();
    check_global_ctx_extension(&prefix, &bindings[1..], 0, FUEL).unwrap();

    let bad = [GlobalBinding::Ty {
        ctx: g_ctx(9),
        layer: Layer::Code,
        level: Level::Zero,
    }];
    assert_eq!(
        check_global_ctx_extension(&prefix, &bad, 0, FUEL).unwrap_err(),
        TypeError::UnboundGlobalVar(9)
    );
}

#[test]
fn global_variables_and_layer_order() {
    let psi = sample_psi();
    // In Γ = g (viewing the innermost binding: g = index 2, U = 1, u = 0),
    // U^id is a type @ 0 at layer c, and u^id : U^id @ 0 — at layers v..m.
    let gamma = g_ctx(2);
    let il = infer_type(&psi, 0, Layer::Code, &gamma, &gty(1, &gamma), FUEL).unwrap();
    assert!(il.equiv(&Level::Zero));
    for layer in [Layer::Var, Layer::Code, Layer::Prog, Layer::Meta] {
        let (ty, l) = infer_term(&psi, 0, layer, &gamma, &gtm(0, &gamma), FUEL).unwrap();
        assert!(ty == gty(1, &gamma));
        assert!(l.equiv(&Level::Zero));
    }
    // A layer-c term binding is not visible at layer v (i' ≤ i fails).
    let psi_c = GlobalCtx::new(vec![
            GlobalBinding::Ctx,
            GlobalBinding::Tm {
                ctx: g_ctx(0),
                layer: Layer::Code,
                ty: rty(Type::Nat),
                level: Level::Zero,
                body: None,
            },
        ]);
    let gamma = g_ctx(1);
    assert_eq!(
        infer_term(&psi_c, 0, Layer::Var, &gamma, &gtm(0, &gamma), FUEL).unwrap_err(),
        TypeError::LayerMismatch
    );
}

#[test]
fn local_substitutions() {
    let psi = GlobalCtx::default();
    // δ = (·⁰, 0/x) : (·, x : Nat @ 0) from Γ = ·.
    let target = ext(&nil_ctx(), Type::Nat, Level::Zero);
    let delta = LocalSubst {
        tail: SubstTail::Empty { len: 0, base: CtxBase::Nil },
        terms: vec![rt(Term::Zero)],
    };
    check_local_subst(&psi, 0, Layer::Prog, &nil_ctx(), &delta, &target, FUEL).unwrap();
    // Entry count mismatch.
    let short = LocalSubst {
        tail: SubstTail::Empty { len: 0, base: CtxBase::Nil },
        terms: vec![],
    };
    assert_eq!(
        check_local_subst(&psi, 0, Layer::Prog, &nil_ctx(), &short, &target, FUEL)
            .unwrap_err(),
        TypeError::SubstMismatch
    );
    // Tail records the wrong source length.
    let bad_len = LocalSubst {
        tail: SubstTail::Empty { len: 3, base: CtxBase::Nil },
        terms: vec![rt(Term::Zero)],
    };
    assert_eq!(
        check_local_subst(&psi, 0, Layer::Prog, &nil_ctx(), &bad_len, &target, FUEL)
            .unwrap_err(),
        TypeError::SubstMismatch
    );
    // At layer v the step terms must be variables: 0/x is rejected there,
    // x'/x (from a matching Γ) is accepted.
    assert_eq!(
        check_local_subst(&psi, 0, Layer::Var, &nil_ctx(), &delta, &target, FUEL)
            .unwrap_err(),
        TypeError::LayerMismatch
    );
    let gamma = ext(&nil_ctx(), Type::Nat, Level::Zero);
    let var_delta = LocalSubst {
        tail: SubstTail::Empty { len: 1, base: CtxBase::Nil },
        terms: vec![rt(v(0))],
    };
    check_local_subst(&psi, 0, Layer::Var, &gamma, &var_delta, &target, FUEL).unwrap();
}

// -------------------------------------------------------------------------
// Contextual types: box, letbox
// -------------------------------------------------------------------------

#[test]
fn box_checks_against_code_types() {
    // box 0 : □(· ⊢ Nat @ 0) @ 0, layer m only.
    let code_nat = Type::CodeTm { ctx: nil_ctx(), ty: rty(Type::Nat), level: Level::Zero };
    check_closed(Layer::Meta, &Term::BoxTm(rt(Term::Zero)), &code_nat, &Level::Zero).unwrap();
    assert_eq!(
        check_closed(Layer::Prog, &Term::BoxTm(rt(Term::Zero)), &code_nat, &Level::Zero)
            .unwrap_err(),
        TypeError::LayerMismatch
    );
    // Code is checked at layer c: a β-redex is fine *syntax* there …
    let code = Term::BoxTm(rt(app(lam(v(0)), Term::Zero)));
    check_closed(Layer::Meta, &code, &code_nat, &Level::Zero).unwrap();
    // … and box is not inferable (its Δ and l are not in the term).
    assert_eq!(
        infer_closed(Layer::Meta, &code).unwrap_err(),
        TypeError::NotInferable
    );
    // box of a *type*: box Nat : □(· ⊢ Ty 0) @ 0.
    let code_ty = Type::CodeTy { ctx: nil_ctx(), level: Level::Zero };
    check_closed(Layer::Meta, &Term::BoxTy(rty(Type::Nat)), &code_ty, &Level::Zero).unwrap();
    // Level mismatch inside the box: Π lives at 0, not 1.
    let code_ty1 = Type::CodeTy { ctx: nil_ctx(), level: c(1) };
    assert_eq!(
        check_closed(Layer::Meta, &Term::BoxTy(rty(nat_to_nat())), &code_ty1, &Level::Zero)
            .unwrap_err(),
        TypeError::LevelMismatch
    );
}

#[test]
fn box_checks_under_binders() {
    // Λ^0(g : Ctx). box Nat : (g : Ctx) ⇒^0 □(g ⊢ Ty 0) — the checking-only
    // box must be reachable through the intro form.
    let t = Term::CtxLam { level: Level::Zero, body: rt(Term::BoxTy(rty(Type::Nat))) };
    let ty = Type::CtxPi {
        level: Level::Zero,
        body: rty(Type::CodeTy { ctx: g_ctx(0), level: Level::Zero }),
    };
    check_closed(Layer::Meta, &t, &ty, &Level::Zero).unwrap();
    // Same wrapped in a λ.
    let t2 = Term::Lam {
        dom_level: Level::Zero,
        cod_level: Level::Zero,
        dom: rty(Type::Nat),
        body: rt(Term::BoxTm(rt(Term::Zero))),
    };
    let ty2 = Type::Pi {
        dom_level: Level::Zero,
        cod_level: Level::Zero,
        dom: rty(Type::Nat),
        cod: rty(Type::CodeTm { ctx: nil_ctx(), ty: rty(Type::Nat), level: Level::Zero }),
    };
    check_closed(Layer::Meta, &t2, &ty2, &Level::Zero).unwrap();
}

#[test]
fn letbox_term() {
    // letbox^{0,0} · Nat (x_t. Nat) (u. u^{·¹}) (box 0) : Nat — splice the
    // bound code back in via the global variable.
    let body = Term::GlobalTm {
        var: GlobalVar(0),
        subst: LocalSubst { tail: SubstTail::Empty { len: 0, base: CtxBase::Nil }, terms: vec![] },
    };
    let t = Term::LetBoxTm {
        motive_level: Level::Zero,
        code_level: Level::Zero,
        ctx: nil_ctx(),
        ty: rty(Type::Nat),
        motive: rty(Type::Nat),
        body: rt(body),
        scrut: rt(Term::BoxTm(rt(Term::Zero))),
    };
    let (ty, l) = infer_closed(Layer::Meta, &t).unwrap();
    assert!(ty == Type::Nat);
    assert!(l.equiv(&Level::Zero));
    assert_eq!(
        infer_closed(Layer::Prog, &t).unwrap_err(),
        TypeError::LayerMismatch
    );
}

// -------------------------------------------------------------------------
// Code recursors
// -------------------------------------------------------------------------

/// Constant-Nat motives: every branch type collapses to Nat.
fn constant_motives() -> Rc<Motives> {
    Rc::new(Motives { ty_motive: rty(Type::Nat), tm_motive: rty(Type::Nat) })
}

fn constant_branches() -> Rc<Branches> {
    let z = || rt(Term::Zero);
    Rc::new(Branches {
        ty_nat: z(),
        ty_pi: z(),
        ty_ty: z(),
        ty_el: z(),
        ty_id: z(),
        ty_sigma: z(),
        tm_var: z(),
        tm_nat: z(),
        tm_pi: z(),
        tm_ty: z(),
        tm_zero: z(),
        tm_succ: z(),
        tm_elim_nat: z(),
        tm_lam: z(),
        tm_app: z(),
        tm_id: z(),
        tm_refl: z(),
        tm_j: z(),
        tm_sigma: z(),
        tm_pair: z(),
        tm_fst: z(),
        tm_snd: z(),
        ty_unit: z(),
        ty_empty: z(),
        tm_unit: z(),
        tm_empty: z(),
        tm_triv: z(),
        tm_elim_empty: z(),
        ty_sum: z(),
        tm_sum: z(),
        tm_inl: z(),
        tm_inr: z(),
        tm_case: z(),
        ty_w: z(),
        tm_w: z(),
        tm_sup: z(),
        tm_elim_w: z(),
        ty_vec: z(),
        tm_vec: z(),
        ty_fin: z(),
        tm_fin: z(),
        ty_wf: z(),
        tm_wf: z(),
        tm_supf: z(),
        tm_elim_wf: z(),
        ty_seq: z(),
        tm_seq: z(),
        ty_sempty: z(),
        tm_sempty: z(),
        tm_srefl: z(),
        tm_transp: z(),
        tm_elim_sempty: z(),
        ty_squash: z(),
        tm_squash: z(),
        tm_squash_in: z(),
        tm_elim_squash: z(),
    })
}

#[test]
fn recursor_with_constant_motive() {
    // elim^Typ over box Nat with constant-Nat motives and all-zero
    // branches: every telescope is entered, every branch type is Nat.
    let t = Term::ElimCodeTy {
        ty_motive_level: Level::Zero,
        tm_motive_level: Level::Zero,
        motives: constant_motives(),
        branches: constant_branches(),
        code_level: Level::Zero,
        ctx: nil_ctx(),
        scrut: rt(Term::BoxTy(rty(Type::Nat))),
    };
    let (ty, l) = infer_closed(Layer::Meta, &t).unwrap();
    assert!(ty == Type::Nat);
    assert!(l.equiv(&Level::Zero));
    // One ill-typed branch poisons the whole recursor.
    let mut bad = constant_branches();
    Rc::make_mut(&mut bad).tm_ty = rt(Term::TmNat);
    let t_bad = Term::ElimCodeTy {
        ty_motive_level: Level::Zero,
        tm_motive_level: Level::Zero,
        motives: constant_motives(),
        branches: bad,
        code_level: Level::Zero,
        ctx: nil_ctx(),
        scrut: rt(Term::BoxTy(rty(Type::Nat))),
    };
    assert!(infer_closed(Layer::Meta, &t_bad).is_err());
    // Layer p may not run recursors.
    assert_eq!(infer_closed(Layer::Prog, &t).unwrap_err(), TypeError::LayerMismatch);
}

/// The identity recursor: motives are the contextual types themselves and
/// every branch re-boxes the code its telescope describes. Checking it
/// exercises each `G_Typ`/`G_Trm` telescope end-to-end: every global
/// binding, recursive-call entry, and instantiated motive type must line
/// up for the re-boxed code to type-check at layer c.
///
/// Telescope views (innermost = 0) follow docs/delam/04 §More Typing:
/// e.g. in `t_app`: g = 4, U_S = 3, U_T = 2, u_t = 1, u_s = 0.
fn identity_motives() -> Rc<Motives> {
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

fn identity_branches() -> Rc<Branches> {
    // Shared telescope contexts.
    let g1 = g_ctx(1);
    let g2 = g_ctx(2);
    let g3 = g_ctx(3);
    let g4 = g_ctx(4);
    // ty_pi / tm_app: (g, x : U_S^id @ ℓ)
    let gx_typi = ext(&g2, gty(1, &g2), lv(1));
    let gx_app = ext(&g4, gty(3, &g4), lv(1));
    // tm_pi: (g, x : El ℓ u_s^id @ ℓ)
    let gx_tmpi = ext(&g2, Type::El { level: lv(1), tm: rt(gtm(1, &g2)) }, lv(1));
    // tm_lam: (g, x : U_S^id @ ℓ)
    let gx_lam = ext(&g3, gty(2, &g3), lv(1));
    // tm_elim_nat: (g, x : Nat @ 0) and (g, x : Nat, y : U_M^id @ ℓ)
    let gx_nat = ext(&g4, Type::Nat, Level::Zero);
    let u_m = Type::GlobalTy { var: GlobalVar(3), subst: LocalSubst::id(&gx_nat) };
    let gxy = ext(&gx_nat, u_m.clone(), lv(0));

    Rc::new(Branches {
        // box Nat
        ty_nat: rt(Term::BoxTy(rty(Type::Nat))),
        // box (Π^{ℓ,ℓ'}(x : U_S^id). U_T^id)
        ty_pi: rt(Term::BoxTy(rty(Type::Pi {
            dom_level: lv(1),
            cod_level: lv(0),
            dom: rty(gty(1, &g2)),
            cod: rty(gty(0, &gx_typi)),
        }))),
        // box (Ty ℓ)
        ty_ty: rt(Term::BoxTy(rty(Type::Ty(lv(0))))),
        // box (El ℓ u_t^id)
        ty_el: rt(Term::BoxTy(rty(Type::El { level: lv(0), tm: rt(gtm(0, &g1)) }))),
        // box u_x^id
        tm_var: rt(Term::BoxTm(rt(gtm(0, &g2)))),
        // box Nat (the encoding)
        tm_nat: rt(Term::BoxTm(rt(Term::TmNat))),
        // box (Π^{ℓ,ℓ'}(x : u_s^id). u_t^id) (the encoding)
        tm_pi: rt(Term::BoxTm(rt(Term::TmPi {
            dom_level: lv(1),
            cod_level: lv(0),
            dom: rt(gtm(1, &g2)),
            cod: rt(gtm(0, &gx_tmpi)),
        }))),
        // box (Ty ℓ) (the encoding)
        tm_ty: rt(Term::BoxTm(rt(Term::TmTy(lv(0))))),
        // box ze
        tm_zero: rt(Term::BoxTm(rt(Term::Zero))),
        // box (su u_t^id)
        tm_succ: rt(Term::BoxTm(rt(Term::Succ(rt(gtm(0, &g1)))))),
        // box (elim_Nat^ℓ (x. U_M^id) u_s^id (x,y. u_s'^id) u_t^id)
        tm_elim_nat: rt(Term::BoxTm(rt(Term::ElimNat {
            level: lv(0),
            motive: rty(u_m),
            base: rt(gtm(2, &g4)),
            step: rt(gtm(1, &gxy)),
            scrut: rt(gtm(0, &g4)),
        }))),
        // box (λ^{ℓ,ℓ'}(x : U_S^id). u_t^id)
        tm_lam: rt(Term::BoxTm(rt(Term::Lam {
            dom_level: lv(1),
            cod_level: lv(0),
            dom: rty(gty(2, &g3)),
            body: rt(gtm(0, &gx_lam)),
        }))),
        // box (app(u_t^id; ℓ,ℓ'; x : U_S^id. U_T^id; u_s^id))
        tm_app: rt(Term::BoxTm(rt(Term::App {
            fun: rt(gtm(1, &g4)),
            dom_level: lv(1),
            cod_level: lv(0),
            dom: rty(gty(3, &g4)),
            cod: rty(gty(2, &gx_app)),
            arg: rt(gtm(0, &g4)),
        }))),
        // -- extension branches (kernel-v1-extensions) --
        // box (Id^ℓ(U_S^id; u_t^id; u_u^id))
        ty_id: rt(Term::BoxTy(rty(Type::Id {
            level: lv(0),
            ty: rty(gty(2, &g3)),
            lhs: rt(gtm(1, &g3)),
            rhs: rt(gtm(0, &g3)),
        }))),
        // box (Σ^{ℓ,ℓ'}(U_S^id; U_T^id))
        ty_sigma: rt(Term::BoxTy(rty(Type::Sigma {
            fst_level: lv(1),
            snd_level: lv(0),
            fst: rty(gty(1, &g2)),
            snd: rty(gty(0, &gx_typi)),
        }))),
        // box (Id^ℓ(u_S^id; u_t^id; u_u^id)) (the encoding)
        tm_id: rt(Term::BoxTm(rt(Term::TmId {
            level: lv(0),
            ty: rt(gtm(2, &g3)),
            lhs: rt(gtm(1, &g3)),
            rhs: rt(gtm(0, &g3)),
        }))),
        // box (refl^ℓ(U_S^id; u_t^id))
        tm_refl: rt(Term::BoxTm(rt(Term::Refl {
            level: lv(0),
            ty: rty(gty(1, &g2)),
            tm: rt(gtm(0, &g2)),
        }))),
        // box (J^{ℓ,ℓ'}(U_S^id; u_a^id; y p. U_M^id; u_c^id; u_r^id; u_e^id))
        tm_j: {
            let g6 = g_ctx(6);
            let gy = ext(&g6, gty(5, &g6), lv(1));
            let p_ty = Type::Id {
                level: lv(1),
                ty: rty(gty(5, &g6).shift_local(1)),
                lhs: rt(gtm(4, &g6).shift_local(1)),
                rhs: rt(Term::Var(LocalVar(0))),
            };
            let gyp = ext(&gy, p_ty, lv(1));
            rt(Term::BoxTm(rt(Term::J {
                ty_level: lv(1),
                motive_level: lv(0),
                ty: rty(gty(5, &g6)),
                lhs: rt(gtm(4, &g6)),
                motive: rty(Type::GlobalTy {
                    var: GlobalVar(3),
                    subst: LocalSubst::id(&gyp),
                }),
                case: rt(gtm(2, &g6)),
                rhs: rt(gtm(1, &g6)),
                proof: rt(gtm(0, &g6)),
            })))
        },
        // box (Σ^{ℓ,ℓ'}(u_S^id; u_t^id)) (the encoding)
        tm_sigma: {
            let gx = ext(&g2, Type::El { level: lv(1), tm: rt(gtm(1, &g2)) }, lv(1));
            rt(Term::BoxTm(rt(Term::TmSigma {
                fst_level: lv(1),
                snd_level: lv(0),
                fst: rt(gtm(1, &g2)),
                snd: rt(gtm(0, &gx)),
            })))
        },
        // box (pair(x:U_S^id. U_T^id; u_a^id; u_b^id))
        tm_pair: rt(Term::BoxTm(rt(Term::Pair {
            fst_level: lv(1),
            snd_level: lv(0),
            fst_ty: rty(gty(3, &g4)),
            snd_ty: rty(gty(2, &gx_app)),
            fst: rt(gtm(1, &g4)),
            snd: rt(gtm(0, &g4)),
        }))),
        // box (fst(x:U_S^id. U_T^id; u_p^id))
        tm_fst: rt(Term::BoxTm(rt(Term::Fst {
            fst_level: lv(1),
            snd_level: lv(0),
            fst_ty: rty(gty(2, &g3)),
            snd_ty: rty(gty(1, &gx_lam)),
            pair: rt(gtm(0, &g3)),
        }))),
        // box (snd(x:U_S^id. U_T^id; u_p^id))
        tm_snd: rt(Term::BoxTm(rt(Term::Snd {
            fst_level: lv(1),
            snd_level: lv(0),
            fst_ty: rty(gty(2, &g3)),
            snd_ty: rty(gty(1, &gx_lam)),
            pair: rt(gtm(0, &g3)),
        }))),
        // box (Unit^ℓ) / box (Empty^ℓ) (the types) — each binds ℓ now.
        ty_unit: rt(Term::BoxTy(rty(Type::Unit { level: lv(0) }))),
        ty_empty: rt(Term::BoxTy(rty(Type::Empty { level: lv(0) }))),
        // box (Unit^ℓ) / box (Empty^ℓ) (the encodings), box ⟨⟩^ℓ
        tm_unit: rt(Term::BoxTm(rt(Term::TmUnit { level: lv(0) }))),
        tm_empty: rt(Term::BoxTm(rt(Term::TmEmpty { level: lv(0) }))),
        tm_triv: rt(Term::BoxTm(rt(Term::Triv { level: lv(0) }))),
        // box (elim_Empty^{ℓ,ℓ'} (x. U_M^id; u_t^id)) — universes ℓ = 1
        // (motive), ℓ' = 0 (scrutinee); telescope g = 2, U_M = 1, u_t = 0.
        tm_elim_empty: {
            let gx_empty = ext(&g2, Type::Empty { level: lv(0) }, lv(0));
            let u_m_e = Type::GlobalTy { var: GlobalVar(1), subst: LocalSubst::id(&gx_empty) };
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
            let g6 = g_ctx(6);
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
        // box (W x:u_s^id. u_t^id) (the encoding) — g = 2, u_s = 1, u_t = 0.
        tm_w: rt(Term::BoxTm(rt(Term::TmW {
            shape_level: lv(1),
            pos_level: lv(0),
            shape: rt(gtm(1, &g2)),
            pos: rt(gtm(0, &gx_tmpi)),
        }))),
        // box (sup(x:U_S^id. U_T^id; u_a^id; u_f^id)) — g = 4, U_S = 3,
        // U_T = 2, u_a = 1, u_f = 0.
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
                fun: rt(Term::Var(LocalVar(1))),
                dom_level: lv(1),
                cod_level: Level::max(lv(2), lv(1)),
                dom: rty(gty(3, &gx5).shift_local(2)),
                cod: rty(w5.shift_local(4)),
                arg: rt(Term::Var(LocalVar(0))),
            };
            let u_m_at_fy = Type::GlobalTy {
                var: GlobalVar(2),
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
        // -- finitary branching branches (docs/wf-former-design.md §6) --
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
                    var: GlobalVar(2),
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
            ty: rty(gty(2, &g_ctx(3))),
            lhs: rt(gtm(1, &g_ctx(3))),
            rhs: rt(gtm(0, &g_ctx(3))),
        }))),
        tm_seq: rt(Term::BoxTm(rt(Term::TmSEq {
            level: lv(0),
            ty: rt(gtm(2, &g_ctx(3))),
            lhs: rt(gtm(1, &g_ctx(3))),
            rhs: rt(gtm(0, &g_ctx(3))),
        }))),
        ty_sempty: rt(Term::BoxTy(rty(Type::SEmpty { level: lv(0) }))),
        tm_sempty: rt(Term::BoxTm(rt(Term::TmSEmpty { level: lv(0) }))),
        tm_srefl: rt(Term::BoxTm(rt(Term::SRefl {
            level: lv(0),
            ty: rty(gty(1, &g_ctx(2))),
            tm: rt(gtm(0, &g_ctx(2))),
        }))),
        tm_transp: {
            // view: g = 6, U_I = 5, U_P = 4, u_a = 3, u_b = 2, u_e = 1,
            // u_t = 0; ℓ = lv(1), ℓ' = lv(0).
            let g6 = g_ctx(6);
            let gx = ext(&g6, gty(5, &g6), lv(1));
            rt(Term::BoxTm(rt(Term::Transp {
                ty_level: lv(1),
                motive_level: lv(0),
                ty: rty(gty(5, &g6)),
                motive: rty(Type::GlobalTy {
                    var: GlobalVar(4),
                    subst: LocalSubst::id(&gx),
                }),
                lhs: rt(gtm(3, &g6)),
                rhs: rt(gtm(2, &g6)),
                proof: rt(gtm(1, &g6)),
                tm: rt(gtm(0, &g6)),
            })))
        },
        tm_elim_sempty: {
            // view: g = 2, U_M = 1, u_t = 0; ℓ = lv(1), ℓ' = lv(0).
            let g2s = g_ctx(2);
            let gxe = ext(&g2s, Type::SEmpty { level: lv(0) }, lv(0));
            rt(Term::BoxTm(rt(Term::ElimSEmpty {
                level: lv(1),
                scrut_level: lv(0),
                motive: rty(Type::GlobalTy {
                    var: GlobalVar(1),
                    subst: LocalSubst::id(&gxe),
                }),
                scrut: rt(gtm(0, &g2s)),
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
                    var: GlobalVar(2),
                    subst: LocalSubst::id(&gz),
                }),
                case: rt(gtm(1, &gx)),
                scrut: rt(gtm(0, &g4s)),
            })))
        },
    })
}

/// **Phase-2 acceptance** (`docs/unit-empty-level-indexing.md` §4): the
/// identity recursor round-trips level-indexed `Unit`/`Empty` code **at a
/// non-zero level**, in a single β-step.
///
/// This is the sharp cross-check of the six reshaped branch telescopes in
/// `rec.rs` against `fire`'s payload wiring in `reduce.rs`: a telescope wrong
/// in either makes the re-boxed code ill-typed or unequal, and at level 0 the
/// two are indistinguishable — which is exactly why the gate existed.
///
/// `elim_Empty` is the one that can go wrong *silently*: it binds two
/// universes, `fire`'s `phi` is innermost-first, and swapping ℓ with ℓ' still
/// typechecks when they happen to be equal. They are distinct here.
#[test]
fn identity_recursor_round_trips_unit_and_empty_at_a_level() {
    let psi = GlobalCtx::default();
    let elim_ty_at = |code_level: Level, code: Type| Term::ElimCodeTy {
        ty_motive_level: Level::Zero,
        tm_motive_level: Level::Zero,
        motives: identity_motives(),
        branches: identity_branches(),
        code_level,
        ctx: nil_ctx(),
        scrut: rt(Term::BoxTy(rty(code))),
    };
    let elim_tm_at = |code_level: Level, ty: Type, code: Term| Term::ElimCodeTm {
        ty_motive_level: Level::Zero,
        tm_motive_level: Level::Zero,
        motives: identity_motives(),
        branches: identity_branches(),
        code_level,
        ctx: nil_ctx(),
        ty: rty(ty),
        scrut: rt(Term::BoxTm(rt(code))),
    };
    let one_step = |t: &Term| {
        heather_kernel::reduce::whnf_term(t, &nil_ctx(), FUEL).expect("recursor must fire")
    };

    for l in [c(1), c(2)] {
        // box (Unit^l) and box (Empty^l), as code of *types*.
        for code in [Type::Unit { level: l.clone() }, Type::Empty { level: l.clone() }] {
            let t = elim_ty_at(l.clone(), code.clone());
            let (ty, _) = infer_closed(Layer::Meta, &t).unwrap();
            assert!(ty == Type::CodeTy { ctx: nil_ctx(), level: l.clone() });
            assert_eq!(one_step(&t), Term::BoxTy(rty(code)), "identity must return its input");
        }
        // box (Unit^l) as code of a *term*: Unit^l : Ty l.
        for code in [Term::TmUnit { level: l.clone() }, Term::TmEmpty { level: l.clone() }] {
            let t = elim_tm_at(Level::succ(l.clone()), Type::Ty(l.clone()), code.clone());
            check_term(&psi, 0, Layer::Meta, &nil_ctx(), &t,
                &Type::CodeTm { ctx: nil_ctx(), ty: rty(Type::Ty(l.clone())), level: Level::succ(l.clone()) },
                &Level::Zero, FUEL).unwrap();
            assert_eq!(one_step(&t), Term::BoxTm(rt(code)));
        }
        // box (⟨⟩^l) : □(· ⊢ Unit^l @ l) — the intro, which is where a term
        // with many types would show up.
        let t = elim_tm_at(l.clone(), Type::Unit { level: l.clone() }, Term::Triv { level: l.clone() });
        check_term(&psi, 0, Layer::Meta, &nil_ctx(), &t,
            &Type::CodeTm { ctx: nil_ctx(), ty: rty(Type::Unit { level: l.clone() }), level: l.clone() },
            &Level::Zero, FUEL).unwrap();
        assert_eq!(one_step(&t), Term::BoxTm(rt(Term::Triv { level: l.clone() })));
    }

    // box (elim_Empty^{2,1}(y. Ty 1; x)) in Δ = (·, x : Empty^1 @ 1) — two
    // universes, DISTINCT (motive 2, scrutinee 1), so an innermost-first slip
    // in `fire`'s `phi` cannot hide behind them being equal. `Empty` has no
    // inhabitants, so the scrutinee is a Δ-variable.
    let delta = ext(&nil_ctx(), Type::Empty { level: c(1) }, c(1));
    let motive = Type::Ty(c(1)); // at level 2 = the motive's level
    let code = Term::ElimEmpty {
        level: c(2),
        scrut_level: c(1),
        motive: rty(motive.clone()),
        scrut: rt(Term::Var(LocalVar(0))),
    };
    check_term(&psi, 0, Layer::Code, &delta, &code, &motive, &c(2), FUEL)
        .expect("elim_Empty^{2,1} must be well-typed code");
    let t = Term::ElimCodeTm {
        ty_motive_level: Level::Zero,
        tm_motive_level: Level::Zero,
        motives: identity_motives(),
        branches: identity_branches(),
        code_level: c(2),
        ctx: delta.clone(),
        ty: rty(motive.clone()),
        scrut: rt(Term::BoxTm(rt(code.clone()))),
    };
    check_term(&psi, 0, Layer::Meta, &nil_ctx(), &t,
        &Type::CodeTm { ctx: delta, ty: rty(motive), level: c(2) },
        &Level::Zero, FUEL)
        .expect("the identity recursor must accept it");
    assert_eq!(one_step(&t), Term::BoxTm(rt(code)), "identity must return its input");
}

/// **The `ℓ`-slot of the scrutinee's recursive call in `t_elimE`**
/// (`docs/delam-extensions.md` §7.7 and §16.1;
/// `issues/recursor-elim-call-level-mismatch.md`).
///
/// `elim_Empty^{ℓ,ℓ'}`'s scrutinee has type `Empty^{ℓ'} @ ℓ'`, so the branch's
/// recursive call `x_t` is declared at `M_Trm[ℓ'/ℓ, Empty^{ℓ'}/U_T, …]` — the
/// **scrutinee's** level, which is what `reduce.rs` supplies
/// (`rec.elim_tm(scrut_level, …)`). The kernel used to declare it at
/// `M_Trm[ℓ/ℓ, Empty^{ℓ'}/U_T, …]`, the *motive's* level, transcribing a typo
/// in ch. 04's `t_elimN` (whose own `t_ze`/`t_succ` write `0/ℓ` for the same
/// `Nat/U_T` slot).
///
/// Every existing branch bundle is blind to this: their `t_elimE` bodies do
/// not *use* `x_t`, so its declared type is never observed. This is the
/// missing observer. Each bundle below is the identity branch with its body
/// routed through `λ(z : dom). box (elim_Empty …)` applied to `x_t`; only
/// `dom` differs, so the assertions isolate `x_t`'s declared type and nothing
/// else. `ℓ` and `ℓ'` are distinct universe *variables* of the telescope, so
/// no instantiation can make the two readings agree.
#[test]
fn elim_empty_branch_recursive_call_is_at_the_scrutinee_level() {
    let psi = GlobalCtx::default();
    let g2 = g_ctx(2);

    // `branches` claiming `x_t : □(g ⊢ Empty^{ty_level} @ call_level)`.
    let branches_claiming = |ty_level: Level, call_level: Level| {
        // box (elim_Empty^{ℓ,ℓ'} (x. U_M^id; u_t^id)) — the identity body.
        let gx_empty = ext(&g2, Type::Empty { level: lv(0) }, lv(0));
        let u_m_e = Type::GlobalTy { var: GlobalVar(1), subst: LocalSubst::id(&gx_empty) };
        let boxed = Term::BoxTm(rt(Term::ElimEmpty {
            level: lv(1),
            scrut_level: lv(0),
            motive: rty(u_m_e),
            scrut: rt(gtm(0, &g2)),
        }));
        // The branch's own type, unchanged: □(g ⊢ U_M^{id, u_t^id/x} @ ℓ).
        let u_m_at_scrut = Type::GlobalTy {
            var: GlobalVar(1),
            subst: LocalSubst::id(&g2).extended(rt(gtm(0, &g2))),
        };
        let branch_ty = Type::CodeTm { ctx: g2.clone(), ty: rty(u_m_at_scrut), level: lv(1) };
        // The λ's annotation — the claim about `x_t` under test.
        let dom = Type::CodeTm {
            ctx: g2.clone(),
            ty: rty(Type::Empty { level: ty_level }),
            level: call_level,
        };
        let mut b = (*identity_branches()).clone();
        b.tm_elim_empty = rt(Term::App {
            fun: rt(Term::Lam {
                dom_level: Level::Zero,
                cod_level: Level::Zero,
                dom: rty(dom.clone()),
                body: rt(boxed),
            }),
            dom_level: Level::Zero,
            cod_level: Level::Zero,
            dom: rty(dom),
            cod: rty(branch_ty),
            // Γ' = Γ, x_M, x_t: the recursive call is the innermost local.
            arg: rt(Term::Var(LocalVar(0))),
        });
        Rc::new(b)
    };

    // The scrutinee: box (elim_Empty^{2,1}(x. Ty 1; x)) in Δ = (·, x : Empty^1),
    // motive level 2 ≠ scrutinee level 1 — an instantiation is not what makes
    // the readings differ (the branch is checked under variables), but it is
    // what makes the surrounding recursor well-typed at all.
    let delta = ext(&nil_ctx(), Type::Empty { level: c(1) }, c(1));
    let motive = Type::Ty(c(1));
    let code = Term::ElimEmpty {
        level: c(2),
        scrut_level: c(1),
        motive: rty(motive.clone()),
        scrut: rt(Term::Var(LocalVar(0))),
    };
    let rec_at = |branches: Rc<Branches>| Term::ElimCodeTm {
        ty_motive_level: Level::Zero,
        tm_motive_level: Level::Zero,
        motives: identity_motives(),
        branches,
        code_level: c(2),
        ctx: delta.clone(),
        ty: rty(motive.clone()),
        scrut: rt(Term::BoxTm(rt(code.clone()))),
    };
    let want = Type::CodeTm { ctx: delta.clone(), ty: rty(motive.clone()), level: c(2) };

    // □(g ⊢ Empty^{ℓ'} @ ℓ') — the corrected declaration. Accepted, and the
    // identity round-trip survives (the λ discards its argument).
    let good = rec_at(branches_claiming(lv(0), lv(0)));
    check_term(&psi, 0, Layer::Meta, &nil_ctx(), &good, &want, &Level::Zero, FUEL)
        .expect("x_t is the recursive call on the scrutinee: it lives at ℓ'");
    assert_eq!(
        heather_kernel::reduce::whnf_term(&good, &nil_ctx(), FUEL).expect("must fire"),
        Term::BoxTm(rt(code.clone())),
    );

    // Negative control: □(g ⊢ Empty^ℓ @ ℓ) — a perfectly well-formed
    // contextual type, and the recursive call on a scrutinee that lived at the
    // motive's level would have it. This scrutinee does not, so it must be
    // rejected; without this control the test would pass for any annotation
    // the λ happened to accept.
    let wrong_level = rec_at(branches_claiming(lv(1), lv(1)));
    check_term(&psi, 0, Layer::Meta, &nil_ctx(), &wrong_level, &want, &Level::Zero, FUEL)
        .expect_err("x_t is not the call on an Empty^ℓ");

    // Second negative control: □(g ⊢ Empty^{ℓ'} @ ℓ) — *exactly* the type the
    // kernel used to declare. It is rejected here not merely as the wrong
    // type but as no type at all: `Empty^{ℓ'}` does not live at ℓ, so the old
    // rule was putting an ill-formed entry into the branch's context. That is
    // why the defect stayed latent — nothing well-formed could ever be
    // checked against it.
    let old_rule = rec_at(branches_claiming(lv(0), lv(1)));
    check_term(&psi, 0, Layer::Meta, &nil_ctx(), &old_rule, &want, &Level::Zero, FUEL)
        .expect_err("□(g ⊢ Empty^{ℓ'} @ ℓ) is not a well-formed contextual type");
}

/// **The `(g, ℓ)` slots of the *type-motive* recursive calls**
/// (`issues/branch-telescope-type-motive-level-slots.md`).
///
/// `M_Typ[l/ℓ, Δ/g, …]` instantiates to `□(Δ ⊢ Ty l)`, which is a well-formed
/// type for *any* in-scope `l`: no formation check can see whether the level
/// slot of `x_S`/`x_T`/`x_M` holds the right level, only whether it holds a
/// level. The whole table is covered generically in `rec.rs`
/// (`every_type_motive_recursive_call_matches_its_code_layer_type_binding`),
/// which pins each call against the layer-c `Typ_c` binding it recurses on.
/// This is the complementary *use-site* observation for three representative
/// slots — the branch body actually consumes the entry at a claimed type, so
/// what is checked here is that a branch author reading the rule off
/// `docs/delam-extensions.md` gets a bundle the kernel accepts, and gets one
/// rejected for every other reading of the slot.
///
/// The pattern is `elim_empty_branch_recursive_call_is_at_the_scrutinee_level`
/// generalised: the identity body is routed through `λ(z : claim). <body>`
/// applied to the entry under test, so only `claim` varies. The harness
/// recursor is `elim^Typ` on `box Nat`: `rec_ga` checks all 56 branches
/// whatever the scrutinee is, so a single trivial scrutinee observes any
/// branch's telescope.
#[test]
fn type_motive_branch_entries_are_usable_at_their_declared_context_and_level() {
    let psi = GlobalCtx::default();
    let g2 = g_ctx(2);
    // ty_pi's telescope: (ℓ, ℓ', g, U_S, U_T, x_S, x_T); (g, x : U_S^id @ ℓ).
    let gx_typi = ext(&g2, gty(1, &g2), lv(1));
    // ty_pi's expected type: □(g ⊢ Ty (ℓ ⊔ ℓ')).
    let ty_pi_branch_ty = Type::CodeTy { ctx: g2.clone(), level: Level::max(lv(1), lv(0)) };
    // tm_elim_empty's telescope: (ℓ, ℓ', g, U_M, u_t, x_M, x_t), with
    // U_M : Typ_c((g, x : Empty^{ℓ'} @ ℓ'), ℓ) and expected type
    // □(g ⊢ U_M^{id, u_t^id/x} @ ℓ).
    let gx_empty = ext(&g2, Type::Empty { level: lv(0) }, lv(0));
    let u_m_at_scrut = Type::GlobalTy {
        var: GlobalVar(1),
        subst: LocalSubst::id(&g2).extended(rt(gtm(0, &g2))),
    };
    let elim_empty_branch_ty =
        Type::CodeTm { ctx: g2.clone(), ty: rty(u_m_at_scrut), level: lv(1) };

    // `body` re-checked through `λ(z : claim). body` applied to local `var`.
    let probe = |body: &Rc<Term>, branch_ty: &Type, claim: Type, var: u32| {
        rt(Term::App {
            fun: rt(Term::Lam {
                dom_level: Level::Zero,
                cod_level: Level::Zero,
                dom: rty(claim.clone()),
                body: rt((**body).clone()),
            }),
            dom_level: Level::Zero,
            cod_level: Level::Zero,
            dom: rty(claim),
            cod: rty(branch_ty.clone()),
            arg: rt(Term::Var(LocalVar(var))),
        })
    };
    // `elim^Typ` over `box Nat`, whose only job is to make `rec_ga` walk the
    // 56 branches; it fires `ty_nat`, which no probe touches.
    let harness = |branches: Rc<Branches>| Term::ElimCodeTy {
        ty_motive_level: Level::Zero,
        tm_motive_level: Level::Zero,
        motives: identity_motives(),
        branches,
        code_level: Level::Zero,
        ctx: nil_ctx(),
        scrut: rt(Term::BoxTy(rty(Type::Nat))),
    };
    let accepts = |branches: Rc<Branches>| {
        let t = harness(branches);
        check_term(
            &psi,
            0,
            Layer::Meta,
            &nil_ctx(),
            &t,
            &Type::CodeTy { ctx: nil_ctx(), level: Level::Zero },
            &Level::Zero,
            FUEL,
        )
    };

    // -- ty_pi's x_S : □(g ⊢ Ty ℓ) -----------------------------------------
    // Γ' = Γ, x_S, x_T, so x_S is LocalVar(1) and x_T is LocalVar(0).
    let with_ty_pi_probe = |claim: Type, var: u32| {
        let base = identity_branches();
        let mut b = (*base).clone();
        b.ty_pi = probe(&base.ty_pi, &ty_pi_branch_ty, claim, var);
        Rc::new(b)
    };
    accepts(with_ty_pi_probe(Type::CodeTy { ctx: g2.clone(), level: lv(1) }, 1))
        .expect("x_S is the call on U_S : Typ_c(g, ℓ)");
    // The falsifier of the issue, seen from the use site: ℓ' is a perfectly
    // good in-scope level, and `Ty ℓ'` a perfectly good type — but it is not
    // this sub-code's.
    accepts(with_ty_pi_probe(Type::CodeTy { ctx: g2.clone(), level: lv(0) }, 1))
        .expect_err("x_S does not live at ℓ'");

    // -- ty_pi's x_T : □((g, x : U_S^id @ ℓ) ⊢ Ty ℓ') ----------------------
    accepts(with_ty_pi_probe(Type::CodeTy { ctx: gx_typi.clone(), level: lv(0) }, 0))
        .expect("x_T is the call on U_T : Typ_c((g, x : U_S^id @ ℓ), ℓ')");
    accepts(with_ty_pi_probe(Type::CodeTy { ctx: gx_typi, level: lv(1) }, 0))
        .expect_err("x_T does not live at ℓ");
    // The context slot is unchecked in exactly the same way as the level:
    // `□(g ⊢ Ty ℓ')` is well formed, just not the codomain's call.
    accepts(with_ty_pi_probe(Type::CodeTy { ctx: g2.clone(), level: lv(0) }, 0))
        .expect_err("x_T's call is under the Π's binder, not in g");

    // -- tm_elim_empty's x_M : □((g, x : Empty^{ℓ'} @ ℓ') ⊢ Ty ℓ) ----------
    // The motive of an eliminator branch: its level is the *motive's* ℓ while
    // its context extends by the *scrutinee's* Empty^{ℓ'} — the one slot pair
    // where the two universe binders of `t_elimE` must not be swapped.
    // Γ' = Γ, x_M, x_t, so x_M is LocalVar(1).
    let with_elim_empty_probe = |claim: Type| {
        let base = identity_branches();
        let mut b = (*base).clone();
        b.tm_elim_empty = probe(&base.tm_elim_empty, &elim_empty_branch_ty, claim, 1);
        Rc::new(b)
    };
    accepts(with_elim_empty_probe(Type::CodeTy { ctx: gx_empty.clone(), level: lv(1) }))
        .expect("x_M is the call on U_M : Typ_c((g, x : Empty^{ℓ'} @ ℓ'), ℓ)");
    accepts(with_elim_empty_probe(Type::CodeTy { ctx: gx_empty, level: lv(0) }))
        .expect_err("the motive does not live at the scrutinee's level");
    accepts(with_elim_empty_probe(Type::CodeTy {
        ctx: ext(&g2, Type::Empty { level: lv(1) }, lv(1)),
        level: lv(1),
    }))
    .expect_err("the motive's context extends by Empty^{ℓ'}, not Empty^ℓ");
}

#[test]
fn identity_recursor_on_code_of_types() {
    let t = Term::ElimCodeTy {
        ty_motive_level: Level::Zero,
        tm_motive_level: Level::Zero,
        motives: identity_motives(),
        branches: identity_branches(),
        code_level: Level::Zero,
        ctx: nil_ctx(),
        scrut: rt(Term::BoxTy(rty(Type::Nat))),
    };
    let (ty, l) = infer_closed(Layer::Meta, &t).unwrap();
    assert!(ty == Type::CodeTy { ctx: nil_ctx(), level: Level::Zero });
    assert!(l.equiv(&Level::Zero));
}

#[test]
fn identity_recursor_on_code_of_terms() {
    let t = Term::ElimCodeTm {
        ty_motive_level: Level::Zero,
        tm_motive_level: Level::Zero,
        motives: identity_motives(),
        branches: identity_branches(),
        code_level: Level::Zero,
        ctx: nil_ctx(),
        ty: rty(Type::Nat),
        scrut: rt(Term::BoxTm(rt(Term::Zero))),
    };
    let (ty, l) = infer_closed(Layer::Meta, &t).unwrap();
    assert!(ty == Type::CodeTm { ctx: nil_ctx(), ty: rty(Type::Nat), level: Level::Zero });
    assert!(l.equiv(&Level::Zero));
}

#[test]
fn identity_recursor_dispatches_to_all_squash_branches() {
    let gamma = nil_ctx();
    let squash_nat_ty = Type::Squash { level: Level::Zero, ty: rty(Type::Nat) };
    let squash_zero = Term::Squash {
        level: Level::Zero,
        ty: rty(Type::Nat),
        tm: rt(Term::Zero),
    };
    let motive = Type::Nat;
    let elim = Term::ElimSquash {
        src_level: Level::Zero,
        dst_level: Level::Zero,
        src_ty: rty(Type::Nat),
        motive: rty(motive),
        case: rt(squash_zero.clone()),
        scrut: rt(squash_zero.clone()),
    };

    let type_codes = [
        Type::Squash { level: Level::Zero, ty: rty(Type::Nat) },
    ];
    for ty in type_codes {
        let boxed = Term::BoxTy(rty(ty));
        let rec = Term::ElimCodeTy {
            ty_motive_level: Level::Zero,
            tm_motive_level: Level::Zero,
            motives: identity_motives(),
            branches: identity_branches(),
            code_level: Level::Zero,
            ctx: gamma.clone(),
            scrut: rt(boxed.clone()),
        };
        assert_eq!(whnf_term(&rec, &gamma, FUEL), Ok(boxed));
    }

    let term_codes = [
        (Term::TmSquash { level: Level::Zero, ty: rt(Term::TmNat) }, Type::Ty(Level::Zero)),
        (squash_zero, squash_nat_ty.clone()),
        (elim, squash_nat_ty),
    ];
    for (tm, ty) in term_codes {
        let boxed = Term::BoxTm(rt(tm));
        let rec = Term::ElimCodeTm {
            ty_motive_level: Level::Zero,
            tm_motive_level: Level::Zero,
            motives: identity_motives(),
            branches: identity_branches(),
            code_level: Level::Zero,
            ctx: gamma.clone(),
            ty: rty(ty),
            scrut: rt(boxed.clone()),
        };
        assert_eq!(whnf_term(&rec, &gamma, FUEL), Ok(boxed));
    }
}

// -------------------------------------------------------------------------
// Types at layer m, fuel
// -------------------------------------------------------------------------

#[test]
fn meta_type_formers_require_layer_m() {
    let psi = GlobalCtx::default();
    let upi = Type::UPi {
        num_vars: 1,
        level: Level::succ(lv(0)),
        body: rty(Type::Ty(lv(0))),
    };
    let il = infer_type(&psi, 0, Layer::Meta, &nil_ctx(), &upi, FUEL).unwrap();
    assert!(il.equiv(&Level::Omega));
    assert_eq!(
        infer_type(&psi, 0, Layer::Prog, &nil_ctx(), &upi, FUEL).unwrap_err(),
        TypeError::LayerMismatch
    );
    let code = Type::CodeTy { ctx: nil_ctx(), level: Level::Zero };
    assert_eq!(
        infer_type(&psi, 0, Layer::Code, &nil_ctx(), &code, FUEL).unwrap_err(),
        TypeError::LayerMismatch
    );
    // ⇒-types: (g : Ctx) ⇒^1 (U : Typ_p(g, 0)) ⇒^{0,1} □(g ⊢ U^id @ 0).
    let nested = Type::CtxPi {
        level: c(1),
        body: rty(Type::TyPi {
            ctx: g_ctx(0),
            arg_level: Level::Zero,
            body_level: c(1),
            body: rty(Type::CodeTm {
                ctx: g_ctx(1),
                ty: rty(gty(0, &g_ctx(1))),
                level: Level::Zero,
            }),
        }),
    };
    // □ lives at 0, so the annotated ⇒-levels above are off by one.
    let il = infer_type(&psi, 0, Layer::Meta, &nil_ctx(), &nested, FUEL);
    assert_eq!(il.unwrap_err(), TypeError::LevelMismatch);
    let nested_ok = Type::CtxPi {
        level: Level::Zero,
        body: rty(Type::TyPi {
            ctx: g_ctx(0),
            arg_level: Level::Zero,
            body_level: Level::Zero,
            body: rty(Type::CodeTm {
                ctx: g_ctx(1),
                ty: rty(gty(0, &g_ctx(1))),
                level: Level::Zero,
            }),
        }),
    };
    let il = infer_type(&psi, 0, Layer::Meta, &nil_ctx(), &nested_ok, FUEL).unwrap();
    assert!(il.equiv(&Level::Zero));
}

#[test]
fn out_of_fuel_is_distinguishable() {
    assert_eq!(
        check_term(
            &GlobalCtx::default(),
            0,
            Layer::Prog,
            &nil_ctx(),
            &Term::Zero,
            &Type::Nat,
            &Level::Zero,
            0,
        )
        .unwrap_err(),
        TypeError::OutOfFuel
    );
    check_type(&GlobalCtx::default(), 0, Layer::Prog, &nil_ctx(), &Type::Nat, &Level::Zero, FUEL)
        .unwrap();
}

// -------------------------------------------------------------------------
// Identity type (extension beyond ch. 04; kernel-v1-extensions)
// -------------------------------------------------------------------------

#[test]
fn id_formation_refl_and_encoding() {
    let psi = GlobalCtx::default();
    // Id^0(Nat; 0; 0) @ 0.
    let id00 = Type::Id {
        level: Level::Zero,
        ty: rty(Type::Nat),
        lhs: rt(Term::Zero),
        rhs: rt(Term::Zero),
    };
    check_type(&psi, 0, Layer::Prog, &nil_ctx(), &id00, &Level::Zero, FUEL).unwrap();
    // Endpoints must check at the carrier.
    let bad = Type::Id {
        level: Level::Zero,
        ty: rty(Type::Nat),
        lhs: rt(Term::TmNat),
        rhs: rt(Term::Zero),
    };
    assert!(check_type(&psi, 0, Layer::Prog, &nil_ctx(), &bad, &Level::Zero, FUEL).is_err());
    // refl^0(Nat; 0) infers Id^0(Nat; 0; 0) @ 0; the point must check.
    let refl0 = Term::Refl { level: Level::Zero, ty: rty(Type::Nat), tm: rt(Term::Zero) };
    let (ty, l) = infer_closed(Layer::Prog, &refl0).unwrap();
    assert!(ty == id00);
    assert!(l.equiv(&Level::Zero));
    let refl_bad =
        Term::Refl { level: Level::Zero, ty: rty(Type::Nat), tm: rt(Term::TmNat) };
    assert!(infer_closed(Layer::Prog, &refl_bad).is_err());
    // Layer v admits neither form.
    assert_eq!(infer_closed(Layer::Var, &refl0).unwrap_err(), TypeError::LayerMismatch);
    // The encoding Id^0(«Nat»; 0; 1) : Ty 0 @ 1, and refl checks against
    // its El-decode (conversion fires through El (Id …) ⇝ Id (El …)).
    let tm_id = Term::TmId {
        level: Level::Zero,
        ty: rt(Term::TmNat),
        lhs: rt(Term::Zero),
        rhs: rt(Term::Zero),
    };
    let (ty, l) = infer_closed(Layer::Prog, &tm_id).unwrap();
    assert!(ty == Type::Ty(Level::Zero));
    assert!(l.equiv(&c(1)));
    let el_id = Type::El { level: Level::Zero, tm: rt(tm_id) };
    check_closed(Layer::Prog, &refl0, &el_id, &Level::Zero).unwrap();
}

#[test]
fn j_paulin_mohring() {
    // Dependent motive M(y, p) = Id^0(Nat; 0; y), scoped in (Γ, y, p).
    let motive = Type::Id {
        level: Level::Zero,
        ty: rty(Type::Nat),
        lhs: rt(Term::Zero),
        rhs: rt(v(1)),
    };
    let refl0 = Term::Refl { level: Level::Zero, ty: rty(Type::Nat), tm: rt(Term::Zero) };
    let j = |rhs: Term, proof: Term| Term::J {
        ty_level: Level::Zero,
        motive_level: Level::Zero,
        ty: rty(Type::Nat),
        lhs: rt(Term::Zero),
        motive: rty(motive.clone()),
        case: rt(refl0.clone()),
        rhs: rt(rhs),
        proof: rt(proof),
    };
    // J … 0 (refl 0) : M[0/y, refl/p] = Id^0(Nat; 0; 0) @ 0.
    let (ty, l) = infer_closed(Layer::Prog, &j(Term::Zero, refl0.clone())).unwrap();
    assert!(
        ty == Type::Id {
            level: Level::Zero,
            ty: rty(Type::Nat),
            lhs: rt(Term::Zero),
            rhs: rt(Term::Zero),
        }
    );
    assert!(l.equiv(&Level::Zero));
    // A proof that is not an Id inhabitant is rejected …
    assert!(infer_closed(Layer::Prog, &j(Term::Zero, Term::Zero)).is_err());
    // … as is a proof whose right endpoint mismatches `rhs`.
    assert!(infer_closed(Layer::Prog, &j(Term::Succ(rt(Term::Zero)), refl0.clone())).is_err());
    // Layer p only (not v).
    assert_eq!(
        infer_closed(Layer::Var, &j(Term::Zero, refl0.clone())).unwrap_err(),
        TypeError::LayerMismatch
    );
}

// -------------------------------------------------------------------------
// Dependent pairs (extension beyond ch. 04; kernel-v1-extensions)
// -------------------------------------------------------------------------

#[test]
fn sigma_formation_and_encoding() {
    let psi = GlobalCtx::default();
    // Σ^{0,0}(x:Nat). Nat @ 0.
    let sig = Type::Sigma {
        fst_level: Level::Zero,
        snd_level: Level::Zero,
        fst: rty(Type::Nat),
        snd: rty(Type::Nat),
    };
    let l = infer_type(&psi, 0, Layer::Prog, &nil_ctx(), &sig, FUEL).unwrap();
    assert!(l.equiv(&Level::Zero));
    // A dependent Σ: Σ(A : Ty 0). El 0 A @ 1.
    let dep = Type::Sigma {
        fst_level: c(1),
        snd_level: Level::Zero,
        fst: rty(Type::Ty(Level::Zero)),
        snd: rty(Type::El { level: Level::Zero, tm: rt(v(0)) }),
    };
    let l = infer_type(&psi, 0, Layer::Prog, &nil_ctx(), &dep, FUEL).unwrap();
    assert!(l.equiv(&c(1)));
    // The encoding Σ^{0,0}(«Nat»; «Nat») : Ty 0 @ 1, El-decoding to the former.
    let tm_sig = Term::TmSigma {
        fst_level: Level::Zero,
        snd_level: Level::Zero,
        fst: rt(Term::TmNat),
        snd: rt(Term::TmNat),
    };
    let (ty, l) = infer_closed(Layer::Prog, &tm_sig).unwrap();
    // The inferred universe is 0⊔0 (a Max node), equivalent to 0.
    let Type::Ty(tl) = &ty else { panic!("encoding should infer a universe") };
    assert!(tl.equiv(&Level::Zero));
    assert!(l.equiv(&c(1)));
    let el_sig = Type::El { level: Level::Zero, tm: rt(tm_sig) };
    // The pair (0, 0) checks against the El-decode (conversion fires through
    // El (Σ …) ⇝ Σ (El …)).
    let pair = Term::Pair {
        fst_level: Level::Zero,
        snd_level: Level::Zero,
        fst_ty: rty(Type::Nat),
        snd_ty: rty(Type::Nat),
        fst: rt(Term::Zero),
        snd: rt(Term::Zero),
    };
    check_closed(Layer::Prog, &pair, &el_sig, &Level::Zero).unwrap();
}

#[test]
fn pair_projections_and_dependency() {
    // A genuinely dependent pair: Σ(A : Ty 0). El 0 A, inhabited by
    // (Nat, 0) — snd : El 0 (fst p) must land on Nat after β on fst.
    let snd_ty = Type::El { level: Level::Zero, tm: rt(v(0)) };
    let mk_pair = || Term::Pair {
        fst_level: c(1),
        snd_level: Level::Zero,
        fst_ty: rty(Type::Ty(Level::Zero)),
        snd_ty: rty(snd_ty.clone()),
        fst: rt(Term::TmNat),
        snd: rt(Term::Zero),
    };
    let sigma = Type::Sigma {
        fst_level: c(1),
        snd_level: Level::Zero,
        fst: rty(Type::Ty(Level::Zero)),
        snd: rty(snd_ty.clone()),
    };
    let (ty, l) = infer_closed(Layer::Prog, &mk_pair()).unwrap();
    assert!(ty == sigma);
    assert!(l.equiv(&c(1)));
    // fst (Nat, 0) : Ty 0 @ 1.
    let fst = Term::Fst {
        fst_level: c(1),
        snd_level: Level::Zero,
        fst_ty: rty(Type::Ty(Level::Zero)),
        snd_ty: rty(snd_ty.clone()),
        pair: rt(mk_pair()),
    };
    let (ty, l) = infer_closed(Layer::Prog, &fst).unwrap();
    assert!(ty == Type::Ty(Level::Zero));
    assert!(l.equiv(&c(1)));
    // snd (Nat, 0) : El 0 (fst (Nat, 0)) @ 0 — and, since fst β-reduces to
    // Nat, this checks against Nat too.
    let snd = Term::Snd {
        fst_level: c(1),
        snd_level: Level::Zero,
        fst_ty: rty(Type::Ty(Level::Zero)),
        snd_ty: rty(snd_ty.clone()),
        pair: rt(mk_pair()),
    };
    let (ty, l) = infer_closed(Layer::Prog, &snd).unwrap();
    assert!(l.equiv(&Level::Zero));
    // The inferred type is El 0 (fst …); it is convertible to Nat.
    assert!(ty == Type::El { level: Level::Zero, tm: rt(fst.clone()) });
    check_closed(Layer::Prog, &snd, &Type::Nat, &Level::Zero).unwrap();
    // A snd whose annotation mismatches the pair's is rejected: the pair
    // must check at Σ(x:S).T with the *given* T.
    let bad = Term::Fst {
        fst_level: c(1),
        snd_level: Level::Zero,
        fst_ty: rty(Type::Ty(Level::Zero)),
        snd_ty: rty(Type::Nat), // wrong: pair's snd_ty is El 0 (Var 0)
        pair: rt(mk_pair()),
    };
    assert!(infer_closed(Layer::Prog, &bad).is_err());
    // Layer v admits neither projection nor pair.
    assert_eq!(infer_closed(Layer::Var, &mk_pair()).unwrap_err(), TypeError::LayerMismatch);
}

/// The **checked spellings** (`docs/intro-by-type-design.md`): the same
/// dependent pair as `pair_projections_and_dependency` above, spelled with the
/// un-reduced type it was checked at rather than that type's components.
///
/// The annotation here is `El ⌜Σ(A : Ty 0). El A⌝`, which *decodes* to the Σ —
/// the non-reflexive case of the premise `T ⇝* former`, and the only one that
/// tests anything the component form does not. Four things are asserted, one
/// per design claim:
///
/// 1. `pair@` infers its annotation **un-reduced**, not the former;
/// 2. `fst@` / `snd@` infer the components of the annotation's whnf, and
///    `snd@`'s substituted projection is the `@` spelling again;
/// 3. the spellings are interconvertible with the component forms in both
///    directions — the translation `⌊·⌋` of §2.4, observed;
/// 4. the guard is §2.3's box side condition, not a layer: layer v refuses
///    them, layer **c** admits them (every body is checked there), and the
///    payload of a `box` refuses them, which is what leaves the code grammar
///    and the 56 recursor branches alone;
/// 5. without an annotation an intro checks against the expected type and
///    does not infer (design §2.1).
#[test]
fn checked_spellings_infer_their_annotation() {
    // ⌜Σ(A : Ty 0). El A⌝ and the Σ it decodes to.
    let code = Term::TmSigma {
        fst_level: c(1),
        snd_level: Level::Zero,
        fst: rt(Term::TmTy(Level::Zero)),
        // `El(A)` for the bound `A : Ty 0` is encoded by `A` itself.
        snd: rt(v(0)),
    };
    let at = Type::El { level: c(1), tm: rt(code) };
    let snd_ty = Type::El { level: Level::Zero, tm: rt(v(0)) };
    let sigma = Type::Sigma {
        fst_level: c(1),
        snd_level: Level::Zero,
        fst: rty(Type::Ty(Level::Zero)),
        snd: rty(snd_ty.clone()),
    };

    let mk_at = || Term::PairAt {
        ty: Some(rty(at.clone())),
        fst: rt(Term::TmNat),
        snd: rt(Term::Zero),
    };
    // (1) The inferred type is `T` itself. This is the whole point: a
    // consumer that converts it against another `T` pays a head comparison.
    let (ty, l) = infer_closed(Layer::Prog, &mk_at()).unwrap();
    assert!(ty == at, "pair@ must infer its annotation un-reduced");
    assert!(l.equiv(&c(1)));
    // (3) …and it is the same term as the component spelling, both ways.
    check_closed(Layer::Prog, &mk_at(), &sigma, &c(1)).unwrap();
    let component = Term::Pair {
        fst_level: c(1),
        snd_level: Level::Zero,
        fst_ty: rty(Type::Ty(Level::Zero)),
        snd_ty: rty(snd_ty.clone()),
        fst: rt(Term::TmNat),
        snd: rt(Term::Zero),
    };
    check_closed(Layer::Prog, &component, &at, &c(1)).unwrap();

    // (2) fst@ infers the component of the annotation's whnf.
    let fst_at = Term::FstAt { pair: rt(mk_at()) };
    let (ty, l) = infer_closed(Layer::Prog, &fst_at).unwrap();
    assert!(l.equiv(&c(1)));
    // The component comes out of the *decode*, so it is `El ⌜Ty 0⌝` rather
    // than `Ty 0` — convertible, and the point is that it is a component of
    // the annotation and not of a reduct the elaborator wrote down.
    assert!(ty == Type::El { level: c(1), tm: rt(Term::TmTy(Level::Zero)) }, "{ty:?}");
    // …and converts with the component projection over the component pair,
    // which is `⌊·⌋` on a projection.
    check_closed(Layer::Prog, &fst_at, &Type::Ty(Level::Zero), &c(1)).unwrap();

    // snd@ infers `U[fst@(T;p)/x]` — the substituted projection is the
    // checked spelling again, so the inferred type stays source-shaped.
    let snd_at_tm = Term::SndAt { pair: rt(mk_at()) };
    let (ty, l) = infer_closed(Layer::Prog, &snd_at_tm).unwrap();
    assert!(l.equiv(&Level::Zero));
    assert!(ty == Type::El { level: Level::Zero, tm: rt(fst_at.clone()) });
    // β fires on the checked pair spelling, so this is `Nat`.
    check_closed(Layer::Prog, &snd_at_tm, &Type::Nat, &Level::Zero).unwrap();

    // The injections, over `El ⌜Nat + Unit 0⌝`. The two summands are
    // **distinct** on purpose: with `Nat + Nat` an `inl@`/`inr@` swap is
    // invisible, which is exactly the negative control
    // `docs/testing-generated-terms.md` asks for.
    let sum_code = Term::TmSum {
        lhs_level: Level::Zero,
        rhs_level: Level::Zero,
        lhs: rt(Term::TmNat),
        rhs: rt(Term::TmUnit { level: Level::Zero }),
    };
    let sum_at = Type::El { level: Level::Zero, tm: rt(sum_code) };
    let sum = Type::Sum {
        lhs_level: Level::Zero,
        rhs_level: Level::Zero,
        lhs: rty(Type::Nat),
        rhs: rty(Type::Unit { level: Level::Zero }),
    };
    let zero = || rt(Term::Zero);
    let triv = || rt(Term::Triv { level: Level::Zero });
    for (right, good, bad) in [(false, zero(), triv()), (true, triv(), zero())] {
        let mk = |v: Rc<Term>| {
            if right {
                Term::InrAt { ty: Some(rty(sum_at.clone())), val: v }
            } else {
                Term::InlAt { ty: Some(rty(sum_at.clone())), val: v }
            }
        };
        let (ty, l) = infer_closed(Layer::Prog, &mk(good)).unwrap();
        assert!(ty == sum_at, "inj@ must infer its annotation un-reduced");
        assert!(l.equiv(&Level::Zero));
        check_closed(Layer::Prog, &mk(Rc::clone(&bad)), &sum, &Level::Zero).unwrap_err();
        // The negative control: the *other* summand's inhabitant is refused,
        // so the rule really reads the injection's side and not just "some
        // component of the annotation's whnf".
        assert!(infer_closed(Layer::Prog, &mk(bad)).is_err());
    }

    // An annotation whose whnf is not the expected former is a head
    // mismatch, not a panic and not an acceptance.
    let wrong = Term::PairAt {
        ty: Some(rty(Type::Nat)),
        fst: rt(Term::Zero),
        snd: rt(Term::Zero),
    };
    assert_eq!(infer_closed(Layer::Prog, &wrong).unwrap_err(), TypeError::HeadMismatch);

    // (4) The guard. Layer v refuses every form, as it refuses the
    // component ones. Layer c admits them — a declaration body is checked
    // there, and δ at a computing layer unfolds it into a term legal there.
    assert_eq!(infer_closed(Layer::Var, &mk_at()).unwrap_err(), TypeError::LayerMismatch);
    assert_eq!(
        infer_closed(Layer::Var, &Term::FstAt { pair: rt(mk_at()) }).unwrap_err(),
        TypeError::LayerMismatch
    );
    infer_closed(Layer::Code, &mk_at()).unwrap();
    infer_closed(Layer::Code, &fst_at).unwrap();
    // The payload of a `box` is what the code recursors range over, so it
    // refuses them — §2.3's side condition, and the reason `rec.rs` has no
    // new branch. The component spelling is the control.
    let code_ty = |ty: Type| Type::CodeTm { ctx: nil_ctx(), ty: rty(ty), level: c(1) };
    assert_eq!(
        check_closed(Layer::Meta, &Term::BoxTm(rt(mk_at())), &code_ty(at.clone()), &Level::Zero)
            .unwrap_err(),
        TypeError::UnderBox
    );
    check_closed(
        Layer::Meta,
        &Term::BoxTm(rt(component.clone())),
        &code_ty(sigma.clone()),
        &Level::Zero,
    )
    .unwrap();

    // (5) Unannotated: checks against the former and against the annotation
    // alike, and is not inferable, as `box` is not.
    let bare = Term::PairAt { ty: None, fst: rt(Term::TmNat), snd: rt(Term::Zero) };
    check_closed(Layer::Prog, &bare, &sigma, &c(1)).unwrap();
    check_closed(Layer::Prog, &bare, &at, &c(1)).unwrap();
    assert_eq!(infer_closed(Layer::Prog, &bare).unwrap_err(), TypeError::NotInferable);
    // A projection's receiver must infer, so it cannot be one.
    assert_eq!(
        infer_closed(Layer::Prog, &Term::FstAt { pair: rt(bare.clone()) }).unwrap_err(),
        TypeError::NotInferable
    );
    // The negative control: the field is checked against the component.
    let bad = Term::PairAt { ty: None, fst: rt(Term::Zero), snd: rt(Term::Zero) };
    assert!(check_closed(Layer::Prog, &bad, &at, &c(1)).is_err());
    for (right, good, bad) in [(false, zero(), triv()), (true, triv(), zero())] {
        let mk = |v: Rc<Term>| {
            if right { Term::InrAt { ty: None, val: v } } else { Term::InlAt { ty: None, val: v } }
        };
        check_closed(Layer::Prog, &mk(Rc::clone(&good)), &sum_at, &Level::Zero).unwrap();
        check_closed(Layer::Prog, &mk(good), &sum, &Level::Zero).unwrap();
        assert!(check_closed(Layer::Prog, &mk(bad), &sum_at, &Level::Zero).is_err());
    }
}

/// `app@(f; a)` (`docs/app-by-head-type-design.md` §3.1, §9's golden tests):
///
/// 1. a head whose type is syntactically a Π — a local here, as a global's
///    statement is — returns **syntax**, the very type the annotated `app`
///    infers (the fast path), across a dependent spine;
/// 2. a head whose type needs reduction — a function stored as a record
///    field, `fst@(pair@^{T}(λx. x; 0))` — checks, and its argument is
///    checked at the domain the head infers: the negative control refuses
///    `⟨⟩` there;
/// 3. β fires on `app@(λ…; a)`;
/// 4. `box(app@(…))` is refused, and the quote boundary's translator writes
///    it as the `app` the box accepts.
#[test]
fn checked_application_reads_its_head() {
    // (1) Γ = f : Π(A : Ty 0). Π(a : El A). El A — dependent, so the second
    // node's type is an instance of the first's codomain.
    let poly = Type::Pi {
        dom_level: c(1),
        cod_level: Level::Zero,
        dom: rty(Type::Ty(Level::Zero)),
        cod: rty(Type::Pi {
            dom_level: Level::Zero,
            cod_level: Level::Zero,
            dom: rty(Type::El { level: Level::Zero, tm: rt(v(0)) }),
            cod: rty(Type::El { level: Level::Zero, tm: rt(v(1)) }),
        }),
    };
    let gamma = ext(&nil_ctx(), poly.clone(), c(1));
    let psi = GlobalCtx::default();
    let at = Term::AppAt {
        fun: rt(Term::AppAt { fun: rt(v(0)), arg: rt(Term::TmNat) }),
        arg: rt(Term::Zero),
    };
    let Type::Pi { cod: inner_pi, .. } = &poly else { unreachable!() };
    let inner_pi_at = inner_pi.apply_local(&LocalSubst::id(&gamma).extended(rt(Term::TmNat)));
    let Type::Pi { dom: d2n, cod: c2n, .. } = &inner_pi_at else { unreachable!() };
    let annotated = Term::App {
        fun: rt(Term::App {
            fun: rt(v(0)),
            dom_level: c(1),
            cod_level: Level::Zero,
            dom: rty(Type::Ty(Level::Zero)),
            cod: Rc::clone(inner_pi),
            arg: rt(Term::TmNat),
        }),
        dom_level: Level::Zero,
        cod_level: Level::Zero,
        dom: Rc::clone(d2n),
        cod: Rc::clone(c2n),
        arg: rt(Term::Zero),
    };
    let (ty_at, l_at) = infer_term(&psi, 0, Layer::Prog, &gamma, &at, FUEL).unwrap();
    let (ty_app, l_app) = infer_term(&psi, 0, Layer::Prog, &gamma, &annotated, FUEL).unwrap();
    assert!(ty_at == ty_app, "the fast path must return app's own syntax: {ty_at:?} vs {ty_app:?}");
    assert!(l_at.equiv(&l_app));
    check_term(&psi, 0, Layer::Prog, &gamma, &at, &Type::Nat, &Level::Zero, FUEL).unwrap();
    // The argument is checked at the head's domain: `⟨⟩` is not a `Ty 0`.
    let bad = Term::AppAt { fun: rt(v(0)), arg: rt(Term::Triv { level: Level::Zero }) };
    assert!(infer_term(&psi, 0, Layer::Prog, &gamma, &bad, FUEL).is_err());

    // (2) T = El ⌜Σ(g : El ⌜Π(x : Nat). Nat⌝). Nat⌝; the head is its field.
    let pi_code = Term::TmPi {
        dom_level: Level::Zero,
        cod_level: Level::Zero,
        dom: rt(Term::TmNat),
        cod: rt(Term::TmNat),
    };
    let rec_ty = Type::El {
        level: Level::Zero,
        tm: rt(Term::TmSigma {
            fst_level: Level::Zero,
            snd_level: Level::Zero,
            fst: rt(pi_code),
            snd: rt(Term::TmNat),
        }),
    };
    let head = || {
        rt(Term::FstAt {
            pair: rt(Term::PairAt {
                ty: Some(rty(rec_ty.clone())),
                fst: rt(lam(v(0))),
                snd: rt(Term::Zero),
            }),
        })
    };
    let call = Term::AppAt { fun: head(), arg: rt(Term::Zero) };
    check_closed(Layer::Prog, &call, &Type::Nat, &Level::Zero).unwrap();
    let (_, l) = infer_closed(Layer::Prog, &call).unwrap();
    assert!(l.equiv(&Level::Zero));
    // The negative control, at a domain only the head's type reveals.
    let refused = Term::AppAt { fun: head(), arg: rt(Term::Triv { level: Level::Zero }) };
    assert!(infer_closed(Layer::Prog, &refused).is_err());
    // A head whose type reveals no Π is a mismatch, not a panic.
    let not_fn = Term::AppAt { fun: rt(Term::Zero), arg: rt(Term::Zero) };
    assert_eq!(infer_closed(Layer::Prog, &not_fn).unwrap_err(), TypeError::HeadMismatch);

    // (3) β, reading nothing from the application.
    let redex = Term::AppAt { fun: rt(lam(Term::Succ(rt(v(0))))), arg: rt(Term::Zero) };
    assert_eq!(whnf_term(&redex, &nil_ctx(), FUEL).unwrap(), Term::Succ(rt(Term::Zero)));
    // And through the record field.
    check_closed(Layer::Prog, &call, &Type::Nat, &Level::Zero).unwrap();

    // (4) The box side condition, and the quote boundary's translation.
    let code_ty = Type::CodeTm { ctx: nil_ctx(), ty: rty(Type::Nat), level: Level::Zero };
    let payload = rt(Term::AppAt { fun: rt(lam(v(0))), arg: rt(Term::Zero) });
    assert_eq!(
        check_closed(Layer::Meta, &Term::BoxTm(Rc::clone(&payload)), &code_ty, &Level::Zero)
            .unwrap_err(),
        TypeError::UnderBox
    );
    let spelled = heather_kernel::typing::spell_checked_in_code(
        &psi,
        0,
        Layer::Code,
        &nil_ctx(),
        payload,
        &Type::Nat,
        &Level::Zero,
        FUEL,
    )
    .unwrap();
    assert!(matches!(&*spelled, Term::App { .. }), "{spelled:?}");
    check_closed(Layer::Meta, &Term::BoxTm(spelled), &code_ty, &Level::Zero).unwrap();
}

// -------------------------------------------------------------------------
// Unit and Empty (extension beyond ch. 04; kernel-v1-extensions)
// -------------------------------------------------------------------------

/// `Unit^l`/`Empty^l`/`⟨⟩^l` are level-indexed at **every** layer, code
/// included (`docs/unit-empty-level-indexing.md`). The phase-1 layer-`c` gate
/// is gone as of phase 2.
#[test]
fn unit_empty_are_level_indexed_at_every_layer() {
    let psi = GlobalCtx::default();
    let g = nil_ctx();
    let infer_at = |layer, t: &Type| infer_type(&psi, 0, layer, &g, t, FUEL);

    // At p, each carries and reports its own level — that is the whole route.
    for l in [Level::Zero, c(1), c(2)] {
        for t in [Type::Unit { level: l.clone() }, Type::Empty { level: l.clone() }] {
            assert!(infer_at(Layer::Prog, &t).unwrap().equiv(&l), "{t:?} must be at {l:?}");
            // …and at no other level, which is uniqueness of types.
            assert_eq!(
                check_type(&psi, 0, Layer::Prog, &g, &t, &Level::succ(l.clone()), FUEL).unwrap_err(),
                TypeError::LevelMismatch,
            );
        }
        // ⟨⟩^l : Unit^l @ l — the annotation is load-bearing, not decoration.
        let (ty, li) = infer_term(&psi, 0, Layer::Prog, &g, &Term::Triv { level: l.clone() }, FUEL).unwrap();
        assert!(ty == Type::Unit { level: l.clone() } && li.equiv(&l));
        // The encodings agree with the types about which levels exist:
        // Unit^l : Ty l, so `El` and `Unit` cannot drift apart.
        let (ty, li) = infer_term(&psi, 0, Layer::Prog, &g, &Term::TmUnit { level: l.clone() }, FUEL).unwrap();
        assert!(ty == Type::Ty(l.clone()) && li.equiv(&Level::succ(l.clone())));
    }

    // The phase-1 gate is GONE (phase 2 reshaped the six branch telescopes),
    // so layer c is level-indexed too — which is what makes `box (Unit^ℓ)`
    // recursable rather than merely well-formed.
    for l in [c(1), c(2)] {
        for t in [Type::Unit { level: l.clone() }, Type::Empty { level: l.clone() }] {
            check_type(&psi, 0, Layer::Code, &g, &t, &l, FUEL)
                .unwrap_or_else(|e| panic!("{t:?} must check at layer c: {e:?}"));
        }
        let (ty, li) =
            infer_term(&psi, 0, Layer::Code, &g, &Term::Triv { level: l.clone() }, FUEL).unwrap();
        assert!(ty == Type::Unit { level: l.clone() } && li.equiv(&l));
    }
    // Level 0 is unaffected at c — everything that used to work still does.
    check_type(&psi, 0, Layer::Code, &g, &Type::Unit { level: Level::Zero }, &Level::Zero, FUEL).unwrap();
    check_term(&psi, 0, Layer::Code, &g, &Term::Triv { level: Level::Zero }, &Type::Unit { level: Level::Zero }, &Level::Zero, FUEL).unwrap();
}

#[test]
fn unit_formation_intro_and_encoding() {
    let psi = GlobalCtx::default();
    // Unit @ 0, and its encoding «Unit» : Ty 0 @ 1.
    assert!(infer_type(&psi, 0, Layer::Prog, &nil_ctx(), &Type::Unit { level: Level::Zero }, FUEL)
        .unwrap()
        .equiv(&Level::Zero));
    let (ty, l) = infer_closed(Layer::Prog, &Term::TmUnit { level: Level::Zero }).unwrap();
    assert!(ty == Type::Ty(Level::Zero) && l.equiv(&c(1)));
    // ⟨⟩ : Unit @ 0, and it checks against the El-decode of the encoding.
    let (ty, l) = infer_closed(Layer::Prog, &Term::Triv { level: Level::Zero }).unwrap();
    assert!(ty == Type::Unit { level: Level::Zero } && l.equiv(&Level::Zero));
    let el_unit = Type::El { level: Level::Zero, tm: rt(Term::TmUnit { level: Level::Zero }) };
    check_closed(Layer::Prog, &Term::Triv { level: Level::Zero }, &el_unit, &Level::Zero).unwrap();
    // Layer v admits neither the intro nor the encoding.
    assert_eq!(infer_closed(Layer::Var, &Term::Triv { level: Level::Zero }).unwrap_err(), TypeError::LayerMismatch);
    assert_eq!(infer_closed(Layer::Var, &Term::TmUnit { level: Level::Zero }).unwrap_err(), TypeError::LayerMismatch);
}

#[test]
fn empty_formation_encoding_and_elimination() {
    let psi = GlobalCtx::default();
    assert!(infer_type(&psi, 0, Layer::Prog, &nil_ctx(), &Type::Empty { level: Level::Zero }, FUEL)
        .unwrap()
        .equiv(&Level::Zero));
    let (ty, l) = infer_closed(Layer::Prog, &Term::TmEmpty { level: Level::Zero }).unwrap();
    assert!(ty == Type::Ty(Level::Zero) && l.equiv(&c(1)));
    // elim_Empty^0 (x. Nat; e) : Nat @ 0 under `e : Empty`. Check in a context
    // with one Empty-typed variable so the scrutinee is a (neutral) variable.
    let gamma = ext(&nil_ctx(), Type::Empty { level: Level::Zero }, Level::Zero);
    let elim = Term::ElimEmpty {
        level: Level::Zero,
            scrut_level: Level::Zero,
        motive: rty(Type::Nat),
        scrut: rt(v(0)),
    };
    let (ty, l) =
        infer_term(&psi, 0, Layer::Prog, &gamma, &elim, FUEL).unwrap();
    assert!(ty == Type::Nat && l.equiv(&Level::Zero));
    // A dependent motive: elim_Empty^0 (x. El 0 «Nat»; e) : El 0 «Nat» @ 0,
    // convertible to Nat via the motive at the scrutinee.
    let dep = Term::ElimEmpty {
        level: Level::Zero,
            scrut_level: Level::Zero,
        motive: rty(Type::El { level: Level::Zero, tm: rt(Term::TmNat) }),
        scrut: rt(v(0)),
    };
    check_term(
        &psi, 0, Layer::Prog, &gamma, &dep, &Type::Nat, &Level::Zero, FUEL,
    )
    .unwrap();
    // A non-Empty scrutinee is rejected.
    let bad = Term::ElimEmpty {
        level: Level::Zero,
            scrut_level: Level::Zero,
        motive: rty(Type::Nat),
        scrut: rt(Term::Zero),
    };
    assert!(infer_closed(Layer::Prog, &bad).is_err());
    // Layer v does not admit the eliminator.
    assert_eq!(
        infer_term(&psi, 0, Layer::Var, &gamma, &elim, FUEL).unwrap_err(),
        TypeError::LayerMismatch
    );
}

// -------------------------------------------------------------------------
// Binary sums (extension beyond ch. 04; kernel-v1-extensions)
// -------------------------------------------------------------------------

#[test]
fn sum_formation_intro_encoding_and_case() {
    let psi = GlobalCtx::default();
    // Nat +^{0,0} Nat @ 0.
    let sum = Type::Sum {
        lhs_level: Level::Zero,
        rhs_level: Level::Zero,
        lhs: rty(Type::Nat),
        rhs: rty(Type::Nat),
    };
    assert!(infer_type(&psi, 0, Layer::Prog, &nil_ctx(), &sum, FUEL)
        .unwrap()
        .equiv(&Level::Zero));
    // A heterogeneous sum: Nat +^{0,1} Ty 0 @ 1 (level is the ⊔).
    let het = Type::Sum {
        lhs_level: Level::Zero,
        rhs_level: c(1),
        lhs: rty(Type::Nat),
        rhs: rty(Type::Ty(Level::Zero)),
    };
    assert!(infer_type(&psi, 0, Layer::Prog, &nil_ctx(), &het, FUEL)
        .unwrap()
        .equiv(&c(1)));
    // Encoding «Nat» +^{0,0} «Nat» : Ty 0 @ 1, El-decoding to Nat + Nat.
    let tm_sum = Term::TmSum {
        lhs_level: Level::Zero,
        rhs_level: Level::Zero,
        lhs: rt(Term::TmNat),
        rhs: rt(Term::TmNat),
    };
    let (ty, l) = infer_closed(Layer::Prog, &tm_sum).unwrap();
    let Type::Ty(tl) = &ty else { panic!("encoding should infer a universe") };
    assert!(tl.equiv(&Level::Zero) && l.equiv(&c(1)));
    // inl 0 : Nat + Nat @ 0, and it checks against the El-decode of the
    // encoding (conversion fires through El (s + t) ⇝ El s + El t).
    let mk_inl = || Term::Inl {
        lhs_level: Level::Zero,
        rhs_level: Level::Zero,
        lhs: rty(Type::Nat),
        rhs: rty(Type::Nat),
        val: rt(Term::Zero),
    };
    let (ty, l) = infer_closed(Layer::Prog, &mk_inl()).unwrap();
    assert!(ty == sum && l.equiv(&Level::Zero));
    let el_sum = Type::El { level: Level::Zero, tm: rt(tm_sum) };
    check_closed(Layer::Prog, &mk_inl(), &el_sum, &Level::Zero).unwrap();
    // inr (S 0) : Nat + Nat @ 0.
    let mk_inr = || Term::Inr {
        lhs_level: Level::Zero,
        rhs_level: Level::Zero,
        lhs: rty(Type::Nat),
        rhs: rty(Type::Nat),
        val: rt(Term::Succ(rt(Term::Zero))),
    };
    assert!(infer_closed(Layer::Prog, &mk_inr()).unwrap().0 == sum);
    // A value not inhabiting the chosen summand is rejected (0 : Nat, not Ty 0).
    let bad_inl = Term::Inl {
        lhs_level: c(1),
        rhs_level: Level::Zero,
        lhs: rty(Type::Ty(Level::Zero)),
        rhs: rty(Type::Nat),
        val: rt(Term::Zero),
    };
    assert!(infer_closed(Layer::Prog, &bad_inl).is_err());
    // case with a constant Nat motive: case (z. Nat; Nat; Nat; x. x; y. y;
    // inl 0) : Nat @ 0.
    let case = Term::Case {
        lhs_level: Level::Zero,
        rhs_level: Level::Zero,
        motive_level: Level::Zero,
        lhs: rty(Type::Nat),
        rhs: rty(Type::Nat),
        motive: rty(Type::Nat),
        case_l: rt(v(0)),
        case_r: rt(v(0)),
        scrut: rt(mk_inl()),
    };
    let (ty, l) = infer_closed(Layer::Prog, &case).unwrap();
    assert!(ty == Type::Nat && l.equiv(&Level::Zero));
    // A dependent motive over a variable scrutinee: with z : Nat + Nat in Γ,
    // case (z. El 0 «Nat»; …; z) : El 0 «Nat» @ 0, convertible to Nat.
    let gamma = ext(&nil_ctx(), sum.clone(), Level::Zero);
    let dep = Term::Case {
        lhs_level: Level::Zero,
        rhs_level: Level::Zero,
        motive_level: Level::Zero,
        lhs: rty(Type::Nat),
        rhs: rty(Type::Nat),
        motive: rty(Type::El { level: Level::Zero, tm: rt(Term::TmNat) }),
        case_l: rt(Term::Zero),
        case_r: rt(Term::Zero),
        scrut: rt(v(0)),
    };
    check_term(&psi, 0, Layer::Prog, &gamma, &dep, &Type::Nat, &Level::Zero, FUEL).unwrap();
    // A non-sum scrutinee is rejected.
    let bad_case = Term::Case {
        lhs_level: Level::Zero,
        rhs_level: Level::Zero,
        motive_level: Level::Zero,
        lhs: rty(Type::Nat),
        rhs: rty(Type::Nat),
        motive: rty(Type::Nat),
        case_l: rt(v(0)),
        case_r: rt(v(0)),
        scrut: rt(Term::Zero),
    };
    assert!(infer_closed(Layer::Prog, &bad_case).is_err());
    // Layer v admits neither intro nor eliminator.
    assert_eq!(infer_closed(Layer::Var, &mk_inl()).unwrap_err(), TypeError::LayerMismatch);
    assert_eq!(infer_closed(Layer::Var, &case).unwrap_err(), TypeError::LayerMismatch);
}

// -------------------------------------------------------------------------
// W-types (extension; kernel-v1-extensions)
// -------------------------------------------------------------------------

#[test]
fn w_formation_intro_encoding_and_elim() {
    let psi = GlobalCtx::default();
    // W^{0,0}(x : Nat). Nat @ 0; heterogeneous W^{0,1}(x : Nat). Ty 0 @ 1.
    let w_nat_nat = Type::W {
        shape_level: Level::Zero,
        pos_level: Level::Zero,
        shape: rty(Type::Nat),
        pos: rty(Type::Nat),
    };
    assert!(infer_type(&psi, 0, Layer::Prog, &nil_ctx(), &w_nat_nat, FUEL)
        .unwrap()
        .equiv(&Level::Zero));
    let het = Type::W {
        shape_level: Level::Zero,
        pos_level: c(1),
        shape: rty(Type::Nat),
        pos: rty(Type::Ty(Level::Zero)),
    };
    assert!(infer_type(&psi, 0, Layer::Prog, &nil_ctx(), &het, FUEL)
        .unwrap()
        .equiv(&c(1)));
    // A dependent position family: W^{0,0}(x : Nat). El 0 «Nat» — the family
    // is checked in (Γ, x : Nat).
    let dep_w = Type::W {
        shape_level: Level::Zero,
        pos_level: Level::Zero,
        shape: rty(Type::Nat),
        pos: rty(Type::El { level: Level::Zero, tm: rt(Term::TmNat) }),
    };
    assert!(infer_type(&psi, 0, Layer::Prog, &nil_ctx(), &dep_w, FUEL)
        .unwrap()
        .equiv(&Level::Zero));
    // Encoding W (x : «Nat»). «Empty» : Ty 0 @ 1.
    let tm_w = Term::TmW {
        shape_level: Level::Zero,
        pos_level: Level::Zero,
        shape: rt(Term::TmNat),
        pos: rt(Term::TmEmpty { level: Level::Zero }),
    };
    let (ty, l) = infer_closed(Layer::Prog, &tm_w).unwrap();
    let Type::Ty(tl) = &ty else { panic!("encoding should infer a universe") };
    assert!(tl.equiv(&Level::Zero) && l.equiv(&c(1)));
    // sup into W(x:Nat).Empty: the childless leaf. f : Π(y : Empty). W.
    let w = Type::W {
        shape_level: Level::Zero,
        pos_level: Level::Zero,
        shape: rty(Type::Nat),
        pos: rty(Type::Empty { level: Level::Zero }),
    };
    let no_children = Term::Lam {
        dom_level: Level::Zero,
        cod_level: Level::Zero,
        dom: rty(Type::Empty { level: Level::Zero }),
        body: rt(Term::ElimEmpty {
            level: Level::Zero,
            scrut_level: Level::Zero,
            motive: rty(w.clone()),
            scrut: rt(v(0)),
        }),
    };
    let mk_sup = |label: Term| Term::Sup {
        shape_level: Level::Zero,
        pos_level: Level::Zero,
        shape_ty: rty(Type::Nat),
        pos_ty: rty(Type::Empty { level: Level::Zero }),
        label: rt(label),
        children: rt(no_children.clone()),
    };
    let (ty, l) = infer_closed(Layer::Prog, &mk_sup(Term::Zero)).unwrap();
    assert!(ty == w && l.equiv(&Level::Zero));
    // It also checks against the El-decode of the encoding (conversion fires
    // through El (W s t) ⇝ W (El s) (El t)).
    let el_w = Type::El { level: Level::Zero, tm: rt(tm_w) };
    check_closed(Layer::Prog, &mk_sup(Term::Zero), &el_w, &Level::Zero).unwrap();
    // A label not inhabiting the shape type is rejected.
    assert!(infer_closed(Layer::Prog, &mk_sup(Term::Triv { level: Level::Zero })).is_err());
    // A subtree function of the wrong type is rejected.
    let bad_sup = Term::Sup {
        shape_level: Level::Zero,
        pos_level: Level::Zero,
        shape_ty: rty(Type::Nat),
        pos_ty: rty(Type::Empty { level: Level::Zero }),
        label: rt(Term::Zero),
        children: rt(Term::Zero),
    };
    assert!(infer_closed(Layer::Prog, &bad_sup).is_err());
    // elim_W with a constant Nat motive: step returns the label a.
    let mk_elim = |step: Term, scrut: Term| Term::ElimW {
        shape_level: Level::Zero,
        pos_level: Level::Zero,
        motive_level: Level::Zero,
        shape: rty(Type::Nat),
        pos: rty(Type::Empty { level: Level::Zero }),
        motive: rty(Type::Nat),
        step: rt(step),
        scrut: rt(scrut),
    };
    let elim = mk_elim(v(2), mk_sup(Term::Zero));
    let (ty, l) = infer_closed(Layer::Prog, &elim).unwrap();
    assert!(ty == Type::Nat && l.equiv(&Level::Zero));
    // The step's binders really carry the (a, f, ih) types: a step returning
    // f (a Π type, not the motive Nat) is rejected…
    assert!(infer_closed(Layer::Prog, &mk_elim(v(1), mk_sup(Term::Zero))).is_err());
    // …and a step that η-uses the ih binder at Π(y : T[a/x]). M is accepted
    // in a position expecting that Π type: check the raw binder against it.
    // (With a constant Nat motive, ih : Π(y : Empty). Nat.)
    let ih_pi = Type::Pi {
        dom_level: Level::Zero,
        cod_level: Level::Zero,
        dom: rty(Type::Empty { level: Level::Zero }),
        cod: rty(Type::Nat),
    };
    let use_ih = mk_elim(
        Term::App {
            fun: rt(Term::Lam {
                dom_level: Level::Zero,
                cod_level: Level::Zero,
                dom: rty(ih_pi.clone()),
                body: rt(Term::Zero),
            }),
            dom_level: Level::Zero,
            cod_level: Level::Zero,
            dom: rty(ih_pi),
            cod: rty(Type::Nat),
            arg: rt(v(0)), // the ih binder
        },
        mk_sup(Term::Zero),
    );
    let (ty, l) = infer_closed(Layer::Prog, &use_ih).unwrap();
    assert!(ty == Type::Nat && l.equiv(&Level::Zero));
    // A dependent motive over a variable scrutinee: with z : W in Γ,
    // elim (z. El 0 «Nat»; a f ih. 0; z) checks against Nat.
    let gamma = ext(&nil_ctx(), w.clone(), Level::Zero);
    let dep = Term::ElimW {
        shape_level: Level::Zero,
        pos_level: Level::Zero,
        motive_level: Level::Zero,
        shape: rty(Type::Nat),
        pos: rty(Type::Empty { level: Level::Zero }),
        motive: rty(Type::El { level: Level::Zero, tm: rt(Term::TmNat) }),
        step: rt(Term::Zero),
        scrut: rt(v(0)),
    };
    check_term(&psi, 0, Layer::Prog, &gamma, &dep, &Type::Nat, &Level::Zero, FUEL).unwrap();
    // A non-W scrutinee is rejected.
    assert!(infer_closed(Layer::Prog, &mk_elim(v(2), Term::Zero)).is_err());
    // Layer v admits neither intro nor eliminator.
    assert_eq!(
        infer_closed(Layer::Var, &mk_sup(Term::Zero)).unwrap_err(),
        TypeError::LayerMismatch
    );
    assert_eq!(infer_closed(Layer::Var, &elim).unwrap_err(), TypeError::LayerMismatch);
}

/// A spine is typed as one walk (`Tc::app_at_spine`): the arguments held and
/// substituted at once. The type it infers is the annotated `app`'s own
/// syntax — one substitution at a time — for a three-node dependent spine
/// under a context the identity is not trivial on; a telescope that stops
/// being a syntactic Π mid-spine (`El ⌜Π⌝`) is taken node by node from
/// there; and each argument is still checked at its domain under the ones
/// before it.
#[test]
fn a_spine_is_typed_in_one_walk() {
    // Γ = n : Nat, f : Π(A : Ty 0). Π(a : El A). Π(b : El A). El A
    let el = |i: u32| Type::El { level: Level::Zero, tm: rt(v(i)) };
    let pi = |dom_level: Level, dom: Type, cod: Type| Type::Pi { dom_level, cod_level: Level::Zero, dom: rty(dom), cod: rty(cod) };
    let f_ty = pi(c(1), Type::Ty(Level::Zero), pi(Level::Zero, el(0), pi(Level::Zero, el(1), el(2))));
    let gamma = ext(&ext(&nil_ctx(), Type::Nat, Level::Zero), f_ty.clone(), c(1));
    let psi = GlobalCtx::default();
    let n = || rt(v(1));
    let at = |fun: Term, arg: Rc<Term>| Term::AppAt { fun: rt(fun), arg };
    let spine = at(at(at(v(0), rt(Term::TmNat)), n()), rt(Term::Zero));
    // The annotated spelling, one substitution per node.
    let id = |t: Rc<Term>| LocalSubst::id(&gamma).extended(t);
    let Type::Pi { cod: c1, .. } = &f_ty else { unreachable!() };
    let t1 = c1.apply_local(&id(rt(Term::TmNat)));
    let Type::Pi { dom: d2, cod: c2, .. } = &t1 else { unreachable!() };
    let t2 = c2.apply_local(&id(n()));
    let Type::Pi { dom: d3, cod: c3, .. } = &t2 else { unreachable!() };
    let app = |fun: Term, dom: &Rc<Type>, cod: &Rc<Type>, arg: Rc<Term>, dom_level: Level| Term::App {
        fun: rt(fun),
        dom_level,
        cod_level: Level::Zero,
        dom: Rc::clone(dom),
        cod: Rc::clone(cod),
        arg,
    };
    let annotated = app(
        app(app(v(0), &rty(Type::Ty(Level::Zero)), c1, rt(Term::TmNat), c(1)), d2, c2, n(), Level::Zero),
        d3,
        c3,
        rt(Term::Zero),
        Level::Zero,
    );
    let (ty_at, _) = infer_term(&psi, 0, Layer::Prog, &gamma, &spine, FUEL).unwrap();
    let (ty_app, _) = infer_term(&psi, 0, Layer::Prog, &gamma, &annotated, FUEL).unwrap();
    assert!(ty_at == ty_app, "one walk must spell what one substitution per node does: {ty_at:?} vs {ty_app:?}");
    // Negative control: the third argument is checked at `El A[Nat/A]`.
    let bad = at(at(at(v(0), rt(Term::TmNat)), n()), rt(Term::Triv { level: Level::Zero }));
    assert!(infer_term(&psi, 0, Layer::Prog, &gamma, &bad, FUEL).is_err());

    // g : Π(A : Ty 0). Π(a : El A). El ⌜Π(x : A). A⌝ — the third node's Π
    // is only a Π after reduction.
    let code = Term::TmPi { dom_level: Level::Zero, cod_level: Level::Zero, dom: rt(v(1)), cod: rt(v(2)) };
    let g_ty = pi(c(1), Type::Ty(Level::Zero), pi(Level::Zero, el(0), Type::El { level: Level::Zero, tm: rt(code) }));
    let gamma = ext(&ext(&nil_ctx(), Type::Nat, Level::Zero), g_ty, c(1));
    let spine = at(at(at(v(0), rt(Term::TmNat)), n()), rt(Term::Zero));
    check_term(&psi, 0, Layer::Prog, &gamma, &spine, &Type::Nat, &Level::Zero, FUEL).unwrap();
    let bad = at(at(at(v(0), rt(Term::TmNat)), n()), rt(Term::Triv { level: Level::Zero }));
    assert!(infer_term(&psi, 0, Layer::Prog, &gamma, &bad, FUEL).is_err());
}

/// A global referenced in the context it was made in, by the identity — a
/// lifted proof, a named value — checks without instantiating each entry
/// (`Tc::subst_ck`'s identity case). The identity's *shape* is not enough:
/// into a context that is not the current one, the entries are checked, and
/// a mismatch is refused.
#[test]
fn an_identity_reference_checks_in_its_own_context_only() {
    // u : Trm_p(x : Nat, y : Nat ⊢ Nat @ 0)
    let delta = ext(&ext(&nil_ctx(), Type::Nat, Level::Zero), Type::Nat, Level::Zero);
    let psi = GlobalCtx::new(vec![GlobalBinding::opaque_tm(delta.clone(), Layer::Prog, rty(Type::Nat), Level::Zero)]);
    check_term(&psi, 0, Layer::Prog, &delta, &gtm(0, &delta), &Type::Nat, &Level::Zero, FUEL).unwrap();
    // Γ = x : Nat, y : Ty 0 — the same length, so `id_Γ` has the identity's
    // shape, but `y` is no `Nat`.
    let gamma = ext(&ext(&nil_ctx(), Type::Nat, Level::Zero), Type::Ty(Level::Zero), c(1));
    assert!(check_term(&psi, 0, Layer::Prog, &gamma, &gtm(0, &gamma), &Type::Nat, &Level::Zero, FUEL).is_err());
}
