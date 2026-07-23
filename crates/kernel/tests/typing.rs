//! Golden tests for the ch. 04 type checker: hand-elaborated instances per
//! judgment family — MLTT at layers c/p (variables, Π/λ/app with the
//! conversion rule firing, elim_Nat, encodings/El), the layer-v and ω
//! disciplines, global contexts and local substitutions, universe
//! polymorphism, contextual types (box/letbox, checking-only box under
//! binders), and the code recursors, including a full *identity recursor*
//! whose 13 branches re-box their telescopes' code — an end-to-end exercise
//! of every `G_Typ`/`G_Trm` telescope.
//!
//! No generator-based properties: the generators produce ill-typed terms,
//! where a legitimate `Err` is indistinguishable from a bug (property tests
//! against conversion are tracked in issues/kernel-conv-properties.md).

use std::rc::Rc;

use heather_kernel::layer::Layer;
use heather_kernel::level::{Level, UnivVar};
use heather_kernel::term::{
    Branches, CtxBase, CtxEntry, GlobalBinding, GlobalCtx, GlobalVar, LocalCtx, LocalSubst,
    LocalVar, Motives, SubstTail, Term, Type,
};
use heather_kernel::typing::{
    check_global_ctx, check_local_ctx, check_local_subst, check_term, check_type, infer_term,
    infer_type, TypeError,
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
    LocalCtx { base: CtxBase::Nil, entries: vec![] }
}

/// The context consisting of the context variable at index `i`.
fn g_ctx(i: u32) -> LocalCtx {
    LocalCtx { base: CtxBase::Var(GlobalVar(i)), entries: vec![] }
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
    GlobalCtx {
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
    }
}

#[test]
fn global_context_formation() {
    check_global_ctx(&sample_psi(), 0, FUEL).unwrap();
    // A Ty binding may not live at layer m …
    let bad = GlobalCtx {
        bindings: vec![GlobalBinding::Ty {
            ctx: nil_ctx(),
            layer: Layer::Meta,
            level: Level::Zero,
        }],
    };
    assert_eq!(check_global_ctx(&bad, 0, FUEL).unwrap_err(), TypeError::LayerMismatch);
    // … and a binding's context must be well-formed in its prefix.
    let unbound = GlobalCtx {
        bindings: vec![GlobalBinding::Ty {
            ctx: g_ctx(0),
            layer: Layer::Code,
            level: Level::Zero,
        }],
    };
    assert_eq!(
        check_global_ctx(&unbound, 0, FUEL).unwrap_err(),
        TypeError::UnboundGlobalVar(0)
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
    let psi_c = GlobalCtx {
        bindings: vec![
            GlobalBinding::Ctx,
            GlobalBinding::Tm {
                ctx: g_ctx(0),
                layer: Layer::Code,
                ty: rty(Type::Nat),
                level: Level::Zero,
            },
        ],
    };
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
        tm_var: z(),
        tm_nat: z(),
        tm_pi: z(),
        tm_ty: z(),
        tm_zero: z(),
        tm_succ: z(),
        tm_elim_nat: z(),
        tm_lam: z(),
        tm_app: z(),
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
    })
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
