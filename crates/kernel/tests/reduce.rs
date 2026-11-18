//! Tests for ch. 06 weak-head reduction: golden tests for every β-rule
//! (including all 22 recursor branches, probing each branch telescope's
//! universe / global / recursive-call instantiation), congruence-order and
//! blocking behavior, and generator-based properties (normal forms do not
//! step; reducts stay well-scoped).

mod common;

use heather_kernel::rc::Rc;

use common::*;
use heather_kernel::level::{Level, UnivVar};
use heather_kernel::reduce::{
    is_neutral_term, is_whnf_term, is_whnf_type, whnf_term,
};
use heather_kernel::term::{
    Branches, CtxBase, CtxEntry, GlobalVar, LocalCtx, LocalSubst, LocalVar, Motives, SubstTail,
    Term, Type,
};

/// The single-step relation, for terms far inside the frame budget.
fn step_term(t: &Term, gamma: &LocalCtx) -> Option<Term> {
    heather_kernel::reduce::step_term(t, gamma).expect("a test term steps within the frame budget")
}

/// The single-step relation, for types far inside the frame budget.
fn step_type(t: &Type, gamma: &LocalCtx) -> Option<Type> {
    heather_kernel::reduce::step_type(t, gamma).expect("a test type steps within the frame budget")
}

// -------------------------------------------------------------------------
// Construction helpers
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

/// `(·, x₀ : Nat @ 0, …)` with `n` entries.
fn nil_ctx(n: u32) -> LocalCtx {
    LocalCtx {
        base: CtxBase::Nil,
        entries: ((0..n)
            .map(|_| CtxEntry { ty: rty(Type::Nat), level: Level::Zero })
            .collect::<Vec<_>>()).into(),
    }
}

/// `Δ, x : ty @ level`.
fn extend(delta: &LocalCtx, ty: Type, level: Level) -> LocalCtx {
    let mut d = delta.clone();
    d.entries.push(CtxEntry { ty: rty(ty), level });
    d
}

/// Application with dummy `Nat` annotations — a "pair" for probing several
/// telescope positions in one branch body.
fn app2(f: Term, a: Term) -> Term {
    Term::App {
        fun: rt(f),
        dom_level: Level::Zero,
        cod_level: Level::Zero,
        dom: rty(Type::Nat),
        cod: rty(Type::Nat),
        arg: rt(a),
    }
}

/// Left-nested `app2` chain packing many probes into one term.
fn chain(items: Vec<Term>) -> Term {
    items.into_iter().reduce(app2).unwrap()
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

/// Numeral.
fn num(n: u32) -> Term {
    let mut t = Term::Zero;
    for _ in 0..n {
        t = Term::Succ(rt(t));
    }
    t
}

/// The identity substitution `wk^k_g` onto an index context `(g, k entries)`
/// — how a branch body references a global binding's own context.
fn wk_id(g: u32, k: u32) -> LocalSubst {
    LocalSubst {
        tail: SubstTail::Wk { len: k, ctx_var: GlobalVar::index(g) },
        terms: (0..k).map(|j| rt(v(k - 1 - j))).collect(),
    }
}

/// Probe `box (U^{id})` for a global type binding `var` with index context
/// `(g, k entries)`; after β it becomes `box` of the payload.
fn box_gty(var: u32, g: u32, k: u32) -> Term {
    Term::BoxTy(rty(Type::GlobalTy { var: GlobalVar::index(var), subst: wk_id(g, k) }))
}

/// Probe `box (u^{id})` for a global term binding, as [`box_gty`].
fn box_gtm(var: u32, g: u32, k: u32) -> Term {
    Term::BoxTm(rt(Term::GlobalTm { var: GlobalVar::index(var), subst: wk_id(g, k) }))
}

/// Probe observing the context variable `g`: `(0 @ g)` becomes `(0 @ Δ)`.
fn ctx_probe(g: u32) -> Term {
    Term::CtxApp {
        fun: rt(Term::Zero),
        ctx: LocalCtx::ctx_var(GlobalVar::index(g)),
    }
}

fn dummy_motives() -> Rc<Motives> {
    Rc::new(Motives { ty_motive: rty(Type::Nat), tm_motive: rty(Type::Nat) })
}

fn dummy_branches() -> Branches {
    let z = || rt(Term::Zero);
    Branches {
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
        ty_id: z(),
        tm_id: z(),
        tm_refl: z(),
        tm_j: z(),
        ty_sigma: z(),
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
        tm_elim_sempty: z(),
        ty_squash: z(),
        tm_squash: z(),
        tm_squash_in: z(),
        tm_elim_squash: z(),
        tm_unsquash_empty: z(),
        ty_m: z(),
        tm_m: z(),
        tm_corec: z(),
        tm_out: z(),
        ty_dvec: z(),
        tm_dvec: z(),
        ty_iwf: z(),
        tm_iwf: z(),
        tm_sup_i: z(),
        tm_elim_iwf: z(),
    }
}

fn elim_ty(branches: &Rc<Branches>, code_level: Level, ctx: LocalCtx, scrut: Term) -> Term {
    Term::ElimCodeTy {
        ty_motive_level: Level::Zero,
        tm_motive_level: Level::Zero,
        motives: dummy_motives(),
        branches: Rc::clone(branches),
        code_level,
        ctx,
        scrut: rt(scrut),
    }
}

fn elim_tm(
    branches: &Rc<Branches>,
    code_level: Level,
    ctx: LocalCtx,
    ty: Type,
    scrut: Term,
) -> Term {
    Term::ElimCodeTm {
        ty_motive_level: Level::Zero,
        tm_motive_level: Level::Zero,
        motives: dummy_motives(),
        branches: Rc::clone(branches),
        code_level,
        ctx,
        ty: rty(ty),
        scrut: rt(scrut),
    }
}

// -------------------------------------------------------------------------
// Type reduction: El decode
// -------------------------------------------------------------------------

#[test]
fn el_decodes_encodings() {
    let gamma = nil_ctx(0);
    // El^0 Nat ⇝ Nat
    let t = Type::El { level: Level::Zero, tm: rt(Term::TmNat) };
    assert_eq!(step_type(&t, &gamma), Some(Type::Nat));
    // El^{1+l} (Ty l) ⇝ Ty l
    let t = Type::El { level: c(4), tm: rt(Term::TmTy(c(3))) };
    assert_eq!(step_type(&t, &gamma), Some(Type::Ty(c(3))));
    // El (Π s t) ⇝ Π (El s) (El t)
    let t = Type::El {
        level: c(2),
        tm: rt(Term::TmPi {
            dom_level: c(1),
            cod_level: c(2),
            dom: rt(Term::TmNat),
            cod: rt(Term::TmTy(c(0))),
        }),
    };
    let expect = Type::Pi {
        dom_level: c(1),
        cod_level: c(2),
        dom: rty(Type::El { level: c(1), tm: rt(Term::TmNat) }),
        cod: rty(Type::El { level: c(2), tm: rt(Term::TmTy(c(0))) }),
    };
    assert_eq!(step_type(&t, &gamma), Some(expect));
}

#[test]
fn el_congruence_and_blocking() {
    let gamma = nil_ctx(0);
    // congruence: the encoding reduces under El
    let t = Type::El {
        level: Level::Zero,
        tm: rt(app2(lam(Term::TmNat), Term::Zero)),
    };
    assert_eq!(
        step_type(&t, &gamma),
        Some(Type::El { level: Level::Zero, tm: rt(Term::TmNat) })
    );
    // neutral encoding: El is neutral, no step
    let t = Type::El { level: Level::Zero, tm: rt(v(0)) };
    assert_eq!(step_type(&t, &nil_ctx(1)), None);
    assert!(is_whnf_type(&t));
}

// -------------------------------------------------------------------------
// Core term β-rules
// -------------------------------------------------------------------------

#[test]
fn beta_app() {
    // (λx. x) 0 ⇝ 0
    let gamma = nil_ctx(0);
    assert_eq!(step_term(&app2(lam(v(0)), Term::Zero), &gamma), Some(Term::Zero));
    // Under Γ with one entry: (λx. x₁) 0 ⇝ x₀ — the body's reference to Γ
    // survives the binder's disappearance.
    let gamma = nil_ctx(1);
    assert_eq!(step_term(&app2(lam(v(1)), Term::Zero), &gamma), Some(v(0)));
}

/// A step stands on one native frame per blocked head above its redex, and
/// fuel never sees those (a closed `pow(3, 5000)` stood on thousands). Past
/// `REDUCER_DEPTH_LIMIT` the step answers `OutOfFuel`; under it, the same
/// spine steps as before.
#[test]
fn a_step_below_the_frame_budget_is_out_of_fuel() {
    use heather_kernel::reduce::{OutOfFuel, REDUCER_DEPTH_LIMIT};
    // `((λx. x) (λx. x)) (λx. x) …`: the redex is at the bottom of the spine.
    let spine = |heads: u32| (0..heads).fold(lam(v(0)), |f, _| app2(f, lam(v(0))));
    let gamma = nil_ctx(0);
    let shallow = spine(REDUCER_DEPTH_LIMIT - 1);
    assert!(matches!(heather_kernel::reduce::step_term(&shallow, &gamma), Ok(Some(_))));
    let deep = spine(REDUCER_DEPTH_LIMIT + 1);
    assert_eq!(heather_kernel::reduce::step_term(&deep, &gamma), Err(OutOfFuel));
    assert_eq!(whnf_term(&deep, &gamma, 64), Err(OutOfFuel));
}

#[test]
fn beta_elim_nat_zero_and_succ() {
    let gamma = nil_ctx(0);
    let elim = |scrut: Term| Term::ElimNat {
        level: Level::Zero,
        motive: rty(Type::Nat),
        base: rt(num(7)),
        step: rt(app2(v(1), v(0))), // probes (x = pred, y = rec)
        scrut: rt(scrut),
    };
    assert_eq!(step_term(&elim(Term::Zero), &gamma), Some(num(7)));
    // elim (su 0) ⇝ step[0/x, elim 0/y]
    assert_eq!(
        step_term(&elim(num(1)), &gamma),
        Some(app2(Term::Zero, elim(Term::Zero)))
    );
}

#[test]
fn whnf_computes_addition() {
    // add m n = elim_Nat (x.Nat) n (x,y. su y) m; 2 + 3 = 5. WHNF stops at
    // each `su`, so read the numeral off by repeated weak-head reduction.
    fn nat_value(t: &Term, gamma: &LocalCtx) -> u32 {
        let mut n = 0;
        let mut cur = t.clone();
        loop {
            match whnf_term(&cur, gamma, 64).unwrap() {
                Term::Zero => return n,
                Term::Succ(inner) => {
                    n += 1;
                    cur = (*inner).clone();
                }
                other => panic!("not a numeral: {other:?}"),
            }
        }
    }
    let gamma = nil_ctx(0);
    let add = Term::ElimNat {
        level: Level::Zero,
        motive: rty(Type::Nat),
        base: rt(num(3)),
        step: rt(Term::Succ(rt(v(0)))),
        scrut: rt(num(2)),
    };
    assert_eq!(nat_value(&add, &gamma), 5);
}

#[test]
fn beta_uapp() {
    let gamma = nil_ctx(0);
    // (Λ ℓ ℓ'. Ty ℓ') $ (1, 2) ⇝ Ty 2 — the written vectors pair
    // positionally, ℓ' is the *inner* binder (de Bruijn 0).
    let t = Term::UApp {
        fun: rt(Term::ULam { num_vars: 2, level: Level::Zero, body: rt(Term::TmTy(lv(0))) }),
        levels: vec![c(1), c(2)],
    };
    assert_eq!(step_term(&t, &gamma), Some(Term::TmTy(c(2))));
    let t = Term::UApp {
        fun: rt(Term::ULam { num_vars: 2, level: Level::Zero, body: rt(Term::TmTy(lv(1))) }),
        levels: vec![c(1), c(2)],
    };
    assert_eq!(step_term(&t, &gamma), Some(Term::TmTy(c(1))));
    // An ambient universe variable in the body renumbers down.
    let t = Term::UApp {
        fun: rt(Term::ULam { num_vars: 1, level: Level::Zero, body: rt(Term::TmTy(lv(1))) }),
        levels: vec![c(9)],
    };
    assert_eq!(step_term(&t, &gamma), Some(Term::TmTy(lv(0))));
    // Arity mismatch: stuck, no rule.
    let t = Term::UApp {
        fun: rt(Term::ULam { num_vars: 2, level: Level::Zero, body: rt(Term::Zero) }),
        levels: vec![c(1)],
    };
    assert_eq!(step_term(&t, &gamma), None);
}

#[test]
fn beta_ctx_app_and_ty_app() {
    let gamma = nil_ctx(0);
    let delta = nil_ctx(2);
    // (Λ g. 0 @ g) @ Δ ⇝ 0 @ Δ
    let t = Term::CtxApp {
        fun: rt(Term::CtxLam { level: Level::Zero, body: rt(ctx_probe(0)) }),
        ctx: delta.clone(),
    };
    assert_eq!(
        step_term(&t, &gamma),
        Some(Term::CtxApp { fun: rt(Term::Zero), ctx: delta })
    );
    // (Λ U. box U^·) @ Nat ⇝ box Nat
    let empty = LocalSubst { tail: SubstTail::Empty, terms: vec![] };
    let t = Term::TyApp {
        fun: rt(Term::TyLam {
            ctx: nil_ctx(0),
            arg_level: Level::Zero,
            body_level: Level::Zero,
            body: rt(Term::BoxTy(rty(Type::GlobalTy { var: GlobalVar::index(0), subst: empty }))),
        }),
        arg: rty(Type::Nat),
    };
    assert_eq!(step_term(&t, &gamma), Some(Term::BoxTy(rty(Type::Nat))));
}

#[test]
fn beta_letbox() {
    let gamma = nil_ctx(0);
    let empty = LocalSubst { tail: SubstTail::Empty, terms: vec![] };
    // letbox (U. box U^·) (box Nat) ⇝ box Nat
    let t = Term::LetBoxTy {
        motive_level: Level::Zero,
        code_level: Level::Zero,
        ctx: nil_ctx(0),
        motive: rty(Type::Nat),
        body: rt(Term::BoxTy(rty(Type::GlobalTy { var: GlobalVar::index(0), subst: empty.clone() }))),
        scrut: rt(Term::BoxTy(rty(Type::Nat))),
    };
    assert_eq!(step_term(&t, &gamma), Some(Term::BoxTy(rty(Type::Nat))));
    // letbox (u. box u^·) (box 0) ⇝ box 0
    let t = Term::LetBoxTm {
        motive_level: Level::Zero,
        code_level: Level::Zero,
        ctx: nil_ctx(0),
        ty: rty(Type::Nat),
        motive: rty(Type::Nat),
        body: rt(Term::BoxTm(rt(Term::GlobalTm { var: GlobalVar::index(0), subst: empty }))),
        scrut: rt(Term::BoxTm(rt(Term::Zero))),
    };
    assert_eq!(step_term(&t, &gamma), Some(Term::BoxTm(rt(Term::Zero))));
}

// -------------------------------------------------------------------------
// Recursor β: code of types
// -------------------------------------------------------------------------

#[test]
fn beta_elim_code_ty_nat() {
    // Telescope (g. t_Nat).
    let gamma = nil_ctx(0);
    let delta = nil_ctx(1);
    let mut b = dummy_branches();
    b.ty_nat = rt(ctx_probe(0));
    let b = Rc::new(b);
    let t = elim_ty(&b, Level::Zero, delta.clone(), Term::BoxTy(rty(Type::Nat)));
    assert_eq!(
        step_term(&t, &gamma),
        Some(Term::CtxApp { fun: rt(Term::Zero), ctx: delta })
    );
}

#[test]
fn beta_elim_code_ty_ty() {
    // Telescope (ℓ, g. t_Ty).
    let gamma = nil_ctx(0);
    let delta = nil_ctx(1);
    let mut b = dummy_branches();
    b.ty_ty = rt(chain(vec![Term::TmTy(lv(0)), ctx_probe(0)]));
    let b = Rc::new(b);
    let t = elim_ty(&b, c(5), delta.clone(), Term::BoxTy(rty(Type::Ty(c(4)))));
    assert_eq!(
        step_term(&t, &gamma),
        Some(chain(vec![
            Term::TmTy(c(4)),
            Term::CtxApp { fun: rt(Term::Zero), ctx: delta }
        ]))
    );
}

#[test]
fn beta_elim_code_ty_pi() {
    // Telescope (ℓ, ℓ', g, U_S, U_T, x_S, x_T. t_Π): globals g=2, U_S=1,
    // U_T=0; locals x_S=1, x_T=0 — probe every position plus an ambient
    // Γ-variable to check the id_Γ prefix.
    let gamma = nil_ctx(1);
    let delta = nil_ctx(1);
    let dom = Type::Nat;
    let cod = Type::Ty(Level::Zero); // scoped in (Δ, x)
    let mut b = dummy_branches();
    b.ty_pi = rt(chain(vec![
        v(1),                    // x_S
        v(0),                    // x_T
        v(2),                    // ambient Γ variable under the two locals
        box_gty(1, 2, 0),        // box U_S^{id}
        box_gty(0, 2, 1),        // box U_T^{id} (context (g, x))
        Term::TmTy(lv(1)),       // ℓ
        Term::TmTy(lv(0)),       // ℓ'
    ]));
    let b = Rc::new(b);
    let code = Type::Pi {
        dom_level: c(1),
        cod_level: c(2),
        dom: rty(dom.clone()),
        cod: rty(cod.clone()),
    };
    let t = elim_ty(&b, c(3), delta.clone(), Term::BoxTy(rty(code)));

    let s_dom = elim_ty(&b, c(1), delta.clone(), Term::BoxTy(rty(dom.clone())));
    let s_cod = elim_ty(
        &b,
        c(2),
        extend(&delta, dom.clone(), c(1)),
        Term::BoxTy(rty(cod.clone())),
    );
    let expect = chain(vec![
        s_dom,
        s_cod,
        v(0),
        Term::BoxTy(rty(dom)),
        Term::BoxTy(rty(cod)),
        Term::TmTy(c(1)),
        Term::TmTy(c(2)),
    ]);
    assert_eq!(step_term(&t, &gamma), Some(expect));
}

#[test]
fn beta_elim_code_ty_el() {
    // Telescope (ℓ, g, u_t, x_t. t_El): x_t recurses at the *term* motive
    // with annotation Ty ℓ at level 1+ℓ.
    let gamma = nil_ctx(0);
    let delta = nil_ctx(1);
    let mut b = dummy_branches();
    b.ty_el = rt(chain(vec![
        v(0),              // x_t
        box_gtm(0, 1, 0),  // box u_t^{id}
        Term::TmTy(lv(0)), // ℓ
    ]));
    let b = Rc::new(b);
    let code = Type::El { level: c(3), tm: rt(Term::TmNat) };
    let t = elim_ty(&b, c(3), delta.clone(), Term::BoxTy(rty(code)));

    let s_tm = elim_tm(&b, c(4), delta.clone(), Type::Ty(c(3)), Term::BoxTm(rt(Term::TmNat)));
    let expect = chain(vec![s_tm, Term::BoxTm(rt(Term::TmNat)), Term::TmTy(c(3))]);
    assert_eq!(step_term(&t, &gamma), Some(expect));
}

// -------------------------------------------------------------------------
// Recursor β: code of terms
// -------------------------------------------------------------------------

#[test]
fn beta_elim_code_tm_var() {
    // Telescope (ℓ, g, U_T, u_x. t_x): U_T is the recursor's annotation,
    // u_x the (layer-v) variable itself.
    let gamma = nil_ctx(0);
    let delta = nil_ctx(1);
    let mut b = dummy_branches();
    b.tm_var = rt(chain(vec![
        Term::TmTy(lv(0)), // ℓ (= the recursor's code level)
        box_gty(1, 2, 0),  // box U_T^{id}
        box_gtm(0, 2, 0),  // box u_x^{id} (u_x's context is (g))
    ]));
    let b = Rc::new(b);
    let t = elim_tm(&b, c(3), delta.clone(), Type::Nat, Term::BoxTm(rt(v(0))));

    let expect = chain(vec![
        Term::TmTy(c(3)),
        Term::BoxTy(rty(Type::Nat)),
        Term::BoxTm(rt(v(0))),
    ]);
    assert_eq!(step_term(&t, &gamma), Some(expect));
}

#[test]
fn beta_elim_code_tm_nat_ty_zero() {
    // The three global-only branches (g. t'_Nat), (ℓ, g. t'_Ty), (g. t_ze).
    let gamma = nil_ctx(0);
    let delta = nil_ctx(1);
    let probe_g = |g| rt(ctx_probe(g));
    let expect_g = Some(Term::CtxApp { fun: rt(Term::Zero), ctx: delta.clone() });

    let mut b = dummy_branches();
    b.tm_nat = probe_g(0);
    let b = Rc::new(b);
    let t = elim_tm(&b, c(1), delta.clone(), Type::Ty(Level::Zero), Term::BoxTm(rt(Term::TmNat)));
    assert_eq!(step_term(&t, &gamma), expect_g);

    let mut b = dummy_branches();
    b.tm_ty = rt(chain(vec![Term::TmTy(lv(0)), ctx_probe(0)]));
    let b = Rc::new(b);
    let t = elim_tm(&b, c(5), delta.clone(), Type::Ty(c(5)), Term::BoxTm(rt(Term::TmTy(c(4)))));
    assert_eq!(
        step_term(&t, &gamma),
        Some(chain(vec![
            Term::TmTy(c(4)),
            Term::CtxApp { fun: rt(Term::Zero), ctx: delta.clone() }
        ]))
    );

    let mut b = dummy_branches();
    b.tm_zero = probe_g(0);
    let b = Rc::new(b);
    let t = elim_tm(&b, Level::Zero, delta.clone(), Type::Nat, Term::BoxTm(rt(Term::Zero)));
    assert_eq!(step_term(&t, &gamma), expect_g);
}

#[test]
fn beta_elim_code_tm_pi() {
    // Telescope (ℓ, ℓ', g, u_s, u_t, x_s, x_t. t'_Π): the codomain code is
    // scoped in (Δ, x : El u_s @ ℓ), recursive calls at annotations Ty ℓ /
    // Ty ℓ'.
    let gamma = nil_ctx(0);
    let delta = nil_ctx(1);
    let dom = Term::TmNat;
    let cod = Term::TmTy(Level::Zero);
    let mut b = dummy_branches();
    b.tm_pi = rt(chain(vec![
        v(1),              // x_s
        v(0),              // x_t
        box_gtm(1, 2, 0),  // box u_s^{id}
        box_gtm(0, 2, 1),  // box u_t^{id} (context (g, x))
        Term::TmTy(lv(1)), // ℓ
        Term::TmTy(lv(0)), // ℓ'
    ]));
    let b = Rc::new(b);
    let code = Term::TmPi {
        dom_level: c(1),
        cod_level: c(2),
        dom: rt(dom.clone()),
        cod: rt(cod.clone()),
    };
    let t = elim_tm(&b, c(4), delta.clone(), Type::Ty(c(3)), Term::BoxTm(rt(code)));

    let s_dom = elim_tm(&b, c(2), delta.clone(), Type::Ty(c(1)), Term::BoxTm(rt(dom.clone())));
    let dx = extend(&delta, Type::El { level: c(1), tm: rt(dom.clone()) }, c(1));
    let s_cod = elim_tm(&b, c(3), dx, Type::Ty(c(2)), Term::BoxTm(rt(cod.clone())));
    let expect = chain(vec![
        s_dom,
        s_cod,
        Term::BoxTm(rt(dom)),
        Term::BoxTm(rt(cod)),
        Term::TmTy(c(1)),
        Term::TmTy(c(2)),
    ]);
    assert_eq!(step_term(&t, &gamma), Some(expect));
}

#[test]
fn beta_elim_code_tm_succ() {
    // Telescope (g, u_t, x_t. t_succ).
    let gamma = nil_ctx(0);
    let delta = nil_ctx(1);
    let mut b = dummy_branches();
    b.tm_succ = rt(chain(vec![v(0), box_gtm(0, 1, 0)]));
    let b = Rc::new(b);
    let t = elim_tm(&b, Level::Zero, delta.clone(), Type::Nat, Term::BoxTm(rt(num(1))));

    let s_pred = elim_tm(&b, Level::Zero, delta.clone(), Type::Nat, Term::BoxTm(rt(Term::Zero)));
    let expect = chain(vec![s_pred, Term::BoxTm(rt(Term::Zero))]);
    assert_eq!(step_term(&t, &gamma), Some(expect));
}

#[test]
fn beta_elim_code_tm_elim_nat() {
    // Telescope (ℓ, g, U_M, u_s, u_s', u_t, x_M, x_s, x_s', x_t. t_elimN):
    // globals g=4, U_M=3, u_s=2, u_s'=1, u_t=0; locals x_M=3, x_s=2,
    // x_s'=1, x_t=0. x_M recurses at the *type* motive; the annotation
    // types of x_s / x_s' instantiate the motive at ze / su x.
    let gamma = nil_ctx(0);
    let delta = nil_ctx(1);
    let motive = Type::Ty(Level::Zero); // scoped in (Δ, x : Nat); closed here
    let base = Term::TmNat; // distinct from step/scrut probes
    let step = v(0);
    let scrut = Term::Zero;
    let mut b = dummy_branches();
    b.tm_elim_nat = rt(chain(vec![
        v(3),                       // x_M
        v(2),                       // x_s
        v(1),                       // x_s'
        v(0),                       // x_t
        box_gty(3, 4, 1),           // box U_M^{id} (context (g, x : Nat))
        box_gtm(2, 4, 0),           // box u_s^{id}
        box_gtm(1, 4, 2),           // box u_s'^{id} (context (g, x, y))
        box_gtm(0, 4, 0),           // box u_t^{id}
        Term::TmTy(lv(0)),          // ℓ
    ]));
    let b = Rc::new(b);
    let code = Term::ElimNat {
        level: c(2),
        motive: rty(motive.clone()),
        base: rt(base.clone()),
        step: rt(step.clone()),
        scrut: rt(scrut.clone()),
    };
    let t = elim_tm(&b, c(2), delta.clone(), Type::Ty(Level::Zero), Term::BoxTm(rt(code)));

    let dx_nat = extend(&delta, Type::Nat, Level::Zero);
    let s_motive = elim_ty(&b, c(2), dx_nat.clone(), Term::BoxTy(rty(motive.clone())));
    // motive is closed, so both instantiations of it are itself
    let s_base =
        elim_tm(&b, c(2), delta.clone(), motive.clone(), Term::BoxTm(rt(base.clone())));
    let dxy = extend(&dx_nat, motive.clone(), c(2));
    let s_step = elim_tm(&b, c(2), dxy, motive.clone(), Term::BoxTm(rt(step.clone())));
    let s_scrut =
        elim_tm(&b, Level::Zero, delta.clone(), Type::Nat, Term::BoxTm(rt(scrut.clone())));
    let expect = chain(vec![
        s_motive,
        s_base,
        s_step,
        s_scrut,
        Term::BoxTy(rty(motive)),
        Term::BoxTm(rt(base)),
        Term::BoxTm(rt(step)),
        Term::BoxTm(rt(scrut)),
        Term::TmTy(c(2)),
    ]);
    assert_eq!(step_term(&t, &gamma), Some(expect));
}

#[test]
fn beta_elim_code_tm_elim_nat_open_motive() {
    // The annotation types of x_s / x_s' when the motive actually mentions
    // its Nat variable: M = El^0 x. Then x_s's annotation is M[ze/x] and
    // x_s''s is M[su x/x] scoped in (Δ, x, y).
    let gamma = nil_ctx(0);
    let delta = nil_ctx(0);
    let motive = Type::El { level: Level::Zero, tm: rt(v(0)) };
    let mut b = dummy_branches();
    b.tm_elim_nat = rt(app2(v(2), v(1))); // (x_s, x_s')
    let b = Rc::new(b);
    let code = Term::ElimNat {
        level: Level::Zero,
        motive: rty(motive.clone()),
        base: rt(Term::Zero),
        step: rt(v(0)),
        scrut: rt(Term::Zero),
    };
    let t = elim_tm(&b, Level::Zero, delta.clone(), Type::Nat, Term::BoxTm(rt(code)));

    let ty_base = Type::El { level: Level::Zero, tm: rt(Term::Zero) };
    let s_base = elim_tm(&b, Level::Zero, delta.clone(), ty_base, Term::BoxTm(rt(Term::Zero)));
    let dx_nat = extend(&delta, Type::Nat, Level::Zero);
    let dxy = extend(&dx_nat, motive.clone(), Level::Zero);
    let ty_step = Type::El { level: Level::Zero, tm: rt(Term::Succ(rt(v(1)))) };
    let s_step = elim_tm(&b, Level::Zero, dxy, ty_step, Term::BoxTm(rt(v(0))));
    assert_eq!(step_term(&t, &gamma), Some(app2(s_base, s_step)));
}

#[test]
fn beta_elim_code_tm_lam() {
    // Telescope (ℓ, ℓ', g, U_S, U_T, u_t, x_S, x_t. t_λ): U_T (layer p, no
    // recursive call) comes off the recursor's WHNF Π annotation.
    let gamma = nil_ctx(0);
    let delta = nil_ctx(1);
    let dom = Type::Nat;
    let cod = Type::Ty(Level::Zero); // scoped in (Δ, x)
    let body = v(0);
    let mut b = dummy_branches();
    b.tm_lam = rt(chain(vec![
        v(1),              // x_S
        v(0),              // x_t
        box_gty(2, 3, 0),  // box U_S^{id}
        box_gty(1, 3, 1),  // box U_T^{id} (context (g, x))
        box_gtm(0, 3, 1),  // box u_t^{id} (context (g, x))
        Term::TmTy(lv(1)), // ℓ
        Term::TmTy(lv(0)), // ℓ'
    ]));
    let b = Rc::new(b);
    let code = Term::Lam {
        dom_level: c(1),
        cod_level: c(2),
        dom: rty(dom.clone()),
        body: rt(body.clone()),
    };
    let ann = Type::Pi {
        dom_level: c(1),
        cod_level: c(2),
        dom: rty(dom.clone()),
        cod: rty(cod.clone()),
    };
    let t = elim_tm(&b, c(3), delta.clone(), ann, Term::BoxTm(rt(code)));

    let s_dom = elim_ty(&b, c(1), delta.clone(), Term::BoxTy(rty(dom.clone())));
    let dx = extend(&delta, dom.clone(), c(1));
    let s_body = elim_tm(&b, c(2), dx, cod.clone(), Term::BoxTm(rt(body.clone())));
    let expect = chain(vec![
        s_dom,
        s_body,
        Term::BoxTy(rty(dom)),
        Term::BoxTy(rty(cod)),
        Term::BoxTm(rt(body)),
        Term::TmTy(c(1)),
        Term::TmTy(c(2)),
    ]);
    assert_eq!(step_term(&t, &gamma), Some(expect));
}

#[test]
fn beta_elim_code_tm_app() {
    // Telescope (ℓ, ℓ', g, U_S, U_T, u_t, u_s, x_S, x_T, x_t, x_s. t_app):
    // globals g=4, U_S=3, U_T=2, u_t=1, u_s=0; locals x_S=3, x_T=2, x_t=1,
    // x_s=0. The recursive call on the function is annotated with the Π
    // rebuilt from the application's own annotations.
    let gamma = nil_ctx(0);
    let delta = nil_ctx(1);
    let dom = Type::Nat;
    let cod = Type::Ty(Level::Zero); // scoped in (Δ, x)
    let fun = v(0);
    let arg = Term::Zero;
    let mut b = dummy_branches();
    b.tm_app = rt(chain(vec![
        v(3),              // x_S
        v(2),              // x_T
        v(1),              // x_t
        v(0),              // x_s
        box_gty(3, 4, 0),  // box U_S^{id}
        box_gty(2, 4, 1),  // box U_T^{id} (context (g, x))
        box_gtm(1, 4, 0),  // box u_t^{id}
        box_gtm(0, 4, 0),  // box u_s^{id}
        Term::TmTy(lv(1)), // ℓ
        Term::TmTy(lv(0)), // ℓ'
    ]));
    let b = Rc::new(b);
    let code = Term::App {
        fun: rt(fun.clone()),
        dom_level: c(1),
        cod_level: c(2),
        dom: rty(dom.clone()),
        cod: rty(cod.clone()),
        arg: rt(arg.clone()),
    };
    let t = elim_tm(&b, c(2), delta.clone(), Type::Ty(Level::Zero), Term::BoxTm(rt(code)));

    let s_dom = elim_ty(&b, c(1), delta.clone(), Term::BoxTy(rty(dom.clone())));
    let dx = extend(&delta, dom.clone(), c(1));
    let s_cod = elim_ty(&b, c(2), dx, Term::BoxTy(rty(cod.clone())));
    let pi = Type::Pi {
        dom_level: c(1),
        cod_level: c(2),
        dom: rty(dom.clone()),
        cod: rty(cod.clone()),
    };
    let s_fun = elim_tm(
        &b,
        Level::max(c(1), c(2)),
        delta.clone(),
        pi,
        Term::BoxTm(rt(fun.clone())),
    );
    let s_arg = elim_tm(&b, c(1), delta.clone(), dom.clone(), Term::BoxTm(rt(arg.clone())));
    let expect = chain(vec![
        s_dom,
        s_cod,
        s_fun,
        s_arg,
        Term::BoxTy(rty(dom)),
        Term::BoxTy(rty(cod)),
        Term::BoxTm(rt(fun)),
        Term::BoxTm(rt(arg)),
        Term::TmTy(c(1)),
        Term::TmTy(c(2)),
    ]);
    assert_eq!(step_term(&t, &gamma), Some(expect));
}

// -------------------------------------------------------------------------
// Congruence order and blocking
// -------------------------------------------------------------------------

#[test]
fn elim_code_tm_reduces_type_before_term() {
    let gamma = nil_ctx(0);
    let b = Rc::new(dummy_branches());
    let redex = app2(lam(v(0)), Term::Zero);
    let t = elim_tm(
        &b,
        Level::Zero,
        nil_ctx(0),
        Type::El { level: Level::Zero, tm: rt(Term::TmNat) },
        redex.clone(),
    );
    // First step: the annotation decodes.
    let t1 = step_term(&t, &gamma).expect("type should reduce first");
    assert_eq!(t1, elim_tm(&b, Level::Zero, nil_ctx(0), Type::Nat, redex));
    // Second step: only now the scrutinee.
    let t2 = step_term(&t1, &gamma).expect("scrutinee should reduce second");
    assert_eq!(t2, elim_tm(&b, Level::Zero, nil_ctx(0), Type::Nat, Term::Zero));
}

#[test]
fn recursors_block_on_boxed_global_variables() {
    let gamma = nil_ctx(0);
    let b = Rc::new(dummy_branches());
    let empty = LocalSubst { tail: SubstTail::Empty, terms: vec![] };
    // elim^Typ … (box U^δ): neutral, no step.
    let t = elim_ty(
        &b,
        Level::Zero,
        nil_ctx(0),
        Term::BoxTy(rty(Type::GlobalTy { var: GlobalVar::index(0), subst: empty.clone() })),
    );
    assert_eq!(step_term(&t, &gamma), None);
    assert!(is_neutral_term(&t));
    // elim^Trm … (box u^δ): neutral, no step.
    let t = elim_tm(
        &b,
        Level::Zero,
        nil_ctx(0),
        Type::Nat,
        Term::BoxTm(rt(Term::GlobalTm { var: GlobalVar::index(0), subst: empty.clone() })),
    );
    assert_eq!(step_term(&t, &gamma), None);
    assert!(is_neutral_term(&t));
    // …but with a reducible type annotation the same term is NOT neutral
    // (it steps in the annotation).
    let t = elim_tm(
        &b,
        Level::Zero,
        nil_ctx(0),
        Type::El { level: Level::Zero, tm: rt(Term::TmNat) },
        Term::BoxTm(rt(Term::GlobalTm { var: GlobalVar::index(0), subst: empty })),
    );
    assert!(!is_neutral_term(&t));
    assert!(step_term(&t, &gamma).is_some());
}

#[test]
fn eliminators_block_on_neutral_scrutinees() {
    let gamma = nil_ctx(1);
    let b = Rc::new(dummy_branches());
    // elim_Nat on a variable.
    let t = Term::ElimNat {
        level: Level::Zero,
        motive: rty(Type::Nat),
        base: rt(Term::Zero),
        step: rt(v(0)),
        scrut: rt(v(0)),
    };
    assert_eq!(step_term(&t, &gamma), None);
    assert!(is_neutral_term(&t));
    // app on a variable head.
    let t = app2(v(0), Term::Zero);
    assert_eq!(step_term(&t, &gamma), None);
    assert!(is_neutral_term(&t));
    // recursor on a neutral (non-box) scrutinee.
    let t = elim_ty(&b, Level::Zero, nil_ctx(0), v(0));
    assert_eq!(step_term(&t, &gamma), None);
    assert!(is_neutral_term(&t));
}

// -------------------------------------------------------------------------
// Properties on generated terms
// -------------------------------------------------------------------------

const CASES: u64 = 300;
const BUDGET: u32 = 8;
const FUEL: u32 = 32;
const SIZE_CAP: u64 = 50_000;

#[test]
fn normal_forms_do_not_step() {
    for seed in 0..CASES {
        let mut r = Rng::new(seed ^ 0xb5297a4d3f84d5b5);
        let sc = gen_scope(&mut r);
        let gamma = materialize(&sc, sc.local);
        let t = gen_term(&sc, &mut r, BUDGET);
        if is_whnf_term(&t) {
            law!(seed, step_term(&t, &gamma).is_none(), true);
        }
        let ty = gen_type(&sc, &mut r, BUDGET);
        if is_whnf_type(&ty) {
            law!(seed, step_type(&ty, &gamma).is_none(), true);
        }
    }
}

/// Step, treating a panic as "precondition violated, skip this seed": the
/// generator does not correlate boxed-code scopes with recursor contexts,
/// so untyped generated terms can violate the scoping preconditions that
/// substitution asserts (a type-checked term never does). cargo captures
/// the panic chatter for passing tests. Law assertions stay *outside* the
/// catch so real violations still fail.
fn try_step(t: &Term, gamma: &LocalCtx) -> Result<Option<Term>, ()> {
    std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| step_term(t, gamma)))
        .map_err(|_| ())
}

#[test]
fn reduction_preserves_scoping() {
    // Every reduct must still be well-scoped: applying the identity local
    // substitution of Γ (which panics on out-of-range local variables and
    // is the identity on well-scoped terms) and the identity universe
    // substitution must both be no-ops. Iteration is capped by fuel *and*
    // node count — untyped terms may grow without bound.
    for seed in 0..CASES {
        let mut r = Rng::new(seed ^ 0x94d049bb133111eb);
        let sc = gen_scope(&mut r);
        let gamma = materialize(&sc, sc.local);
        let id_local = LocalSubst::id(&gamma);
        let id_univ: Vec<_> = (0..sc.univ).map(|i| Level::Var(UnivVar(i))).collect();
        let mut cur = (*gen_term(&sc, &mut r, BUDGET)).clone();
        for _ in 0..FUEL {
            match try_step(&cur, &gamma) {
                Err(()) | Ok(None) => break,
                Ok(Some(next)) => {
                    law!(seed, next.apply_local(&id_local), next);
                    law!(seed, next.apply_univ(&id_univ), next);
                    cur = next;
                }
            }
            if count_term(&cur) > SIZE_CAP {
                break;
            }
        }
    }
}

#[test]
fn classified_normal_forms_are_stable_under_more_steps() {
    // Once reduction stops and the result is a classified normal form, the
    // classification and step agree: stepping again yields nothing.
    for seed in 0..CASES {
        let mut r = Rng::new(seed ^ 0xbf58476d1ce4e5b9);
        let sc = gen_scope(&mut r);
        let gamma = materialize(&sc, sc.local);
        let mut cur = (*gen_term(&sc, &mut r, BUDGET)).clone();
        let mut finished = false;
        for _ in 0..FUEL {
            match try_step(&cur, &gamma) {
                Err(()) => break,
                Ok(None) => {
                    finished = true;
                    break;
                }
                Ok(Some(next)) => cur = next,
            }
            if count_term(&cur) > SIZE_CAP {
                break;
            }
        }
        if finished && is_whnf_term(&cur) {
            law!(seed, step_term(&cur, &gamma).is_none(), true);
        }
    }
}

// -------------------------------------------------------------------------
// Identity type (extension beyond ch. 04; kernel-v1-extensions)
// -------------------------------------------------------------------------

#[test]
fn el_decodes_tm_id() {
    // El^0 (Id^0(«Nat»; 0; 1)) ⇝ Id^0(El^0 «Nat»; 0; 1).
    let gamma = nil_ctx(0);
    let t = Type::El {
        level: Level::Zero,
        tm: rt(Term::TmId {
            level: Level::Zero,
            ty: rt(Term::TmNat),
            lhs: rt(Term::Zero),
            rhs: rt(num(1)),
        }),
    };
    let expect = Type::Id {
        level: Level::Zero,
        ty: rty(Type::El { level: Level::Zero, tm: rt(Term::TmNat) }),
        lhs: rt(Term::Zero),
        rhs: rt(num(1)),
    };
    assert_eq!(step_type(&t, &gamma), Some(expect.clone()));
    assert!(is_whnf_type(&expect));
}

#[test]
fn beta_j_refl_and_congruence() {
    let gamma = nil_ctx(1);
    let refl0 = Term::Refl { level: Level::Zero, ty: rty(Type::Nat), tm: rt(Term::Zero) };
    let j = |proof: Term| Term::J {
        ty_level: Level::Zero,
        motive_level: Level::Zero,
        ty: rty(Type::Nat),
        lhs: rt(Term::Zero),
        motive: rty(Type::Nat),
        case: rt(num(2)),
        rhs: rt(Term::Zero),
        proof: rt(proof),
    };
    // J … refl ⇝ c.
    assert_eq!(step_term(&j(refl0.clone()), &gamma), Some(num(2)));
    // Congruence reduces the proof first.
    let letbox_refl = Term::LetBoxTm {
        motive_level: Level::Zero,
        code_level: Level::Zero,
        ctx: nil_ctx(0),
        ty: rty(Type::Nat),
        motive: rty(Type::Nat),
        body: rt(refl0.clone().shift_global(1)),
        scrut: rt(Term::BoxTm(rt(Term::Zero))),
    };
    let stepped = step_term(&j(letbox_refl), &gamma).unwrap();
    assert_eq!(step_term(&stepped, &gamma), Some(num(2)));
    // Blocked on a neutral proof: no rule, classified neutral.
    let blocked = j(v(0));
    assert_eq!(step_term(&blocked, &gamma), None);
    assert!(is_neutral_term(&blocked));
    // refl and the encoding are WHNFs.
    assert!(is_whnf_term(&refl0));
    assert!(is_whnf_term(&Term::TmId {
        level: Level::Zero,
        ty: rt(Term::TmNat),
        lhs: rt(Term::Zero),
        rhs: rt(Term::Zero),
    }));
}

#[test]
fn beta_elim_code_ty_id() {
    // Telescope (ℓ, g, U_S, u_t, u_u, x_S, x_t, x_u. t_Id):
    // globals g=3, U_S=2, u_t=1, u_u=0; locals x_S=2, x_t=1, x_u=0.
    let gamma = nil_ctx(0);
    let delta = nil_ctx(1);
    let mut b = dummy_branches();
    b.ty_id = rt(chain(vec![
        v(2),             // x_S
        v(1),             // x_t
        v(0),             // x_u
        box_gty(2, 3, 0), // box U_S^{id}
        box_gtm(1, 3, 0), // box u_t^{id}
        box_gtm(0, 3, 0), // box u_u^{id}
        Term::TmTy(lv(0)), // ℓ
    ]));
    let b = Rc::new(b);
    let code = Type::Id {
        level: c(2),
        ty: rty(Type::Nat),
        lhs: rt(Term::Zero),
        rhs: rt(num(1)),
    };
    let t = elim_ty(&b, c(2), delta.clone(), Term::BoxTy(rty(code)));

    let s_ty = elim_ty(&b, c(2), delta.clone(), Term::BoxTy(rty(Type::Nat)));
    let s_lhs = elim_tm(&b, c(2), delta.clone(), Type::Nat, Term::BoxTm(rt(Term::Zero)));
    let s_rhs = elim_tm(&b, c(2), delta.clone(), Type::Nat, Term::BoxTm(rt(num(1))));
    let expect = chain(vec![
        s_ty,
        s_lhs,
        s_rhs,
        Term::BoxTy(rty(Type::Nat)),
        Term::BoxTm(rt(Term::Zero)),
        Term::BoxTm(rt(num(1))),
        Term::TmTy(c(2)),
    ]);
    assert_eq!(step_term(&t, &gamma), Some(expect));
}

#[test]
fn beta_elim_code_tm_refl() {
    // Telescope (ℓ, g, U_S, u_t, x_S, x_t. t_refl): globals g=2, U_S=1,
    // u_t=0; locals x_S=1, x_t=0.
    let gamma = nil_ctx(0);
    let delta = nil_ctx(1);
    let mut b = dummy_branches();
    b.tm_refl = rt(chain(vec![
        v(1),             // x_S
        v(0),             // x_t
        box_gty(1, 2, 0), // box U_S^{id}
        box_gtm(0, 2, 0), // box u_t^{id}
        Term::TmTy(lv(0)), // ℓ
    ]));
    let b = Rc::new(b);
    let code = Term::Refl { level: c(3), ty: rty(Type::Nat), tm: rt(num(1)) };
    let ann = Type::Id {
        level: c(3),
        ty: rty(Type::Nat),
        lhs: rt(num(1)),
        rhs: rt(num(1)),
    };
    let t = elim_tm(&b, c(3), delta.clone(), ann, Term::BoxTm(rt(code)));

    let s_ty = elim_ty(&b, c(3), delta.clone(), Term::BoxTy(rty(Type::Nat)));
    let s_tm = elim_tm(&b, c(3), delta.clone(), Type::Nat, Term::BoxTm(rt(num(1))));
    let expect = chain(vec![
        s_ty,
        s_tm,
        Term::BoxTy(rty(Type::Nat)),
        Term::BoxTm(rt(num(1))),
        Term::TmTy(c(3)),
    ]);
    assert_eq!(step_term(&t, &gamma), Some(expect));
}

#[test]
fn beta_elim_code_tm_j() {
    // Telescope (ℓ, ℓ', g, U_S, u_a, U_M, u_c, u_r, u_e, x_S, x_a, x_M,
    // x_c, x_r, x_e. t_J): globals g=6, U_S=5, u_a=4, U_M=3, u_c=2, u_r=1,
    // u_e=0; locals x_S=5, x_a=4, x_M=3, x_c=2, x_r=1, x_e=0. The motive
    // code is scoped in (Δ, y, p); the case's annotation instantiates it at
    // (a, refl).
    let gamma = nil_ctx(0);
    let delta = nil_ctx(1);
    let motive = Type::Ty(Level::Zero); // scoped in (Δ, y, p); closed here
    let mut b = dummy_branches();
    b.tm_j = rt(chain(vec![
        v(5),              // x_S
        v(4),              // x_a
        v(3),              // x_M
        v(2),              // x_c
        v(1),              // x_r
        v(0),              // x_e
        box_gty(5, 6, 0),  // box U_S^{id}
        box_gtm(4, 6, 0),  // box u_a^{id}
        box_gty(3, 6, 2),  // box U_M^{id} (context (g, y, p))
        box_gtm(2, 6, 0),  // box u_c^{id}
        box_gtm(1, 6, 0),  // box u_r^{id}
        box_gtm(0, 6, 0),  // box u_e^{id}
        Term::TmTy(lv(1)), // ℓ
        Term::TmTy(lv(0)), // ℓ'
    ]));
    let b = Rc::new(b);
    let code = Term::J {
        ty_level: c(1),
        motive_level: c(2),
        ty: rty(Type::Nat),
        lhs: rt(Term::Zero),
        motive: rty(motive.clone()),
        case: rt(Term::TmNat),
        rhs: rt(num(1)),
        proof: rt(num(2)),
    };
    let t = elim_tm(&b, c(2), delta.clone(), Type::Ty(Level::Zero), Term::BoxTm(rt(code)));

    let s_ty = elim_ty(&b, c(1), delta.clone(), Term::BoxTy(rty(Type::Nat)));
    let s_a = elim_tm(&b, c(1), delta.clone(), Type::Nat, Term::BoxTm(rt(Term::Zero)));
    let dy = extend(&delta, Type::Nat, c(1));
    let p_ty = Type::Id {
        level: c(1),
        ty: rty(Type::Nat),
        lhs: rt(Term::Zero),
        rhs: rt(v(0)),
    };
    let dyp = extend(&dy, p_ty, c(1));
    let s_motive = elim_ty(&b, c(2), dyp, Term::BoxTy(rty(motive.clone())));
    // The motive is closed, so its instantiation at (a, refl) is itself.
    let s_case =
        elim_tm(&b, c(2), delta.clone(), motive.clone(), Term::BoxTm(rt(Term::TmNat)));
    let s_rhs = elim_tm(&b, c(1), delta.clone(), Type::Nat, Term::BoxTm(rt(num(1))));
    let id_a_r = Type::Id {
        level: c(1),
        ty: rty(Type::Nat),
        lhs: rt(Term::Zero),
        rhs: rt(num(1)),
    };
    let s_proof = elim_tm(&b, c(1), delta.clone(), id_a_r, Term::BoxTm(rt(num(2))));
    let expect = chain(vec![
        s_ty,
        s_a,
        s_motive,
        s_case,
        s_rhs,
        s_proof,
        Term::BoxTy(rty(Type::Nat)),
        Term::BoxTm(rt(Term::Zero)),
        Term::BoxTy(rty(motive)),
        Term::BoxTm(rt(Term::TmNat)),
        Term::BoxTm(rt(num(1))),
        Term::BoxTm(rt(num(2))),
        Term::TmTy(c(1)),
        Term::TmTy(c(2)),
    ]);
    assert_eq!(step_term(&t, &gamma), Some(expect));
}

// -------------------------------------------------------------------------
// Dependent pairs (extension beyond ch. 04; kernel-v1-extensions)
// -------------------------------------------------------------------------

#[test]
fn el_decodes_tm_sigma() {
    // El^{1⊔2} (Σ^{1,2}(«Ty 0»; «Nat»)) ⇝ Σ^{1,2}(El^1 «Ty 0»; El^2 «Nat»).
    let gamma = nil_ctx(0);
    let t = Type::El {
        level: Level::max(c(1), c(2)),
        tm: rt(Term::TmSigma {
            fst_level: c(1),
            snd_level: c(2),
            fst: rt(Term::TmTy(c(0))),
            snd: rt(Term::TmNat),
        }),
    };
    let expect = Type::Sigma {
        fst_level: c(1),
        snd_level: c(2),
        fst: rty(Type::El { level: c(1), tm: rt(Term::TmTy(c(0))) }),
        snd: rty(Type::El { level: c(2), tm: rt(Term::TmNat) }),
    };
    assert_eq!(step_type(&t, &gamma), Some(expect.clone()));
    assert!(is_whnf_type(&expect));
}

#[test]
fn beta_fst_snd_and_congruence() {
    let gamma = nil_ctx(1);
    let pair = |a: Term, b: Term| Term::Pair {
        fst_level: Level::Zero,
        snd_level: Level::Zero,
        fst_ty: rty(Type::Nat),
        snd_ty: rty(Type::Nat),
        fst: rt(a),
        snd: rt(b),
    };
    let fst = |p: Term| Term::Fst {
        fst_level: Level::Zero,
        snd_level: Level::Zero,
        fst_ty: rty(Type::Nat),
        snd_ty: rty(Type::Nat),
        pair: rt(p),
    };
    let snd = |p: Term| Term::Snd {
        fst_level: Level::Zero,
        snd_level: Level::Zero,
        fst_ty: rty(Type::Nat),
        snd_ty: rty(Type::Nat),
        pair: rt(p),
    };
    // fst (pair 1 2) ⇝ 1, snd (pair 1 2) ⇝ 2.
    assert_eq!(step_term(&fst(pair(num(1), num(2))), &gamma), Some(num(1)));
    assert_eq!(step_term(&snd(pair(num(1), num(2))), &gamma), Some(num(2)));
    // Congruence reduces the pair first (β-redex inside).
    let redex = app2(lam(pair(num(1), num(2))), Term::Zero);
    let stepped = step_term(&fst(redex), &gamma).unwrap();
    assert_eq!(step_term(&stepped, &gamma), Some(num(1)));
    // Blocked on a neutral pair: classified neutral, no step.
    let blocked = fst(v(0));
    assert_eq!(step_term(&blocked, &gamma), None);
    assert!(is_neutral_term(&blocked));
    assert!(is_neutral_term(&snd(v(0))));
    // pair and the encoding are WHNFs.
    assert!(is_whnf_term(&pair(num(1), num(2))));
    assert!(is_whnf_term(&Term::TmSigma {
        fst_level: Level::Zero,
        snd_level: Level::Zero,
        fst: rt(Term::TmNat),
        snd: rt(Term::TmNat),
    }));
}

#[test]
fn beta_elim_code_ty_sigma() {
    // Telescope (ℓ, ℓ', g, U_S, U_T, x_S, x_T. t_Σ): globals g=2, U_S=1,
    // U_T=0; locals x_S=1, x_T=0. Univs ℓ=1, ℓ'=0.
    let gamma = nil_ctx(0);
    let delta = nil_ctx(1);
    let mut b = dummy_branches();
    b.ty_sigma = rt(chain(vec![
        v(1),              // x_S
        v(0),              // x_T
        box_gty(1, 2, 0),  // box U_S^{id}
        box_gty(0, 2, 1),  // box U_T^{id} (context (g, x))
        Term::TmTy(lv(1)), // ℓ
        Term::TmTy(lv(0)), // ℓ'
    ]));
    let b = Rc::new(b);
    let code = Type::Sigma {
        fst_level: c(1),
        snd_level: c(2),
        fst: rty(Type::Nat),
        snd: rty(Type::Nat),
    };
    let t = elim_ty(&b, Level::max(c(1), c(2)), delta.clone(), Term::BoxTy(rty(code)));

    let s_fst = elim_ty(&b, c(1), delta.clone(), Term::BoxTy(rty(Type::Nat)));
    let dx = extend(&delta, Type::Nat, c(1));
    let s_snd = elim_ty(&b, c(2), dx, Term::BoxTy(rty(Type::Nat)));
    let expect = chain(vec![
        s_fst,
        s_snd,
        Term::BoxTy(rty(Type::Nat)),
        Term::BoxTy(rty(Type::Nat)),
        Term::TmTy(c(1)),
        Term::TmTy(c(2)),
    ]);
    assert_eq!(step_term(&t, &gamma), Some(expect));
}

#[test]
fn beta_elim_code_tm_pair() {
    // Telescope (ℓ, ℓ', g, U_S, U_T, u_a, u_b, x_S, x_T, x_a, x_b. t_pair):
    // globals g=4, U_S=3, U_T=2, u_a=1, u_b=0; locals x_S=3, x_T=2, x_a=1,
    // x_b=0. Univs ℓ=1, ℓ'=0.
    let gamma = nil_ctx(0);
    let delta = nil_ctx(1);
    let mut b = dummy_branches();
    b.tm_pair = rt(chain(vec![
        v(3),              // x_S
        v(2),              // x_T
        v(1),              // x_a
        v(0),              // x_b
        box_gty(3, 4, 0),  // box U_S^{id}
        box_gty(2, 4, 1),  // box U_T^{id} (context (g, x))
        box_gtm(1, 4, 0),  // box u_a^{id}
        box_gtm(0, 4, 0),  // box u_b^{id}
        Term::TmTy(lv(1)), // ℓ
        Term::TmTy(lv(0)), // ℓ'
    ]));
    let b = Rc::new(b);
    let code = Term::Pair {
        fst_level: c(1),
        snd_level: c(2),
        fst_ty: rty(Type::Nat),
        snd_ty: rty(Type::Nat),
        fst: rt(Term::Zero),
        snd: rt(num(1)),
    };
    let t = elim_tm(
        &b,
        Level::max(c(1), c(2)),
        delta.clone(),
        Type::Sigma {
            fst_level: c(1),
            snd_level: c(2),
            fst: rty(Type::Nat),
            snd: rty(Type::Nat),
        },
        Term::BoxTm(rt(code)),
    );

    let s_fst_ty = elim_ty(&b, c(1), delta.clone(), Term::BoxTy(rty(Type::Nat)));
    let dx = extend(&delta, Type::Nat, c(1));
    let s_snd_ty = elim_ty(&b, c(2), dx, Term::BoxTy(rty(Type::Nat)));
    let s_a = elim_tm(&b, c(1), delta.clone(), Type::Nat, Term::BoxTm(rt(Term::Zero)));
    // snd_ty[fst/x] = Nat (closed), so b : Nat.
    let s_b = elim_tm(&b, c(2), delta.clone(), Type::Nat, Term::BoxTm(rt(num(1))));
    let expect = chain(vec![
        s_fst_ty,
        s_snd_ty,
        s_a,
        s_b,
        Term::BoxTy(rty(Type::Nat)),
        Term::BoxTy(rty(Type::Nat)),
        Term::BoxTm(rt(Term::Zero)),
        Term::BoxTm(rt(num(1))),
        Term::TmTy(c(1)),
        Term::TmTy(c(2)),
    ]);
    assert_eq!(step_term(&t, &gamma), Some(expect));
}

#[test]
fn beta_elim_code_tm_fst_and_snd() {
    // Telescope (ℓ, ℓ', g, U_S, U_T, u_p, x_S, x_T, x_p. t_fst/t_snd):
    // globals g=3, U_S=2, U_T=1, u_p=0; locals x_S=2, x_T=1, x_p=0.
    let gamma = nil_ctx(0);
    let delta = nil_ctx(1);
    let probe = |field: &mut Rc<Term>| {
        *field = rt(chain(vec![
            v(2),              // x_S
            v(1),              // x_T
            v(0),              // x_p
            box_gty(2, 3, 0),  // box U_S^{id}
            box_gty(1, 3, 1),  // box U_T^{id} (context (g, x))
            box_gtm(0, 3, 0),  // box u_p^{id}
            Term::TmTy(lv(1)), // ℓ
            Term::TmTy(lv(0)), // ℓ'
        ]));
    };
    let sigma = Type::Sigma {
        fst_level: c(1),
        snd_level: c(2),
        fst: rty(Type::Nat),
        snd: rty(Type::Nat),
    };
    let s_fst_ty = |b: &Rc<Branches>| elim_ty(b, c(1), delta.clone(), Term::BoxTy(rty(Type::Nat)));
    let s_snd_ty = |b: &Rc<Branches>| {
        elim_ty(b, c(2), extend(&delta, Type::Nat, c(1)), Term::BoxTy(rty(Type::Nat)))
    };
    let s_pair = |b: &Rc<Branches>| {
        elim_tm(b, Level::max(c(1), c(2)), delta.clone(), sigma.clone(), Term::BoxTm(rt(num(3))))
    };
    let tail = |b: &Rc<Branches>| {
        vec![
            s_fst_ty(b),
            s_snd_ty(b),
            s_pair(b),
            Term::BoxTy(rty(Type::Nat)),
            Term::BoxTy(rty(Type::Nat)),
            Term::BoxTm(rt(num(3))),
            Term::TmTy(c(1)),
            Term::TmTy(c(2)),
        ]
    };

    // fst.
    let mut bf = dummy_branches();
    probe(&mut bf.tm_fst);
    let bf = Rc::new(bf);
    let code = Term::Fst {
        fst_level: c(1),
        snd_level: c(2),
        fst_ty: rty(Type::Nat),
        snd_ty: rty(Type::Nat),
        pair: rt(num(3)),
    };
    let t = elim_tm(&bf, c(1), delta.clone(), Type::Nat, Term::BoxTm(rt(code)));
    assert_eq!(step_term(&t, &gamma), Some(chain(tail(&bf))));

    // snd (result type U_T[fst/x] = Nat, closed).
    let mut bs = dummy_branches();
    probe(&mut bs.tm_snd);
    let bs = Rc::new(bs);
    let code = Term::Snd {
        fst_level: c(1),
        snd_level: c(2),
        fst_ty: rty(Type::Nat),
        snd_ty: rty(Type::Nat),
        pair: rt(num(3)),
    };
    let t = elim_tm(&bs, c(2), delta.clone(), Type::Nat, Term::BoxTm(rt(code)));
    assert_eq!(step_term(&t, &gamma), Some(chain(tail(&bs))));
}

// -------------------------------------------------------------------------
// Unit and Empty (extension beyond ch. 04; kernel-v1-extensions)
// -------------------------------------------------------------------------

#[test]
fn el_decodes_tm_unit_and_empty() {
    // El^0 «Unit» ⇝ Unit, El^0 «Empty» ⇝ Empty.
    let gamma = nil_ctx(0);
    assert_eq!(
        step_type(&Type::El { level: c(0), tm: rt(Term::TmUnit { level: Level::Zero }) }, &gamma),
        Some(Type::Unit { level: Level::Zero })
    );
    assert_eq!(
        step_type(&Type::El { level: c(0), tm: rt(Term::TmEmpty { level: Level::Zero }) }, &gamma),
        Some(Type::Empty { level: Level::Zero })
    );
    assert!(is_whnf_type(&Type::Unit { level: Level::Zero }) && is_whnf_type(&Type::Empty { level: Level::Zero }));
    assert!(is_whnf_term(&Term::Triv { level: Level::Zero }));
    assert!(is_whnf_term(&Term::TmUnit { level: Level::Zero }) && is_whnf_term(&Term::TmEmpty { level: Level::Zero }));
}

#[test]
fn elim_empty_is_neutral_and_reduces_scrutinee() {
    let gamma = nil_ctx(1);
    // elim_Empty has no β rule: stuck (and neutral) on a neutral scrutinee.
    let neutral = Term::ElimEmpty { level: Level::Zero,
            scrut_level: Level::Zero, motive: rty(Type::Nat), scrut: rt(v(0)) };
    assert_eq!(step_term(&neutral, &gamma), None);
    assert!(is_neutral_term(&neutral));
    // Congruence: a reducible scrutinee steps (untyped reduction).
    let redex = Term::ElimEmpty {
        level: Level::Zero,
            scrut_level: Level::Zero,
        motive: rty(Type::Nat),
        scrut: rt(app2(lam(v(0)), Term::Zero)),
    };
    assert_eq!(
        step_term(&redex, &gamma),
        Some(Term::ElimEmpty { level: Level::Zero,
            scrut_level: Level::Zero, motive: rty(Type::Nat), scrut: rt(Term::Zero) })
    );
}

#[test]
fn beta_elim_code_unit_empty_nullary_branches() {
    // ty_unit/ty_empty/tm_unit/tm_empty/tm_triv all have the single-`g`
    // telescope: firing substitutes only Δ, so a closed marker body passes
    // through unchanged. Distinct markers confirm the dispatch.
    let gamma = nil_ctx(0);
    let delta = nil_ctx(1);
    let mut b = dummy_branches();
    b.ty_unit = rt(Term::BoxTy(rty(Type::Ty(c(0)))));
    b.ty_empty = rt(Term::BoxTy(rty(Type::Ty(c(1)))));
    b.tm_unit = rt(Term::BoxTm(rt(num(1))));
    b.tm_empty = rt(Term::BoxTm(rt(num(2))));
    b.tm_triv = rt(Term::BoxTm(rt(num(3))));
    let b = Rc::new(b);
    assert_eq!(
        step_term(&elim_ty(&b, c(0), delta.clone(), Term::BoxTy(rty(Type::Unit { level: Level::Zero }))), &gamma),
        Some(Term::BoxTy(rty(Type::Ty(c(0)))))
    );
    assert_eq!(
        step_term(&elim_ty(&b, c(0), delta.clone(), Term::BoxTy(rty(Type::Empty { level: Level::Zero }))), &gamma),
        Some(Term::BoxTy(rty(Type::Ty(c(1)))))
    );
    assert_eq!(
        step_term(
            &elim_tm(&b, c(1), delta.clone(), Type::Ty(c(0)), Term::BoxTm(rt(Term::TmUnit { level: Level::Zero }))),
            &gamma
        ),
        Some(Term::BoxTm(rt(num(1))))
    );
    assert_eq!(
        step_term(
            &elim_tm(&b, c(1), delta.clone(), Type::Ty(c(0)), Term::BoxTm(rt(Term::TmEmpty { level: Level::Zero }))),
            &gamma
        ),
        Some(Term::BoxTm(rt(num(2))))
    );
    assert_eq!(
        step_term(
            &elim_tm(&b, Level::Zero, delta.clone(), Type::Unit { level: Level::Zero }, Term::BoxTm(rt(Term::Triv { level: Level::Zero }))),
            &gamma
        ),
        Some(Term::BoxTm(rt(num(3))))
    );
}

#[test]
fn beta_elim_code_tm_elim_empty() {
    // Telescope (ℓ, ℓ', g, U_M, u_t, x_M, x_t. t_elimE): universes ℓ = lv(1)
    // (the motive's) and ℓ' = lv(0) (the scrutinee's `Empty^{ℓ'}`); globals
    // g=2, U_M=1, u_t=0; locals x_M=1, x_t=0. `x_M` recurses at the *type*
    // motive, `x_t` at the term motive.
    //
    // The two levels are deliberately **distinct** here (2 and 1): that is the
    // degree of freedom level-indexing `Empty` adds
    // (docs/kernel/unit-empty-level-indexing.md §3), and firing them in the wrong
    // order — `fire`'s `phi` is innermost-first — swaps them silently.
    let gamma = nil_ctx(0);
    let delta = nil_ctx(1);
    let motive = Type::Ty(Level::Zero); // scoped in (Δ, x : Empty^{ℓ'})
    let inner_scrut = Term::TmNat; // the u_t payload probe
    let mut b = dummy_branches();
    b.tm_elim_empty = rt(chain(vec![
        v(1),              // x_M
        v(0),              // x_t
        box_gty(1, 2, 1),  // box U_M^{id} (context (g, x : Empty^{ℓ'}))
        box_gtm(0, 2, 0),  // box u_t^{id}
        Term::TmTy(lv(1)), // ℓ  — the motive's level
        Term::TmTy(lv(0)), // ℓ' — the scrutinee's level
    ]));
    let b = Rc::new(b);
    let code = Term::ElimEmpty {
        level: c(2),
        scrut_level: c(1),
        motive: rty(motive.clone()),
        scrut: rt(inner_scrut.clone()),
    };
    let t = elim_tm(&b, c(2), delta.clone(), motive.clone(), Term::BoxTm(rt(code)));

    let empty1 = Type::Empty { level: c(1) };
    let dx_empty = extend(&delta, empty1.clone(), c(1));
    let s_motive = elim_ty(&b, c(2), dx_empty, Term::BoxTy(rty(motive.clone())));
    let s_scrut = elim_tm(&b, c(1), delta.clone(), empty1, Term::BoxTm(rt(inner_scrut.clone())));
    let expect = chain(vec![
        s_motive,
        s_scrut,
        Term::BoxTy(rty(motive)),
        Term::BoxTm(rt(inner_scrut)),
        Term::TmTy(c(2)),
        Term::TmTy(c(1)),
    ]);
    assert_eq!(step_term(&t, &gamma), Some(expect));
}

// -------------------------------------------------------------------------
// Binary sums (extension beyond ch. 04; kernel-v1-extensions)
// -------------------------------------------------------------------------

#[test]
fn el_decodes_tm_sum() {
    // El^{1⊔2} («Ty 0» +^{1,2} «Nat») ⇝ El^1 «Ty 0» +^{1,2} El^2 «Nat».
    let gamma = nil_ctx(0);
    let t = Type::El {
        level: Level::max(c(1), c(2)),
        tm: rt(Term::TmSum {
            lhs_level: c(1),
            rhs_level: c(2),
            lhs: rt(Term::TmTy(c(0))),
            rhs: rt(Term::TmNat),
        }),
    };
    let expect = Type::Sum {
        lhs_level: c(1),
        rhs_level: c(2),
        lhs: rty(Type::El { level: c(1), tm: rt(Term::TmTy(c(0))) }),
        rhs: rty(Type::El { level: c(2), tm: rt(Term::TmNat) }),
    };
    assert_eq!(step_type(&t, &gamma), Some(expect.clone()));
    assert!(is_whnf_type(&expect));
}

#[test]
fn beta_case_and_congruence() {
    let gamma = nil_ctx(1);
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
    // case (z. Nat; x. S x; y. y; scrut) — left injects successor, right is
    // the identity on its value.
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
    // case (inl 1) ⇝ S 1 = 2; case (inr 1) ⇝ 1.
    assert_eq!(step_term(&case(inl(num(1))), &gamma), Some(num(2)));
    assert_eq!(step_term(&case(inr(num(1))), &gamma), Some(num(1)));
    // Congruence reduces a redex scrutinee first.
    let redex = app2(lam(inl(num(1))), Term::Zero);
    let stepped = step_term(&case(redex), &gamma).unwrap();
    assert_eq!(step_term(&stepped, &gamma), Some(num(2)));
    // Blocked on a neutral scrutinee: neutral, no step.
    let blocked = case(v(0));
    assert_eq!(step_term(&blocked, &gamma), None);
    assert!(is_neutral_term(&blocked));
    // inl/inr and the encoding are WHNFs.
    assert!(is_whnf_term(&inl(num(1))) && is_whnf_term(&inr(num(1))));
    assert!(is_whnf_term(&Term::TmSum {
        lhs_level: Level::Zero,
        rhs_level: Level::Zero,
        lhs: rt(Term::TmNat),
        rhs: rt(Term::TmNat),
    }));
}

#[test]
fn beta_elim_code_ty_sum() {
    // Telescope (ℓ, ℓ', g, U_A, U_B, x_A, x_B. t_+): globals g=2, U_A=1,
    // U_B=0; locals x_A=1, x_B=0. Both summands live in g (non-dependent).
    let gamma = nil_ctx(0);
    let delta = nil_ctx(1);
    let mut b = dummy_branches();
    b.ty_sum = rt(chain(vec![
        v(1),              // x_A
        v(0),              // x_B
        box_gty(1, 2, 0),  // box U_A^{id}
        box_gty(0, 2, 0),  // box U_B^{id} (context g — not extended)
        Term::TmTy(lv(1)), // ℓ
        Term::TmTy(lv(0)), // ℓ'
    ]));
    let b = Rc::new(b);
    let code = Type::Sum {
        lhs_level: c(1),
        rhs_level: c(2),
        lhs: rty(Type::Nat),
        rhs: rty(Type::Nat),
    };
    let t = elim_ty(&b, Level::max(c(1), c(2)), delta.clone(), Term::BoxTy(rty(code)));

    let s_lhs = elim_ty(&b, c(1), delta.clone(), Term::BoxTy(rty(Type::Nat)));
    let s_rhs = elim_ty(&b, c(2), delta.clone(), Term::BoxTy(rty(Type::Nat)));
    let expect = chain(vec![
        s_lhs,
        s_rhs,
        Term::BoxTy(rty(Type::Nat)),
        Term::BoxTy(rty(Type::Nat)),
        Term::TmTy(c(1)),
        Term::TmTy(c(2)),
    ]);
    assert_eq!(step_term(&t, &gamma), Some(expect));
}

#[test]
fn beta_elim_code_tm_sum() {
    // Telescope (ℓ, ℓ', g, u_a, u_b, x_a, x_b. t'_+): globals g=2, u_a=1,
    // u_b=0; locals x_a=1, x_b=0. The encoding; both encodings live in g.
    let gamma = nil_ctx(0);
    let delta = nil_ctx(1);
    let mut b = dummy_branches();
    b.tm_sum = rt(chain(vec![
        v(1),              // x_a
        v(0),              // x_b
        box_gtm(1, 2, 0),  // box u_a^{id}
        box_gtm(0, 2, 0),  // box u_b^{id}
        Term::TmTy(lv(1)), // ℓ
        Term::TmTy(lv(0)), // ℓ'
    ]));
    let b = Rc::new(b);
    let lmax = Level::max(c(1), Level::Zero);
    let code = Term::TmSum {
        lhs_level: c(1),
        rhs_level: Level::Zero,
        lhs: rt(Term::TmTy(c(0))), // : Ty 1
        rhs: rt(Term::TmNat),      // : Ty 0
    };
    let t = elim_tm(&b, Level::succ(lmax.clone()), delta.clone(), Type::Ty(lmax), Term::BoxTm(rt(code)));

    let s_lhs = elim_tm(
        &b,
        Level::succ(c(1)),
        delta.clone(),
        Type::Ty(c(1)),
        Term::BoxTm(rt(Term::TmTy(c(0)))),
    );
    let s_rhs = elim_tm(
        &b,
        Level::succ(Level::Zero),
        delta.clone(),
        Type::Ty(Level::Zero),
        Term::BoxTm(rt(Term::TmNat)),
    );
    let expect = chain(vec![
        s_lhs,
        s_rhs,
        Term::BoxTm(rt(Term::TmTy(c(0)))),
        Term::BoxTm(rt(Term::TmNat)),
        Term::TmTy(c(1)),
        Term::TmTy(Level::Zero),
    ]);
    assert_eq!(step_term(&t, &gamma), Some(expect));
}

#[test]
fn beta_elim_code_tm_inl_and_inr() {
    // Telescope (ℓ, ℓ', g, U_A, U_B, u_v, x_A, x_B, x_v. t_inl/t_inr):
    // globals g=3, U_A=2, U_B=1, u_v=0; locals x_A=2, x_B=1, x_v=0.
    let gamma = nil_ctx(0);
    let delta = nil_ctx(1);
    let probe = |field: &mut Rc<Term>| {
        *field = rt(chain(vec![
            v(2),              // x_A
            v(1),              // x_B
            v(0),              // x_v
            box_gty(2, 3, 0),  // box U_A^{id}
            box_gty(1, 3, 0),  // box U_B^{id}
            box_gtm(0, 3, 0),  // box u_v^{id}
            Term::TmTy(lv(1)), // ℓ
            Term::TmTy(lv(0)), // ℓ'
        ]));
    };
    let mut b = dummy_branches();
    probe(&mut b.tm_inl);
    probe(&mut b.tm_inr);
    let b = Rc::new(b);
    let sum = Type::Sum {
        lhs_level: c(1),
        rhs_level: c(2),
        lhs: rty(Type::Nat),
        rhs: rty(Type::Nat),
    };
    // inl: value inhabits A (level ℓ=1); inr: value inhabits B (level ℓ'=2).
    for (is_inl, val_level, inner_val) in [(true, c(1), num(1)), (false, c(2), num(2))] {
        let code = if is_inl {
            Term::Inl {
                lhs_level: c(1),
                rhs_level: c(2),
                lhs: rty(Type::Nat),
                rhs: rty(Type::Nat),
                val: rt(inner_val.clone()),
            }
        } else {
            Term::Inr {
                lhs_level: c(1),
                rhs_level: c(2),
                lhs: rty(Type::Nat),
                rhs: rty(Type::Nat),
                val: rt(inner_val.clone()),
            }
        };
        let t = elim_tm(&b, Level::max(c(1), c(2)), delta.clone(), sum.clone(), Term::BoxTm(rt(code)));
        let s_lhs = elim_ty(&b, c(1), delta.clone(), Term::BoxTy(rty(Type::Nat)));
        let s_rhs = elim_ty(&b, c(2), delta.clone(), Term::BoxTy(rty(Type::Nat)));
        let s_val = elim_tm(
            &b,
            val_level,
            delta.clone(),
            Type::Nat,
            Term::BoxTm(rt(inner_val.clone())),
        );
        let expect = chain(vec![
            s_lhs,
            s_rhs,
            s_val,
            Term::BoxTy(rty(Type::Nat)),
            Term::BoxTy(rty(Type::Nat)),
            Term::BoxTm(rt(inner_val)),
            Term::TmTy(c(1)),
            Term::TmTy(c(2)),
        ]);
        assert_eq!(step_term(&t, &gamma), Some(expect));
    }
}

#[test]
fn beta_elim_code_tm_case() {
    // Telescope (ℓ, ℓ', ℓ'', g, U_A, U_B, U_M, u_l, u_r, u_t, x_A, x_B, x_M,
    // x_l, x_r, x_t. t_case): globals g=6, U_A=5, U_B=4, U_M=3, u_l=2, u_r=1,
    // u_t=0; locals x_A=5 … x_t=0. Univs ℓ=2, ℓ'=1, ℓ''=0. x_M recurses at the
    // *type* motive.
    let gamma = nil_ctx(0);
    let delta = nil_ctx(1);
    let mut b = dummy_branches();
    b.tm_case = rt(chain(vec![
        v(5),              // x_A
        v(4),              // x_B
        v(3),              // x_M
        v(2),              // x_l
        v(1),              // x_r
        v(0),              // x_t
        box_gty(5, 6, 0),  // box U_A^{id}
        box_gty(4, 6, 0),  // box U_B^{id}
        box_gty(3, 6, 1),  // box U_M^{id} (context (g, z : A + B))
        box_gtm(2, 6, 1),  // box u_l^{id} (context (g, x : A))
        box_gtm(1, 6, 1),  // box u_r^{id} (context (g, y : B))
        box_gtm(0, 6, 0),  // box u_t^{id}
        Term::TmTy(lv(2)), // ℓ
        Term::TmTy(lv(1)), // ℓ'
        Term::TmTy(lv(0)), // ℓ''
    ]));
    let b = Rc::new(b);
    // A closed Nat motive keeps M[inl x/z] = M[inr y/z] = Nat.
    let code = Term::Case {
        lhs_level: c(1),
        rhs_level: c(2),
        motive_level: Level::Zero,
        lhs: rty(Type::Nat),
        rhs: rty(Type::Nat),
        motive: rty(Type::Nat),
        case_l: rt(num(1)),
        case_r: rt(num(2)),
        scrut: rt(num(3)),
    };
    let lmax = Level::max(c(1), c(2));
    let t = elim_tm(&b, Level::Zero, delta.clone(), Type::Nat, Term::BoxTm(rt(code)));

    let sum = Type::Sum {
        lhs_level: c(1),
        rhs_level: c(2),
        lhs: rty(Type::Nat),
        rhs: rty(Type::Nat),
    };
    let s_lhs = elim_ty(&b, c(1), delta.clone(), Term::BoxTy(rty(Type::Nat)));
    let s_rhs = elim_ty(&b, c(2), delta.clone(), Term::BoxTy(rty(Type::Nat)));
    let dz = extend(&delta, sum.clone(), lmax.clone());
    let s_motive = elim_ty(&b, Level::Zero, dz, Term::BoxTy(rty(Type::Nat)));
    let dx = extend(&delta, Type::Nat, c(1));
    let s_case_l = elim_tm(&b, Level::Zero, dx, Type::Nat, Term::BoxTm(rt(num(1))));
    let dy = extend(&delta, Type::Nat, c(2));
    let s_case_r = elim_tm(&b, Level::Zero, dy, Type::Nat, Term::BoxTm(rt(num(2))));
    let s_scrut = elim_tm(&b, lmax, delta.clone(), sum, Term::BoxTm(rt(num(3))));
    let expect = chain(vec![
        s_lhs,
        s_rhs,
        s_motive,
        s_case_l,
        s_case_r,
        s_scrut,
        Term::BoxTy(rty(Type::Nat)),
        Term::BoxTy(rty(Type::Nat)),
        Term::BoxTy(rty(Type::Nat)),
        Term::BoxTm(rt(num(1))),
        Term::BoxTm(rt(num(2))),
        Term::BoxTm(rt(num(3))),
        Term::TmTy(c(1)),
        Term::TmTy(c(2)),
        Term::TmTy(Level::Zero),
    ]);
    assert_eq!(step_term(&t, &gamma), Some(expect));
}

// -------------------------------------------------------------------------
// W-types (extension; kernel-v1-extensions)
// -------------------------------------------------------------------------

/// `W^{0,0}(x : Nat). Empty` — Nat-labeled leaves (every node childless).
fn w_nat_empty() -> Type {
    Type::W {
        shape_level: Level::Zero,
        pos_level: Level::Zero,
        shape: rty(Type::Nat),
        pos: rty(Type::Empty { level: Level::Zero }),
    }
}

/// `λ^{0,0}(y : Empty). elim_Empty^0 (x. W; y)` — the childless subtree
/// function (everything closed, so no shifts are needed).
fn no_children() -> Term {
    Term::Lam {
        dom_level: Level::Zero,
        cod_level: Level::Zero,
        dom: rty(Type::Empty { level: Level::Zero }),
        body: rt(Term::ElimEmpty {
            level: Level::Zero,
            scrut_level: Level::Zero,
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
        pos_ty: rty(Type::Empty { level: Level::Zero }),
        label: rt(label),
        children: rt(no_children()),
    }
}

#[test]
fn el_decodes_tm_w() {
    // El^{1⊔2} (W (x : «Ty 0»). «Nat») ⇝ W (x : El^1 «Ty 0»). El^2 «Nat».
    let gamma = nil_ctx(0);
    let t = Type::El {
        level: Level::max(c(1), c(2)),
        tm: rt(Term::TmW {
            shape_level: c(1),
            pos_level: c(2),
            shape: rt(Term::TmTy(c(0))),
            pos: rt(Term::TmNat),
        }),
    };
    let expect = Type::W {
        shape_level: c(1),
        pos_level: c(2),
        shape: rty(Type::El { level: c(1), tm: rt(Term::TmTy(c(0))) }),
        pos: rty(Type::El { level: c(2), tm: rt(Term::TmNat) }),
    };
    assert_eq!(step_type(&t, &gamma), Some(expect.clone()));
    assert!(is_whnf_type(&expect));
}

#[test]
fn beta_elim_w_and_congruence() {
    let gamma = nil_ctx(1);
    // elim_W^{0,0,0}(x:Nat. Empty; z. Nat; a f ih. step; scrut).
    let elim = |step: Term, scrut: Term| Term::ElimW {
        shape_level: Level::Zero,
        pos_level: Level::Zero,
        motive_level: Level::Zero,
        shape: rty(Type::Nat),
        pos: rty(Type::Empty { level: Level::Zero }),
        motive: rty(Type::Nat),
        step: rt(step),
        scrut: rt(scrut),
    };
    // step = a: β yields the label.
    assert_eq!(step_term(&elim(v(2), sup_leaf(num(1))), &gamma), Some(num(1)));
    // step = f: β yields the subtree function verbatim.
    assert_eq!(
        step_term(&elim(v(1), sup_leaf(num(1))), &gamma),
        Some(no_children())
    );
    // step = ih: β synthesizes λ(y : T[a/x]). elim_W … (f y) — everything
    // here is closed, so the expected term is exact.
    let f_y = Term::App {
        fun: rt(no_children()),
        dom_level: Level::Zero,
        cod_level: Level::max(Level::Zero, Level::Zero),
        dom: rty(Type::Empty { level: Level::Zero }),
        cod: rty(w_nat_empty()),
        arg: rt(v(0)),
    };
    let expect_ih = Term::Lam {
        dom_level: Level::Zero,
        cod_level: Level::Zero,
        dom: rty(Type::Empty { level: Level::Zero }),
        body: rt(elim(v(0), f_y)),
    };
    assert_eq!(step_term(&elim(v(0), sup_leaf(num(1))), &gamma), Some(expect_ih));
    // Congruence reduces a redex scrutinee first.
    let redex = app2(lam(sup_leaf(num(2))), Term::Zero);
    let stepped = step_term(&elim(v(2), redex), &gamma).unwrap();
    assert_eq!(step_term(&stepped, &gamma), Some(num(2)));
    // Blocked on a neutral scrutinee: neutral, no step.
    let blocked = elim(v(2), v(0));
    assert_eq!(step_term(&blocked, &gamma), None);
    assert!(is_neutral_term(&blocked));
    // sup and the encoding are WHNFs.
    assert!(is_whnf_term(&sup_leaf(num(1))));
    assert!(is_whnf_term(&Term::TmW {
        shape_level: Level::Zero,
        pos_level: Level::Zero,
        shape: rt(Term::TmNat),
        pos: rt(Term::TmNat),
    }));
}

#[test]
fn beta_elim_code_ty_w() {
    // Telescope (ℓ, ℓ', g, U_S, U_T, x_S, x_T. t_W): globals g=2, U_S=1,
    // U_T=0; locals x_S=1, x_T=0. Univs ℓ=1, ℓ'=0. Mirrors ty_sigma.
    let gamma = nil_ctx(0);
    let delta = nil_ctx(1);
    let mut b = dummy_branches();
    b.ty_w = rt(chain(vec![
        v(1),              // x_S
        v(0),              // x_T
        box_gty(1, 2, 0),  // box U_S^{id}
        box_gty(0, 2, 1),  // box U_T^{id} (context (g, x))
        Term::TmTy(lv(1)), // ℓ
        Term::TmTy(lv(0)), // ℓ'
    ]));
    let b = Rc::new(b);
    let code = Type::W {
        shape_level: c(1),
        pos_level: c(2),
        shape: rty(Type::Nat),
        pos: rty(Type::Nat),
    };
    let t = elim_ty(&b, Level::max(c(1), c(2)), delta.clone(), Term::BoxTy(rty(code)));

    let s_shape = elim_ty(&b, c(1), delta.clone(), Term::BoxTy(rty(Type::Nat)));
    let dx = extend(&delta, Type::Nat, c(1));
    let s_pos = elim_ty(&b, c(2), dx, Term::BoxTy(rty(Type::Nat)));
    let expect = chain(vec![
        s_shape,
        s_pos,
        Term::BoxTy(rty(Type::Nat)),
        Term::BoxTy(rty(Type::Nat)),
        Term::TmTy(c(1)),
        Term::TmTy(c(2)),
    ]);
    assert_eq!(step_term(&t, &gamma), Some(expect));
}

#[test]
fn beta_elim_code_tm_w() {
    // Telescope (ℓ, ℓ', g, u_s, u_t, x_s, x_t. t'_W): globals g=2, u_s=1,
    // u_t=0; locals x_s=1, x_t=0. The encoding; u_t lives in (g, x : El u_s).
    let gamma = nil_ctx(0);
    let delta = nil_ctx(1);
    let mut b = dummy_branches();
    b.tm_w = rt(chain(vec![
        v(1),              // x_s
        v(0),              // x_t
        box_gtm(1, 2, 0),  // box u_s^{id}
        box_gtm(0, 2, 1),  // box u_t^{id} (context (g, x))
        Term::TmTy(lv(1)), // ℓ
        Term::TmTy(lv(0)), // ℓ'
    ]));
    let b = Rc::new(b);
    let lmax = Level::max(c(1), Level::Zero);
    let code = Term::TmW {
        shape_level: c(1),
        pos_level: Level::Zero,
        shape: rt(Term::TmTy(c(0))), // : Ty 1
        pos: rt(Term::TmNat),        // : Ty 0
    };
    let t = elim_tm(
        &b,
        Level::succ(lmax.clone()),
        delta.clone(),
        Type::Ty(lmax),
        Term::BoxTm(rt(code)),
    );

    let s_shape = elim_tm(
        &b,
        Level::succ(c(1)),
        delta.clone(),
        Type::Ty(c(1)),
        Term::BoxTm(rt(Term::TmTy(c(0)))),
    );
    let dx = extend(
        &delta,
        Type::El { level: c(1), tm: rt(Term::TmTy(c(0))) },
        c(1),
    );
    let s_pos = elim_tm(
        &b,
        Level::succ(Level::Zero),
        dx,
        Type::Ty(Level::Zero),
        Term::BoxTm(rt(Term::TmNat)),
    );
    let expect = chain(vec![
        s_shape,
        s_pos,
        Term::BoxTm(rt(Term::TmTy(c(0)))),
        Term::BoxTm(rt(Term::TmNat)),
        Term::TmTy(c(1)),
        Term::TmTy(Level::Zero),
    ]);
    assert_eq!(step_term(&t, &gamma), Some(expect));
}

#[test]
fn beta_elim_code_tm_sup() {
    // Telescope (ℓ, ℓ', g, U_S, U_T, u_a, u_f, x_S, x_T, x_a, x_f. t_sup):
    // globals g=4, U_S=3, U_T=2, u_a=1, u_f=0; locals x_S=3, x_T=2, x_a=1,
    // x_f=0. Univs ℓ=1, ℓ'=0. Mirrors tm_pair.
    let gamma = nil_ctx(0);
    let delta = nil_ctx(1);
    let mut b = dummy_branches();
    b.tm_sup = rt(chain(vec![
        v(3),              // x_S
        v(2),              // x_T
        v(1),              // x_a
        v(0),              // x_f
        box_gty(3, 4, 0),  // box U_S^{id}
        box_gty(2, 4, 1),  // box U_T^{id} (context (g, x))
        box_gtm(1, 4, 0),  // box u_a^{id}
        box_gtm(0, 4, 0),  // box u_f^{id}
        Term::TmTy(lv(1)), // ℓ
        Term::TmTy(lv(0)), // ℓ'
    ]));
    let b = Rc::new(b);
    let code = sup_leaf(num(1));
    let t = elim_tm(
        &b,
        Level::max(Level::Zero, Level::Zero),
        delta.clone(),
        w_nat_empty(),
        Term::BoxTm(rt(code)),
    );

    let s_shape = elim_ty(&b, Level::Zero, delta.clone(), Term::BoxTy(rty(Type::Nat)));
    let dx = extend(&delta, Type::Nat, Level::Zero);
    let s_pos = elim_ty(&b, Level::Zero, dx, Term::BoxTy(rty(Type::Empty { level: Level::Zero })));
    let s_label = elim_tm(
        &b,
        Level::Zero,
        delta.clone(),
        Type::Nat,
        Term::BoxTm(rt(num(1))),
    );
    let lmax = Level::max(Level::Zero, Level::Zero);
    let f_ty = Type::Pi {
        dom_level: Level::Zero,
        cod_level: lmax.clone(),
        dom: rty(Type::Empty { level: Level::Zero }),
        cod: rty(w_nat_empty()),
    };
    let s_children = elim_tm(
        &b,
        Level::max(Level::Zero, lmax),
        delta.clone(),
        f_ty,
        Term::BoxTm(rt(no_children())),
    );
    let expect = chain(vec![
        s_shape,
        s_pos,
        s_label,
        s_children,
        Term::BoxTy(rty(Type::Nat)),
        Term::BoxTy(rty(Type::Empty { level: Level::Zero })),
        Term::BoxTm(rt(num(1))),
        Term::BoxTm(rt(no_children())),
        Term::TmTy(Level::Zero),
        Term::TmTy(Level::Zero),
    ]);
    assert_eq!(step_term(&t, &gamma), Some(expect));
}

#[test]
fn beta_elim_code_tm_elim_w() {
    // Telescope (ℓ, ℓ', ℓ'', g, U_S, U_T, U_M, u_s, u_t, x_S, x_T, x_M, x_s,
    // x_t. t_elimW): globals g=5, U_S=4, U_T=3, U_M=2, u_s=1, u_t=0; locals
    // x_S=4, x_T=3, x_M=2, x_s=1, x_t=0. All annotations here are closed, so
    // every shift is the identity and the expected term is exact.
    let gamma = nil_ctx(0);
    let delta = nil_ctx(1);
    let mut b = dummy_branches();
    b.tm_elim_w = rt(chain(vec![
        v(4),              // x_S
        v(3),              // x_T
        v(2),              // x_M
        v(1),              // x_s
        v(0),              // x_t
        box_gty(4, 5, 0),  // box U_S^{id}
        box_gty(3, 5, 1),  // box U_T^{id} (context (g, x))
        box_gty(2, 5, 1),  // box U_M^{id} (context (g, z))
        box_gtm(1, 5, 3),  // box u_s^{id} (context (g, a, f, ih))
        box_gtm(0, 5, 0),  // box u_t^{id}
        Term::TmTy(lv(2)), // ℓ
        Term::TmTy(lv(1)), // ℓ'
        Term::TmTy(lv(0)), // ℓ''
    ]));
    let b = Rc::new(b);
    let code = Term::ElimW {
        shape_level: Level::Zero,
        pos_level: Level::Zero,
        motive_level: Level::Zero,
        shape: rty(Type::Nat),
        pos: rty(Type::Empty { level: Level::Zero }),
        motive: rty(Type::Nat),
        step: rt(num(2)),
        scrut: rt(sup_leaf(num(1))),
    };
    let t = elim_tm(&b, Level::Zero, delta.clone(), Type::Nat, Term::BoxTm(rt(code)));

    let lmax = Level::max(Level::Zero, Level::Zero);
    let w = w_nat_empty();
    let s_shape = elim_ty(&b, Level::Zero, delta.clone(), Term::BoxTy(rty(Type::Nat)));
    let da = extend(&delta, Type::Nat, Level::Zero);
    let s_pos = elim_ty(&b, Level::Zero, da.clone(), Term::BoxTy(rty(Type::Empty { level: Level::Zero })));
    let dz = extend(&delta, w.clone(), lmax.clone());
    let s_motive = elim_ty(&b, Level::Zero, dz, Term::BoxTy(rty(Type::Nat)));
    let f_ty = Type::Pi {
        dom_level: Level::Zero,
        cod_level: lmax.clone(),
        dom: rty(Type::Empty { level: Level::Zero }),
        cod: rty(w.clone()),
    };
    let daf = extend(&da, f_ty, Level::max(Level::Zero, lmax.clone()));
    let ih_ty = Type::Pi {
        dom_level: Level::Zero,
        cod_level: Level::Zero,
        dom: rty(Type::Empty { level: Level::Zero }),
        cod: rty(Type::Nat),
    };
    let dafi = extend(&daf, ih_ty, Level::max(Level::Zero, Level::Zero));
    let s_step = elim_tm(&b, Level::Zero, dafi, Type::Nat, Term::BoxTm(rt(num(2))));
    let s_scrut = elim_tm(&b, lmax, delta.clone(), w, Term::BoxTm(rt(sup_leaf(num(1)))));
    let expect = chain(vec![
        s_shape,
        s_pos,
        s_motive,
        s_step,
        s_scrut,
        Term::BoxTy(rty(Type::Nat)),
        Term::BoxTy(rty(Type::Empty { level: Level::Zero })),
        Term::BoxTy(rty(Type::Nat)),
        Term::BoxTm(rt(num(2))),
        Term::BoxTm(rt(sup_leaf(num(1)))),
        Term::TmTy(Level::Zero),
        Term::TmTy(Level::Zero),
        Term::TmTy(Level::Zero),
    ]);
    assert_eq!(step_term(&t, &gamma), Some(expect));
}

/// β on the projections fires on **either** pair spelling, in all four
/// combinations, and reads nothing from either annotation
/// (`docs/elaborator/intro-by-type-design.md` §2.4; `docs/kernel/delam-extensions.md` §16.2
/// already says this for the component form).
///
/// The cross combinations are the ones worth a test: a `fst` over a `pair@`
/// and a `fst@` over a `pair` are exactly what a module containing both
/// spellings produces, and neither is reachable from the same-spelling arms.
/// The annotations here are deliberately *wrong* — `Empty` is not a Σ — to
/// pin "reads nothing from the annotations": reduction is untyped, and a rule
/// that consulted them would have to fail or diverge here.
#[test]
fn projection_beta_fires_on_either_pair_spelling() {
    let gamma = nil_ctx(0);
    let junk = || Rc::new(Type::Empty { level: Level::Zero });
    let component = || {
        Term::Pair {
            fst_level: Level::Zero,
            snd_level: Level::Zero,
            fst_ty: junk(),
            snd_ty: junk(),
            fst: Rc::new(num(3)),
            snd: Rc::new(num(4)),
        }
    };
    let checked =
        || Term::PairAt { ty: Some(junk()), fst: Rc::new(num(3)), snd: Rc::new(num(4)) };

    for pair in [component(), checked()] {
        let p = Rc::new(pair);
        let fst = Term::Fst {
            fst_level: Level::Zero,
            snd_level: Level::Zero,
            fst_ty: junk(),
            snd_ty: junk(),
            pair: Rc::clone(&p),
        };
        let snd = Term::Snd {
            fst_level: Level::Zero,
            snd_level: Level::Zero,
            fst_ty: junk(),
            snd_ty: junk(),
            pair: Rc::clone(&p),
        };
        let fst_at = Term::FstAt { pair: Rc::clone(&p) };
        let snd_at = Term::SndAt { pair: Rc::clone(&p) };
        assert_eq!(step_term(&fst, &gamma), Some(num(3)));
        assert_eq!(step_term(&fst_at, &gamma), Some(num(3)));
        assert_eq!(step_term(&snd, &gamma), Some(num(4)));
        assert_eq!(step_term(&snd_at, &gamma), Some(num(4)));
        // The intros are weak head normal, and the projections over them are
        // not — the grammar and the step relation must agree, which
        // `whnf_grammar_agrees_with_the_step_relation` checks in general and
        // this pins for the new forms.
        assert!(is_whnf_term(&p));
        assert!(!is_whnf_term(&fst_at));
        assert!(!is_neutral_term(&fst_at));
    }

    // Over a *neutral* pair both spellings are neutral, and the checked one
    // does not step its annotation looking for a former it cannot use.
    let stuck = Term::FstAt { pair: Rc::new(v(0)) };
    assert!(is_neutral_term(&stuck));
    assert!(is_whnf_term(&stuck));
    assert_eq!(step_term(&stuck, &nil_ctx(1)), None);
}
