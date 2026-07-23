//! Tests for ch. 06 weak-head reduction: golden tests for every β-rule
//! (including all 13 recursor branches, probing each branch telescope's
//! universe / global / recursive-call instantiation), congruence-order and
//! blocking behavior, and generator-based properties (normal forms do not
//! step; reducts stay well-scoped).

mod common;

use std::rc::Rc;

use common::*;
use heather_kernel::level::{Level, UnivVar};
use heather_kernel::reduce::{
    is_neutral_term, is_whnf_term, is_whnf_type, step_term, step_type, whnf_term,
};
use heather_kernel::term::{
    Branches, CtxBase, CtxEntry, GlobalVar, LocalCtx, LocalSubst, LocalVar, Motives, SubstTail,
    Term, Type,
};

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
        entries: (0..n)
            .map(|_| CtxEntry { ty: rty(Type::Nat), level: Level::Zero })
            .collect(),
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
        tail: SubstTail::Wk { len: k, ctx_var: GlobalVar(g) },
        terms: (0..k).map(|j| rt(v(k - 1 - j))).collect(),
    }
}

/// Probe `box (U^{id})` for a global type binding `var` with index context
/// `(g, k entries)`; after β it becomes `box` of the payload.
fn box_gty(var: u32, g: u32, k: u32) -> Term {
    Term::BoxTy(rty(Type::GlobalTy { var: GlobalVar(var), subst: wk_id(g, k) }))
}

/// Probe `box (u^{id})` for a global term binding, as [`box_gty`].
fn box_gtm(var: u32, g: u32, k: u32) -> Term {
    Term::BoxTm(rt(Term::GlobalTm { var: GlobalVar(var), subst: wk_id(g, k) }))
}

/// Probe observing the context variable `g`: `(0 @ g)` becomes `(0 @ Δ)`.
fn ctx_probe(g: u32) -> Term {
    Term::CtxApp {
        fun: rt(Term::Zero),
        ctx: LocalCtx { base: CtxBase::Var(GlobalVar(g)), entries: vec![] },
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
    let empty = LocalSubst { tail: SubstTail::Empty { len: 0, base: CtxBase::Nil }, terms: vec![] };
    let t = Term::TyApp {
        fun: rt(Term::TyLam {
            ctx: nil_ctx(0),
            arg_level: Level::Zero,
            body_level: Level::Zero,
            body: rt(Term::BoxTy(rty(Type::GlobalTy { var: GlobalVar(0), subst: empty }))),
        }),
        arg: rty(Type::Nat),
    };
    assert_eq!(step_term(&t, &gamma), Some(Term::BoxTy(rty(Type::Nat))));
}

#[test]
fn beta_letbox() {
    let gamma = nil_ctx(0);
    let empty = LocalSubst { tail: SubstTail::Empty { len: 0, base: CtxBase::Nil }, terms: vec![] };
    // letbox (U. box U^·) (box Nat) ⇝ box Nat
    let t = Term::LetBoxTy {
        motive_level: Level::Zero,
        code_level: Level::Zero,
        ctx: nil_ctx(0),
        motive: rty(Type::Nat),
        body: rt(Term::BoxTy(rty(Type::GlobalTy { var: GlobalVar(0), subst: empty.clone() }))),
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
        body: rt(Term::BoxTm(rt(Term::GlobalTm { var: GlobalVar(0), subst: empty }))),
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
    let empty = LocalSubst { tail: SubstTail::Empty { len: 0, base: CtxBase::Nil }, terms: vec![] };
    // elim^Typ … (box U^δ): neutral, no step.
    let t = elim_ty(
        &b,
        Level::Zero,
        nil_ctx(0),
        Term::BoxTy(rty(Type::GlobalTy { var: GlobalVar(0), subst: empty.clone() })),
    );
    assert_eq!(step_term(&t, &gamma), None);
    assert!(is_neutral_term(&t));
    // elim^Trm … (box u^δ): neutral, no step.
    let t = elim_tm(
        &b,
        Level::Zero,
        nil_ctx(0),
        Type::Nat,
        Term::BoxTm(rt(Term::GlobalTm { var: GlobalVar(0), subst: empty.clone() })),
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
        Term::BoxTm(rt(Term::GlobalTm { var: GlobalVar(0), subst: empty })),
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
