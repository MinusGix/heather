//! Codes and recursor branches for `DVec` and `IWf`: step 4 of the `IWf`
//! landing (`docs/iwf-former-design.md` §13; `issues/iwf-former.md`), the
//! round that lets indexed families land at layer c.
//!
//! `TmDVec` and `TmIWf` are the codes of the two formers (the index inside
//! `TmIWf`, as `TmM` carries its own), and `El` decodes them. `DVec`, `IWf`,
//! `sup_i` and `elim_IWf` are admitted at layer c. The sharp test is the
//! **identity recursor**: it rebuilds every boxed form in one β-step, which
//! pins the six telescopes in `rec.rs` (heather-coq `RecSpec` branches
//! 55–60) against `reduce.rs`'s payload wiring. On the axes of
//! `docs/testing-generated-terms.md`: a literal and a neutral index or
//! length, a neutral code piece, checking positions (the recursor's
//! annotations), and negative controls (ill-formed codes, a wrong branch,
//! layer v).
//!
//! The family is `Bush`: `IWf(Nat; a : Nat. a; a. a; a i. 0)` — a node
//! labelled `a` is at index `a` and has `a` children, each a leaf at index
//! 0. It needs no `case`, so every piece is a variable or a numeral.

mod common;

use heather_kernel::rc::Rc;

use common::wt::{identity_branches, identity_motives, FUEL};
use heather_kernel::conv::conv_type;
use heather_kernel::layer::Layer;
use heather_kernel::level::Level;
use heather_kernel::reduce::{whnf_term, whnf_type};
use heather_kernel::term::{iwf_children_ty, CtxEntry, GlobalCtx, IWfSig, LocalCtx, LocalVar, Term, Type};
use heather_kernel::typing::{check_term, check_type, TypeError};

// -------------------------------------------------------------------------
// Helpers
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

fn v(i: u32) -> Term {
    Term::Var(LocalVar(i))
}

fn nil_ctx() -> LocalCtx {
    LocalCtx::nil()
}

fn ext(gamma: &LocalCtx, ty: Type, level: Level) -> LocalCtx {
    let mut g = gamma.clone();
    g.entries.push(CtxEntry { ty: rty(ty), level });
    g
}

fn nat(n: u64) -> Term {
    let mut t = Term::Zero;
    for _ in 0..n {
        t = Term::Succ(rt(t));
    }
    t
}

fn el(code: Term) -> Type {
    Type::El { level: c(0), tm: rt(code) }
}

fn dvec(len: Term, fam: Type) -> Type {
    Type::DVec { level: c(0), len: rt(len), fam: rty(fam) }
}

/// `Bush`: shapes `Nat`, arity `a`, output `a`, every child at 0.
fn bush() -> Rc<IWfSig> {
    Rc::new(IWfSig {
        level: c(0),
        idx_level: c(0),
        idx: rty(Type::Nat),
        shape: rty(Type::Nat),
        arity: rt(v(0)),
        out: rt(v(0)),
        child: rt(Term::Zero),
    })
}

/// `Bush`'s code at index `m`, with another shape code for the neutral and
/// ill-formed variants. The arity and output read the shape, so they are
/// numerals unless the shape code is `Nat`'s.
fn bush_code_at(shape: Term, arity: Term, out: Term, index: Term) -> Term {
    Term::TmIWf {
        level: c(0),
        idx_level: c(0),
        idx: rt(Term::TmNat),
        shape: rt(shape),
        arity: rt(arity),
        out: rt(out),
        child: rt(Term::Zero),
        index: rt(index),
    }
}

fn bush_code(m: Term) -> Term {
    bush_code_at(Term::TmNat, v(0), v(0), m)
}

/// The leaf `sup_i(0; ⟨⟩) : Bush(0)`.
fn leaf() -> Term {
    bush().supi(rt(nat(0)), rt(Term::Triv { level: c(0) }))
}

/// `sup_i(1; (leaf, ⟨⟩)) : Bush(1)`, its pair at the annotations the
/// children's type reduces to.
fn node1() -> Term {
    let sig = bush();
    let cs_ty = whnf_type(&iwf_children_ty(&sig, &nat(1)), &nil_ctx(), FUEL).expect("enough fuel");
    let Type::Sigma { fst_level, snd_level, fst, snd } = cs_ty else {
        panic!("DVec at a literal length reduces to Σ, got {cs_ty:?}")
    };
    let children = Term::Pair {
        fst_level,
        snd_level,
        fst_ty: fst,
        snd_ty: snd,
        fst: rt(leaf()),
        snd: rt(Term::Triv { level: c(0) }),
    };
    sig.supi(rt(nat(1)), rt(children))
}

/// `elim_IWf(Bush; _ _. Nat; a cs ih. a; m; t)`: the root's label.
fn label(m: Term, t: Term) -> Term {
    Term::ElimIWf {
        sig: bush(),
        motive_level: c(0),
        motive: rty(Type::Nat),
        step: rt(v(2)),
        index: rt(m),
        scrut: rt(t),
    }
}

fn check_ty_at(layer: Layer, gamma: &LocalCtx, t: &Type, l: &Level) -> Result<(), TypeError> {
    check_type(&GlobalCtx::default(), 0, layer, gamma, t, l, FUEL)
}

fn check_tm_at(layer: Layer, gamma: &LocalCtx, t: &Term, ty: &Type, l: &Level) -> Result<(), TypeError> {
    check_term(&GlobalCtx::default(), 0, layer, gamma, t, ty, l, FUEL)
}

fn conv_ty(gamma: &LocalCtx, a: &Type, b: &Type) -> bool {
    conv_type(&GlobalCtx::default(), gamma, Layer::Prog, a, b, &c(0), FUEL).is_ok()
}

// -------------------------------------------------------------------------
// The codes and their `El` decoding
// -------------------------------------------------------------------------

#[test]
fn dvec_codes_check_and_decode() {
    // A literal length: TmDVec(2; Nat) : Ty 0, and El of it is DVec(2; Nat).
    let code = Term::TmDVec { level: c(0), len: rt(nat(2)), fam: rt(Term::TmNat) };
    check_tm_at(Layer::Code, &nil_ctx(), &code, &Type::Ty(c(0)), &c(1)).expect("the code checks at c");
    assert!(conv_ty(&nil_ctx(), &el(code.clone()), &dvec(nat(2), Type::Nat)));
    assert!(!conv_ty(&nil_ctx(), &el(code), &dvec(nat(1), Type::Nat)));

    // A neutral length: Γ = (n : Nat). El(TmDVec(n; Nat)) is the stuck
    // DVec(n; Nat), and not DVec(S n; Nat).
    let g = ext(&nil_ctx(), Type::Nat, c(0));
    let code = Term::TmDVec { level: c(0), len: rt(v(0)), fam: rt(Term::TmNat) };
    check_tm_at(Layer::Code, &g, &code, &Type::Ty(c(0)), &c(1)).expect("a neutral length checks");
    let w = whnf_type(&el(code.clone()), &g, FUEL).expect("enough fuel");
    assert!(matches!(w, Type::DVec { .. }), "El(TmDVec) at a neutral length is DVec, got {w:?}");
    assert!(conv_ty(&g, &el(code.clone()), &dvec(v(0), Type::Nat)));
    assert!(!conv_ty(&g, &el(code), &dvec(Term::Succ(rt(v(0))), Type::Nat)));

    // A neutral family code: Γ = (n : Nat, u : Ty 0); under `i` it is Var(1).
    let g = ext(&g, Type::Ty(c(0)), c(1));
    let code = Term::TmDVec { level: c(0), len: rt(v(1)), fam: rt(v(1)) };
    check_tm_at(Layer::Code, &g, &code, &Type::Ty(c(0)), &c(1)).expect("a neutral family code checks");
    assert!(conv_ty(&g, &el(code.clone()), &dvec(v(1), el(v(1)))));
    assert!(!conv_ty(&g, &el(code), &dvec(v(1), Type::Nat)));
}

#[test]
fn iwf_codes_check_and_decode() {
    // A literal index: El(Bush code at 2) is Bush(2), not Bush(1).
    let code = bush_code(nat(2));
    check_tm_at(Layer::Code, &nil_ctx(), &code, &Type::Ty(c(0)), &c(1)).expect("the Bush code checks at c");
    let w = whnf_type(&el(code.clone()), &nil_ctx(), FUEL).expect("enough fuel");
    assert!(matches!(w, Type::IWf { .. }), "El(TmIWf) reduces to IWf, got {w:?}");
    assert!(conv_ty(&nil_ctx(), &el(code.clone()), &bush().at(rt(nat(2)))));
    assert!(!conv_ty(&nil_ctx(), &el(code), &bush().at(rt(nat(1)))));

    // A neutral index: Γ = (j : Nat).
    let g = ext(&nil_ctx(), Type::Nat, c(0));
    let code = bush_code(v(0));
    check_tm_at(Layer::Code, &g, &code, &Type::Ty(c(0)), &c(1)).expect("a neutral index checks");
    assert!(conv_ty(&g, &el(code.clone()), &bush().at(rt(v(0)))));
    assert!(!conv_ty(&g, &el(code), &bush().at(rt(Term::Succ(rt(v(0)))))));

    // A neutral shape code: Γ = (u : Ty 0), the shapes `El u`, arity and
    // output constant. The decoding reads `El u` for the shapes.
    let g = ext(&nil_ctx(), Type::Ty(c(0)), c(1));
    let code = bush_code_at(v(0), nat(0), nat(0), nat(0));
    check_tm_at(Layer::Code, &g, &code, &Type::Ty(c(0)), &c(1)).expect("a neutral shape code checks");
    let decoded = Rc::new(IWfSig {
        shape: rty(el(v(0))),
        arity: rt(nat(0)),
        out: rt(nat(0)),
        ..(*bush()).clone()
    })
    .at(rt(nat(0)));
    assert!(conv_ty(&g, &el(code.clone()), &decoded));
    let as_nat = Rc::new(IWfSig { arity: rt(nat(0)), out: rt(nat(0)), ..(*bush()).clone() }).at(rt(nat(0)));
    assert!(!conv_ty(&g, &el(code), &as_nat), "a neutral shape is not Nat");
}

#[test]
fn ill_formed_codes_are_refused() {
    let ty0 = Type::Ty(c(0));
    // An index outside the decoded index type.
    let bad = bush_code(Term::Triv { level: c(0) });
    assert!(check_tm_at(Layer::Code, &nil_ctx(), &bad, &ty0, &c(1)).is_err());
    // An output outside it.
    let bad = bush_code_at(Term::TmNat, v(0), Term::Triv { level: c(0) }, nat(0));
    assert!(check_tm_at(Layer::Code, &nil_ctx(), &bad, &ty0, &c(1)).is_err());
    // A shape piece that is not a code.
    let bad = bush_code_at(nat(0), nat(0), nat(0), nat(0));
    assert!(check_tm_at(Layer::Code, &nil_ctx(), &bad, &ty0, &c(1)).is_err());
    // The level is the family's: not Ty 1.
    assert!(check_tm_at(Layer::Code, &nil_ctx(), &bush_code(nat(0)), &Type::Ty(c(1)), &c(2)).is_err());
    // A DVec family that is not a code, and a length that is not a Nat.
    let bad = Term::TmDVec { level: c(0), len: rt(nat(1)), fam: rt(nat(0)) };
    assert!(check_tm_at(Layer::Code, &nil_ctx(), &bad, &ty0, &c(1)).is_err());
    let bad = Term::TmDVec { level: c(0), len: rt(Term::TmNat), fam: rt(Term::TmNat) };
    assert!(check_tm_at(Layer::Code, &nil_ctx(), &bad, &ty0, &c(1)).is_err());
}

// -------------------------------------------------------------------------
// Layer c
// -------------------------------------------------------------------------

#[test]
fn the_formers_and_their_terms_are_admitted_at_layer_c() {
    let g = ext(&nil_ctx(), Type::Nat, c(0));
    check_ty_at(Layer::Code, &g, &dvec(v(0), Type::Nat), &c(0)).expect("DVec at c");
    check_ty_at(Layer::Code, &g, &bush().at(rt(v(0))), &c(0)).expect("IWf at c");
    let at1 = bush().at(rt(nat(1)));
    check_tm_at(Layer::Code, &nil_ctx(), &node1(), &at1, &c(0)).expect("sup_i at c");
    check_tm_at(Layer::Code, &nil_ctx(), &label(nat(1), node1()), &Type::Nat, &c(0)).expect("elim_IWf at c");
    // A node is at its output index only.
    assert!(check_tm_at(Layer::Code, &nil_ctx(), &node1(), &bush().at(rt(nat(0))), &c(0)).is_err());
    // Layer v still admits only variables.
    assert_eq!(check_tm_at(Layer::Var, &nil_ctx(), &node1(), &at1, &c(0)), Err(TypeError::LayerMismatch));
    let ty0 = Type::Ty(c(0));
    assert_eq!(check_tm_at(Layer::Var, &nil_ctx(), &bush_code(nat(0)), &ty0, &c(1)), Err(TypeError::LayerMismatch));
}

#[test]
fn the_label_computes() {
    // The positive control for the boxes below: outside a box, β fires.
    let w = whnf_term(&label(nat(1), node1()), &nil_ctx(), FUEL).expect("enough fuel");
    assert_eq!(w, nat(1));
}

// -------------------------------------------------------------------------
// The identity recursor rebuilds every form
// -------------------------------------------------------------------------

fn identity_ty(code: Type) {
    let t = Term::ElimCodeTy {
        ty_motive_level: c(0),
        tm_motive_level: c(0),
        motives: identity_motives(),
        branches: identity_branches(),
        code_level: c(0),
        ctx: nil_ctx(),
        scrut: rt(Term::BoxTy(rty(code.clone()))),
    };
    let expect = Type::CodeTy { ctx: nil_ctx(), level: c(0) };
    check_term(&GlobalCtx::default(), 0, Layer::Meta, &nil_ctx(), &t, &expect, &c(0), FUEL)
        .unwrap_or_else(|e| panic!("identity elim^Typ ill-typed on {code:?}: {e:?}"));
    let w = whnf_term(&t, &nil_ctx(), FUEL).expect("identity elim^Typ exhausted fuel");
    assert!(w == Term::BoxTy(rty(code)), "identity elim^Typ is not the identity");
}

fn identity_tm(code: Term, ty: Type, level: Level) {
    let t = Term::ElimCodeTm {
        ty_motive_level: c(0),
        tm_motive_level: c(0),
        motives: identity_motives(),
        branches: identity_branches(),
        code_level: level.clone(),
        ctx: nil_ctx(),
        ty: rty(ty.clone()),
        scrut: rt(Term::BoxTm(rt(code.clone()))),
    };
    let expect = Type::CodeTm { ctx: nil_ctx(), ty: rty(ty), level };
    check_term(&GlobalCtx::default(), 0, Layer::Meta, &nil_ctx(), &t, &expect, &c(0), FUEL)
        .unwrap_or_else(|e| panic!("identity elim^Trm ill-typed on {code:?}: {e:?}"));
    let w = whnf_term(&t, &nil_ctx(), FUEL).expect("identity elim^Trm exhausted fuel");
    assert!(w == Term::BoxTm(rt(code)), "identity elim^Trm is not the identity");
}

#[test]
fn identity_recursor_round_trips_the_types() {
    identity_ty(dvec(nat(2), Type::Nat));
    identity_ty(bush().at(rt(nat(2))));
}

#[test]
fn identity_recursor_round_trips_the_codes() {
    let ty0 = Type::Ty(c(0));
    identity_tm(Term::TmDVec { level: c(0), len: rt(nat(2)), fam: rt(Term::TmNat) }, ty0.clone(), c(1));
    identity_tm(bush_code(nat(2)), ty0, c(1));
}

#[test]
fn identity_recursor_round_trips_sup_i_and_elim_iwf() {
    // tm_sup_i, nested: the leaf inside the node's children.
    identity_tm(node1(), bush().at(rt(nat(1))), c(0));
    // tm_elim_iwf, the widest telescope: ten globals, the step at
    // iwf_step_telescope. A boxed elimination is inert syntax.
    identity_tm(label(nat(1), node1()), Type::Nat, c(0));
}

/// A branch whose box is well-scoped but the wrong code poisons the whole
/// recursor, whichever code it is run on.
#[test]
fn a_wrong_new_branch_poisons_the_recursor() {
    for which in 0..6 {
        let mut bad = (*identity_branches()).clone();
        let zero = rt(Term::BoxTm(rt(Term::Zero)));
        match which {
            0 => bad.ty_dvec = rt(Term::BoxTy(rty(Type::Nat))),
            1 => bad.tm_dvec = zero,
            2 => bad.ty_iwf = rt(Term::BoxTy(rty(Type::Nat))),
            3 => bad.tm_iwf = zero,
            4 => bad.tm_sup_i = zero,
            _ => bad.tm_elim_iwf = zero,
        }
        let t = Term::ElimCodeTy {
            ty_motive_level: c(0),
            tm_motive_level: c(0),
            motives: identity_motives(),
            branches: Rc::new(bad),
            code_level: c(0),
            ctx: nil_ctx(),
            scrut: rt(Term::BoxTy(rty(Type::Nat))),
        };
        let expect = Type::CodeTy { ctx: nil_ctx(), level: c(0) };
        assert!(
            check_term(&GlobalCtx::default(), 0, Layer::Meta, &nil_ctx(), &t, &expect, &c(0), FUEL).is_err(),
            "a mismatched branch {which} must be rejected"
        );
    }
}
