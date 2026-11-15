//! Codes and recursor branches for `M`: `docs/kernel/kernel-m-codes-design.md`
//! (`issues/codata-codes.md`), the round that lets codata land at layer c.
//!
//! `TmM` is the code of `M`, with the index inside the code, and `El`
//! decodes it to the former. `M`, `corec` and `out` are admitted at layer c,
//! where a boxed `corec` is inert syntax: reduction never enters a box, so
//! `box(hd(zeros))` is not `box(0)` although `hd(zeros) ≡ 0`. The sharp test
//! is `wf_codes.rs`'s: the **identity recursor** rebuilds every boxed `M`,
//! `TmM`, `corec` and `out` in one β-step, which pins the four telescopes in
//! `rec.rs` against `reduce.rs`'s payload wiring. On the axes of
//! `docs/testing-generated-terms.md`: a literal and a neutral index, a
//! neutral code piece, checking positions (the recursor's annotations), and
//! negative controls (the box, a wrong branch, layer v).

mod common;

use heather_kernel::rc::Rc;

use common::wt::{gen_encoding, gen_wt_env, identity_branches, identity_motives, FUEL};
use common::Rng;
use heather_kernel::conv::{conv_term, conv_type};
use heather_kernel::layer::Layer;
use heather_kernel::level::Level;
use heather_kernel::reduce::{whnf_term, whnf_type};
use heather_kernel::term::{m_out_ty, m_step_ty, CtxEntry, GlobalCtx, LocalCtx, LocalVar, MSig, Term, Type};
use heather_kernel::typing::{check_term, check_type, TypeError};

// -------------------------------------------------------------------------
// Helpers (the families of `tests/m.rs`)
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

fn unit0() -> Type {
    Type::Unit { level: c(0) }
}

fn triv() -> Term {
    Term::Triv { level: c(0) }
}

fn tm_unit() -> Term {
    Term::TmUnit { level: c(0) }
}

fn el(code: Term) -> Type {
    Type::El { level: c(0), tm: rt(code) }
}

/// Streams of `Nat`: `M(Unit; _. Nat; _ _. Unit; _ _ _. ⟨⟩)`.
fn stream() -> Rc<MSig> {
    Rc::new(MSig {
        level: c(0),
        pos_level: c(0),
        idx_level: c(0),
        idx: rty(unit0()),
        shape: rty(Type::Nat),
        pos: rty(unit0()),
        next: rt(triv()),
    })
}

fn stream_ty() -> Type {
    stream().at(rt(triv()))
}

/// `Stream`'s code: the same signature, every piece coded.
fn stream_code() -> Term {
    stream_code_at(Term::TmNat, triv())
}

/// `Stream`'s code with another shape code and index, for the neutral and
/// ill-formed variants.
fn stream_code_at(shape: Term, index: Term) -> Term {
    Term::TmM {
        level: c(0),
        pos_level: c(0),
        idx_level: c(0),
        idx: rt(tm_unit()),
        shape: rt(shape),
        pos: rt(tm_unit()),
        next: rt(triv()),
        index: rt(index),
    }
}

/// `From`: a node at index `i` holds `i` with a proof, its child at `S i`.
fn from_sig() -> Rc<MSig> {
    let shape = Type::Sigma {
        fst_level: c(0),
        snd_level: c(0),
        fst: rty(Type::Nat),
        snd: rty(Type::Id { level: c(0), ty: rty(Type::Nat), lhs: rt(v(0)), rhs: rt(v(1)) }),
    };
    Rc::new(MSig {
        level: c(0),
        pos_level: c(0),
        idx_level: c(0),
        idx: rty(Type::Nat),
        shape: rty(shape),
        pos: rty(unit0()),
        next: rt(Term::Succ(rt(v(2)))),
    })
}

/// `From`'s code at index `j`.
fn from_code(j: Term) -> Term {
    let shape = Term::TmSigma {
        fst_level: c(0),
        snd_level: c(0),
        fst: rt(Term::TmNat),
        snd: rt(Term::TmId { level: c(0), ty: rt(Term::TmNat), lhs: rt(v(0)), rhs: rt(v(1)) }),
    };
    Term::TmM {
        level: c(0),
        pos_level: c(0),
        idx_level: c(0),
        idx: rt(Term::TmNat),
        shape: rt(shape),
        pos: rt(tm_unit()),
        next: rt(Term::Succ(rt(v(2)))),
        index: rt(j),
    }
}

/// `out`'s Σ at `j`, taken apart.
fn out_parts(sig: &Rc<MSig>, j: &Term) -> (Level, Level, Rc<Type>, Rc<Type>) {
    match m_out_ty(sig, j) {
        Type::Sigma { fst_level, snd_level, fst, snd } => (fst_level, snd_level, fst, snd),
        _ => unreachable!("m_out_ty builds a Σ"),
    }
}

fn out(sig: &Rc<MSig>, j: Term, m: Term) -> Term {
    Term::Out { sig: Rc::clone(sig), index: rt(j), scrut: rt(m) }
}

/// `fst(out(m))` at `Stream`: the head.
fn hd(m: Term) -> Term {
    let sig = stream();
    let (fst_level, snd_level, fst_ty, snd_ty) = out_parts(&sig, &triv());
    Term::Fst { fst_level, snd_level, fst_ty, snd_ty, pair: rt(out(&sig, triv(), m)) }
}

/// `head, head, …` over the carrier `Unit`: the step is `pair(head; λp.
/// inl ⟨⟩)` at `m_step_ty`'s annotations.
fn constant(head: Term) -> Term {
    let sig = stream();
    let Type::Sigma { fst_level, snd_level, fst: fst_ty, snd: snd_ty } =
        m_step_ty(&sig, &c(0), &unit0()).shift_local(1)
    else {
        unreachable!("m_step_ty builds a Σ")
    };
    let Type::Pi { dom_level, cod_level, dom, cod } = snd_ty.inst_top(0, &head) else {
        unreachable!("the step's second component is a Π")
    };
    let Type::Sum { lhs_level, rhs_level, lhs, rhs } = (*cod).clone() else {
        unreachable!("a child is a sum")
    };
    let kid = Term::Inl { lhs_level, rhs_level, lhs, rhs, val: rt(triv()) };
    let step = Term::Pair {
        fst_level,
        snd_level,
        fst_ty,
        snd_ty,
        fst: rt(head),
        snd: rt(Term::Lam { dom_level, cod_level, dom, body: rt(kid) }),
    };
    Term::Corec {
        sig,
        carrier_level: c(0),
        carrier: rty(unit0()),
        step: rt(step),
        index: rt(triv()),
        seed: rt(triv()),
    }
}

fn zeros() -> Term {
    constant(nat(0))
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
// The code and its `El` decoding (design §1)
// -------------------------------------------------------------------------

#[test]
fn codes_check_and_decode() {
    // Closed, at a literal index: TmM(…) : Ty 0, and El of it is Stream.
    let code = stream_code();
    check_tm_at(Layer::Code, &nil_ctx(), &code, &Type::Ty(c(0)), &c(1)).expect("the Stream code checks at c");
    assert!(conv_ty(&nil_ctx(), &el(code.clone()), &stream_ty()), "El(Stream code) ⇝ Stream");
    let w = whnf_type(&el(code), &nil_ctx(), FUEL).expect("enough fuel");
    assert!(matches!(w, Type::M { .. }), "El(TmM) reduces to M");

    // A neutral index: Γ = (j : Nat), El(From code at j) is From(j), and not
    // From(S j).
    let g = ext(&nil_ctx(), Type::Nat, c(0));
    let code = from_code(v(0));
    check_tm_at(Layer::Code, &g, &code, &Type::Ty(c(0)), &c(1)).expect("the From code checks at c");
    assert!(conv_ty(&g, &el(code.clone()), &from_sig().at(rt(v(0)))), "El(From code) ⇝ From(j)");
    assert!(!conv_ty(&g, &el(code), &from_sig().at(rt(Term::Succ(rt(v(0)))))), "From(j) is not From(S j)");

    // A neutral piece: Γ = (u : Ty 0), shapes coded by `u` (under `i`, so
    // `Var(1)`): the decoding reads `El u` for the shapes.
    let g = ext(&nil_ctx(), Type::Ty(c(0)), c(1));
    let code = stream_code_at(v(1), triv());
    check_tm_at(Layer::Code, &g, &code, &Type::Ty(c(0)), &c(1)).expect("a neutral shape code checks");
    let decoded = Rc::new(MSig { shape: rty(el(v(1))), ..(*stream()).clone() }).at(rt(triv()));
    assert!(conv_ty(&g, &el(code.clone()), &decoded), "El(TmM(u…)) ⇝ M(…; El u; …)");
    assert!(!conv_ty(&g, &el(code), &stream_ty()), "a neutral shape is not Nat");
}

#[test]
fn ill_formed_codes_are_refused() {
    // An index that is not in the decoded index type.
    let bad_index = stream_code_at(Term::TmNat, nat(0));
    assert!(check_tm_at(Layer::Code, &nil_ctx(), &bad_index, &Type::Ty(c(0)), &c(1)).is_err());
    // A piece that is not a code.
    let bad_piece = stream_code_at(nat(0), triv());
    assert!(check_tm_at(Layer::Code, &nil_ctx(), &bad_piece, &Type::Ty(c(0)), &c(1)).is_err());
    // The level is the family's: not Ty 1.
    assert!(check_tm_at(Layer::Code, &nil_ctx(), &stream_code(), &Type::Ty(c(1)), &c(2)).is_err());
}

// -------------------------------------------------------------------------
// Layer c (design §0)
// -------------------------------------------------------------------------

#[test]
fn m_and_its_terms_are_admitted_at_layer_c() {
    let ty = stream_ty();
    check_ty_at(Layer::Code, &nil_ctx(), &ty, &c(0)).expect("M at c");
    check_tm_at(Layer::Code, &nil_ctx(), &zeros(), &ty, &c(0)).expect("corec at c");
    check_tm_at(Layer::Code, &nil_ctx(), &hd(zeros()), &Type::Nat, &c(0)).expect("out at c");
    // Layer v still admits only variables.
    assert_eq!(check_tm_at(Layer::Var, &nil_ctx(), &zeros(), &ty, &c(0)), Err(TypeError::LayerMismatch));
    assert_eq!(check_tm_at(Layer::Var, &nil_ctx(), &stream_code(), &Type::Ty(c(0)), &c(1)), Err(TypeError::LayerMismatch));
}

#[test]
fn a_boxed_corec_is_inert() {
    // Outside a box, hd(zeros) computes to 0 (the positive control) …
    let psi = GlobalCtx::default();
    conv_term(&psi, &nil_ctx(), Layer::Prog, &hd(zeros()), &nat(0), &Type::Nat, &c(0), FUEL)
        .expect("hd(zeros) ≡ 0");
    // … and inside one it is syntax: box(hd(zeros)) is not box(0), and two
    // corecs of one stream are two codes.
    let code_ty = Type::CodeTm { ctx: nil_ctx(), ty: rty(Type::Nat), level: c(0) };
    let boxed = |t: Term| Term::BoxTm(rt(t));
    for t in [hd(zeros()), nat(0)] {
        check_tm_at(Layer::Meta, &nil_ctx(), &boxed(t), &code_ty, &c(0)).expect("the box checks");
    }
    assert!(conv_term(&psi, &nil_ctx(), Layer::Meta, &boxed(hd(zeros())), &boxed(nat(0)), &code_ty, &c(0), FUEL).is_err());
    let stream_code_ty = Type::CodeTm { ctx: nil_ctx(), ty: rty(stream_ty()), level: c(0) };
    let ones = constant(nat(1));
    assert!(
        conv_term(&psi, &nil_ctx(), Layer::Meta, &boxed(zeros()), &boxed(ones), &stream_code_ty, &c(0), FUEL).is_err()
    );
    conv_term(&psi, &nil_ctx(), Layer::Meta, &boxed(zeros()), &boxed(zeros()), &stream_code_ty, &c(0), FUEL)
        .expect("a box is its own code");
}

// -------------------------------------------------------------------------
// The identity recursor rebuilds every form (design §2, §4)
// -------------------------------------------------------------------------

fn identity_ty(gamma: &LocalCtx, code: Type) {
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
    check_term(&GlobalCtx::default(), 0, Layer::Meta, gamma, &t, &expect, &c(0), FUEL)
        .unwrap_or_else(|e| panic!("identity elim^Typ ill-typed on {code:?}: {e:?}"));
    let w = whnf_term(&t, gamma, FUEL).expect("identity elim^Typ exhausted fuel");
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
fn identity_recursor_round_trips_m_types() {
    identity_ty(&nil_ctx(), stream_ty());
    // The index and shapes of From are under binders and the index computes.
    identity_ty(&nil_ctx(), from_sig().at(rt(nat(2))));
}

#[test]
fn identity_recursor_round_trips_the_code() {
    identity_tm(stream_code(), Type::Ty(c(0)), c(1));
    identity_tm(from_code(nat(2)), Type::Ty(c(0)), c(1));
}

#[test]
fn identity_recursor_round_trips_corec_and_out() {
    // tm_corec, the widest telescope: nine globals, the step at m_step_ty.
    identity_tm(zeros(), stream_ty(), c(0));
    identity_tm(out(&stream(), triv(), zeros()), m_out_ty(&stream(), &triv()), c(0));
    // Nested: tm_fst around tm_out around tm_corec.
    identity_tm(hd(zeros()), Type::Nat, c(0));
}

/// A branch whose box is well-scoped but the wrong code poisons the whole
/// recursor, whichever code it is run on.
#[test]
fn a_wrong_new_branch_poisons_the_recursor() {
    let mut bad = (*identity_branches()).clone();
    bad.tm_corec = rt(Term::BoxTm(rt(Term::Zero)));
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
        "a mismatched tm_corec branch must be rejected"
    );
}

// -------------------------------------------------------------------------
// Coverage: the well-typed generator reaches the code
// -------------------------------------------------------------------------

/// The property suites drive the new branches and `TmM`'s congruence only
/// if `wt.rs` produces the code; this pins that it does.
#[test]
fn the_well_typed_generator_reaches_the_m_code() {
    fn in_tm(t: &Term) -> bool {
        match t {
            Term::TmM { .. } => true,
            Term::TmPi { dom, cod, .. } => in_tm(dom) || in_tm(cod),
            Term::TmSigma { fst, snd, .. } => in_tm(fst) || in_tm(snd),
            Term::TmSum { lhs, rhs, .. } => in_tm(lhs) || in_tm(rhs),
            Term::TmW { shape, pos, .. } => in_tm(shape) || in_tm(pos),
            Term::TmId { ty, .. } => in_tm(ty),
            _ => false,
        }
    }
    let mut r = Rng::new(11);
    let mut hits = 0;
    for _ in 0..200 {
        let env = gen_wt_env(&mut r);
        if in_tm(&gen_encoding(&env, &mut r, 4).0) {
            hits += 1;
        }
    }
    assert!(hits > 5, "generated M codes only {hits}/200 times");
}
