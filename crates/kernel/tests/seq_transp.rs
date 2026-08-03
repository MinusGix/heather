//! `sEq`/`srefl`/`transp`: step 3 of the SProp landing
//! (`docs/sprop-design.md` §8, `issues/sprop-strict-prop.md`).
//!
//! The round's whole content is three conversion behaviours — the
//! irrelevance arm at `sEq`, the strip rule for stuck `transp`s at
//! convertible endpoints, and the endpoint-keyed congruence that skips
//! proofs — plus a β that is ordinary. The tests vary the four axes of
//! `docs/testing-generated-terms.md`: the proof is exercised *literal*
//! (`srefl`, β) and *neutral* (a hypothesis, strip); the endpoints are
//! *open* (`plus0(n)` vs `n` with `n` a variable — convertible, not
//! syntactically equal); the strip is exercised in a *checking* position
//! (`check_term` against the stripped type, `srefl` against convertible
//! endpoints) and not only via `conv_term`; and every positive behaviour
//! has a *negative control* (distinct neutral endpoints do not strip,
//! `srefl` does not check at genuinely different endpoints, the guard's
//! failure is `NotConvertible`-caught but `OutOfFuel`-propagated).

mod common;

use std::rc::Rc;

use common::Rng;
use heather_kernel::conv::{conv_term, conv_type, ConvError};
use heather_kernel::layer::Layer;
use heather_kernel::level::Level;
use heather_kernel::reduce::whnf_term;
use heather_kernel::term::{
    CtxBase, CtxEntry, GlobalCtx, LocalCtx, LocalSubst, LocalVar, SubstTail, Term, Type,
};
use heather_kernel::typing::{check_term, check_type, infer_term};

const FUEL: u64 = 100_000;

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
    LocalCtx { base: CtxBase::Nil, entries: vec![] }
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

fn seq(ty: Type, lhs: Term, rhs: Term) -> Type {
    Type::SEq { level: c(0), ty: rty(ty), lhs: rt(lhs), rhs: rt(rhs) }
}

fn srefl(ty: Type, tm: Term) -> Term {
    Term::SRefl { level: c(0), ty: rty(ty), tm: rt(tm) }
}

/// `transp^{0,0}(Nat; x.P; a; b; e; t)`.
fn transp(motive: Type, lhs: Term, rhs: Term, proof: Term, tm: Term) -> Term {
    Term::Transp {
        ty_level: c(0),
        motive_level: c(0),
        ty: rty(Type::Nat),
        motive: rty(motive),
        lhs: rt(lhs),
        rhs: rt(rhs),
        proof: rt(proof),
        tm: rt(tm),
    }
}

fn vec_nat(len: Term) -> Type {
    Type::Vec { level: c(0), elem: rty(Type::Nat), len: rt(len) }
}

/// `plus0(k)` := `elim_Nat^0(x.Nat; k; x ih. S ih; 0)` — reduces to `k`
/// (the base) on the literal scrutinee `0`, but is not syntactically `k`.
/// The canonical "convertible, not equal" endpoint pair of the design doc.
fn plus0(k: Term) -> Term {
    Term::ElimNat {
        level: c(0),
        motive: rty(Type::Nat),
        base: rt(k),
        step: rt(Term::Succ(rt(v(0)))),
        scrut: rt(Term::Zero),
    }
}

fn ck_ty(gamma: &LocalCtx, t: &Type, level: Level) {
    check_type(&GlobalCtx::default(), 0, Layer::Prog, gamma, t, &level, FUEL)
        .unwrap_or_else(|e| panic!("type does not check: {e:?}"));
}

fn ck(gamma: &LocalCtx, t: &Term, ty: &Type, level: Level) {
    ck_ty(gamma, ty, level.clone());
    check_term(&GlobalCtx::default(), 0, Layer::Prog, gamma, t, ty, &level, FUEL)
        .unwrap_or_else(|e| panic!("term does not check: {e:?}"));
}

fn no_ck(gamma: &LocalCtx, t: &Term, ty: &Type, level: Level) {
    check_term(&GlobalCtx::default(), 0, Layer::Prog, gamma, t, ty, &level, FUEL)
        .expect_err("expected ill-typed");
}

fn conv_ty(gamma: &LocalCtx, a: &Type, b: &Type, level: Level) {
    conv_type(&GlobalCtx::default(), gamma, Layer::Prog, a, b, &level, FUEL)
        .unwrap_or_else(|e| panic!("types not convertible: {e:?}"));
}

fn conv_tm(gamma: &LocalCtx, a: &Term, b: &Term, ty: &Type, level: Level) {
    conv_term(&GlobalCtx::default(), gamma, Layer::Prog, a, b, ty, &level, FUEL)
        .unwrap_or_else(|e| panic!("terms not convertible: {e:?}"));
}

fn not_conv_tm(gamma: &LocalCtx, a: &Term, b: &Term, ty: &Type, level: Level) {
    conv_term(&GlobalCtx::default(), gamma, Layer::Prog, a, b, ty, &level, FUEL)
        .expect_err("expected inconvertible");
}

/// `Γ = n : Nat, e : sEq(Nat; plus0(n); n), t : Vec(Nat; plus0(n))` — the
/// strip scenario: a *neutral* proof whose endpoints are convertible but
/// not syntactically equal, and a payload at the motive over the left
/// endpoint. In this context: `n = v(2)`, `e = v(1)`, `t = v(0)`.
fn strip_ctx() -> LocalCtx {
    let g = ext(&nil_ctx(), Type::Nat, c(0));
    let g = ext(&g, seq(Type::Nat, plus0(v(0)), v(0)), c(0));
    ext(&g, vec_nat(plus0(v(1))), c(0))
}

// -------------------------------------------------------------------------
// Reduction: β on srefl, and nothing else
// -------------------------------------------------------------------------

#[test]
fn transp_beta_fires_on_srefl() {
    // transp(Nat; x.Nat; 0; 0; srefl(Nat; 0); 42) ⇝ 42, closed.
    let t = transp(Type::Nat, nat(0), nat(0), srefl(Type::Nat, nat(0)), nat(42));
    assert_eq!(whnf_term(&t, &nil_ctx(), FUEL).expect("fuel"), nat(42));
}

#[test]
fn transp_is_reduction_stuck_on_a_neutral_proof() {
    // Reduction (as opposed to conversion) must NOT strip: with e neutral
    // the transp is a whnf, whatever its endpoints. The strip is conv.rs's
    // business — that separation is the withdrawn "punctures" claim.
    let g = strip_ctx();
    let t = transp(vec_nat(v(0)), plus0(v(2)), v(2), v(1), v(0));
    assert_eq!(whnf_term(&t, &g, FUEL).expect("fuel"), t);
}

// -------------------------------------------------------------------------
// The strip rule
// -------------------------------------------------------------------------

#[test]
fn strip_fires_on_a_neutral_proof_at_convertible_endpoints() {
    // transp(Nat; x.Vec(Nat;x); plus0(n); n; e; t) ≡ t at Vec(Nat; n):
    // the endpoints convert (plus0(n) ⇝ n) without being syntactically
    // equal, so the fast path misses and the guarded query decides.
    let g = strip_ctx();
    let t = transp(vec_nat(v(0)), plus0(v(2)), v(2), v(1), v(0));
    ck(&g, &t, &vec_nat(v(2)), c(0));
    conv_tm(&g, &t, &v(0), &vec_nat(v(2)), c(0));
    // Symmetric: the stripped side on the right.
    conv_tm(&g, &v(0), &t, &vec_nat(v(2)), c(0));
}

#[test]
fn strip_is_invisible_in_a_checking_position() {
    // The transp synthesizes P[b] = Vec(Nat; n); checking it against the
    // *left* endpoint's instance Vec(Nat; plus0(n)) crosses the strip-
    // adjacent type equation P[a] ≡ P[b] in tm_check's conversion — the
    // checking-position axis, not just conv_term.
    let g = strip_ctx();
    let t = transp(vec_nat(v(0)), plus0(v(2)), v(2), v(1), v(0));
    ck(&g, &t, &vec_nat(plus0(v(2))), c(0));
    // And the payload variable itself checks at the transported type.
    ck(&g, &v(0), &vec_nat(v(2)), c(0));
}

#[test]
fn negative_control_distinct_endpoints_do_not_strip() {
    // Γ = m, n : Nat, e : sEq(Nat; m; n), t : Nat. The endpoints are
    // genuinely different neutrals: transp(e; t) is honestly stuck and NOT
    // convertible with its payload.
    let g = ext(&nil_ctx(), Type::Nat, c(0));
    let g = ext(&g, Type::Nat, c(0));
    let g = ext(&g, seq(Type::Nat, v(1), v(0)), c(0));
    let g = ext(&g, Type::Nat, c(0));
    // m = v(3), n = v(2), e = v(1), t = v(0).
    let t = transp(Type::Nat, v(3), v(2), v(1), v(0));
    ck(&g, &t, &Type::Nat, c(0));
    not_conv_tm(&g, &t, &v(0), &Type::Nat, c(0));
}

#[test]
fn congruence_skips_the_proofs() {
    // Two stuck transps over *different* neutral proofs are convertible:
    // the tm_ne arm compares I, P, a, b, t and deliberately not e — the
    // inversion of J's discipline, justified by the irrelevance arm.
    let g = ext(&nil_ctx(), Type::Nat, c(0));
    let g = ext(&g, Type::Nat, c(0));
    let g = ext(&g, seq(Type::Nat, v(1), v(0)), c(0));
    let g = ext(&g, seq(Type::Nat, v(2), v(1)), c(0));
    let g = ext(&g, Type::Nat, c(0));
    // m = v(4), n = v(3), e1 = v(2), e2 = v(1), t = v(0).
    let t1 = transp(Type::Nat, v(4), v(3), v(2), v(0));
    let t2 = transp(Type::Nat, v(4), v(3), v(1), v(0));
    conv_tm(&g, &t1, &t2, &Type::Nat, c(0));
}

#[test]
fn nested_transps_strip_iteratively() {
    // A transp whose payload is itself a strippable transp: the loop
    // strips, re-whnfs, and strips again — termination is the payload
    // being a strict subterm. The outer transports back along a reversed
    // hypothesis (irrelevance does not make `e` bidirectional; its *type*
    // fixes the direction, so the reverse is its own hypothesis).
    // strip_ctx + e_rev : sEq(Nat; n; plus0(n)); then n = v(3), e = v(2),
    // t = v(1), e_rev = v(0).
    let g = ext(&strip_ctx(), seq(Type::Nat, v(2), plus0(v(2))), c(0));
    let inner = transp(vec_nat(v(0)), plus0(v(3)), v(3), v(2), v(1));
    let outer = transp(vec_nat(v(0)), v(3), plus0(v(3)), v(0), inner);
    ck(&g, &outer, &vec_nat(plus0(v(3))), c(0));
    conv_tm(&g, &outer, &v(1), &vec_nat(plus0(v(3))), c(0));
}

// -------------------------------------------------------------------------
// Irrelevance
// -------------------------------------------------------------------------

#[test]
fn any_two_proofs_are_convertible() {
    // Γ = n : Nat, p q : sEq(Nat; n; n): p ≡ q, p ≡ srefl(n) — UIP is the
    // irrelevance arm firing, not a theorem.
    let g = ext(&nil_ctx(), Type::Nat, c(0));
    let g = ext(&g, seq(Type::Nat, v(0), v(0)), c(0));
    let g = ext(&g, seq(Type::Nat, v(1), v(1)), c(0));
    // n = v(2), p = v(1), q = v(0).
    let ty = seq(Type::Nat, v(2), v(2));
    conv_tm(&g, &v(1), &v(0), &ty, c(0));
    conv_tm(&g, &v(1), &srefl(Type::Nat, v(2)), &ty, c(0));
}

#[test]
fn pi_closure_of_irrelevance_is_a_theorem() {
    // Γ = f g : Π(x:Nat). sEq(Nat; x; x): f ≡ g with *no* new conversion
    // code — Π-η compares applications at the codomain, where the sEq arm
    // accepts. The design doc §1's derived closure, pinned.
    let pi = Type::Pi {
        dom_level: c(0),
        cod_level: c(0),
        dom: rty(Type::Nat),
        cod: rty(seq(Type::Nat, v(0), v(0))),
    };
    let g = ext(&nil_ctx(), pi.clone(), c(0));
    let g = ext(&g, pi.clone(), c(0));
    conv_tm(&g, &v(1), &v(0), &pi, c(0));
}

#[test]
fn srefl_checks_against_convertible_endpoints() {
    // srefl synthesizes sEq(I; a; a); checking against sEq(I; plus0(n); n)
    // goes through the sEq *type* congruence on the endpoints — the
    // checking-position axis for the intro form.
    let g = ext(&nil_ctx(), Type::Nat, c(0));
    ck(&g, &srefl(Type::Nat, v(0)), &seq(Type::Nat, plus0(v(0)), v(0)), c(0));
    // Negative control: genuinely different endpoints reject it.
    let g2 = ext(&g, Type::Nat, c(0));
    no_ck(&g2, &srefl(Type::Nat, v(0)), &seq(Type::Nat, v(1), v(0)), c(0));
}

// -------------------------------------------------------------------------
// Derived checks (design doc §5.4)
// -------------------------------------------------------------------------

#[test]
fn vec_at_a_transported_length_strips() {
    // Vec(Nat; transp(e; n)) ≡ Vec(Nat; n): stuck type-level reduction on
    // both sides, neutral-Vec congruence compares lengths *as terms*, and
    // the strip fires there. No type-level strip rule exists or is needed.
    let g = strip_ctx();
    let len = transp(Type::Nat, plus0(v(2)), v(2), v(1), v(2));
    conv_ty(&g, &vec_nat(len), &vec_nat(v(2)), c(0));
}

// -------------------------------------------------------------------------
// The head-only strip gap at the type formers — negatives pinning a known
// INCOMPLETENESS, not desired behaviour
// (`docs/metatheory-ch07-extensions.md` §22.4,
//  `issues/seq-strip-type-former-negatives.md`,
//  `docs/sprop-design.md` §5.4's correction)
// -------------------------------------------------------------------------
//
// The specification's `⇝ₛ` (§19.1) strips wherever ch. 06's evaluation
// contexts look for a redex, which includes a `Vec`/`Fin` length and an `El`
// code; the algorithm strips only at the outermost head of a compared term
// (`Conv::strip`, called from `Conv::tm_w`), and `reduce.rs` is strip-blind.
// So a `transp` at convertible endpoints whose *payload is canonical* keeps
// a type-former's index neutral — `is_neutral_term(Transp{proof,..})` follows
// the proof — while the payload's own instance reduces away. `ty_nf` then
// compares a neutral view against a canonical one and rejects a pair the
// declarative system (§18's strip rule under the `Vec`/`Fin`/`El`
// congruences) equates.
//
// The three tests below assert that rejection. They are pinning the gap so it
// cannot close or widen silently; a failure here means the kernel started
// accepting, which is a *discovery* about §22.4 and not a broken test. The
// direction of the incompleteness is the safe one: never an unsound accept,
// never non-termination (§22.3).
//
// Each pairs the negative with the positive it is the shadow of: the very same
// length/code, compared *as a term*, does strip — the head is where the
// algorithm looks. The gap is positional, not about the terms.

/// `Γ = n : Nat, e : sEq(Nat; plus0(n); n)` with a *canonical* payload: the
/// axis `vec_at_a_transported_length_strips` misses, whose length is a context
/// variable so both sides stay neutral `Vec`s
/// (`docs/testing-generated-terms.md`'s first axis).
fn canonical_payload_ctx() -> LocalCtx {
    let g = ext(&nil_ctx(), Type::Nat, c(0));
    ext(&g, seq(Type::Nat, plus0(v(0)), v(0)), c(0))
}

/// `transp(Nat; x.Nat; plus0(n); n; e; 0)` in [`canonical_payload_ctx`] —
/// stuck (its proof `e = v(0)` is neutral), convertible to `0` at the head,
/// and *canonical* underneath the strip the algorithm will not perform in an
/// index position.
fn transported_zero() -> Term {
    transp(Type::Nat, plus0(v(1)), v(1), v(0), nat(0))
}

#[test]
fn vec_at_a_transported_canonical_length_does_not_strip() {
    // §22.4's first bullet, and item 1 of issues/seq-strip-type-former-negatives.
    let g = canonical_payload_ctx();
    let len = transported_zero();
    ck(&g, &len, &Type::Nat, c(0));

    // The positive it shadows: at the head, the strip fires, so the two
    // lengths are convertible *as terms* and the two `Vec`s are declaratively
    // convertible by the `Vec` congruence.
    conv_tm(&g, &len, &nat(0), &Type::Nat, c(0));

    // The pinned incompleteness: `Vec(Nat; 0) ⇝ Unit^0` while
    // `Vec(Nat; transp(…; 0))` is a whnf neutral type, so `ty_nf` sees
    // Vec-vs-Unit and rejects. NOT desired behaviour — see the section note.
    conv_type(&GlobalCtx::default(), &g, Layer::Prog, &vec_nat(len.clone()), &vec_nat(nat(0)), &c(0), FUEL)
        .expect_err("§22.4 gap closed: the kernel now accepts Vec(T; transp(e;0)) ≡ Vec(T; 0)");
    // Same rejection against the reduct the right-hand side has, stated in
    // §22.4's own words (`Vec^l(T; transp(…;e;ze))` against `Unit^l`).
    conv_type(&GlobalCtx::default(), &g, Layer::Prog, &vec_nat(len), &Type::Unit { level: c(0) }, &c(0), FUEL)
        .expect_err("§22.4 gap closed at Vec-vs-Unit");
}

#[test]
fn fin_at_a_transported_canonical_length_does_not_strip() {
    // §22.4's second bullet at `Fin`, and item 2 of the issue: the *same*
    // cause (a strip-blind length stepper plus `is_neutral_term` following the
    // proof) in a second type-former position, so "one cause, three positions"
    // stays pinned from more than one angle.
    let g = canonical_payload_ctx();
    let len = transported_zero();
    let fin = Type::Fin { len: rt(len.clone()) };
    ck_ty(&g, &fin, c(0));
    conv_tm(&g, &len, &nat(0), &Type::Nat, c(0));

    conv_type(&GlobalCtx::default(), &g, Layer::Prog, &fin, &Type::Fin { len: rt(nat(0)) }, &c(0), FUEL)
        .expect_err("§22.4 gap closed: the kernel now accepts Fin(transp(e;0)) ≡ Fin(0)");
    conv_type(&GlobalCtx::default(), &g, Layer::Prog, &fin, &Type::Empty { level: c(0) }, &c(0), FUEL)
        .expect_err("§22.4 gap closed at Fin-vs-Empty");
}

#[test]
fn el_at_a_transported_canonical_code_does_not_strip() {
    // The third position of §22.4, and the one whose mechanism differs: the
    // index here is a *code*, `El`'s decoding is what the strip would unblock,
    // and the whole configuration sits one universe level up
    // (`sEq^1(Ty 0; …)`, a large elimination for the stuck endpoint).
    //
    // Γ = A : Ty 0 @ 1, e : sEq^1(Ty 0; code_plus0(A); A) @ 1 — endpoints
    // convertible (`code_plus0` reduces to its base) and stuck; the payload
    // `TmNat` is canonical.
    let ty0 = Type::Ty(c(0));
    let code_plus0 = |a: Term| Term::ElimNat {
        level: c(1),
        motive: rty(ty0.clone()),
        base: rt(a),
        step: rt(v(0)), // x ih. ih
        scrut: rt(Term::Zero),
    };
    let g = ext(&nil_ctx(), ty0.clone(), c(1));
    let g = ext(
        &g,
        Type::SEq { level: c(1), ty: rty(ty0.clone()), lhs: rt(code_plus0(v(0))), rhs: rt(v(0)) },
        c(1),
    );
    // A = v(1), e = v(0).
    let code = Term::Transp {
        ty_level: c(1),
        motive_level: c(1),
        ty: rty(ty0.clone()),
        motive: rty(ty0.clone()),
        lhs: rt(code_plus0(v(1))),
        rhs: rt(v(1)),
        proof: rt(v(0)),
        tm: rt(Term::TmNat),
    };
    ck(&g, &code, &ty0, c(1));

    // The positive it shadows: as a *term* at `Ty 0` the code strips to
    // `TmNat`, so `El` of the two is declaratively convertible.
    conv_tm(&g, &code, &Term::TmNat, &ty0, c(1));

    let el = Type::El { level: c(0), tm: rt(code) };
    ck_ty(&g, &el, c(0));
    conv_type(&GlobalCtx::default(), &g, Layer::Prog, &el, &Type::Nat, &c(0), FUEL)
        .expect_err("§22.4 gap closed: the kernel now accepts El(transp(e;TmNat)) ≡ Nat");
    conv_type(
        &GlobalCtx::default(),
        &g,
        Layer::Prog,
        &el,
        &Type::El { level: c(0), tm: rt(Term::TmNat) },
        &c(0),
        FUEL,
    )
    .expect_err("§22.4 gap closed at El-vs-El");
}

#[test]
fn transp_synthesizes_the_right_endpoint_instance() {
    let g = strip_ctx();
    let t = transp(vec_nat(v(0)), plus0(v(2)), v(2), v(1), v(0));
    let (ty, l) = infer_term(&GlobalCtx::default(), 0, Layer::Prog, &g, &t, FUEL)
        .expect("transp infers");
    assert_eq!(ty, vec_nat(v(2)));
    assert_eq!(l, c(0));
}

// -------------------------------------------------------------------------
// Guard semantics: budget behaviour
// -------------------------------------------------------------------------

#[test]
fn guard_exhaustion_is_out_of_fuel_never_a_verdict() {
    // The one observable of the settled failure semantics: on a pair that
    // IS convertible (via the strip), every insufficient budget must die
    // as OutOfFuel — a caught guard failure wrongly treated as a verdict
    // would surface as NotConvertible at some budget below the threshold.
    let g = strip_ctx();
    let t = transp(vec_nat(v(0)), plus0(v(2)), v(2), v(1), v(0));
    let mut succeeded = false;
    for fuel in 0..200 {
        match conv_term(
            &GlobalCtx::default(),
            &g,
            Layer::Prog,
            &t,
            &v(0),
            &vec_nat(v(2)),
            &c(0),
            fuel,
        ) {
            Ok(()) => {
                succeeded = true;
            }
            Err(ConvError::OutOfFuel) => {
                assert!(!succeeded, "fuel is monotone: no failure after a success");
            }
            Err(ConvError::NotConvertible) => {
                panic!("budget death leaked as a verdict at fuel {fuel}");
            }
        }
    }
    assert!(succeeded, "200 fuel is enough for the strip scenario");
}

// -------------------------------------------------------------------------
// sEmpty (design doc §2.2)
// -------------------------------------------------------------------------

fn sempty() -> Type {
    Type::SEmpty { level: c(0) }
}

#[test]
fn sempty_proofs_are_irrelevant_where_empty_neutrals_are_not() {
    // Two hypotheses at sEmpty are convertible; the same two at Empty are
    // not (structural neutrals) — the §2.2 contrast that priced the
    // Empty-reuse alternative, pinned so the two formers cannot drift
    // together silently.
    let g = ext(&nil_ctx(), sempty(), c(0));
    let g = ext(&g, sempty(), c(0));
    conv_tm(&g, &v(1), &v(0), &sempty(), c(0));
    let h = ext(&nil_ctx(), Type::Empty { level: c(0) }, c(0));
    let h = ext(&h, Type::Empty { level: c(0) }, c(0));
    not_conv_tm(&h, &v(1), &v(0), &Type::Empty { level: c(0) }, c(0));
}

#[test]
fn elim_sempty_congruence_skips_the_scrutinees() {
    // Two stuck elim_sEmptys over different absurdity hypotheses are
    // convertible: the tm_ne arm compares levels and motive, and skips
    // the scrutinees (they sit at an irrelevant type).
    let g = ext(&nil_ctx(), sempty(), c(0));
    let g = ext(&g, sempty(), c(0));
    let e1 = Term::ElimSEmpty {
        level: c(0),
        scrut_level: c(0),
        motive: rty(Type::Nat),
        scrut: rt(v(1)),
    };
    let e2 = Term::ElimSEmpty {
        level: c(0),
        scrut_level: c(0),
        motive: rty(Type::Nat),
        scrut: rt(v(0)),
    };
    ck(&g, &e1, &Type::Nat, c(0));
    conv_tm(&g, &e1, &e2, &Type::Nat, c(0));
    // No β: the eliminator is a whnf on a neutral scrutinee.
    assert_eq!(whnf_term(&e1, &g, FUEL).expect("fuel"), e1);
}

#[test]
fn elim_sempty_eliminates_anywhere() {
    // "Eliminates anywhere": a large elimination — motive Ty 0 at level 1
    // — checks. (SProp inductives otherwise eliminate into props only;
    // sEmpty and sEq's transp are the two exceptions, issue decision 3.)
    let g = ext(&nil_ctx(), sempty(), c(0));
    let e = Term::ElimSEmpty {
        level: c(1),
        scrut_level: c(0),
        motive: rty(Type::Ty(c(0))),
        scrut: rt(v(0)),
    };
    ck(&g, &e, &Type::Ty(c(0)), c(1));
}

// -------------------------------------------------------------------------
// Layer c (gate lifted with the rec.rs round; design doc §8 step 5)
// -------------------------------------------------------------------------

#[test]
fn seq_family_is_code() {
    // With TmSEq/TmSEmpty and the seven rec.rs branches landed, the phase
    // gate is gone: the family checks at layer c (and still at m), so the
    // formers can appear inside boxed code and stay recursable.
    let g = ext(&nil_ctx(), Type::Nat, c(0));
    let ty = seq(Type::Nat, v(0), v(0));
    for layer in [Layer::Code, Layer::Meta] {
        check_type(&GlobalCtx::default(), 0, layer, &g, &ty, &c(0), FUEL)
            .unwrap_or_else(|e| panic!("sEq must check at {layer:?}: {e:?}"));
        check_term(&GlobalCtx::default(), 0, layer, &g, &srefl(Type::Nat, v(0)), &ty, &c(0), FUEL)
            .unwrap_or_else(|e| panic!("srefl must check at {layer:?}: {e:?}"));
        check_type(&GlobalCtx::default(), 0, layer, &nil_ctx(), &sempty(), &c(0), FUEL)
            .unwrap_or_else(|e| panic!("sEmpty must check at {layer:?}: {e:?}"));
    }
    // Layer v still rejects (only variables live there).
    check_term(
        &GlobalCtx::default(),
        0,
        Layer::Var,
        &g,
        &srefl(Type::Nat, v(0)),
        &ty,
        &c(0),
        FUEL,
    )
    .expect_err("srefl is not a layer-v form");
}

// -------------------------------------------------------------------------
// The two `⇝ₛ` lemmas of `docs/metatheory-ch07-extensions.md` §19
// -------------------------------------------------------------------------
//
// §19.1 defines the strip-aware reduction `⇝ₛ` as ch. 06's reduction plus one
// rule — `transp^{l,l'}(I; x.P; a; b; e; t) ⇝ₛ t` when `Γ ⊢ a ≈ b : I @ l` —
// with the congruence rule that reduces a `transp`'s *proof* restricted to the
// complementary side condition `Γ ⊬ a ≈ b`. Two lemmas about that notion are
// checked below, on generated instances rather than on a hand case, because
// both are statements about a *family* of substitutions and side conditions:
//
// - §19.4, the one lemma of the round that genuinely weakens: reduction no
//   longer *commutes* with substitution (a `δ` can make `a[δ] ≈ b[δ]` and so
//   invalidate the congruence step's side condition), it only *joins*;
// - §19.3, determinacy: the strip and the proof congruence can never both
//   apply, and on well-typed terms the strip subsumes `transp`-β.
//
// Which side of §22.4's line these sit on: the *algorithm*. `reduce.rs` is
// strip-blind and applies the proof congruence unconditionally, and
// `Conv::strip` performs the strip at the outermost head only, so the joins
// these tests observe are observed through **conversion** — the only place the
// kernel exposes `⇝ₛ` at all. A common `⇝ₛ`-reduct is therefore checked as
// "both sides convert to the payload, and to each other".
//
// Failure reporting is seed-only, as in `subst_laws.rs`'s `law!` macro: a
// substituted kernel term is not something to Debug-format into a panic
// message 200 times.

const CASES: u64 = 200;

fn succs(n: u32, mut t: Term) -> Term {
    for _ in 0..n {
        t = Term::Succ(rt(t));
    }
    t
}

/// `(λ y : T. y) p` — a β-redex at `T`. Giving a `transp`'s proof a
/// *reducible* face without changing what it proves is what makes the
/// congruence rule of §19.1 applicable at all.
fn id_app(ty: Type, arg: Term) -> Term {
    Term::App {
        fun: rt(Term::Lam {
            dom_level: c(0),
            cod_level: c(0),
            dom: rty(ty.clone()),
            body: rt(v(0)),
        }),
        dom_level: c(0),
        cod_level: c(0),
        dom: rty(ty.clone()),
        cod: rty(ty.shift_local(1)),
        arg: rt(arg),
    }
}

fn ck_seed(seed: u64, gamma: &LocalCtx, t: &Term, ty: &Type) {
    check_type(&GlobalCtx::default(), 0, Layer::Prog, gamma, ty, &c(0), FUEL)
        .unwrap_or_else(|_| panic!("type does not check at seed {seed} (output suppressed)"));
    check_term(&GlobalCtx::default(), 0, Layer::Prog, gamma, t, ty, &c(0), FUEL)
        .unwrap_or_else(|_| panic!("term does not check at seed {seed} (output suppressed)"));
}

fn no_ck_seed(seed: u64, gamma: &LocalCtx, t: &Term, ty: &Type, what: &str) {
    if check_term(&GlobalCtx::default(), 0, Layer::Prog, gamma, t, ty, &c(0), FUEL).is_ok() {
        panic!("{what}: expected ill-typed at seed {seed} (output suppressed)");
    }
}

fn conv_seed(seed: u64, gamma: &LocalCtx, a: &Term, b: &Term, ty: &Type, what: &str) {
    conv_term(&GlobalCtx::default(), gamma, Layer::Prog, a, b, ty, &c(0), FUEL)
        .unwrap_or_else(|_| panic!("{what}: not convertible at seed {seed} (output suppressed)"));
}

fn not_conv_seed(seed: u64, gamma: &LocalCtx, a: &Term, b: &Term, ty: &Type, what: &str) {
    if conv_term(&GlobalCtx::default(), gamma, Layer::Prog, a, b, ty, &c(0), FUEL).is_ok() {
        panic!("{what}: expected inconvertible at seed {seed} (output suppressed)");
    }
}

/// One instance of the family both §19 property tests are stated over. Three
/// contexts of the same shape, two of them images of the first:
///
/// - `apart` = `m, n : Nat, e : sEq(Nat; L(m); R(n)), u : P[L(m)]` — the
///   endpoints are distinct neutrals, so `Γ ⊬ a ≈ b` and it is §19.1's
///   *restricted congruence* rule that applies at the `transp`;
/// - `together` = `n : Nat, e : sEq(Nat; L(n); R(n)), u : P[L(n)]` — the image
///   under `join` (`m ↦ n`), where the endpoints convert, the side condition
///   is flipped, and the strip rule applies instead;
/// - `miss` = `n : Nat, e : sEq(Nat; L(k); R(n)), u : P[L(k)]` — the image
///   under `miss_subst` (`m ↦ k`), a substitution that does *not* flip it.
///
/// `L(x)` is `S^j x` optionally wrapped in `plus0` and `R(x)` is `S^j x`, so
/// `wrap` decides whether `Conv::strip`'s syntactic fast path or its guarded
/// query is the one that decides in `together`. Every endpoint that has to
/// stay apart mentions a variable, so no motive instance ever reduces to
/// `Unit` or to a `Σ`-tuple and the negative controls compare neutrals.
struct Fam {
    apart: LocalCtx,
    together: LocalCtx,
    miss: LocalCtx,
    join: LocalSubst,
    miss_subst: LocalSubst,
    motive: Type,
    j: u32,
    k: u32,
    wrap: bool,
}

impl Fam {
    fn wrapped(&self, t: Term) -> Term {
        if self.wrap {
            plus0(t)
        } else {
            t
        }
    }

    /// `L(x)` at the de Bruijn index `ix`.
    fn lhs(&self, ix: u32) -> Term {
        self.wrapped(succs(self.j, v(ix)))
    }

    /// `L(k)` — the left endpoint at a numeral, for the non-flipping `δ`.
    fn lhs_lit(&self) -> Term {
        self.wrapped(succs(self.j, nat(self.k as u64)))
    }

    /// `R(x)` at the de Bruijn index `ix`.
    fn rhs(&self, ix: u32) -> Term {
        succs(self.j, v(ix))
    }

    /// `P[t/x]`, for `t` scoped in `gamma`.
    fn inst(&self, gamma: &LocalCtx, t: Term) -> Type {
        self.motive.apply_local(&LocalSubst::id(gamma).extended(rt(t)))
    }
}

fn subst_onto(source_len: u32, terms: Vec<Rc<Term>>) -> LocalSubst {
    LocalSubst {
        tail: SubstTail::Empty { len: source_len, base: CtxBase::Nil },
        terms,
    }
}

fn fam(r: &mut Rng) -> Fam {
    let j = r.below(3);
    // k ≥ 1 so that `L(k)` is a numeral distinguishable from a variable at
    // every `j`, which is what keeps `miss` a genuine negative control.
    let k = 1 + r.below(3);
    let wrap = r.below(2) == 1;
    // The motive varies the element/index-type axis of
    // docs/testing-generated-terms.md: a constant motive, one mentioning the
    // bound endpoint, and one mentioning it under a redex.
    let motive = match r.below(3) {
        0 => Type::Nat,
        1 => vec_nat(v(0)),
        _ => vec_nat(plus0(v(0))),
    };
    let mut f = Fam {
        apart: nil_ctx(),
        together: nil_ctx(),
        miss: nil_ctx(),
        join: LocalSubst::id(&nil_ctx()),
        miss_subst: LocalSubst::id(&nil_ctx()),
        motive,
        j,
        k,
        wrap,
    };

    // Γ = m, n : Nat, e : sEq(Nat; L(m); R(n)), u : P[L(m)].
    let g = ext(&nil_ctx(), Type::Nat, c(0));
    let g = ext(&g, Type::Nat, c(0));
    let g = ext(&g, seq(Type::Nat, f.lhs(1), f.rhs(0)), c(0));
    let payload_ty = f.inst(&g, f.lhs(2));
    f.apart = ext(&g, payload_ty, c(0));

    // Γ_join = n : Nat, e : sEq(Nat; L(n); R(n)), u : P[L(n)].
    let h = ext(&nil_ctx(), Type::Nat, c(0));
    let h = ext(&h, seq(Type::Nat, f.lhs(0), f.rhs(0)), c(0));
    let payload_ty = f.inst(&h, f.lhs(1));
    f.together = ext(&h, payload_ty, c(0));

    // Γ_miss = n : Nat, e : sEq(Nat; L(k); R(n)), u : P[L(k)].
    let m = ext(&nil_ctx(), Type::Nat, c(0));
    let m = ext(&m, seq(Type::Nat, f.lhs_lit(), f.rhs(0)), c(0));
    let payload_ty = f.inst(&m, f.lhs_lit());
    f.miss = ext(&m, payload_ty, c(0));

    // Both substitutions target Γ's four entries (m, n, e, u) from a
    // three-entry source (n, e, u); `terms` is outermost-first.
    f.join = subst_onto(3, vec![rt(v(2)), rt(v(2)), rt(v(1)), rt(v(0))]);
    f.miss_subst = subst_onto(3, vec![rt(nat(f.k as u64)), rt(v(2)), rt(v(1)), rt(v(0))]);
    f
}

#[test]
fn substitution_joins_rather_than_commutes_at_a_strip_redex() {
    // §19.4. In `apart` the endpoints are distinct neutrals, so the step the
    // specification licenses at the `transp` is the *restricted congruence*
    // one — reduce the proof, side condition `Γ ⊬ a ≈ b` discharged. Write
    // `t` for the redex face and `t'` for its reduct. Commutation would say
    // `t[δ] ⇝ₛ t'[δ]`; that is false, because `join` makes the endpoints
    // convert and the congruence step's side condition fails on the image.
    // What holds, and what the lemma claims, is that `t[join]` and `t'[join]`
    // have a common `⇝ₛ`-reduct — here `u[join]`, reached by the strip in one
    // step from each. The kernel exposes the join through conversion.
    for seed in 0..CASES {
        let mut r = Rng::new(seed ^ 0x3c79ac492ba7b653);
        let f = fam(&mut r);

        // In Γ: m = v(3), n = v(2), e = v(1), u = v(0).
        let e_ty = seq(Type::Nat, f.lhs(3), f.rhs(2));
        let payload = v(0);
        let ty = f.inst(&f.apart, f.rhs(2));
        let redex =
            transp(f.motive.clone(), f.lhs(3), f.rhs(2), id_app(e_ty, v(1)), payload.clone());
        let reduct = transp(f.motive.clone(), f.lhs(3), f.rhs(2), v(1), payload.clone());
        ck_seed(seed, &f.apart, &redex, &ty);
        ck_seed(seed, &f.apart, &reduct, &ty);
        // The premise of the step: neither face strips in Γ, so the transp is
        // honestly stuck and the congruence rule is the applicable one.
        not_conv_seed(seed, &f.apart, &redex, &payload, &ty, "redex strips in Γ");
        not_conv_seed(seed, &f.apart, &reduct, &payload, &ty, "reduct strips in Γ");

        // The flipping substitution: both images join at `u[δ]`.
        let (a, b) = (redex.apply_local(&f.join), reduct.apply_local(&f.join));
        let u = payload.apply_local(&f.join);
        let ty_j = ty.apply_local(&f.join);
        ck_seed(seed, &f.together, &a, &ty_j);
        ck_seed(seed, &f.together, &b, &ty_j);
        conv_seed(seed, &f.together, &a, &u, &ty_j, "t[δ] ⇝ₛ* u[δ]");
        conv_seed(seed, &f.together, &b, &u, &ty_j, "t'[δ] ⇝ₛ* u[δ]");
        conv_seed(seed, &f.together, &a, &b, &ty_j, "t[δ] and t'[δ] join");

        // Negative control: a `δ` that does *not* make the endpoints convert
        // leaves the transp stuck, so the join above is the substitution's
        // doing and not the family's.
        let (a, b) = (redex.apply_local(&f.miss_subst), reduct.apply_local(&f.miss_subst));
        let u = payload.apply_local(&f.miss_subst);
        let ty_m = ty.apply_local(&f.miss_subst);
        ck_seed(seed, &f.miss, &a, &ty_m);
        ck_seed(seed, &f.miss, &b, &ty_m);
        not_conv_seed(seed, &f.miss, &a, &u, &ty_m, "t[δ] strips under a non-flipping δ");
        not_conv_seed(seed, &f.miss, &b, &u, &ty_m, "t'[δ] strips under a non-flipping δ");
    }
}

#[test]
fn strip_and_proof_reduction_have_complementary_side_conditions() {
    // §19.3, stated as the property rather than as the algorithm's
    // determinism-by-construction. At a `transp` the strip rule and the
    // proof-reducing congruence rule have complementary side conditions, so
    // whichever face the proof wears the term has one `⇝ₛ`-normal form:
    //
    // - endpoints convertible ⇒ the strip fires, and it subsumes `transp`-β
    //   (§19.1, second bullet), so all four faces below — a stuck-but-
    //   strippable hypothesis, a β-redex over it, `srefl`, and a β-redex over
    //   `srefl` — are convertible with the payload and with each other, even
    //   though `reduce.rs` treats them differently (it fires β on two of them
    //   and is stuck on the other two);
    // - endpoints not convertible ⇒ the proof may still reduce, but the
    //   `transp` never equals its payload, and `srefl` is not even well-typed
    //   at the proof's type — which is §19.1's "when `a ≉ b` the proof
    //   provably never reaches `srefl`", i.e. why the restriction costs
    //   nothing.
    for seed in 0..CASES {
        let mut r = Rng::new(seed ^ 0x6a09e667f3bcc909);
        let f = fam(&mut r);

        // (A) Convertible endpoints. In Γ_join: n = v(2), e = v(1), u = v(0).
        let e_ty = seq(Type::Nat, f.lhs(2), f.rhs(2));
        let payload = v(0);
        let ty = f.inst(&f.together, f.rhs(2));
        let refl = srefl(Type::Nat, f.rhs(2));
        let faces = [
            v(1),
            id_app(e_ty.clone(), v(1)),
            refl.clone(),
            id_app(e_ty.clone(), refl.clone()),
        ];
        ck_seed(seed, &f.together, &refl, &e_ty);
        let mut transps = Vec::new();
        for face in faces {
            let t = transp(f.motive.clone(), f.lhs(2), f.rhs(2), face, payload.clone());
            ck_seed(seed, &f.together, &t, &ty);
            conv_seed(seed, &f.together, &t, &payload, &ty, "a face does not reach the payload");
            transps.push(t);
        }
        for a in &transps {
            for b in &transps {
                conv_seed(seed, &f.together, a, b, &ty, "two faces do not join");
            }
        }
        // The faces really are different for `reduce.rs`: β fires on the
        // `srefl` one and the hypothesis one is a whnf. Conversion identifies
        // them anyway, which is the content of "the strip subsumes β".
        let stuck = whnf_term(&transps[0], &f.together, FUEL)
            .unwrap_or_else(|_| panic!("out of fuel at seed {seed}"));
        assert!(stuck == transps[0], "the hypothesis face reduced at seed {seed}");
        let fired = whnf_term(&transps[2], &f.together, FUEL)
            .unwrap_or_else(|_| panic!("out of fuel at seed {seed}"));
        assert!(fired == payload, "the srefl face did not β-reduce at seed {seed}");

        // (B) The complementary side. In Γ: m = v(3), n = v(2), e = v(1).
        let e_ty = seq(Type::Nat, f.lhs(3), f.rhs(2));
        let ty = f.inst(&f.apart, f.rhs(2));
        no_ck_seed(seed, &f.apart, &srefl(Type::Nat, f.rhs(2)), &e_ty, "srefl at R");
        no_ck_seed(seed, &f.apart, &srefl(Type::Nat, f.lhs(3)), &e_ty, "srefl at L");
        let stuck = transp(f.motive.clone(), f.lhs(3), f.rhs(2), v(1), payload.clone());
        let reducible =
            transp(f.motive.clone(), f.lhs(3), f.rhs(2), id_app(e_ty, v(1)), payload.clone());
        ck_seed(seed, &f.apart, &stuck, &ty);
        ck_seed(seed, &f.apart, &reducible, &ty);
        not_conv_seed(seed, &f.apart, &stuck, &payload, &ty, "stuck face equals its payload");
        not_conv_seed(seed, &f.apart, &reducible, &payload, &ty, "reducible face equals payload");
        // They are still convertible with *each other*: the endpoint-keyed
        // congruence skips the proof, so reducing it changes nothing.
        conv_seed(seed, &f.apart, &stuck, &reducible, &ty, "the two faces disagree");
    }
}
