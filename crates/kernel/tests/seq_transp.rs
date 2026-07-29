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

use std::rc::Rc;

use heather_kernel::conv::{conv_term, conv_type, ConvError};
use heather_kernel::layer::Layer;
use heather_kernel::level::Level;
use heather_kernel::reduce::whnf_term;
use heather_kernel::term::{CtxBase, CtxEntry, GlobalCtx, LocalCtx, LocalVar, Term, Type};
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
