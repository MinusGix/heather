//! `sEq`/`srefl`/`sEmpty`: the strict propositions of the SProp landing
//! (`docs/sprop-design.md`, `issues/sprop-strict-prop.md`), as they stand
//! since `transp` was removed (`docs/iwf-former-design.md` §7, §13 step 6).
//!
//! `sEq` has no eliminator: it is a type inhabited exactly when its endpoints
//! convert, with one proof up to conversion. What is left to pin is the
//! irrelevance arm (any two proofs convert, at a neutral proof and at
//! `srefl`, and under Π by η alone), `srefl` checking at *convertible*
//! endpoints and not at different ones, `sEmpty`'s irrelevance and its
//! eliminator, and the formers' admission at layer c. The deleted half of
//! this file was `transp`'s β and the strip rule, with the head-only strip
//! gap's negatives (`issues/seq-strip-type-former-negatives.md`, moot now).

use heather_kernel::rc::Rc;

use heather_kernel::conv::conv_term;
use heather_kernel::layer::Layer;
use heather_kernel::level::Level;
use heather_kernel::reduce::whnf_term;
use heather_kernel::term::{CtxEntry, GlobalCtx, LocalCtx, LocalVar, Term, Type};
use heather_kernel::typing::{check_term, check_type};

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
    LocalCtx::nil()
}

fn ext(gamma: &LocalCtx, ty: Type, level: Level) -> LocalCtx {
    let mut g = gamma.clone();
    g.entries.push(CtxEntry { ty: rty(ty), level });
    g
}

fn seq(ty: Type, lhs: Term, rhs: Term) -> Type {
    Type::SEq { level: c(0), ty: rty(ty), lhs: rt(lhs), rhs: rt(rhs) }
}

fn srefl(ty: Type, tm: Term) -> Term {
    Term::SRefl { level: c(0), ty: rty(ty), tm: rt(tm) }
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

fn conv_tm(gamma: &LocalCtx, a: &Term, b: &Term, ty: &Type, level: Level) {
    conv_term(&GlobalCtx::default(), gamma, Layer::Prog, a, b, ty, &level, FUEL)
        .unwrap_or_else(|e| panic!("terms not convertible: {e:?}"));
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

#[test]
fn a_closed_seq_between_different_numerals_is_a_type_with_no_srefl() {
    // sEq(Nat; 0; 1) is a well-formed (empty) type; with no eliminator
    // nothing turns it into anything else, and srefl does not check at it.
    let t = seq(Type::Nat, Term::Zero, Term::Succ(rt(Term::Zero)));
    ck_ty(&nil_ctx(), &t, c(0));
    no_ck(&nil_ctx(), &srefl(Type::Nat, Term::Zero), &t, c(0));
}

// -------------------------------------------------------------------------
// sEmpty (design doc §2.2)
// -------------------------------------------------------------------------

fn sempty() -> Type {
    Type::SEmpty { level: c(0) }
}

#[test]
fn sempty_and_empty_proofs_are_both_irrelevant() {
    // Two hypotheses at sEmpty are convertible, and since Empty η the same
    // two at Empty are too. §2.2 priced the Empty-reuse alternative on
    // this contrast, which Empty η has since removed
    // (docs/metatheory-ch07-extensions.md §28); sEmpty stays a separate
    // former for its layer-c admission.
    let g = ext(&nil_ctx(), sempty(), c(0));
    let g = ext(&g, sempty(), c(0));
    conv_tm(&g, &v(1), &v(0), &sempty(), c(0));
    let h = ext(&nil_ctx(), Type::Empty { level: c(0) }, c(0));
    let h = ext(&h, Type::Empty { level: c(0) }, c(0));
    conv_tm(&h, &v(1), &v(0), &Type::Empty { level: c(0) }, c(0));
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
    // sEmpty was one of two exceptions, issue decision 3; the other, sEq's
    // transp, is gone.)
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
