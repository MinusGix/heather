//! Codes and recursor branches for `sEq`/`sEmpty`: the rec.rs round of the
//! SProp landing (`docs/sprop-design.md` §6, §8 step 5;
//! `issues/sprop-strict-prop.md`).
//!
//! The gate-lift invariant is `wf_codes.rs`'s: the branch bundle must stay
//! exhaustive over the layer-c syntactic formers, so the formers enter
//! layer c exactly when their branches exist (seven when they landed, six
//! since `transp` was removed, `docs/iwf-former-design.md` §13 step 6). The
//! sharp test is the **identity recursor** round-tripping each new code in a
//! single β-step — a telescope wrong in either `rec.rs` or `reduce.rs` makes
//! the re-boxed code ill-typed or unequal. One thing this file pins that
//! `wf_codes.rs` had no analogue for: a *stuck* `elim_sEmpty` as code (a
//! scrutinee from the code's own context Δ) round-trips as syntax —
//! irrelevance is a conversion fact about terms, and does not reach inside a
//! box.

mod common;

use heather_kernel::rc::Rc;

use common::wt::{identity_branches, identity_motives, FUEL};
use heather_kernel::conv::conv_type;
use heather_kernel::layer::Layer;
use heather_kernel::level::Level;
use heather_kernel::reduce::whnf_term;
use heather_kernel::term::{CtxEntry, GlobalCtx, LocalCtx, LocalVar, Term, Type};
use heather_kernel::typing::check_term;

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

fn seq_nat(lhs: Term, rhs: Term) -> Type {
    Type::SEq { level: c(0), ty: rty(Type::Nat), lhs: rt(lhs), rhs: rt(rhs) }
}

/// Identity `elim^Typ` over `box(Δ ⊢ code)`, expected to re-box `code`.
fn identity_ty_in(delta: LocalCtx, code: Type) {
    let t = Term::ElimCodeTy {
        ty_motive_level: Level::Zero,
        tm_motive_level: Level::Zero,
        motives: identity_motives(),
        branches: identity_branches(),
        code_level: Level::Zero,
        ctx: delta.clone(),
        scrut: rt(Term::BoxTy(rty(code.clone()))),
    };
    let expect = Type::CodeTy { ctx: delta, level: Level::Zero };
    check_term(&GlobalCtx::default(), 0, Layer::Meta, &nil_ctx(), &t, &expect, &Level::Zero, FUEL)
        .unwrap_or_else(|e| panic!("identity elim^Typ ill-typed on {code:?}: {e:?}"));
    let w = whnf_term(&t, &nil_ctx(), FUEL).expect("identity elim^Typ exhausted fuel");
    assert!(w == Term::BoxTy(rty(code)), "identity elim^Typ is not the identity");
}

/// Identity `elim^Trm` over `box(Δ ⊢ code : ty @ level)`.
fn identity_tm_in(delta: LocalCtx, code: Term, ty: Type, level: Level) {
    let t = Term::ElimCodeTm {
        ty_motive_level: Level::Zero,
        tm_motive_level: Level::Zero,
        motives: identity_motives(),
        branches: identity_branches(),
        code_level: level.clone(),
        ctx: delta.clone(),
        ty: rty(ty.clone()),
        scrut: rt(Term::BoxTm(rt(code.clone()))),
    };
    let expect = Type::CodeTm { ctx: delta, ty: rty(ty), level };
    check_term(&GlobalCtx::default(), 0, Layer::Meta, &nil_ctx(), &t, &expect, &Level::Zero, FUEL)
        .unwrap_or_else(|e| panic!("identity elim^Trm ill-typed on {code:?}: {e:?}"));
    let w = whnf_term(&t, &nil_ctx(), FUEL).expect("identity elim^Trm exhausted fuel");
    assert!(w == Term::BoxTm(rt(code)), "identity elim^Trm is not the identity");
}

// -------------------------------------------------------------------------
// El decoding
// -------------------------------------------------------------------------

#[test]
fn el_decodes_the_encodings() {
    // El (sEq^0(Nat; 0; 0)) ≡ sEq^0(Nat; 0; 0), through El(TmNat) ⇝ Nat.
    let enc = Type::El {
        level: c(0),
        tm: rt(Term::TmSEq {
            level: c(0),
            ty: rt(Term::TmNat),
            lhs: rt(Term::Zero),
            rhs: rt(Term::Zero),
        }),
    };
    conv_type(
        &GlobalCtx::default(),
        &nil_ctx(),
        Layer::Prog,
        &enc,
        &seq_nat(Term::Zero, Term::Zero),
        &c(0),
        FUEL,
    )
    .expect("El (sEq code) ⇝ sEq");
    let enc = Type::El { level: c(0), tm: rt(Term::TmSEmpty { level: c(0) }) };
    conv_type(
        &GlobalCtx::default(),
        &nil_ctx(),
        Layer::Prog,
        &enc,
        &Type::SEmpty { level: c(0) },
        &c(0),
        FUEL,
    )
    .expect("El (sEmpty code) ⇝ sEmpty");
}

// -------------------------------------------------------------------------
// The identity recursor round-trips the new code (the branch tables)
// -------------------------------------------------------------------------

#[test]
fn identity_recursor_round_trips_the_types() {
    identity_ty_in(nil_ctx(), seq_nat(Term::Zero, nat_lit(2)));
    identity_ty_in(nil_ctx(), Type::SEmpty { level: c(0) });
}

#[test]
fn identity_recursor_round_trips_the_encodings() {
    identity_tm_in(
        nil_ctx(),
        Term::TmSEq {
            level: c(0),
            ty: rt(Term::TmNat),
            lhs: rt(Term::Zero),
            rhs: rt(nat_lit(1)),
        },
        Type::Ty(c(0)),
        c(1),
    );
    identity_tm_in(nil_ctx(), Term::TmSEmpty { level: c(0) }, Type::Ty(c(0)), c(1));
}

#[test]
fn identity_recursor_round_trips_srefl() {
    identity_tm_in(
        nil_ctx(),
        Term::SRefl { level: c(0), ty: rty(Type::Nat), tm: rt(Term::Zero) },
        seq_nat(Term::Zero, Term::Zero),
        c(0),
    );
}

#[test]
fn identity_recursor_round_trips_stuck_code() {
    // Δ = x : sEmpty — an elim_sEmpty as code. Irrelevance does not reach
    // inside the box: the round-trip is syntactic.
    let d_sempty = ext(&nil_ctx(), Type::SEmpty { level: c(0) }, c(0));
    identity_tm_in(
        d_sempty,
        Term::ElimSEmpty {
            level: c(0),
            scrut_level: c(0),
            motive: rty(Type::Nat),
            scrut: rt(v(0)),
        },
        Type::Nat,
        c(0),
    );
}

/// One new branch swapped for a well-scoped but wrong box poisons the whole
/// recursor — the motives are only used through the branch types, so the
/// tables cannot be rescued.
#[test]
fn a_wrong_new_branch_poisons_the_recursor() {
    let mut bad = (*identity_branches()).clone();
    // ty_sempty's telescope binds one universe and no globals beyond g;
    // re-boxing `Ty 0` instead of `sEmpty^ℓ` is well-scoped but not the
    // code the motive demands.
    bad.ty_sempty = rt(Term::BoxTy(rty(Type::Ty(Level::Zero))));
    let t = Term::ElimCodeTy {
        ty_motive_level: Level::Zero,
        tm_motive_level: Level::Zero,
        motives: identity_motives(),
        branches: Rc::new(bad),
        code_level: Level::Zero,
        ctx: nil_ctx(),
        scrut: rt(Term::BoxTy(rty(Type::SEmpty { level: c(0) }))),
    };
    let expect = Type::CodeTy { ctx: nil_ctx(), level: Level::Zero };
    check_term(&GlobalCtx::default(), 0, Layer::Meta, &nil_ctx(), &t, &expect, &Level::Zero, FUEL)
        .expect_err("a mismatched ty_sempty branch must poison the recursor");
}

fn nat_lit(n: u64) -> Term {
    let mut t = Term::Zero;
    for _ in 0..n {
        t = Term::Succ(rt(t));
    }
    t
}
