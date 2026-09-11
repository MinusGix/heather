//! INVESTIGATION SCAFFOLDING — `issues/surface-existential.md`, 2026-08-01.
//! Deliberately uncommitted and NOT wired into CI; see
//! `docs/surface-existential-investigation.md` §B.
//!
//! The question: can today's kernel, with no new former, express a
//! **value-indexed existential**
//!
//! ```text
//! Converges(p, env, ir, vs) := Σ (n : Nat). eval(n, p)(env, ir) = Out(vs)
//! ```
//!
//! — a Σ whose second component's type mentions (a) the first component,
//! (b) a *computed* function applied to it, and (c) free **value**
//! parameters that the surface would supply?
//!
//! The miniature used below is faithful on all three counts and cheap:
//!
//! ```text
//! Halts(m) := Σ (n : Nat). Id(Nat; dbl n; m)
//! ```
//!
//! with `dbl` a real `elim_Nat`-defined function (the stand-in for `eval`,
//! which the *surface* half of the investigation exercises for real —
//! scratchpad `dep_field.hthr` puts a recursive surface `fn` inside a record
//! field's type), `n` the bound witness, and `m` a **free variable** — the
//! value parameter route 1 would let the surface write.
//!
//! Axes per `docs/testing-generated-terms.md`: the parameter `m` is open
//! (§1, §4, §5, §7), the eliminated family `Q` is an open type family (§4),
//! §4 is a checking position, and §6/§8 are negative controls.

use std::sync::Arc as Rc;

use heather_kernel::conv::conv_term;
use heather_kernel::layer::Layer;
use heather_kernel::level::Level;
use heather_kernel::term::{CtxEntry, GlobalCtx, LocalCtx, LocalVar, Term, Type};
use heather_kernel::typing::{check_term, check_type};

const FUEL: u64 = 1_000_000;

// ---------------------------------------------------------------------------
// Construction helpers (idioms lifted from `indexed_route1.rs`)
// ---------------------------------------------------------------------------

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
fn nat(n: u64) -> Term {
    let mut t = Term::Zero;
    for _ in 0..n {
        t = Term::Succ(rt(t));
    }
    t
}
fn nil_ctx() -> LocalCtx {
    LocalCtx::nil()
}
fn ext(gamma: &LocalCtx, ty: Type, level: Level) -> LocalCtx {
    let mut g = gamma.clone();
    g.entries.push(CtxEntry { ty: rty(ty), level });
    g
}
fn nat_ctx(n: usize) -> LocalCtx {
    let mut g = nil_ctx();
    for _ in 0..n {
        g = ext(&g, Type::Nat, c(0));
    }
    g
}

fn ck(gamma: &LocalCtx, t: &Term, ty: &Type, level: Level) {
    check_type(&GlobalCtx::default(), 0, Layer::Prog, gamma, ty, &level, FUEL)
        .unwrap_or_else(|e| panic!("type is not well-formed: {e:?}"));
    check_term(&GlobalCtx::default(), 0, Layer::Prog, gamma, t, ty, &level, FUEL)
        .unwrap_or_else(|e| panic!("term does not check: {e:?}"));
}
fn ck_ty(gamma: &LocalCtx, ty: &Type, level: Level) {
    check_type(&GlobalCtx::default(), 0, Layer::Prog, gamma, ty, &level, FUEL)
        .unwrap_or_else(|e| panic!("type is not well-formed: {e:?}"));
}
fn ck_fails(gamma: &LocalCtx, t: &Term, ty: &Type, level: Level) {
    check_term(&GlobalCtx::default(), 0, Layer::Prog, gamma, t, ty, &level, FUEL)
        .expect_err("the kernel gate must reject this");
}
fn conv(gamma: &LocalCtx, a: &Term, b: &Term, ty: &Type, level: Level) {
    conv_term(&GlobalCtx::default(), gamma, Layer::Prog, a, b, ty, &level, FUEL)
        .unwrap_or_else(|e| panic!("not convertible: {e:?}"));
}
fn not_conv(gamma: &LocalCtx, a: &Term, b: &Term, ty: &Type, level: Level) {
    conv_term(&GlobalCtx::default(), gamma, Layer::Prog, a, b, ty, &level, FUEL)
        .expect_err("expected inconvertible");
}

// ---------------------------------------------------------------------------
// `dbl` — the computed function that stands in for `eval`
// ---------------------------------------------------------------------------

/// `dbl t = elim_Nat(_ . Nat; 0; _ rec. S (S rec); t)`. A *recursive*
/// kerneltime function applied to whatever `t` is; neutral at a neutral `t`,
/// which is the property that matters (it is what `eval(n, p)(env, ir)` is
/// at an open `n`).
fn dbl(t: Term) -> Term {
    Term::ElimNat {
        level: c(0),
        motive: rty(Type::Nat),
        base: rt(Term::Zero),
        step: rt(Term::Succ(rt(Term::Succ(rt(v(0)))))),
        scrut: rt(t),
    }
}

/// `Halts(m) = Σ(n : Nat). Id^0(Nat; dbl n; m)` — the whole point. `m` is
/// scoped in the ambient Γ; under the Σ binder it must be shifted by one.
fn halts(m: Term) -> Type {
    Type::Sigma {
        fst_level: c(0),
        snd_level: c(0),
        fst: rty(Type::Nat),
        snd: rty(Type::Id {
            level: c(0),
            ty: rty(Type::Nat),
            lhs: rt(dbl(v(0))),
            rhs: rt(m.shift_local(1)),
        }),
    }
}

/// The `pair` annotations for `Halts(m)`, shared by intro and projections.
fn halts_ann(m: Term) -> (Rc<Type>, Rc<Type>) {
    match halts(m) {
        Type::Sigma { fst, snd, .. } => (fst, snd),
        _ => unreachable!(),
    }
}

fn halts_pair(m: Term, witness: Term, proof: Term) -> Term {
    let (fst_ty, snd_ty) = halts_ann(m);
    Term::Pair {
        fst_level: c(0),
        snd_level: c(0),
        fst_ty,
        snd_ty,
        fst: rt(witness),
        snd: rt(proof),
    }
}

fn halts_fst(m: Term, p: Term) -> Term {
    let (fst_ty, snd_ty) = halts_ann(m);
    Term::Fst { fst_level: c(0), snd_level: c(0), fst_ty, snd_ty, pair: rt(p) }
}

fn halts_snd(m: Term, p: Term) -> Term {
    let (fst_ty, snd_ty) = halts_ann(m);
    Term::Snd { fst_level: c(0), snd_level: c(0), fst_ty, snd_ty, pair: rt(p) }
}

// ---------------------------------------------------------------------------
// §1  Formation at an OPEN value parameter
// ---------------------------------------------------------------------------

/// The type route 1 would have the surface write as `Halts(m)` for a
/// *variable* `m`. This is the whole question A: nothing new is needed.
#[test]
fn forms_at_an_open_value_parameter() {
    // Γ = [m : Nat]
    let gamma = nat_ctx(1);
    ck_ty(&gamma, &halts(v(0)), c(0));
}

/// The level is the Σ's join, `0 ⊔ 0 = 0` — the record would land at 0,
/// where the prelude's `sym`/`trans`/`j` quantify (§G of the report).
#[test]
fn lands_at_level_zero_and_not_at_one() {
    let gamma = nat_ctx(1);
    ck_ty(&gamma, &halts(v(0)), c(0));
    check_type(&GlobalCtx::default(), 0, Layer::Prog, &gamma, &halts(v(0)), &c(1), FUEL)
        .expect_err("non-cumulative: the Σ has exactly one level, and it is 0");
}

// ---------------------------------------------------------------------------
// §2  Introduction at a CLOSED parameter — conversion closes the equation
// ---------------------------------------------------------------------------

/// `⟨2, refl⟩ : Halts(4)`. The `refl` checks only because the kernel runs
/// `dbl 2 ⇝ 4`: this is exactly the "discharge by computed bound" story of
/// `docs/ir-simulate-design.md` §6, and it is what an `equiv` instance does.
#[test]
fn intro_at_a_closed_parameter_discharges_by_conversion() {
    let gamma = nil_ctx();
    let proof = Term::Refl { level: c(0), ty: rty(Type::Nat), tm: rt(nat(4)) };
    ck(&gamma, &halts_pair(nat(4), nat(2), proof), &halts(nat(4)), c(0));
}

// ---------------------------------------------------------------------------
// §3  Introduction at an OPEN witness and an OPEN parameter
// ---------------------------------------------------------------------------

/// Γ = [k : Nat]; `⟨k, refl⟩ : Halts(dbl k)`. Everything is open: the
/// witness is a variable and the parameter is a *computed* term over it, so
/// the second component's type is a neutral `Id` on both sides.
#[test]
fn intro_on_fully_open_data() {
    let gamma = nat_ctx(1); // k = Var 0
    let m = dbl(v(0));
    let proof = Term::Refl { level: c(0), ty: rty(Type::Nat), tm: rt(dbl(v(0))) };
    ck(&gamma, &halts_pair(m.clone(), v(0), proof), &halts(m), c(0));
}

// ---------------------------------------------------------------------------
// §4  ELIMINATION — use the witness AND the equation to conclude something
// ---------------------------------------------------------------------------

/// The consumer shape. Γ = [m : Nat, q : Π(x : Nat). Ty 0,
/// f : Π(k : Nat). El (q (dbl k)), h : Halts(m)] ⊢ ? : El (q m).
///
/// The proof: instantiate `f` at the *witness* `fst h`, giving
/// `El (q (dbl (fst h)))`, then transport along the *equation* `snd h` with
/// `J` at motive `y _. El (q y)`. That is precisely how a consumer would use
/// `converges` — and `q` is an **open** type family, so nothing here can be
/// discharged by computation.
#[test]
fn elimination_uses_the_witness_and_the_equation() {
    // Γ layout (de Bruijn from the right): h = 0, f = 1, q = 2, m = 3.
    let q_ty = Type::Pi {
        dom_level: c(0),
        cod_level: c(1),
        dom: rty(Type::Nat),
        cod: rty(Type::Ty(c(0))),
    };
    // `q_at(x)` = `El (q x)` with `q` at de Bruijn index `qi`.
    let q_at = |qi: u32, x: Term| -> Type {
        Type::El {
            level: c(0),
            tm: rt(Term::App {
                fun: rt(v(qi)),
                dom_level: c(0),
                cod_level: c(1),
                dom: rty(Type::Nat),
                cod: rty(Type::Ty(c(0))),
                arg: rt(x),
            }),
        }
    };

    let gamma = nat_ctx(1); // m
    let gamma = ext(&gamma, q_ty, c(1)); // q
    // f : Π(k : Nat). El (q (dbl k)) — under the binder q is Var 1.
    let f_ty = Type::Pi {
        dom_level: c(0),
        cod_level: c(0),
        dom: rty(Type::Nat),
        cod: rty(q_at(1, dbl(v(0)))),
    };
    let gamma = ext(&gamma, f_ty.clone(), c(0)); // f
    let gamma = ext(&gamma, halts(v(2)), c(0)); // h : Halts(m)

    let witness = halts_fst(v(3), v(0));
    let equation = halts_snd(v(3), v(0));

    // f (fst h) : El (q (dbl (fst h)))
    let base = Term::App {
        fun: rt(v(1)),
        dom_level: c(0),
        cod_level: c(0),
        dom: rty(Type::Nat),
        cod: rty(q_at(3, dbl(v(0)))),
        arg: rt(witness.clone()),
    };

    // J at motive `y p. El (q y)`, left endpoint `dbl (fst h)`, right `m`.
    // The motive binds two locals, so `q` is Var 4 inside it.
    let term = Term::J {
        ty_level: c(0),
        motive_level: c(0),
        ty: rty(Type::Nat),
        lhs: rt(dbl(witness.clone())),
        motive: rty(q_at(4, v(1))),
        case: rt(base),
        rhs: rt(v(3)),
        proof: rt(equation),
    };

    ck(&gamma, &term, &q_at(2, v(3)), c(0));
}

// ---------------------------------------------------------------------------
// §5  β through the pair: the projections compute
// ---------------------------------------------------------------------------

#[test]
fn projections_beta_reduce_and_eta_holds() {
    // Γ = [k : Nat]; p = ⟨k, refl⟩ : Halts(dbl k)
    let gamma = nat_ctx(1);
    let m = dbl(v(0));
    let proof = Term::Refl { level: c(0), ty: rty(Type::Nat), tm: rt(dbl(v(0))) };
    let p = halts_pair(m.clone(), v(0), proof);
    // fst ⟨k, _⟩ ≡ k, on open data.
    conv(&gamma, &halts_fst(m.clone(), p.clone()), &v(0), &Type::Nat, c(0));

    // η at a NEUTRAL pair: h ≡ ⟨fst h, snd h⟩ (the record-η the surface
    // records suite already relies on, here at a value-indexed Σ).
    let gamma2 = ext(&nat_ctx(1), halts(v(0)), c(0)); // [m, h]
    let repack = halts_pair(v(1), halts_fst(v(1), v(0)), halts_snd(v(1), v(0)));
    conv(&gamma2, &repack, &v(0), &halts(v(1)), c(0));
}

// ---------------------------------------------------------------------------
// §6  NEGATIVE CONTROL — the parameter really indexes the proposition
// ---------------------------------------------------------------------------

/// The reason an un-indexed Σ "proves nothing about a particular program"
/// (the issue's own words): at a *different* parameter the same witness is
/// rejected. If this passed, route 1 would be pointless.
#[test]
fn a_witness_for_one_parameter_does_not_inhabit_another() {
    let gamma = nil_ctx();
    let proof = Term::Refl { level: c(0), ty: rty(Type::Nat), tm: rt(nat(4)) };
    let p = halts_pair(nat(4), nat(2), proof);
    ck_fails(&gamma, &p, &halts(nat(5)), c(0));

    // Same point at an OPEN parameter: a concrete witness cannot prove
    // `Halts(m)` for a variable `m`.
    let open = nat_ctx(1);
    ck_fails(&open, &p, &halts(v(0)), c(0));

    // And the two propositions are distinct as *codes*, i.e. the surface
    // `Halts(4)` and `Halts(5)` are not the same type.
    let code = |m: Term| Term::TmSigma {
        fst_level: c(0),
        snd_level: c(0),
        fst: rt(Term::TmNat),
        snd: rt(Term::TmId {
            level: c(0),
            ty: rt(Term::TmNat),
            lhs: rt(dbl(v(0))),
            rhs: rt(m.shift_local(1)),
        }),
    };
    ck(&gamma, &code(nat(4)), &Type::Ty(c(0)), c(1));
    not_conv(&gamma, &code(nat(4)), &code(nat(5)), &Type::Ty(c(0)), c(1));
}

// ---------------------------------------------------------------------------
// §7  ITERATED Σ — the inversion-lemma shape (report §F)
// ---------------------------------------------------------------------------

/// `k_bind(...) = Out(vs) -> Σ ws. (r = Out(ws)) × …` is a Σ whose second
/// component is itself a Σ, and whose *third* component mentions both the
/// bound witness and an outer parameter. Miniature: Γ = [r : Nat, m : Nat],
///
/// ```text
/// Inv(r, m) := Σ(w : Nat). Σ(_ : Id(Nat; r; S w)). Id(Nat; dbl w; m)
/// ```
#[test]
fn iterated_sigma_forms_and_inhabits() {
    let inv = |r: Term, m: Term| -> Type {
        // Under `w` (one binder) then under the inner Σ's binder (two).
        Type::Sigma {
            fst_level: c(0),
            snd_level: c(0),
            fst: rty(Type::Nat),
            snd: rty(Type::Sigma {
                fst_level: c(0),
                snd_level: c(0),
                fst: rty(Type::Id {
                    level: c(0),
                    ty: rty(Type::Nat),
                    lhs: rt(r.shift_local(1)),
                    rhs: rt(Term::Succ(rt(v(0)))),
                }),
                snd: rty(Type::Id {
                    level: c(0),
                    ty: rty(Type::Nat),
                    lhs: rt(dbl(v(1))),
                    rhs: rt(m.shift_local(2)),
                }),
            }),
        }
    };

    // Formation at fully open r and m.
    let gamma = nat_ctx(2); // r = Var 1, m = Var 0
    ck_ty(&gamma, &inv(v(1), v(0)), c(0));

    // Inhabitation at r := 4, m := 6, w := 3.
    let ty = inv(nat(4), nat(6));
    let (o_fst, o_snd) = match &ty {
        Type::Sigma { fst, snd, .. } => (fst.clone(), snd.clone()),
        _ => unreachable!(),
    };
    // The inner pair's annotations are the outer `snd`'s **with the witness
    // substituted** (w := 3) — writing them un-substituted is the generator
    // hazard §8 is about, and the kernel catches it (`UnboundLocalVar`).
    let inner_fst = Type::Id {
        level: c(0),
        ty: rty(Type::Nat),
        lhs: rt(nat(4)),
        rhs: rt(Term::Succ(rt(nat(3)))),
    };
    let inner_snd = Type::Id {
        level: c(0),
        ty: rty(Type::Nat),
        lhs: rt(dbl(nat(3))),
        rhs: rt(nat(6)),
    };
    let inner_pair = Term::Pair {
        fst_level: c(0),
        snd_level: c(0),
        fst_ty: rty(inner_fst),
        snd_ty: rty(inner_snd),
        fst: rt(Term::Refl { level: c(0), ty: rty(Type::Nat), tm: rt(nat(4)) }),
        snd: rt(Term::Refl { level: c(0), ty: rty(Type::Nat), tm: rt(nat(6)) }),
    };
    let outer = Term::Pair {
        fst_level: c(0),
        snd_level: c(0),
        fst_ty: o_fst,
        snd_ty: o_snd,
        fst: rt(nat(3)),
        snd: rt(inner_pair),
    };
    ck(&nil_ctx(), &outer, &ty, c(0));
}

// ---------------------------------------------------------------------------
// §8  NEGATIVE CONTROL — a mis-scoped parameter is caught
// ---------------------------------------------------------------------------

/// The one thing a value-parameter generator must get right is the shift of
/// the parameter under the Σ binder. Forgetting it silently captures the
/// witness — and the kernel does NOT catch that as a type error here (both
/// spellings are well-formed `Nat`s), so it is a *generator* obligation, not
/// a kernel-gated one. Pinned as the hazard it is: the two types differ.
#[test]
fn an_unshifted_parameter_captures_the_witness() {
    let gamma = nat_ctx(1); // m = Var 0
    // WRONG: `m` written as Var 0 under the binder — that is the witness.
    let captured = Type::Sigma {
        fst_level: c(0),
        snd_level: c(0),
        fst: rty(Type::Nat),
        snd: rty(Type::Id {
            level: c(0),
            ty: rty(Type::Nat),
            lhs: rt(dbl(v(0))),
            rhs: rt(v(0)),
        }),
    };
    // It is well-formed — the kernel cannot see the intent.
    ck_ty(&gamma, &captured, c(0));
    // But it is a different proposition: ⟨0, refl⟩ inhabits it outright,
    // while `Halts(m)` at an open `m` has no such inhabitant.
    let triv = Term::Pair {
        fst_level: c(0),
        snd_level: c(0),
        fst_ty: rty(Type::Nat),
        snd_ty: match &captured {
            Type::Sigma { snd, .. } => snd.clone(),
            _ => unreachable!(),
        },
        fst: rt(Term::Zero),
        snd: rt(Term::Refl { level: c(0), ty: rty(Type::Nat), tm: rt(Term::Zero) }),
    };
    ck(&gamma, &triv, &captured, c(0));
    ck_fails(&gamma, &triv, &halts(v(0)), c(0));
}
