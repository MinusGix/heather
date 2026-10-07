//! `Vec` and `Fin`: phase 1 of the `Wf` landing
//! (`docs/wf-former-design.md` §1, `issues/wf-former.md`).
//!
//! These two formers carry no introduction or elimination forms of their
//! own — their whole content is the length-driven reduction into existing
//! formers, and everything downstream (η, canonical-form uniqueness,
//! proof irrelevance at arity 0) is supposed to arrive *through* those
//! reductions rather than from new conversion rules. That claim is what
//! this file pins, because it is the reason route C was chosen over route
//! A (`docs/branching-inductives-choice.md` §15): children stored in
//! `Σ`/`Unit` reach the η the kernel already has, children stored in `Π`
//! do not.
//!
//! Coverage: the reductions at literal lengths, neutrality at a neutral
//! length (with structural congruence there), formation and its level,
//! the componentwise Σ-η / Unit-irrelevance that `Wf`'s arm obligation
//! will depend on.

use std::sync::Arc as Rc;

use heather_kernel::conv::{conv_term, conv_type};
use heather_kernel::layer::Layer;
use heather_kernel::level::Level;
use heather_kernel::reduce::whnf_type;
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

fn nat(n: u64) -> Term {
    let mut t = Term::Zero;
    for _ in 0..n {
        t = Term::Succ(rt(t));
    }
    t
}

fn vec(elem: Type, len: Term) -> Type {
    Type::Vec { level: c(0), elem: rty(elem), len: rt(len) }
}

fn fin(len: Term) -> Type {
    Type::Fin { len: rt(len) }
}

fn sigma(fst: Type, snd: Type) -> Type {
    Type::Sigma {
        fst_level: c(0),
        snd_level: c(0),
        fst: rty(fst),
        snd: rty(snd),
    }
}

fn pair(fst_ty: Type, snd_ty: Type, fst: Term, snd: Term) -> Term {
    Term::Pair {
        fst_level: c(0),
        snd_level: c(0),
        fst_ty: rty(fst_ty),
        snd_ty: rty(snd_ty),
        fst: rt(fst),
        snd: rt(snd),
    }
}

fn whnf(t: &Type, gamma: &LocalCtx) -> Type {
    whnf_type(t, gamma, FUEL).expect("enough fuel")
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

fn conv_ty(gamma: &LocalCtx, a: &Type, b: &Type, level: Level) {
    conv_type(&GlobalCtx::default(), gamma, Layer::Prog, a, b, &level, FUEL)
        .unwrap_or_else(|e| panic!("types not convertible: {e:?}"));
}

fn not_conv_ty(gamma: &LocalCtx, a: &Type, b: &Type, level: Level) {
    conv_type(&GlobalCtx::default(), gamma, Layer::Prog, a, b, &level, FUEL)
        .expect_err("expected inconvertible");
}

fn conv_tm(gamma: &LocalCtx, a: &Term, b: &Term, ty: &Type, level: Level) {
    conv_term(&GlobalCtx::default(), gamma, Layer::Prog, a, b, ty, &level, FUEL)
        .unwrap_or_else(|e| panic!("terms not convertible: {e:?}"));
}

// -------------------------------------------------------------------------
// Reduction
// -------------------------------------------------------------------------

#[test]
fn vec_reduces_on_a_literal_length() {
    let g = nil_ctx();
    // Vec(Nat; 0) ⇝ Unit.
    assert_eq!(whnf(&vec(Type::Nat, nat(0)), &g), Type::Unit { level: Level::Zero });
    // Vec(Nat; 2) ⇝ Σ(_ : Nat). Vec(Nat; 1) — one step at a time, so the
    // head is a Σ whose tail is still a `Vec`.
    let one = whnf(&vec(Type::Nat, nat(2)), &g);
    let Type::Sigma { fst, snd, .. } = &one else {
        panic!("expected Σ, got {one:?}");
    };
    assert_eq!(**fst, Type::Nat);
    assert_eq!(**snd, vec(Type::Nat, nat(1)));
    // …and the whole chain is convertible with the explicit tuple type.
    conv_ty(
        &g,
        &vec(Type::Nat, nat(2)),
        &sigma(Type::Nat, sigma(Type::Nat, Type::Unit { level: Level::Zero })),
        c(0),
    );
}

#[test]
fn fin_reduces_on_a_literal_length() {
    let g = nil_ctx();
    assert_eq!(whnf(&fin(nat(0)), &g), Type::Empty { level: Level::Zero });
    conv_ty(
        &g,
        &fin(nat(2)),
        &Type::Sum {
            lhs_level: c(0),
            rhs_level: c(0),
            lhs: rty(Type::Unit { level: Level::Zero }),
            rhs: rty(Type::Sum {
                lhs_level: c(0),
                rhs_level: c(0),
                lhs: rty(Type::Unit { level: Level::Zero }),
                rhs: rty(Type::Empty { level: Level::Zero }),
            }),
        },
        c(0),
    );
}

#[test]
fn the_length_reduces_before_the_former_does() {
    // A length that is not literal but *computes* — `Vec` must whnf its
    // length first, which is what makes an arity read off a shape
    // (`arity a` in the generator) usable in a type.
    let g = nil_ctx();
    let computed = Term::ElimNat {
        level: c(0),
        motive: rty(Type::Nat),
        base: rt(nat(0)),
        step: rt(Term::Succ(rt(Term::Succ(rt(v(1)))))),
        scrut: rt(nat(1)),
    };
    conv_ty(&g, &vec(Type::Nat, computed.clone()), &vec(Type::Nat, nat(2)), c(0));
    conv_ty(&g, &fin(computed), &fin(nat(2)), c(0));
}

#[test]
fn neutral_at_a_neutral_length() {
    // Γ = (k : Nat): `Vec(Nat; k)` and `Fin(k)` are stuck — no reduction,
    // and congruence compares element and length structurally. This is
    // wrinkle 3 of the choice doc (§6): an unknown arity has an unknown
    // tuple, and that is the intended behaviour.
    let g = ext(&nil_ctx(), Type::Nat, c(0));
    let vk = vec(Type::Nat, v(0));
    assert_eq!(whnf(&vk, &g), vk);
    assert_eq!(whnf(&fin(v(0)), &g), fin(v(0)));

    conv_ty(&g, &vk, &vec(Type::Nat, v(0)), c(0));
    conv_ty(&g, &fin(v(0)), &fin(v(0)), c(0));
    // Different lengths, and different elements, are distinguished.
    not_conv_ty(&g, &vk, &vec(Type::Nat, Term::Succ(rt(v(0)))), c(0));
    not_conv_ty(&g, &vk, &vec(Type::Unit { level: Level::Zero }, v(0)), c(0));
    // A neutral length is not convertible with a literal one.
    not_conv_ty(&g, &vk, &vec(Type::Nat, nat(2)), c(0));

    // Successor of a neutral still reduces: Vec(T; S k) ⇝ Σ(_ : T). Vec(T; k).
    conv_ty(
        &g,
        &vec(Type::Nat, Term::Succ(rt(v(0)))),
        &sigma(Type::Nat, vec(Type::Nat, v(1))),
        c(0),
    );
}

// -------------------------------------------------------------------------
// Formation
// -------------------------------------------------------------------------

#[test]
fn formation_and_levels() {
    let g = nil_ctx();
    // Vec lives at its element's level; Fin at 0.
    ck_ty(&g, &vec(Type::Nat, nat(3)), c(0));
    ck_ty(&g, &fin(nat(3)), c(0));
    ck_ty(&g, &Type::Vec { level: c(1), elem: rty(Type::Ty(c(0))), len: rt(nat(2)) }, c(1));
    // The length must be a Nat.
    let bad = Type::Vec { level: c(0), elem: rty(Type::Nat), len: rt(Term::Triv { level: Level::Zero }) };
    check_type(&GlobalCtx::default(), 0, Layer::Prog, &g, &bad, &c(0), FUEL)
        .expect_err("a non-Nat length must be rejected");
    // A length may be open, and may mention the context.
    let g1 = ext(&nil_ctx(), Type::Nat, c(0));
    ck_ty(&g1, &vec(Type::Nat, v(0)), c(0));
    ck_ty(&g1, &fin(v(0)), c(0));
}

/// `Vec^l(T; 0) ⇝ Unit^l` **keeps its level** — DeLaM ch. 06's Preservation
/// lemma (`06:264`), at the same `l`, for the reduction that used to break it.
///
/// This was `vec_at_zero_drops_its_level_known_gap`, which pinned the defect
/// so it could not close silently. Route (a) closed it
/// (`docs/unit-empty-level-indexing.md`), so the pin becomes its positive.
#[test]
fn vec_at_zero_keeps_its_level() {
    let g = nil_ctx();
    let big = Type::Vec { level: c(1), elem: rty(Type::Ty(c(0))), len: rt(Term::Zero) };
    ck_ty(&g, &big, c(1));
    // The reduct is `Unit^1`, not `Unit^0`…
    assert_eq!(whnf(&big, &g), Type::Unit { level: c(1) });
    ck_ty(&g, &whnf(&big, &g), c(1));
    // …so a well-formed Π stays well-formed across the step, which is the
    // shape the lemma is actually consumed in.
    let pi = |dom: Type| Type::Pi {
        dom_level: c(1),
        cod_level: c(0),
        dom: rty(dom),
        cod: rty(Type::Nat),
    };
    ck_ty(&g, &pi(big.clone()), c(1));
    ck_ty(&g, &pi(whnf(&big, &g)), c(1));
    // Successor lengths preserved it all along…
    let big1 = Type::Vec { level: c(1), elem: rty(Type::Ty(c(0))), len: rt(nat(1)) };
    ck_ty(&g, &whnf(&big1, &g), c(1));
    // …and `Fin` is unaffected: declared at 0, both reducts land at 0.
    ck_ty(&g, &whnf(&fin(Term::Zero), &g), c(0));
    ck_ty(&g, &whnf(&fin(nat(1)), &g), c(0));
}

/// The functional hole the level drop left, closed. `Vec^l(child; 0)` is the
/// children type of a **nullary constructor** of a `Wf` whose shape sits at
/// level `l`, so before route (a) `Leaf` could not be built for any
/// polymorphic branching inductive: `Triv : Vec^1(Ty 0;0) @ 1` was a
/// `LevelMismatch`, and it only checked at the *wrong* level 0.
#[test]
fn the_nullary_arm_is_inhabited_at_its_own_level() {
    let g = nil_ctx();
    let psi = GlobalCtx::default();
    let children = Type::Vec { level: c(1), elem: rty(Type::Ty(c(0))), len: rt(Term::Zero) };
    ck_ty(&g, &children, c(1));
    ck(&g, &Term::Triv { level: c(1) }, &children, c(1));
    // And the annotation is not decoration: the *wrong* level is rejected,
    // which is what keeps `⟨⟩` from having many types.
    check_term(&psi, 0, Layer::Prog, &g, &Term::Triv { level: Level::Zero }, &children, &c(1), FUEL)
        .expect_err("⟨⟩^0 must not inhabit Vec^1(_;0)");
    check_term(&psi, 0, Layer::Prog, &g, &Term::Triv { level: c(1) }, &Type::Unit { level: Level::Zero }, &Level::Zero, FUEL)
        .expect_err("⟨⟩^1 must not inhabit Unit^0");
}

/// The invariant the repair must not break: **each type has one level**, so
/// each `box T` has one type. This is what `rec.rs`'s branch telescopes are
/// built against — `ty_ty` binds a universe because `Ty ℓ`'s level varies,
/// `ty_unit` binds none because `Unit`'s does not.
#[test]
fn every_type_has_exactly_one_level() {
    let g = nil_ctx();
    let psi = GlobalCtx::default();
    let ck_at = |t: &Type, l: Level| check_type(&psi, 0, Layer::Prog, &g, t, &l, FUEL);

    for (name, t) in [
        ("Unit", Type::Unit { level: Level::Zero }),
        ("Empty", Type::Empty { level: Level::Zero }),
        ("Nat", Type::Nat),
        ("Fin 2", fin(nat(2))),
        ("Vec^0(Nat;0)", Type::Vec { level: c(0), elem: rty(Type::Nat), len: rt(Term::Zero) }),
    ] {
        ck_at(&t, c(0)).unwrap_or_else(|e| panic!("{name} must check at 0: {e:?}"));
        ck_at(&t, c(1)).expect_err(&format!("{name} must NOT also check at 1"));
    }
    // And the box that reads off that level stays single-typed.
    let bu = Term::BoxTy(rty(Type::Unit { level: Level::Zero }));
    let code_at = |l: Level| Type::CodeTy { ctx: nil_ctx(), level: l };
    check_term(&psi, 0, Layer::Meta, &g, &bu, &code_at(c(0)), &c(0), FUEL)
        .expect("box Unit : □(· ⊢ Ty 0)");
    check_term(&psi, 0, Layer::Meta, &g, &bu, &code_at(c(1)), &c(0), FUEL)
        .expect_err("box Unit must NOT also inhabit □(· ⊢ Ty 1)");
}

#[test]
fn layer_c_accepts_vec_and_fin() {
    // Phase 1 gated both out of layer c until they had code formers and
    // recursor branches; phase 3 gave them both, so boxed code may now
    // mention them (docs/wf-former-design.md §6). The codes themselves and
    // the round-trip through the recursor live in `tests/wf_codes.rs`.
    let g = nil_ctx();
    for t in [vec(Type::Nat, nat(2)), fin(nat(2))] {
        check_type(&GlobalCtx::default(), 0, Layer::Code, &g, &t, &c(0), FUEL)
            .expect("layer c accepts Vec/Fin since phase 3");
    }
}

// -------------------------------------------------------------------------
// What the reductions buy: η, componentwise, without new conversion rules
// -------------------------------------------------------------------------

#[test]
fn tuples_inhabit_vec_and_compare_componentwise() {
    // The canonical 2-tuple checks *at the `Vec` type* — no coercion, the
    // reduction does it — and distinct tuples stay distinguishable.
    let g = nil_ctx();
    let ty = vec(Type::Nat, nat(2));
    let tup = |a: u64, b: u64| {
        pair(
            Type::Nat,
            vec(Type::Nat, nat(1)),
            nat(a),
            pair(Type::Nat, vec(Type::Nat, nat(0)), nat(b), Term::Triv { level: Level::Zero }),
        )
    };
    ck(&g, &tup(1, 2), &ty, c(0));
    conv_tm(&g, &tup(1, 2), &tup(1, 2), &ty, c(0));
    conv_term(&GlobalCtx::default(), &g, Layer::Prog, &tup(1, 2), &tup(2, 1), &ty, &c(0), FUEL)
        .expect_err("distinct tuples must be distinguishable");
}

#[test]
fn arity_zero_is_proof_irrelevant() {
    // `Vec(T; 0) ⇝ Unit`, so *any* two inhabitants are convertible — this
    // is route C's "leaf uniqueness is definitional" (§6), and it is
    // inherited from Unit rather than stated anew.
    let g = ext(&nil_ctx(), vec(Type::Nat, nat(0)), c(0));
    let ty = vec(Type::Nat, nat(0));
    ck(&g, &Term::Triv { level: Level::Zero }, &ty, c(0));
    // A variable of the type and `⟨⟩` are convertible.
    conv_tm(&g, &v(0), &Term::Triv { level: Level::Zero }, &ty, c(0));
}

#[test]
fn sigma_eta_reaches_through_vec() {
    // THE property `Wf`'s arm obligation will rest on: for a *neutral*
    // tuple `cs : Vec(Nat; 2)`, `cs` is convertible with its own
    // projections repackaged. Route A's analogue needs funext; here it is
    // Σ-η plus Unit-irrelevance, both already in conv.rs, reached through
    // the `Vec` reduction (docs/branching-inductives-choice.md §15).
    let ty = vec(Type::Nat, nat(2));
    let g = ext(&nil_ctx(), ty.clone(), c(0));
    let tail_ty = vec(Type::Nat, nat(1));
    let fst = Term::Fst {
        fst_level: c(0),
        snd_level: c(0),
        fst_ty: rty(Type::Nat),
        snd_ty: rty(tail_ty.clone()),
        pair: rt(v(0)),
    };
    let snd = Term::Snd {
        fst_level: c(0),
        snd_level: c(0),
        fst_ty: rty(Type::Nat),
        snd_ty: rty(tail_ty.clone()),
        pair: rt(v(0)),
    };
    let snd_fst = Term::Fst {
        fst_level: c(0),
        snd_level: c(0),
        fst_ty: rty(Type::Nat),
        snd_ty: rty(vec(Type::Nat, nat(0))),
        pair: rt(snd.clone()),
    };
    // cs ≡ (fst cs, (fst (snd cs), ⟨⟩)) — the second component's tail is
    // filled by `⟨⟩` via Unit-irrelevance, not by a projection.
    let repacked = pair(
        Type::Nat,
        tail_ty,
        fst,
        pair(Type::Nat, vec(Type::Nat, nat(0)), snd_fst, Term::Triv { level: Level::Zero }),
    );
    ck(&g, &repacked, &ty, c(0));
    conv_tm(&g, &v(0), &repacked, &ty, c(0));
}

#[test]
fn fin_indices_are_the_sum_injections() {
    // `Fin(2)` inhabitants are `inl ⟨⟩` / `inr (inl ⟨⟩)`, checked at the
    // `Fin` type directly — what the generated ih will be applied to.
    let g = nil_ctx();
    let inner = Type::Sum {
        lhs_level: c(0),
        rhs_level: c(0),
        lhs: rty(Type::Unit { level: Level::Zero }),
        rhs: rty(Type::Empty { level: Level::Zero }),
    };
    let i0 = Term::Inl {
        lhs_level: c(0),
        rhs_level: c(0),
        lhs: rty(Type::Unit { level: Level::Zero }),
        rhs: rty(inner.clone()),
        val: rt(Term::Triv { level: Level::Zero }),
    };
    let i1 = Term::Inr {
        lhs_level: c(0),
        rhs_level: c(0),
        lhs: rty(Type::Unit { level: Level::Zero }),
        rhs: rty(inner),
        val: rt(Term::Inl {
            lhs_level: c(0),
            rhs_level: c(0),
            lhs: rty(Type::Unit { level: Level::Zero }),
            rhs: rty(Type::Empty { level: Level::Zero }),
            val: rt(Term::Triv { level: Level::Zero }),
        }),
    };
    ck(&g, &i0, &fin(nat(2)), c(0));
    ck(&g, &i1, &fin(nat(2)), c(0));
    conv_term(&GlobalCtx::default(), &g, Layer::Prog, &i0, &i1, &fin(nat(2)), &c(0), FUEL)
        .expect_err("distinct indices must be distinguishable");
    // `Fin(0)` is `Empty`: it eliminates into anything.
    let g1 = ext(&nil_ctx(), fin(nat(0)), c(0));
    let absurd = Term::ElimEmpty { level: c(0),
            scrut_level: Level::Zero, motive: rty(Type::Nat), scrut: rt(v(0)) };
    ck(&g1, &absurd, &Type::Nat, c(0));
}

#[test]
fn fin_zero_is_proof_irrelevant() {
    // `Fin(0) ⇝ Empty`, and Empty η is dispatched on the type's whnf, so
    // two distinct indices at `Fin(0)` are convertible, and so are two
    // eliminations of them.
    let g = ext(&ext(&nil_ctx(), fin(nat(0)), c(0)), fin(nat(0)), c(0));
    conv_tm(&g, &v(0), &v(1), &fin(nat(0)), c(0));
    let absurd = |x: u32| Term::ElimEmpty { level: c(0),
            scrut_level: Level::Zero, motive: rty(Type::Nat), scrut: rt(v(x)) };
    ck(&g, &absurd(0), &Type::Nat, c(0));
    conv_tm(&g, &absurd(0), &absurd(1), &Type::Nat, c(0));
    // Negative control: at a *stuck* `Fin(n)` (n a variable) the type is
    // not Empty, and distinct indices stay distinct. Substituting 0 for n
    // later only adds convertible pairs, so this is stable.
    let h = ext(&ext(&ext(&nil_ctx(), Type::Nat, c(0)), fin(v(0)), c(0)), fin(v(1)), c(0));
    conv_term(&GlobalCtx::default(), &h, Layer::Prog, &v(0), &v(1), &fin(v(2)), &c(0), FUEL)
        .expect_err("indices at a stuck Fin(n) must stay distinguishable");
}

#[test]
fn substitution_reaches_the_length() {
    // The length is a term in Γ with no binder of its own, so substitution
    // must reach it — the `nth`/`arity` plumbing depends on this.
    let g = ext(&nil_ctx(), Type::Nat, c(0));
    let open = vec(Type::Nat, v(0));
    // Instantiating the context variable with a literal makes it reduce.
    let inst = open.apply_local(
        &heather_kernel::term::LocalSubst::id(&nil_ctx()).extended(rt(nat(2))),
    );
    conv_ty(&nil_ctx(), &inst, &sigma(Type::Nat, sigma(Type::Nat, Type::Unit { level: Level::Zero })), c(0));
    // …and weakening keeps it stuck at the shifted variable.
    let _ = g;
    let shifted = open.shift_local(1);
    assert_eq!(shifted, vec(Type::Nat, v(1)));
}

#[path = "common/mod.rs"]
mod common;

/// Sanity: the property-test generator actually produces `Vec`/`Fin`, so
/// the substitution/conversion property suites really cover them.
#[test]
fn the_generators_reach_vec_and_fin() {
    fn has(t: &Type) -> bool {
        match t {
            Type::Vec { .. } | Type::Fin { .. } => true,
            Type::Pi { dom, cod, .. } => has(dom) || has(cod),
            Type::Sigma { fst, snd, .. } => has(fst) || has(snd),
            Type::Sum { lhs, rhs, .. } => has(lhs) || has(rhs),
            Type::W { shape, pos, .. } => has(shape) || has(pos),
            Type::Id { ty, .. } => has(ty),
            _ => false,
        }
    }
    let sc = common::Sc {
        univ: 1,
        globals: vec![],
        local: common::Shape { base: common::BaseRef::Nil, len: 2 },
    };
    let mut r = common::Rng::new(7);
    let hits = (0..300).filter(|_| has(&common::gen_type(&sc, &mut r, 4))).count();
    assert!(hits > 20, "generator produced Vec/Fin only {hits}/300 times");
}

/// The **witness has to be generated**, not merely generatable — the lesson
/// of `issues/metatheory-lemma-sweep.md`. Level-indexing `Unit`/`Empty`
/// (`docs/unit-empty-level-indexing.md`) is only covered by the property
/// suite if `gen_wt_type` actually reaches `Unit^l` with `l ≠ 0`; before this
/// round the well-typed generator produced no `Unit`/`Empty` at all, so the
/// whole route would have been untested by everything in `conv_properties`
/// and `ch05_06_lemmas`.
#[test]
fn the_well_typed_generator_reaches_unit_at_a_nonzero_level() {
    fn find(t: &Type, out: &mut (u32, u32)) {
        match t {
            Type::Unit { level } | Type::Empty { level } => {
                out.0 += 1;
                if !level.equiv(&Level::Zero) {
                    out.1 += 1;
                }
            }
            Type::Pi { dom, cod, .. } | Type::Sigma { fst: dom, snd: cod, .. } => {
                find(dom, out);
                find(cod, out);
            }
            Type::Sum { lhs, rhs, .. } | Type::W { shape: lhs, pos: rhs, .. } => {
                find(lhs, out);
                find(rhs, out);
            }
            Type::Vec { elem, .. } => find(elem, out),
            Type::Wf { shape, .. } => find(shape, out),
            Type::Id { ty, .. } => find(ty, out),
            _ => {}
        }
    }
    let mut seen = (0u32, 0u32);
    for seed in 0..300u64 {
        let mut r = common::Rng::new(seed ^ 0xa076_1d64_78bd_642f);
        let env = common::wt::gen_wt_env(&mut r);
        let (ty, _) = common::wt::gen_wt_type(&env, &mut r, 8);
        find(&ty, &mut seen);
    }
    assert!(seen.0 > 30, "generator reached Unit/Empty only {} times in 300", seen.0);
    assert!(
        seen.1 > 5,
        "generator reached Unit/Empty at a NON-ZERO level only {} times in 300 — \
         the level-indexing round would be covered only at level 0",
        seen.1,
    );
}

// -------------------------------------------------------------------------
// Two sides both spelled `Vec` (`Conv::vec_ty`, 2026-09-11;
// docs/wf-former-design.md §5). The verdicts here are the encoding's — every
// case below held before the rule and is pinned so that the rule stays a
// shortcut and never becomes a stricter or looser judgment than the
// reductions give.
// -------------------------------------------------------------------------

fn unit() -> Type {
    Type::Unit { level: c(0) }
}

fn lit(n: u64) -> Term {
    if n == 0 { Term::Zero } else { Term::NatLit(n.into()) }
}

#[test]
fn spelled_vectors_at_length_zero_convert_whatever_their_elements() {
    let g = nil_ctx();
    // Both are `Unit`; the element types are not compared at all.
    conv_ty(&g, &vec(Type::Nat, nat(0)), &vec(unit(), nat(0)), c(0));
    conv_ty(&g, &vec(Type::Nat, lit(0)), &vec(sigma(unit(), unit()), Term::Zero), c(0));
}

#[test]
fn spelled_vectors_at_equal_positive_length_need_convertible_elements() {
    let g = nil_ctx();
    conv_ty(&g, &vec(Type::Nat, nat(3)), &vec(Type::Nat, nat(3)), c(0));
    // Packed against unary: the lengths are compared as `Nat` terms.
    conv_ty(&g, &vec(Type::Nat, lit(3)), &vec(Type::Nat, nat(3)), c(0));
    // The elements are compared as types, not spellings.
    conv_ty(&g, &vec(vec(Type::Nat, nat(1)), nat(2)), &vec(sigma(Type::Nat, unit()), nat(2)), c(0));
    not_conv_ty(&g, &vec(Type::Nat, nat(3)), &vec(unit(), nat(3)), c(0));
}

#[test]
fn spelled_vectors_at_different_canonical_lengths_do_not_convert() {
    let g = nil_ctx();
    not_conv_ty(&g, &vec(Type::Nat, nat(2)), &vec(Type::Nat, nat(3)), c(0));
    not_conv_ty(&g, &vec(Type::Nat, nat(0)), &vec(Type::Nat, nat(1)), c(0));
    not_conv_ty(&g, &vec(Type::Nat, lit(2)), &vec(Type::Nat, lit(3)), c(0));
}

#[test]
fn spelled_vector_against_a_neutral_length_takes_the_reductions_verdict() {
    let g = ext(&nil_ctx(), Type::Nat, c(0));
    // A canonical length against a stuck one: `Σ` against a neutral `Vec`.
    not_conv_ty(&g, &vec(Type::Nat, nat(1)), &vec(Type::Nat, v(0)), c(0));
    not_conv_ty(&g, &vec(Type::Nat, Term::Succ(rt(v(0)))), &vec(Type::Nat, nat(1)), c(0));
    // Two stuck lengths: structural, as before.
    conv_ty(&g, &vec(Type::Nat, Term::Succ(rt(v(0)))), &vec(Type::Nat, Term::Succ(rt(v(0)))), c(0));
    not_conv_ty(&g, &vec(Type::Nat, Term::Succ(rt(v(0)))), &vec(unit(), Term::Succ(rt(v(0)))), c(0));
}

#[test]
fn spelled_vector_against_its_encoding_still_converts() {
    let g = nil_ctx();
    // Only one side is spelled `Vec`: the rule stands aside and the
    // reductions decide.
    conv_ty(&g, &vec(Type::Nat, nat(2)), &sigma(Type::Nat, sigma(Type::Nat, unit())), c(0));
    conv_ty(&g, &sigma(Type::Nat, vec(Type::Nat, nat(1))), &vec(Type::Nat, lit(2)), c(0));
    not_conv_ty(&g, &vec(Type::Nat, nat(2)), &sigma(Type::Nat, unit()), c(0));
}

/// The literal shape the elaborator emits for `[x, …, x] : [T; n]`: a
/// right-nested pair whose every level is annotated with its tail's `Vec`
/// type. The element is the variable `x : T` at the head of Γ.
fn pair_literal(elem: &Type, n: usize) -> Term {
    let mut acc = Term::Triv { level: c(0) };
    for j in (0..n).rev() {
        let tail = elem.shift_local(1);
        acc = pair(elem.clone(), vec(tail, lit((n - 1 - j) as u64)), v(0), acc);
    }
    acc
}

/// An element type whose comparison is not free: a right-nested `Σ` of
/// units, the shape a decoded record code has.
fn wide_unit(depth: usize) -> Type {
    let mut t = unit();
    for _ in 0..depth {
        t = sigma(unit(), t);
    }
    t
}

/// The literal at the elaborator's shape checks, at a length where the
/// encodings' `n²/2` element comparisons were seconds. Its *scaling* is the
/// bench family `conv/vec-literal`'s datum (quadratic through the encodings,
/// linear now); fuel does not see the difference — the repeated work was the
/// element type's forcing and weakening, not counted steps — so no fuel pin
/// can stand in for the bench here.
#[test]
fn nested_pair_literal_at_the_elaborators_shape_checks() {
    let elem = wide_unit(8);
    let g = ext(&nil_ctx(), elem.clone(), c(0));
    let t = pair_literal(&elem, 256);
    ck(&g, &t, &vec(elem, lit(256)), c(0));
}
