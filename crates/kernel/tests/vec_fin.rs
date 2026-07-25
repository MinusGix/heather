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

use std::rc::Rc;

use heather_kernel::conv::{conv_term, conv_type};
use heather_kernel::layer::Layer;
use heather_kernel::level::Level;
use heather_kernel::reduce::whnf_type;
use heather_kernel::term::{CtxBase, CtxEntry, GlobalCtx, LocalCtx, LocalVar, Term, Type};
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
    assert_eq!(whnf(&vec(Type::Nat, nat(0)), &g), Type::Unit);
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
        &sigma(Type::Nat, sigma(Type::Nat, Type::Unit)),
        c(0),
    );
}

#[test]
fn fin_reduces_on_a_literal_length() {
    let g = nil_ctx();
    assert_eq!(whnf(&fin(nat(0)), &g), Type::Empty);
    conv_ty(
        &g,
        &fin(nat(2)),
        &Type::Sum {
            lhs_level: c(0),
            rhs_level: c(0),
            lhs: rty(Type::Unit),
            rhs: rty(Type::Sum {
                lhs_level: c(0),
                rhs_level: c(0),
                lhs: rty(Type::Unit),
                rhs: rty(Type::Empty),
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
    not_conv_ty(&g, &vk, &vec(Type::Unit, v(0)), c(0));
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
    let bad = Type::Vec { level: c(0), elem: rty(Type::Nat), len: rt(Term::Triv) };
    check_type(&GlobalCtx::default(), 0, Layer::Prog, &g, &bad, &c(0), FUEL)
        .expect_err("a non-Nat length must be rejected");
    // A length may be open, and may mention the context.
    let g1 = ext(&nil_ctx(), Type::Nat, c(0));
    ck_ty(&g1, &vec(Type::Nat, v(0)), c(0));
    ck_ty(&g1, &fin(v(0)), c(0));
}

/// **Known gap**, pinned so it cannot change silently:
/// `Vec^l(T; 0) ⇝ Unit` drops the level, so type-level preservation
/// (DeLaM ch. 06, Lemma *Preservation*: `⊢ T @ l` and `T ⇝ T'` imply
/// `⊢ T' @ l`) fails for every `l ≠ 0`.
///
/// `Vec` is the kernel's first type former whose whnf is chosen by a *term*.
/// `El` is chosen by a term too but cannot drop a level, because its term is
/// a code that carries one; `Vec`'s length is a bare `Nat`, and at `0` the
/// reduct `Unit` has nothing to do with `l`.
///
/// The obvious repair — letting `Unit`/`Empty` check at any level — was tried
/// and **reverted**: it gives `box Unit` a type at every level, and DeLaM
/// ch. 04 §Non-cumulativity makes unique types load-bearing for the code
/// eliminator (`rec.rs`'s `ty_unit` binds no universe and reconstructs at
/// `ℓ := 0`, so the recursor's `M[code_level/ℓ]` and the branch's `M[0/ℓ]`
/// come apart). Three candidate fixes and the full evidence are in
/// `issues/unit-level-and-vec-preservation.md`.
#[test]
fn vec_at_zero_drops_its_level_known_gap() {
    let g = nil_ctx();
    let big = Type::Vec { level: c(1), elem: rty(Type::Ty(c(0))), len: rt(Term::Zero) };
    ck_ty(&g, &big, c(1));
    assert_eq!(whnf(&big, &g), Type::Unit);
    // The reduct is *not* well-formed at the level it was declared at.
    check_type(&GlobalCtx::default(), 0, Layer::Prog, &g, &Type::Unit, &c(1), FUEL)
        .expect_err("Unit is level-polymorphic again — see the issue before celebrating");
    // …and the gap is observable where the level is actually consumed.
    let pi = |dom: Type| Type::Pi {
        dom_level: c(1),
        cod_level: c(0),
        dom: rty(dom),
        cod: rty(Type::Nat),
    };
    ck_ty(&g, &pi(big.clone()), c(1));
    check_type(&GlobalCtx::default(), 0, Layer::Prog, &g, &pi(whnf(&big, &g)), &c(1), FUEL)
        .expect_err("the reduct of a well-formed Π is well-formed — gap closed?");
    // Successor lengths preserve the level on the nose, so the nullary case
    // is the *only* one at issue…
    let big1 = Type::Vec { level: c(1), elem: rty(Type::Ty(c(0))), len: rt(nat(1)) };
    ck_ty(&g, &whnf(&big1, &g), c(1));
    // …and `Fin` is unaffected: declared at 0, both reducts land at 0.
    ck_ty(&g, &whnf(&fin(Term::Zero), &g), c(0));
    ck_ty(&g, &whnf(&fin(nat(1)), &g), c(0));
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
        ("Unit", Type::Unit),
        ("Empty", Type::Empty),
        ("Nat", Type::Nat),
        ("Fin 2", fin(nat(2))),
        ("Vec^0(Nat;0)", Type::Vec { level: c(0), elem: rty(Type::Nat), len: rt(Term::Zero) }),
    ] {
        ck_at(&t, c(0)).unwrap_or_else(|e| panic!("{name} must check at 0: {e:?}"));
        ck_at(&t, c(1)).expect_err(&format!("{name} must NOT also check at 1"));
    }
    // And the box that reads off that level stays single-typed.
    let bu = Term::BoxTy(rty(Type::Unit));
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
            pair(Type::Nat, vec(Type::Nat, nat(0)), nat(b), Term::Triv),
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
    ck(&g, &Term::Triv, &ty, c(0));
    // A variable of the type and `⟨⟩` are convertible.
    conv_tm(&g, &v(0), &Term::Triv, &ty, c(0));
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
        pair(Type::Nat, vec(Type::Nat, nat(0)), snd_fst, Term::Triv),
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
        lhs: rty(Type::Unit),
        rhs: rty(Type::Empty),
    };
    let i0 = Term::Inl {
        lhs_level: c(0),
        rhs_level: c(0),
        lhs: rty(Type::Unit),
        rhs: rty(inner.clone()),
        val: rt(Term::Triv),
    };
    let i1 = Term::Inr {
        lhs_level: c(0),
        rhs_level: c(0),
        lhs: rty(Type::Unit),
        rhs: rty(inner),
        val: rt(Term::Inl {
            lhs_level: c(0),
            rhs_level: c(0),
            lhs: rty(Type::Unit),
            rhs: rty(Type::Empty),
            val: rt(Term::Triv),
        }),
    };
    ck(&g, &i0, &fin(nat(2)), c(0));
    ck(&g, &i1, &fin(nat(2)), c(0));
    conv_term(&GlobalCtx::default(), &g, Layer::Prog, &i0, &i1, &fin(nat(2)), &c(0), FUEL)
        .expect_err("distinct indices must be distinguishable");
    // `Fin(0)` is `Empty`: it eliminates into anything.
    let g1 = ext(&nil_ctx(), fin(nat(0)), c(0));
    let absurd = Term::ElimEmpty { level: c(0), motive: rty(Type::Nat), scrut: rt(v(0)) };
    ck(&g1, &absurd, &Type::Nat, c(0));
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
    conv_ty(&nil_ctx(), &inst, &sigma(Type::Nat, sigma(Type::Nat, Type::Unit)), c(0));
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
