//! Codes and recursor branches for `Vec`/`Fin`/`Wf`: phase 3 of the landing
//! (`docs/wf-former-design.md` §6, `issues/wf-former.md`).
//!
//! Phases 1–2 gated all three formers out of layer c so that the branch
//! bundle stayed exhaustive over the layer-c *syntactic formers* — which is
//! the actual invariant. It is not "every boxed code is recursable": DeLaM
//! ch. 06's neutral grammar (`06_…tex:31–38`) lists
//! `elim_Typ(…; box U^δ)` and `elim_Trm(…; box u^δ)` as neutral and says
//! *"for the recursive principles, we block on global variables"*, so
//! global variables are legal at layer c and deliberately have no branch
//! (`reduce.rs::recursors_block_on_boxed_global_variables`).
//! This file is what lets the gate go: the
//! encodings `TmVec`/`TmFin`/`TmWf` decode through `El`, the formers and
//! their intro/elim forms are accepted at layer c, and — the sharp test —
//! the **identity recursor** round-trips every one of them in a single
//! β-step. That last property exercises the eight new branch telescopes
//! against `reduce.rs`'s `fire` payload wiring: a telescope wrong in either
//! `rec.rs` or `reduce.rs` makes the re-boxed code ill-typed or unequal.

mod common;

use heather_kernel::rc::Rc;

use common::wt::{gen_encoding, gen_wt_env, gen_wt_type, identity_branches, identity_motives, FUEL};
use common::Rng;
use heather_kernel::conv::conv_type;
use heather_kernel::layer::Layer;
use heather_kernel::level::Level;
use heather_kernel::reduce::whnf_term;
use heather_kernel::term::{GlobalCtx, LocalCtx, LocalVar, Term, Type};
use heather_kernel::typing::{check_term, check_type};

// -------------------------------------------------------------------------
// Helpers — the Tree of `tests/wf.rs`, rebuilt at layer c
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

fn nil_ctx() -> LocalCtx {
    LocalCtx::nil()
}

fn nat(n: u64) -> Term {
    let mut t = Term::Zero;
    for _ in 0..n {
        t = Term::Succ(rt(t));
    }
    t
}

/// `Unit + Unit` — the tag of `Tree { Leaf, Node(Tree, Tree) }`.
fn shape() -> Type {
    Type::Sum {
        lhs_level: Level::Zero,
        rhs_level: Level::Zero,
        lhs: rty(Type::Unit { level: Level::Zero }),
        rhs: rty(Type::Unit { level: Level::Zero }),
    }
}

/// The arity `case x of inl _ ⇒ 0 | inr _ ⇒ 2`, in `(Γ, x : Unit + Unit)`.
fn arity() -> Term {
    Term::Case {
        lhs_level: Level::Zero,
        rhs_level: Level::Zero,
        motive_level: Level::Zero,
        lhs: rty(Type::Unit { level: Level::Zero }),
        rhs: rty(Type::Unit { level: Level::Zero }),
        motive: rty(Type::Nat),
        case_l: rt(Term::Zero),
        case_r: rt(nat(2)),
        scrut: rt(Term::Var(LocalVar(0))),
    }
}

fn tree() -> Type {
    Type::Wf { level: Level::Zero, shape: rty(shape()), arity: rt(arity()) }
}

/// `inl ⟨⟩ : Unit + Unit` — the `Leaf` tag.
fn leaf_tag() -> Term {
    Term::Inl {
        lhs_level: Level::Zero,
        rhs_level: Level::Zero,
        lhs: rty(Type::Unit { level: Level::Zero }),
        rhs: rty(Type::Unit { level: Level::Zero }),
        val: rt(Term::Triv { level: Level::Zero }),
    }
}

/// `sup_f(x:S. n; inl ⟨⟩; ⟨⟩)` — arity 0, so the children tuple is `Unit`.
fn leaf() -> Term {
    Term::Supf {
        level: Level::Zero,
        shape: rty(shape()),
        arity: rt(arity()),
        label: rt(leaf_tag()),
        children: rt(Term::Triv { level: Level::Zero }),
    }
}

/// `elim_Wf (z. Nat) (a cs ih. 0) leaf : Nat` — a closed eliminator whose
/// motive is constant, so it needs nothing from the step telescope.
fn elim_leaf() -> Term {
    Term::ElimWf {
        level: Level::Zero,
        motive_level: Level::Zero,
        shape: rty(shape()),
        arity: rt(arity()),
        motive: rty(Type::Nat),
        step: rt(Term::Zero),
        scrut: rt(leaf()),
    }
}

fn check_ty_at(layer: Layer, t: &Type, l: &Level) {
    check_type(&GlobalCtx::default(), 0, layer, &nil_ctx(), t, l, FUEL)
        .unwrap_or_else(|e| panic!("{t:?} must check at {layer:?}: {e:?}"));
}

fn check_tm_at(layer: Layer, t: &Term, ty: &Type, l: &Level) {
    check_term(&GlobalCtx::default(), 0, layer, &nil_ctx(), t, ty, l, FUEL)
        .unwrap_or_else(|e| panic!("{t:?} must check at {layer:?}: {e:?}"));
}

// -------------------------------------------------------------------------
// The encodings and their `El` decoding (§6)
// -------------------------------------------------------------------------

#[test]
fn codes_check_and_decode() {
    // Vec^0(Nat; 2) : Ty 0, and El of it is the type former.
    let code_vec = Term::TmVec { level: Level::Zero, elem: rt(Term::TmNat), len: rt(nat(2)) };
    check_tm_at(Layer::Code, &code_vec, &Type::Ty(Level::Zero), &c(1));
    let el_vec = Type::El { level: Level::Zero, tm: rt(code_vec.clone()) };
    conv_type(
        &GlobalCtx::default(),
        &nil_ctx(),
        Layer::Prog,
        &el_vec,
        &Type::Vec { level: Level::Zero, elem: rty(Type::Nat), len: rt(nat(2)) },
        &c(0),
        FUEL,
    )
    .expect("El (Vec code) ⇝ Vec");

    // Fin(2) : Ty 0 — at level 0 whatever the length.
    let code_fin = Term::TmFin { len: rt(nat(2)) };
    check_tm_at(Layer::Code, &code_fin, &Type::Ty(Level::Zero), &c(1));
    conv_type(
        &GlobalCtx::default(),
        &nil_ctx(),
        Layer::Prog,
        &Type::El { level: Level::Zero, tm: rt(code_fin) },
        &Type::Fin { len: rt(nat(2)) },
        &c(0),
        FUEL,
    )
    .expect("El (Fin code) ⇝ Fin");

    // Wf^0(x : Unit + Unit). n : Ty 0 — the shape decodes, the arity rides
    // along under the same binder.
    let code_shape = Term::TmSum {
        lhs_level: Level::Zero,
        rhs_level: Level::Zero,
        lhs: rt(Term::TmUnit { level: Level::Zero }),
        rhs: rt(Term::TmUnit { level: Level::Zero }),
    };
    let code_wf = Term::TmWf {
        level: Level::Zero,
        shape: rt(code_shape.clone()),
        arity: rt(arity()),
    };
    check_tm_at(Layer::Code, &code_wf, &Type::Ty(Level::Zero), &c(1));
    conv_type(
        &GlobalCtx::default(),
        &nil_ctx(),
        Layer::Prog,
        &Type::El { level: Level::Zero, tm: rt(code_wf) },
        &tree(),
        &c(0),
        FUEL,
    )
    .expect("El (Wf code) ⇝ Wf");
}

#[test]
fn the_layer_gate_is_gone() {
    // Phases 1–2 rejected all of these at layer c; phase 3 accepts them,
    // because every one now has a code-recursor branch.
    check_ty_at(Layer::Code, &Type::Vec { level: Level::Zero, elem: rty(Type::Nat), len: rt(nat(2)) }, &c(0));
    check_ty_at(Layer::Code, &Type::Fin { len: rt(nat(2)) }, &c(0));
    check_ty_at(Layer::Code, &tree(), &c(0));
    check_tm_at(Layer::Code, &leaf(), &tree(), &c(0));
    check_tm_at(Layer::Code, &elim_leaf(), &Type::Nat, &c(0));
}

// -------------------------------------------------------------------------
// The identity recursor round-trips the new code (the branch tables)
// -------------------------------------------------------------------------

fn identity_ty(code: Type) {
    let t = Term::ElimCodeTy {
        ty_motive_level: Level::Zero,
        tm_motive_level: Level::Zero,
        motives: identity_motives(),
        branches: identity_branches(),
        code_level: Level::Zero,
        ctx: nil_ctx(),
        scrut: rt(Term::BoxTy(rty(code.clone()))),
    };
    let expect = Type::CodeTy { ctx: nil_ctx(), level: Level::Zero };
    check_term(&GlobalCtx::default(), 0, Layer::Meta, &nil_ctx(), &t, &expect, &Level::Zero, FUEL)
        .unwrap_or_else(|e| panic!("identity elim^Typ ill-typed on {code:?}: {e:?}"));
    let w = whnf_term(&t, &nil_ctx(), FUEL).expect("identity elim^Typ exhausted fuel");
    assert!(w == Term::BoxTy(rty(code)), "identity elim^Typ is not the identity");
}

fn identity_tm(code: Term, ty: Type, level: Level) {
    let t = Term::ElimCodeTm {
        ty_motive_level: Level::Zero,
        tm_motive_level: Level::Zero,
        motives: identity_motives(),
        branches: identity_branches(),
        code_level: level.clone(),
        ctx: nil_ctx(),
        ty: rty(ty.clone()),
        scrut: rt(Term::BoxTm(rt(code.clone()))),
    };
    let expect = Type::CodeTm { ctx: nil_ctx(), ty: rty(ty), level };
    check_term(&GlobalCtx::default(), 0, Layer::Meta, &nil_ctx(), &t, &expect, &Level::Zero, FUEL)
        .unwrap_or_else(|e| panic!("identity elim^Trm ill-typed on {code:?}: {e:?}"));
    let w = whnf_term(&t, &nil_ctx(), FUEL).expect("identity elim^Trm exhausted fuel");
    assert!(w == Term::BoxTm(rt(code)), "identity elim^Trm is not the identity");
}

#[test]
fn identity_recursor_round_trips_vec_and_fin_types() {
    identity_ty(Type::Vec { level: Level::Zero, elem: rty(Type::Nat), len: rt(nat(2)) });
    identity_ty(Type::Fin { len: rt(nat(2)) });
}

#[test]
fn identity_recursor_round_trips_wf_type() {
    identity_ty(tree());
}

#[test]
fn identity_recursor_round_trips_the_encodings() {
    identity_tm(
        Term::TmVec { level: Level::Zero, elem: rt(Term::TmNat), len: rt(nat(2)) },
        Type::Ty(Level::Zero),
        c(1),
    );
    identity_tm(Term::TmFin { len: rt(nat(2)) }, Type::Ty(Level::Zero), c(1));
    identity_tm(
        Term::TmWf {
            level: Level::Zero,
            shape: rt(Term::TmSum {
                lhs_level: Level::Zero,
                rhs_level: Level::Zero,
                lhs: rt(Term::TmUnit { level: Level::Zero }),
                rhs: rt(Term::TmUnit { level: Level::Zero }),
            }),
            arity: rt(arity()),
        },
        Type::Ty(Level::Zero),
        c(1),
    );
}

#[test]
fn identity_recursor_round_trips_supf_and_elim_wf() {
    // The two deepest telescopes: `tm_supf` (children at the `Vec` type) and
    // `tm_elim_wf` (five recursive calls, the step under `wf_step_telescope`).
    identity_tm(leaf(), tree(), Level::Zero);
    identity_tm(elim_leaf(), Type::Nat, Level::Zero);
}

/// The motives are only used through the branch types, so a recursor whose
/// branches disagree with the tables cannot be rescued by them: swap one new
/// branch for a mismatched box and the whole recursor must fail to check.
#[test]
fn a_wrong_new_branch_poisons_the_recursor() {
    let mut bad = (*identity_branches()).clone();
    // ty_fin's telescope has no universe binder; re-boxing `Ty 0` instead of
    // `Fin u_k` is well-scoped but not the code the motive demands.
    bad.ty_fin = rt(Term::BoxTy(rty(Type::Ty(Level::Zero))));
    let t = Term::ElimCodeTy {
        ty_motive_level: Level::Zero,
        tm_motive_level: Level::Zero,
        motives: identity_motives(),
        branches: Rc::new(bad),
        code_level: Level::Zero,
        ctx: nil_ctx(),
        scrut: rt(Term::BoxTy(rty(Type::Nat))),
    };
    let expect = Type::CodeTy { ctx: nil_ctx(), level: Level::Zero };
    assert!(
        check_term(
            &GlobalCtx::default(),
            0,
            Layer::Meta,
            &nil_ctx(),
            &t,
            &expect,
            &Level::Zero,
            FUEL
        )
        .is_err(),
        "a mismatched ty_fin branch must be rejected"
    );
}

// -------------------------------------------------------------------------
// Coverage: the well-typed generator reaches the new formers
// -------------------------------------------------------------------------

/// The property suites (`conv_properties`, `conv_pair_properties`) drive the
/// new branches only if `wt.rs` actually produces the formers and their
/// encodings — this pins that, the way `tests/vec_fin.rs` pins it for the
/// scope-only generator.
#[test]
fn the_well_typed_generator_reaches_the_new_formers() {
    fn in_ty(t: &Type) -> bool {
        match t {
            Type::Vec { .. } | Type::Fin { .. } | Type::Wf { .. } => true,
            Type::Pi { dom, cod, .. } => in_ty(dom) || in_ty(cod),
            Type::Sigma { fst, snd, .. } => in_ty(fst) || in_ty(snd),
            Type::Sum { lhs, rhs, .. } => in_ty(lhs) || in_ty(rhs),
            Type::W { shape, pos, .. } => in_ty(shape) || in_ty(pos),
            Type::Id { ty, .. } => in_ty(ty),
            Type::El { tm, .. } => in_tm(tm),
            _ => false,
        }
    }
    fn in_tm(t: &Term) -> bool {
        match t {
            Term::TmVec { .. } | Term::TmFin { .. } | Term::TmWf { .. } => true,
            Term::TmPi { dom, cod, .. } => in_tm(dom) || in_tm(cod),
            Term::TmSigma { fst, snd, .. } => in_tm(fst) || in_tm(snd),
            Term::TmSum { lhs, rhs, .. } => in_tm(lhs) || in_tm(rhs),
            Term::TmW { shape, pos, .. } => in_tm(shape) || in_tm(pos),
            Term::TmId { ty, .. } => in_tm(ty),
            _ => false,
        }
    }
    let mut r = Rng::new(11);
    let mut ty_hits = 0;
    let mut code_hits = 0;
    for _ in 0..200 {
        let env = gen_wt_env(&mut r);
        if in_ty(&gen_wt_type(&env, &mut r, 4).0) {
            ty_hits += 1;
        }
        if in_tm(&gen_encoding(&env, &mut r, 4).0) {
            code_hits += 1;
        }
    }
    assert!(ty_hits > 15, "generated Vec/Fin/Wf types only {ty_hits}/200 times");
    assert!(code_hits > 15, "generated Vec/Fin/Wf codes only {code_hits}/200 times");
}
