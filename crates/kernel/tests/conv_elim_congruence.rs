//! Typed neutral congruence for the eliminators
//! (issues/conversion-typed-eliminator-congruence.md; heather-coq
//! `ELIM_CONGRUENCE.md`): two neutral `case`s, `elim_W`s, `elim_Wf`s and
//! `J`s compare their scrutinees, the motive's level, the motive and the
//! branches, and never what the scrutinee's type forces (`A`/`B`, the
//! shape and positions or arity, `J`'s `A`/`a`/`u`, levels included).
//!
//! Each eliminator is exercised on the four axes of
//! docs/testing-generated-terms.md that apply to it: a neutral and a literal
//! scrutinee, forced annotations spelled differently but convertibly on the
//! right (`El «Nat»` for `Nat`, `(λx. x) 0` for `0`, `0 ⊔ 0` for `0`), and
//! the negative controls — a differing branch, a differing scrutinee, and a
//! motive that agrees with `Nat` on every constructor but not on the
//! neutral. Every term is checked first, because conversion presupposes
//! well-typed inputs. That the forced annotations are *skipped*, not merely
//! convertible, is pinned by fuel: the differently spelled pair converts in
//! exactly the budget of two identical spellings (`El «Nat»` against `Nat`
//! needs budget of its own, see tests/conv.rs).

use std::sync::Arc as Rc;

use heather_kernel::conv::{conv_term, ConvError};
use heather_kernel::layer::Layer;
use heather_kernel::level::Level;
use heather_kernel::term::{CtxBase, CtxEntry, GlobalCtx, LocalCtx, LocalVar, Term, Type};
use heather_kernel::typing::check_term;

const FUEL: u64 = 100_000;

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

fn num(n: u32) -> Term {
    let mut t = Term::Zero;
    for _ in 0..n {
        t = Term::Succ(rt(t));
    }
    t
}

/// `(·, x : ty₁, …)`, outermost first.
fn ctx(tys: Vec<Type>) -> LocalCtx {
    LocalCtx {
        base: CtxBase::Nil,
        entries: tys
            .into_iter()
            .map(|ty| CtxEntry { ty: rty(ty), level: Level::Zero })
            .collect::<Vec<_>>()
            .into(),
    }
}

/// `(λ^{0,0}(x : Nat). x) 0` — `0`, spelled as a β-redex.
fn beta_zero() -> Term {
    Term::App {
        fun: rt(Term::Lam {
            dom_level: Level::Zero,
            cod_level: Level::Zero,
            dom: rty(Type::Nat),
            body: rt(v(0)),
        }),
        dom_level: Level::Zero,
        cod_level: Level::Zero,
        dom: rty(Type::Nat),
        cod: rty(Type::Nat),
        arg: rt(Term::Zero),
    }
}

/// `El «Nat»` — `Nat`, spelled as a decoding.
fn el_nat() -> Type {
    Type::El { level: Level::Zero, tm: rt(Term::TmNat) }
}

/// `El «Empty»` — `Empty`, spelled as a decoding.
fn el_empty() -> Type {
    Type::El { level: Level::Zero, tm: rt(Term::TmEmpty { level: Level::Zero }) }
}

/// `0 ⊔ 0` — level `0`, spelled as a maximum.
fn zero_max() -> Level {
    Level::max(Level::Zero, Level::Zero)
}

/// `El^0 t` for a code `t : Ty 0` — the "agrees on every constructor"
/// motive is `El` of the same elimination into `Ty 0` with every branch
/// `«Nat»`.
fn el(t: Term) -> Type {
    Type::El { level: Level::Zero, tm: rt(t) }
}

fn well_typed(gamma: &LocalCtx, t: &Term, ty: &Type) {
    check_term(&GlobalCtx::default(), 0, Layer::Prog, gamma, t, ty, &Level::Zero, FUEL)
        .unwrap_or_else(|e| panic!("does not check: {e:?}"));
}

fn conv(gamma: &LocalCtx, a: &Term, b: &Term) -> Result<(), ConvError> {
    conv_term(&GlobalCtx::default(), gamma, Layer::Prog, a, b, &Type::Nat, &Level::Zero, FUEL)
}

/// The least budget `conv_term` accepts `a ≈ b : Nat` in (it is monotone).
fn min_fuel(gamma: &LocalCtx, a: &Term, b: &Term) -> u64 {
    let ok = |f| {
        conv_term(&GlobalCtx::default(), gamma, Layer::Prog, a, b, &Type::Nat, &Level::Zero, f)
            .is_ok()
    };
    assert!(ok(FUEL));
    let (mut lo, mut hi) = (0, FUEL);
    while lo + 1 < hi {
        let mid = (lo + hi) / 2;
        if ok(mid) { hi = mid } else { lo = mid }
    }
    hi
}

/// The shared checks. `elim(spelled, motive, branch, scrut)` builds an
/// elimination at `Nat`'s motive level whose forced annotations are the
/// canonical ones, or (`spelled`) differently spelled convertible ones.
/// `branch` selects between two inconvertible branch bodies. `neutral` and
/// `other` are distinct neutral scrutinees in `gamma`, `literal` a canonical
/// one; `dep_motive` agrees with `Nat` on every constructor, and `dep_at`
/// is its instance at `neutral`, the type its elimination checks at.
fn exercise(
    gamma: &LocalCtx,
    elim: &dyn Fn(bool, Type, Level, bool, Term) -> Term,
    neutral: Term,
    other: Term,
    literal: Term,
    dep_motive: Type,
    dep_at: Type,
) {
    let nat = |spelled, branch, scrut| elim(spelled, Type::Nat, Level::Zero, branch, scrut);
    for t in [
        nat(false, false, neutral.clone()),
        nat(true, false, neutral.clone()),
        nat(false, true, neutral.clone()),
        nat(false, false, other.clone()),
        nat(false, false, literal.clone()),
        nat(true, false, literal.clone()),
        nat(false, true, literal.clone()),
    ] {
        well_typed(gamma, &t, &Type::Nat);
    }
    let dep = elim(false, dep_motive, Level::Zero, false, neutral.clone());
    well_typed(gamma, &dep, &dep_at);

    // Neutral scrutinee: differently spelled forced annotations convert,
    // in the budget of identical ones.
    let left = nat(false, false, neutral.clone());
    let same = nat(false, false, neutral.clone());
    let spelled = nat(true, false, neutral.clone());
    assert_eq!(conv(gamma, &left, &spelled), Ok(()));
    assert_eq!(conv(gamma, &spelled, &left), Ok(()));
    assert_eq!(min_fuel(gamma, &left, &spelled), min_fuel(gamma, &left, &same));
    // Negative controls: a differing branch, a differing scrutinee, a
    // motive that agrees on constructors only.
    let nc = Err(ConvError::NotConvertible);
    assert_eq!(conv(gamma, &left, &nat(true, true, neutral.clone())), nc);
    assert_eq!(conv(gamma, &left, &nat(true, false, other)), nc);
    assert_eq!(conv(gamma, &left, &dep), nc);
    assert_eq!(conv(gamma, &dep, &left), nc);

    // Literal scrutinee: β decides, whatever the annotations' spelling.
    let lit = nat(false, false, literal.clone());
    assert_eq!(conv(gamma, &lit, &nat(true, false, literal.clone())), Ok(()));
    assert_eq!(conv(gamma, &lit, &nat(true, true, literal)), nc);
}

// -------------------------------------------------------------------------
// case
// -------------------------------------------------------------------------

fn sum(spelled: bool) -> (Type, Type) {
    if spelled { (el_nat(), el_nat()) } else { (Type::Nat, Type::Nat) }
}

fn case(spelled: bool, motive: Type, ml: Level, branch: bool, scrut: Term) -> Term {
    let (lhs, rhs) = sum(spelled);
    let lv = if spelled { zero_max() } else { Level::Zero };
    Term::Case {
        lhs_level: lv.clone(),
        rhs_level: lv,
        motive_level: ml,
        lhs: rty(lhs),
        rhs: rty(rhs),
        motive: rty(motive),
        case_l: rt(if branch { Term::Succ(rt(v(0))) } else { v(0) }),
        case_r: rt(v(0)),
        scrut: rt(scrut),
    }
}

#[test]
fn case_compares_scrutinee_motive_and_branches_only() {
    let s = Type::Sum {
        lhs_level: Level::Zero,
        rhs_level: Level::Zero,
        lhs: rty(Type::Nat),
        rhs: rty(Type::Nat),
    };
    let gamma = ctx(vec![s.clone(), s]);
    let inl = Term::Inl {
        lhs_level: Level::Zero,
        rhs_level: Level::Zero,
        lhs: rty(Type::Nat),
        rhs: rty(Type::Nat),
        val: rt(num(2)),
    };
    // z. El(case(z; Ty 0; «Nat»; «Nat»)) — Nat at inl x and inr y.
    let dep = |z: Term| el(Term::Case {
        lhs_level: Level::Zero,
        rhs_level: Level::Zero,
        motive_level: c(1),
        lhs: rty(Type::Nat),
        rhs: rty(Type::Nat),
        motive: rty(Type::Ty(Level::Zero)),
        case_l: rt(Term::TmNat),
        case_r: rt(Term::TmNat),
        scrut: rt(z),
    });
    exercise(&gamma, &case, v(0), v(1), inl, dep(v(0)), dep(v(0)));
}

// -------------------------------------------------------------------------
// elim_W
// -------------------------------------------------------------------------

/// `W^{0,0}(x : Nat). Empty` — Nat-labeled leaves.
fn w_leaves() -> Type {
    Type::W {
        shape_level: Level::Zero,
        pos_level: Level::Zero,
        shape: rty(Type::Nat),
        pos: rty(Type::Empty { level: Level::Zero }),
    }
}

/// `sup(n; λ(y : Empty). elim_Empty(_. W; y))`.
fn leaf(n: u32) -> Term {
    Term::Sup {
        shape_level: Level::Zero,
        pos_level: Level::Zero,
        shape_ty: rty(Type::Nat),
        pos_ty: rty(Type::Empty { level: Level::Zero }),
        label: rt(num(n)),
        children: rt(Term::Lam {
            dom_level: Level::Zero,
            cod_level: Level::Zero,
            dom: rty(Type::Empty { level: Level::Zero }),
            body: rt(Term::ElimEmpty {
                level: Level::Zero,
                scrut_level: Level::Zero,
                motive: rty(w_leaves()),
                scrut: rt(v(0)),
            }),
        }),
    }
}

/// The step binds `a, f, ih`; branch `a` or `su a`.
fn elim_w(spelled: bool, motive: Type, ml: Level, branch: bool, scrut: Term) -> Term {
    let lv = if spelled { zero_max() } else { Level::Zero };
    Term::ElimW {
        shape_level: lv.clone(),
        pos_level: lv,
        motive_level: ml,
        shape: rty(if spelled { el_nat() } else { Type::Nat }),
        pos: rty(if spelled { el_empty() } else { Type::Empty { level: Level::Zero } }),
        motive: rty(motive),
        step: rt(if branch { Term::Succ(rt(v(2))) } else { v(2) }),
        scrut: rt(scrut),
    }
}

#[test]
fn elim_w_compares_scrutinee_motive_and_step_only() {
    let gamma = ctx(vec![w_leaves(), w_leaves()]);
    // z. El(elim_W(z; Ty 0; «Nat»)) — Nat at every sup.
    let dep = |z: Term| el(Term::ElimW {
        shape_level: Level::Zero,
        pos_level: Level::Zero,
        motive_level: c(1),
        shape: rty(Type::Nat),
        pos: rty(Type::Empty { level: Level::Zero }),
        motive: rty(Type::Ty(Level::Zero)),
        step: rt(Term::TmNat),
        scrut: rt(z),
    });
    exercise(&gamma, &elim_w, v(0), v(1), leaf(2), dep(v(0)), dep(v(0)));
}

// -------------------------------------------------------------------------
// elim_Wf
// -------------------------------------------------------------------------

/// `Wf^0(x : Nat). 0` — Nat-labeled leaves.
fn wf_leaves() -> Type {
    Type::Wf { level: Level::Zero, shape: rty(Type::Nat), arity: rt(Term::Zero) }
}

/// `sup_f(n; ⟨⟩)` — the children are `Vec(Wf; 0) ⇝ Unit`.
fn leaf_f(n: u32) -> Term {
    Term::Supf {
        level: Level::Zero,
        shape: rty(Type::Nat),
        arity: rt(Term::Zero),
        label: rt(num(n)),
        children: rt(Term::Triv { level: Level::Zero }),
    }
}

/// The step binds `a, cs, ih`; branch `a` or `su a`. Spelled: the shape
/// `El «Nat»`, the arity `(λx. x) 0`, the level `0 ⊔ 0`.
fn elim_wf(spelled: bool, motive: Type, ml: Level, branch: bool, scrut: Term) -> Term {
    Term::ElimWf {
        level: if spelled { zero_max() } else { Level::Zero },
        motive_level: ml,
        shape: rty(if spelled { el_nat() } else { Type::Nat }),
        arity: rt(if spelled { beta_zero() } else { Term::Zero }),
        motive: rty(motive),
        step: rt(if branch { Term::Succ(rt(v(2))) } else { v(2) }),
        scrut: rt(scrut),
    }
}

#[test]
fn elim_wf_compares_scrutinee_motive_and_step_only() {
    let gamma = ctx(vec![wf_leaves(), wf_leaves()]);
    // z. El(elim_Wf(z; Ty 0; «Nat»)) — Nat at every sup_f.
    let dep = |z: Term| el(Term::ElimWf {
        level: Level::Zero,
        motive_level: c(1),
        shape: rty(Type::Nat),
        arity: rt(Term::Zero),
        motive: rty(Type::Ty(Level::Zero)),
        step: rt(Term::TmNat),
        scrut: rt(z),
    });
    exercise(&gamma, &elim_wf, v(0), v(1), leaf_f(2), dep(v(0)), dep(v(0)));
}

// -------------------------------------------------------------------------
// J
// -------------------------------------------------------------------------

/// `Id^0(Nat; 0; 0)`.
fn id00() -> Type {
    Type::Id { level: Level::Zero, ty: rty(Type::Nat), lhs: rt(Term::Zero), rhs: rt(Term::Zero) }
}

/// The motive binds `y, p`; the refl case is `0` or `1`. Spelled: `A` as
/// `El «Nat»`, `a` and `u` as `(λx. x) 0`, `A`'s level as `0 ⊔ 0`.
fn j(spelled: bool, motive: Type, ml: Level, branch: bool, proof: Term) -> Term {
    Term::J {
        ty_level: if spelled { zero_max() } else { Level::Zero },
        motive_level: ml,
        ty: rty(if spelled { el_nat() } else { Type::Nat }),
        lhs: rt(if spelled { beta_zero() } else { Term::Zero }),
        motive: rty(motive),
        case: rt(if branch { num(1) } else { Term::Zero }),
        rhs: rt(if spelled { beta_zero() } else { Term::Zero }),
        proof: rt(proof),
    }
}

#[test]
fn j_compares_proof_motive_and_case_only() {
    let gamma = ctx(vec![id00(), id00()]);
    let refl = Term::Refl { level: Level::Zero, ty: rty(Type::Nat), tm: rt(Term::Zero) };
    // y p. El(J(Nat; 0; _ _. Ty 0; «Nat»; y; p)) — Nat at (0, refl 0).
    let dep = |y: Term, p: Term| el(Term::J {
        ty_level: Level::Zero,
        motive_level: c(1),
        ty: rty(Type::Nat),
        lhs: rt(Term::Zero),
        motive: rty(Type::Ty(Level::Zero)),
        case: rt(Term::TmNat),
        rhs: rt(y),
        proof: rt(p),
    });
    // The motive's own y, p are v(1), v(0); its instance at the neutral
    // proof v(0) has y := 0.
    exercise(&gamma, &j, v(0), v(1), refl, dep(v(1), v(0)), dep(Term::Zero, v(0)));
}
