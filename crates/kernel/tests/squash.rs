//! Propositional truncation: formation, irrelevance, and dependent beta.

use heather_kernel::rc::Rc;

use heather_kernel::conv::conv_term;
use heather_kernel::layer::Layer;
use heather_kernel::level::Level;
use heather_kernel::reduce::whnf_term;
use heather_kernel::term::{GlobalCtx, LocalCtx, LocalSubst, LocalVar, Term, Type};
use heather_kernel::typing::{check_term, check_type};

const FUEL: u64 = 100_000;

fn rt(t: Term) -> Rc<Term> {
    Rc::new(t)
}

fn rty(t: Type) -> Rc<Type> {
    Rc::new(t)
}

fn squash_nat(t: Term) -> Term {
    Term::Squash { level: Level::Zero, ty: rty(Type::Nat), tm: rt(t) }
}

fn squash_nat_ty() -> Type {
    Type::Squash { level: Level::Zero, ty: rty(Type::Nat) }
}

#[test]
fn squash_forms_and_its_witnesses_are_irrelevant() {
    let gamma = LocalCtx::nil();
    let ty = squash_nat_ty();
    check_type(&GlobalCtx::default(), 0, Layer::Prog, &gamma, &ty, &Level::Zero, FUEL)
        .unwrap();
    let a = squash_nat(Term::Zero);
    let b = squash_nat(Term::Succ(rt(Term::Zero)));
    check_term(
        &GlobalCtx::default(),
        0,
        Layer::Prog,
        &gamma,
        &a,
        &ty,
        &Level::Zero,
        FUEL,
    )
    .unwrap();
    conv_term(
        &GlobalCtx::default(),
        &gamma,
        Layer::Prog,
        &a,
        &b,
        &ty,
        &Level::Zero,
        FUEL,
    )
    .unwrap();
}

#[test]
fn dependent_elimination_beta_reveals_only_inside_another_squash() {
    let gamma = LocalCtx::nil();
    // B(z) genuinely mentions z: Id(∥Nat∥; z; z).
    let motive = Type::Id {
        level: Level::Zero,
        ty: rty(squash_nat_ty().shift_local(1)),
        lhs: rt(Term::Var(LocalVar(0))),
        rhs: rt(Term::Var(LocalVar(0))),
    };
    let packed_x = squash_nat(Term::Var(LocalVar(0)));
    let branch_inner = motive.apply_local(
        &LocalSubst::id(&gamma).shift_local(1).extended(rt(packed_x.clone())),
    );
    let branch = Term::Squash {
        level: Level::Zero,
        ty: rty(branch_inner),
        tm: rt(Term::Refl {
            level: Level::Zero,
            ty: rty(squash_nat_ty().shift_local(1)),
            tm: rt(packed_x),
        }),
    };
    let elim = Term::ElimSquash {
        src_level: Level::Zero,
        dst_level: Level::Zero,
        src_ty: rty(Type::Nat),
        motive: rty(motive),
        case: rt(branch.clone()),
        scrut: rt(squash_nat(Term::Zero)),
    };
    let result_inner = Type::Id {
        level: Level::Zero,
        ty: rty(squash_nat_ty()),
        lhs: rt(squash_nat(Term::Zero)),
        rhs: rt(squash_nat(Term::Zero)),
    };
    let result_ty = Type::Squash { level: Level::Zero, ty: rty(result_inner) };
    check_term(
        &GlobalCtx::default(),
        0,
        Layer::Prog,
        &gamma,
        &elim,
        &result_ty,
        &Level::Zero,
        FUEL,
    )
    .unwrap();

    let expected = branch.apply_local(&LocalSubst::id(&gamma).extended(rt(Term::Zero)));
    assert_eq!(whnf_term(&elim, &gamma, FUEL), Ok(expected));
}


// ---------------------------------------------------------------------------
// unsquash_empty (docs/kernel/metatheory-ch07-extensions.md §29)
// ---------------------------------------------------------------------------

fn empty_ty() -> Type {
    Type::Empty { level: Level::Zero }
}

fn squash_empty_ty() -> Type {
    Type::Squash { level: Level::Zero, ty: rty(empty_ty()) }
}

fn unsquash(q: Term) -> Term {
    Term::UnsquashEmpty { level: Level::Zero, scrut: rt(q) }
}

fn check_at(gamma: &LocalCtx, t: &Term, ty: &Type) -> Result<(), heather_kernel::typing::TypeError> {
    check_term(&GlobalCtx::default(), 0, Layer::Prog, gamma, t, ty, &Level::Zero, FUEL)
}

#[test]
fn unsquash_empty_releases_a_squashed_absurdity() {
    // q : ∥Empty∥ ⊢ unsquash_empty(q) : Empty, and it is neutral.
    let gamma = LocalCtx::nil().extended(rty(squash_empty_ty()), Level::Zero);
    let t = unsquash(Term::Var(LocalVar(0)));
    check_at(&gamma, &t, &empty_ty()).unwrap();
    assert_eq!(whnf_term(&t, &gamma, FUEL).unwrap(), t, "neutral on a neutral argument");
    // The release fed to `elim_Empty` proves anything: here, `Nat`.
    let anything = Term::ElimEmpty {
        level: Level::Zero,
        scrut_level: Level::Zero,
        motive: rty(Type::Nat),
        scrut: rt(t),
    };
    check_at(&gamma, &anything, &Type::Nat).unwrap();
}

#[test]
fn unsquash_empty_refuses_a_squash_of_another_type() {
    // Negative control: q : ∥Nat∥ is not a squashed absurdity.
    let gamma = LocalCtx::nil().extended(rty(squash_nat_ty()), Level::Zero);
    let t = unsquash(Term::Var(LocalVar(0)));
    assert!(matches!(
        check_at(&gamma, &t, &empty_ty()),
        Err(heather_kernel::typing::TypeError::NotConvertible)
    ));
    // Nor is an unsquashed `Empty` an argument.
    let gamma = LocalCtx::nil().extended(rty(empty_ty()), Level::Zero);
    let t = unsquash(Term::Var(LocalVar(0)));
    assert!(matches!(
        check_at(&gamma, &t, &empty_ty()),
        Err(heather_kernel::typing::TypeError::NotConvertible)
    ));
}

#[test]
fn unsquash_empty_of_a_squash_is_its_payload() {
    // x : Empty ⊢ unsquash_empty(squash(Empty; x)) ⇝ x, by both reducers.
    let gamma = LocalCtx::nil().extended(rty(empty_ty()), Level::Zero);
    let x = Term::Var(LocalVar(0));
    let t = rt(unsquash(Term::Squash { level: Level::Zero, ty: rty(empty_ty()), tm: rt(x.clone()) }));
    check_at(&gamma, &t, &empty_ty()).unwrap();
    assert_eq!(whnf_term(&t, &gamma, FUEL).unwrap(), x);
    let arena = heather_kernel::value::ValueArena::new();
    let v = heather_kernel::eval::whnf_value(
        &arena,
        &t,
        &gamma,
        heather_kernel::reduce::Defs::opaque(),
        FUEL,
    )
    .unwrap();
    assert!(
        matches!(&*v, heather_kernel::value::Val::Neutral(_)),
        "the value machine fires β too, leaving the variable"
    );
}

#[test]
fn two_releases_convert_whatever_their_arguments() {
    // p, q : ∥Empty∥ ⊢ unsquash_empty(p) ≈ unsquash_empty(q) : Empty.
    let gamma = LocalCtx::nil()
        .extended(rty(squash_empty_ty()), Level::Zero)
        .extended(rty(squash_empty_ty()), Level::Zero);
    let a = unsquash(Term::Var(LocalVar(0)));
    let b = unsquash(Term::Var(LocalVar(1)));
    conv_term(&GlobalCtx::default(), &gamma, Layer::Prog, &a, &b, &empty_ty(), &Level::Zero, FUEL)
        .unwrap();
}
