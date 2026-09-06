//! Property tests for the lazy decode's interaction with substitution, on
//! the same randomly generated well-scoped terms as `subst_laws.rs`
//! (`common/mod.rs`'s generators; `gen_type` reaches `El` of every code
//! former through `gen_term`).
//!
//! The law the elaborator's emission sites lean on
//! (`crates/elab/src/inductive.rs`'s `decode_deep`,
//! docs/annotation-component-respell-design.md §2.4): pushing the `El` decode
//! rules of `reduce::step_type` through every type component of a type
//! commutes with local substitution,
//!
//! - decode:  decode(T[δ]) = decode(T)[δ]
//!
//! so a projection chain that writes link `k`'s tail as the decoded type and
//! link `k+1`'s pair type as the decode of *that tail instantiated* states
//! the same type twice, and the kernel's syntactic shortcut sees it. The
//! decode here is the kernel-side twin of `decode_deep`, written against
//! `step_type` directly so the law is about the kernel's rules and not about
//! the elaborator's copy of them; `decode_roundtrip` pins that the twin does
//! what the elaborator's does on the one input that matters, `El ⌜T⌝` for a
//! canonical former.

mod common;

use std::rc::Rc;

use common::*;
use heather_kernel::reduce::step_type;
use heather_kernel::term::{LocalCtx, Term, Type};

const CASES: u64 = 300;
const BUDGET: u32 = 10;

/// Is `t` an `El` of a canonical code former — the guard the elaborator's
/// `decoded` uses, so the decode is a context-free rewrite and never a δ.
fn is_literal(t: &Type) -> bool {
    matches!(
        t,
        Type::El { tm, .. } if matches!(
            &**tm,
            Term::TmNat
                | Term::TmTy(_)
                | Term::TmPi { .. }
                | Term::TmId { .. }
                | Term::TmSigma { .. }
                | Term::TmUnit { .. }
                | Term::TmEmpty { .. }
                | Term::TmSum { .. }
                | Term::TmW { .. }
                | Term::TmVec { .. }
                | Term::TmFin { .. }
                | Term::TmWf { .. }
                | Term::TmSEq { .. }
        )
    )
}

/// `step_type` at the head while the head is a literal, then into every
/// type component. The `Wf` arity's `Case` annotations are left alone here:
/// `decode_deep` decodes them too, but they are terms and `step_type` is a
/// type rule; the type-component law is what the emission sites rely on.
fn decode(t: &Type) -> Type {
    let empty = LocalCtx::nil();
    let mut cur = t.clone();
    while is_literal(&cur) {
        match step_type(&cur, &empty) {
            Some(next) => cur = next,
            None => break,
        }
    }
    let d = |x: &Rc<Type>| Rc::new(decode(x));
    match &cur {
        Type::Pi { dom_level, cod_level, dom, cod } => Type::Pi {
            dom_level: dom_level.clone(),
            cod_level: cod_level.clone(),
            dom: d(dom),
            cod: d(cod),
        },
        Type::Sigma { fst_level, snd_level, fst, snd } => Type::Sigma {
            fst_level: fst_level.clone(),
            snd_level: snd_level.clone(),
            fst: d(fst),
            snd: d(snd),
        },
        Type::Sum { lhs_level, rhs_level, lhs, rhs } => Type::Sum {
            lhs_level: lhs_level.clone(),
            rhs_level: rhs_level.clone(),
            lhs: d(lhs),
            rhs: d(rhs),
        },
        Type::Vec { level, elem, len } => Type::Vec {
            level: level.clone(),
            elem: d(elem),
            len: Rc::clone(len),
        },
        Type::Wf { level, shape, arity } => Type::Wf {
            level: level.clone(),
            shape: d(shape),
            arity: Rc::clone(arity),
        },
        Type::Id { level, ty, lhs, rhs } => Type::Id {
            level: level.clone(),
            ty: d(ty),
            lhs: Rc::clone(lhs),
            rhs: Rc::clone(rhs),
        },
        Type::SEq { level, ty, lhs, rhs } => Type::SEq {
            level: level.clone(),
            ty: d(ty),
            lhs: Rc::clone(lhs),
            rhs: Rc::clone(rhs),
        },
        Type::Squash { level, ty } => Type::Squash {
            level: level.clone(),
            ty: d(ty),
        },
        other => other.clone(),
    }
}

/// decode(T[δ]) = decode(T)[δ], for a generated `T` in the scope `δ` targets
/// and a generated `δ` — the seeded, output-suppressed form of
/// `subst_laws.rs`, since a failing case is a type the reader should
/// regenerate, not read.
#[test]
fn decode_commutes_with_local_substitution() {
    heather_kernel::checks::set_skip_verification(heather_kernel::checks::SkipVerification::Full);
    let mut literal_cases = 0u32;
    for seed in 0..CASES {
        let mut r = Rng::new(seed ^ 0x2545f4914f6cdd1d);
        let mut sc = gen_scope(&mut r);
        let base = sc.local.base;
        let target = Shape { base, len: r.below(4) };
        let source = Shape { base, len: r.below(4) };
        sc.local = target;
        let t = gen_type(&sc, &mut r, BUDGET);
        sc.local = source;
        let d = gen_subst(&sc, &mut r, BUDGET, target); // source ⊢ target
        if is_literal(&t) {
            literal_cases += 1;
        }
        law!(seed, decode(&t.apply_local(&d)), decode(&t).apply_local(&d));
    }
    // The generators do reach the interesting case; a corpus that never
    // produced a literal head would make the law vacuous.
    assert!(literal_cases > 0, "no generated type was an `El` of a code former");
}

/// The twin agrees with the elaborator's `decode_deep` on its defining case:
/// one decode step on `El ⌜T⌝` for each canonical former is the kernel's
/// `step_type` rule, and the deep walk then leaves a *neutral* `El` — a
/// variable's or a global's code — exactly as it is.
#[test]
fn decode_roundtrip_on_literals_and_neutrals() {
    let nat = Type::El {
        level: heather_kernel::level::Level::Zero,
        tm: Rc::new(Term::TmNat),
    };
    assert_eq!(decode(&nat), Type::Nat);
    let sigma = Type::El {
        level: heather_kernel::level::Level::Zero,
        tm: Rc::new(Term::TmSigma {
            fst_level: heather_kernel::level::Level::Zero,
            snd_level: heather_kernel::level::Level::Zero,
            fst: Rc::new(Term::TmNat),
            snd: Rc::new(Term::TmUnit {
                level: heather_kernel::level::Level::Zero,
            }),
        }),
    };
    let Type::Sigma { fst, snd, .. } = decode(&sigma) else {
        panic!("a Σ code decodes to a Σ")
    };
    assert_eq!(*fst, Type::Nat);
    assert_eq!(
        *snd,
        Type::Unit {
            level: heather_kernel::level::Level::Zero
        }
    );
    let neutral = Type::El {
        level: heather_kernel::level::Level::Zero,
        tm: Rc::new(Term::Var(heather_kernel::term::LocalVar(0))),
    };
    assert_eq!(decode(&neutral), neutral);
}
