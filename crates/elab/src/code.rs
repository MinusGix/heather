//! Quoting a kernel type into its **code** — the `Type → Term : Ty l`
//! direction of the Tarski universe (docs/surface-polymorphism.md §2.2).
//!
//! The kernel already has the other direction: `El^l ⌜T⌝ ⇝ T` is a reduction
//! (`crates/kernel/src/reduce.rs:77`), every code has a formation rule
//! (`typing.rs:731`) and a congruence (`conv.rs:632`). So this module is the
//! elaborator's half, needed in exactly two places: a written type argument
//! (`f<List<Nat>>(…)`) and a solved implicit one.
//!
//! It is **partial on purpose**. A former with no code — a universe above the
//! ones that have one, a `UPi` — returns `None` and becomes a diagnostic
//! rather than a wrong term. And it cannot be silently wrong in the other
//! direction either: a code that decodes to something else is a kernel
//! rejection when the declaration is re-checked, since the parameter's type
//! is `El A` and the argument's is whatever `⌜·⌝` actually said.

use std::rc::Rc;

use heather_kernel::term::{Term, Type};

/// `⌜T⌝ : Ty l`, where `l` is `T`'s level. `None` for a type this universe
/// has no code for.
///
/// Every arm mirrors one line of `reduce.rs`'s `decode`, in the same order,
/// so the round trip `El ⌜T⌝ ⇝ T` is checkable by reading the two side by
/// side rather than by trusting a comment. `El` itself is the identity: the
/// code of a decoded code is the code.
pub(crate) fn code_of(t: &Type) -> Option<Term> {
    Some(match t {
        Type::Nat => Term::TmNat,
        Type::Ty(l) => Term::TmTy(l.clone()),
        Type::El { tm, .. } => (**tm).clone(),
        Type::Pi { dom_level, cod_level, dom, cod } => Term::TmPi {
            dom_level: dom_level.clone(),
            cod_level: cod_level.clone(),
            dom: Rc::new(code_of(dom)?),
            cod: Rc::new(code_of(cod)?),
        },
        Type::Id { level, ty, lhs, rhs } => Term::TmId {
            level: level.clone(),
            ty: Rc::new(code_of(ty)?),
            lhs: Rc::clone(lhs),
            rhs: Rc::clone(rhs),
        },
        Type::Sigma { fst_level, snd_level, fst, snd } => Term::TmSigma {
            fst_level: fst_level.clone(),
            snd_level: snd_level.clone(),
            fst: Rc::new(code_of(fst)?),
            snd: Rc::new(code_of(snd)?),
        },
        Type::Unit { level } => Term::TmUnit { level: level.clone() },
        Type::Empty { level } => Term::TmEmpty { level: level.clone() },
        Type::Sum { lhs_level, rhs_level, lhs, rhs } => Term::TmSum {
            lhs_level: lhs_level.clone(),
            rhs_level: rhs_level.clone(),
            lhs: Rc::new(code_of(lhs)?),
            rhs: Rc::new(code_of(rhs)?),
        },
        Type::W { shape_level, pos_level, shape, pos } => Term::TmW {
            shape_level: shape_level.clone(),
            pos_level: pos_level.clone(),
            shape: Rc::new(code_of(shape)?),
            pos: Rc::new(code_of(pos)?),
        },
        Type::Vec { level, elem, len } => Term::TmVec {
            level: level.clone(),
            elem: Rc::new(code_of(elem)?),
            len: Rc::clone(len),
        },
        Type::Fin { len } => Term::TmFin { len: Rc::clone(len) },
        Type::Squash { level, ty } => Term::TmSquash {
            level: level.clone(),
            ty: Rc::new(code_of(ty)?),
        },
        // The index equation of a forded family
        // (`docs/inductive-fording-lowering.md` §6.2): having a code is what
        // lets a forded family be a *field* of another declaration.
        Type::SEq { level, ty, lhs, rhs } => Term::TmSEq {
            level: level.clone(),
            ty: Rc::new(code_of(ty)?),
            lhs: Rc::clone(lhs),
            rhs: Rc::clone(rhs),
        },
        Type::Wf { level, shape, arity } => Term::TmWf {
            level: level.clone(),
            shape: Rc::new(code_of(shape)?),
            arity: Rc::clone(arity),
        },
        // No code: `UPi` is layer m, and the box/context formers are not
        // types a type argument can be.
        _ => return None,
    })
}
