//! Which theorems keep their proof sealed
//! (`issues/theorem-witness-unfolding.md`, option D).
//!
//! A `theorem` binds an opaque global, as it always has; what is new is that
//! Ψ may keep its proof *sealed* beside the binding
//! ([`heather_kernel::term::GlobalCtx::sealed`]), so that a client that
//! projects a witness out of it, or matches on the branch it picked, computes
//! with what the proof built. Nothing else ever opens it.
//!
//! Keeping every proof is what the issue's probe measured at +10–31% peak
//! memory, and almost all of that is proofs no elimination can ever be stuck
//! on usefully: an equation, an inequality that reduces to `True`, a
//! negation. So a proof is kept only when its statement **carries data** —
//! when, under its parameters, it reduces to a former with a component a
//! client could compute with (a witness, a branch, a number, a function
//! returning one). The test is a function of the statement and the
//! definitions before it, so two theorems with one statement are treated
//! alike and the choice is part of what a statement already determines.
//!
//! Erring towards "carries data" only costs memory; erring the other way
//! leaves a theorem opaque, which is what every theorem was before.

use std::sync::Arc as Rc;

use heather_kernel::eval::whnf_value_ty;
use heather_kernel::reduce::Defs;
use heather_kernel::term::{GlobalCtx, LocalCtx, Term, Type};
use heather_kernel::value::{Head, VNeTy, VTy, Val, ValueArena};

use crate::oracle::SemanticOracle;

/// Reduction budget per former visited: generous for a `fn` into `Type`
/// that unfolds a few layers, small next to the declaration's own check.
/// Spent through the elaborator's own head probe ([`SemanticOracle`]), which
/// decides in the value domain and copies no definition bodies.
const FUEL: u64 = 4096;

/// How deep into a statement the test looks before answering "carries
/// data" — a Σ nest past this is assumed to carry some.
const DEPTH: u32 = 32;

/// Whether a theorem with statement `stmt` (closed, scoped over `psi`) keeps
/// its proof sealed.
pub(crate) fn carries_data(psi: &GlobalCtx, stmt: &Type) -> bool {
    data(psi, &SemanticOracle::in_world(psi.clone(), FUEL), &LocalCtx::nil(), stmt, DEPTH)
}

fn data(psi: &GlobalCtx, oracle: &SemanticOracle, gamma: &LocalCtx, ty: &Type, depth: u32) -> bool {
    let Some(depth) = depth.checked_sub(1) else { return true };
    if matches!(ty, Type::El { .. }) {
        if let Some(answer) = decoded(psi, gamma, ty) {
            return answer;
        }
    }
    let Ok(ty) = oracle.whnf_type(gamma, ty) else { return true };
    match &ty {
        // No component to compute with: a proof of one of these is all
        // there is to know about it.
        Type::Id { .. } | Type::SEq { .. } | Type::SEmpty { .. } | Type::Squash { .. } => false,
        Type::Unit { .. } | Type::Empty { .. } => false,
        // A function carries what its result carries: `∀ n. ∃ m. …` is the
        // shape of a modulus.
        Type::Pi { dom, dom_level, cod, .. } => data(psi, oracle, &gamma.extended(Rc::clone(dom), dom_level.clone()), cod, depth),
        Type::UPi { body, .. } | Type::CtxPi { body, .. } | Type::TyPi { body, .. } => {
            // Under a binder Γ does not describe; answer for the body
            // without reducing it further.
            shape(body)
        }
        Type::Sigma { fst, fst_level, snd, .. } => {
            data(psi, oracle, gamma, fst, depth) || data(psi, oracle, &gamma.extended(Rc::clone(fst), fst_level.clone()), snd, depth)
        }
        Type::Vec { elem, .. } => data(psi, oracle, gamma, elem, depth),
        // A stuck decoding: data only when what is stuck is a type
        // parameter, which an instantiation may make anything. A recursion
        // into `Type` stuck on an open argument (`n <= m` at a variable `n`)
        // is a family of propositions, and a proof of one is not opened.
        Type::El { tm, .. } => matches!(head(tm), Term::Var(_)),
        // A choice, a number, a code, an opaque type: all data.
        Type::Nat
        | Type::Ty(_)
        | Type::Sum { .. }
        | Type::W { .. }
        | Type::Wf { .. }
        | Type::Fin { .. }
        | Type::GlobalTy { .. }
        | Type::CodeTy { .. }
        | Type::CodeTm { .. } => true,
    }
}

/// [`data`] for a decoding, answered from its weak head value alone when the
/// former has no components to look into — which is almost every statement
/// spelled through a `fn … → Type` (`a <= b`, `x ≈ y` at a stuck argument).
/// Only a decoding to `Π`/`Σ`/`Vec` (`None`) is spelled and recursed into:
/// spelling is the reducer, which copies the definition bodies it unfolds.
fn decoded(psi: &GlobalCtx, gamma: &LocalCtx, ty: &Type) -> Option<bool> {
    let arena = ValueArena::new();
    let Ok(v) = whnf_value_ty(&arena, &Rc::new(ty.clone()), gamma, Defs::transparent(psi), FUEL) else {
        return Some(true);
    };
    Some(match &*v {
        VTy::Id { .. } | VTy::SEq { .. } | VTy::SEmpty { .. } | VTy::Squash { .. } => false,
        VTy::Unit { .. } | VTy::Empty { .. } => false,
        VTy::Pi { .. } | VTy::Sigma { .. } | VTy::Vec { .. } => return None,
        VTy::UPi { .. } | VTy::CtxPi { .. } | VTy::TyPi { .. } => return None,
        VTy::Neutral(VNeTy::Global { .. }) => true,
        // The value-domain reading of the syntax rule below: stuck on a
        // local applied to arguments, and on nothing else.
        VTy::Neutral(VNeTy::El { tm, .. }) => match &**tm {
            Val::Neutral(n) => {
                matches!(n.head, Head::Var(_) | Head::BaseVar(_)) && n.spine.iter_rev().all(|e| e.is_application())
            }
            _ => true,
        },
        VTy::Nat
        | VTy::Ty(_)
        | VTy::Sum { .. }
        | VTy::W { .. }
        | VTy::Wf { .. }
        | VTy::Fin { .. }
        | VTy::CodeTy { .. }
        | VTy::CodeTm { .. } => true,
    })
}

/// [`data`] without reduction, for a body under a binder the test does not
/// enter: only the formers that are certainly propositions say no.
fn shape(ty: &Type) -> bool {
    !matches!(
        ty,
        Type::Id { .. } | Type::SEq { .. } | Type::SEmpty { .. } | Type::Squash { .. } | Type::Unit { .. } | Type::Empty { .. }
    )
}

fn head(t: &Term) -> &Term {
    match t {
        Term::App { fun, .. } | Term::AppAt { fun, .. } | Term::UApp { fun, .. } => head(fun),
        _ => t,
    }
}
