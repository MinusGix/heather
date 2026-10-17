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
//! **Unknown means opaque.** A statement the test cannot settle within its
//! budget keeps its proof out, which is what every theorem was before. The
//! other default is not just a memory cost: a kept proof is *run* wherever an
//! elimination is stuck on it, and the statements too big to classify cheaply
//! are the ones whose proofs are expensive to run — residency of a generated
//! program's code (`CodeResident`, a conjunction per byte) is the case that
//! decided it.

use std::sync::Arc as Rc;

use heather_kernel::eval::Eval;
use heather_kernel::reduce::Defs;
use heather_kernel::term::{CtxBase, GlobalCtx, Type};
use heather_kernel::value::{Env, Head, TmClo, TyClo, VNeTy, VTy, Val, ValueArena};

/// Reduction budget for the whole test: generous for a `fn` into `Type`
/// that unfolds a few layers (`x < y` on the reals is three), small next to
/// the declaration's own check.
const FUEL: u64 = 1 << 16;

/// Formers the test visits before giving up. A `Σ` nest longer than this
/// is a conjunction over something computed, not a statement anyone reads a
/// witness out of.
const NODES: u32 = 64;

/// Whether a theorem with statement `stmt` (closed, scoped over `psi`) keeps
/// its proof sealed. Decided in the value domain, under fresh variables for
/// the binders it enters, so nothing is spelled and no body is copied.
pub(crate) fn carries_data(psi: &GlobalCtx, stmt: &Type) -> bool {
    let arena = ValueArena::new();
    let mut ev = Eval::new(FUEL, Defs::transparent(psi), CtxBase::Nil, &arena);
    let mut walk = Walk { ev: &mut ev, arena: &arena, nodes: NODES };
    let Ok(v) = walk.ev.eval_ty(stmt, &Env::identity(&arena, 0)) else { return false };
    walk.data(v, 0).unwrap_or(false)
}

struct Walk<'e, 'a, 'v> {
    ev: &'e mut Eval<'a, 'v>,
    arena: &'v ValueArena<'v>,
    nodes: u32,
}

impl<'v> Walk<'_, '_, 'v> {
    /// `None`: out of fuel or of nodes — unknown, so opaque.
    fn data(&mut self, ty: Rc<VTy<'v>>, depth: u32) -> Option<bool> {
        self.nodes = self.nodes.checked_sub(1)?;
        let ty = self.ev.delta_whnf_ty(ty).ok()?;
        Some(match &*ty {
            // No component to compute with: a proof of one of these is all
            // there is to know about it.
            VTy::Id { .. } | VTy::SEq { .. } | VTy::SEmpty { .. } | VTy::Squash { .. } => false,
            VTy::Unit { .. } | VTy::Empty { .. } => false,
            // A function carries what its result carries: `∀ n. ∃ m. …` is
            // the shape of a modulus.
            VTy::Pi { cod, .. } => {
                let cod = self.under(cod, depth)?;
                self.data(cod, depth + 1)?
            }
            VTy::Sigma { fst, snd, .. } => {
                let fst = self.ev.force_ty(fst).ok()?;
                self.data(fst, depth)? || {
                    let snd = self.under(snd, depth)?;
                    self.data(snd, depth + 1)?
                }
            }
            VTy::Vec { elem, .. } => {
                let elem = self.ev.force_ty(elem).ok()?;
                self.data(elem, depth)?
            }
            // Under a universe, context or type binder: rare in a theorem's
            // statement, and not entered.
            VTy::UPi { .. } | VTy::CtxPi { .. } | VTy::TyPi { .. } => return None,
            VTy::Neutral(VNeTy::Global { .. }) => true,
            // A stuck decoding: data only when it is stuck on a local applied
            // to arguments — a type parameter, which an instantiation may make
            // anything. A recursion into `Type` stuck on an open argument
            // (`n <= m` at a variable `n`) is a family of propositions, and a
            // proof of one is not opened.
            VTy::Neutral(VNeTy::El { tm, .. }) => match &**tm {
                Val::Neutral(n) => {
                    matches!(n.head, Head::Var(_) | Head::BaseVar(_))
                        && n.spine.iter_rev().all(|e| e.is_application())
                }
                _ => return None,
            },
            // A choice, a number, a code, an opaque type: all data.
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

    /// A one-binder type closure under a fresh variable at level `depth`.
    fn under(&mut self, clo: &'v TyClo<'v>, depth: u32) -> Option<Rc<VTy<'v>>> {
        let x = self.arena.tm(TmClo::val(Rc::new(Val::var(depth))));
        self.ev.apply_ty(clo, &[x]).ok()
    }
}
