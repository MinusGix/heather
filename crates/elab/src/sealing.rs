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


use heather_kernel::eval::Eval;
use heather_kernel::reduce::Defs;
use heather_kernel::term::{CtxBase, GlobalCtx, Type};
use heather_kernel::value::{Elim, Env, Head, TmClo, TyClo, VNeTy, VTy, Val, ValueArena};

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
    let mut walk = Walk { ev: &mut ev, psi, arena: &arena, nodes: NODES };
    let Ok(v) = walk.ev.eval_ty(stmt, &Env::identity(&arena, 0)) else { return false };
    walk.data(v, 0, true).unwrap_or(false)
}

/// Fuel for [`Walk::never_data`]'s look at a family alone: it unfolds one
/// definition at variables, so it never runs anything the statement computes.
const FAMILY_FUEL: u64 = 1 << 10;

/// Formers [`Walk::never_data`] visits.
const FAMILY_NODES: u32 = 16;

struct Walk<'e, 'a, 'v> {
    ev: &'e mut Eval<'a, 'v>,
    psi: &'a GlobalCtx,
    arena: &'v ValueArena<'v>,
    nodes: u32,
}

impl<'v> Walk<'_, '_, 'v> {
    /// `None`: out of fuel or of nodes — unknown, so opaque.
    ///
    /// `last` says nothing is asked after this answer: the walk's verdict is
    /// this one, and an unknown here is the same opaque `false` as a no. There,
    /// and only there, a statement that is a family no instance of which can
    /// carry data ([`Self::never_data`]) answers `false` without being run: the
    /// one answer the full test could give. `x.IsTrue()` of a `Bool` program is
    /// the case that decided it: the test otherwise runs the program, to its
    /// fuel when it is large (a generated certificate's `checked` pass), only to
    /// learn that `True` and `False` carry nothing. Not under a `Σ`'s first
    /// component, where an unknown makes the whole statement unknown but a no
    /// goes on to the second.
    fn data(&mut self, ty: &'v VTy<'v>, depth: u32, last: bool) -> Option<bool> {
        self.nodes = self.nodes.checked_sub(1)?;
        if last && self.never_data(&ty, depth) {
            return Some(false);
        }
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
                self.data(cod, depth + 1, last)?
            }
            VTy::Sigma { fst, snd, .. } => {
                let fst = self.ev.force_ty(fst).ok()?;
                self.data(fst, depth, false)? || {
                    let snd = self.under(snd, depth)?;
                    self.data(snd, depth + 1, last)?
                }
            }
            VTy::Vec { elem, .. } => {
                let elem = self.ev.force_ty(elem).ok()?;
                self.data(elem, depth, last)?
            }
            // A tuple carries what its family carries at a fresh position.
            VTy::DVec { fam, .. } => {
                let fam = self.under(fam, depth)?;
                self.data(fam, depth + 1, last)?
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
            | VTy::IWf { .. }
            | VTy::M { .. }
            | VTy::Fin { .. }
            | VTy::CodeTy { .. }
            | VTy::CodeTm { .. } => true,
        })
    }

    /// Whether `ty` is `El` of a global type family `F(a⃗)` such that *no*
    /// `F(b⃗)` carries data: `F` at fresh variables, decided in a walk of its
    /// own ([`Family::never`]) with its own fuel, so the arguments — however
    /// much they would compute — are never forced, and the main walk's fuel
    /// and nodes are untouched. A `false` here only means "not shown".
    fn never_data(&mut self, ty: &'v VTy<'v>, depth: u32) -> bool {
        let VTy::Neutral(VNeTy::El { level, tm }) = &*ty else { return false };
        let Val::Neutral(n) = &*tm else { return false };
        let Head::Global { var, subst } = &n.head else { return false };
        if n.unfold.is_none() || n.spine.is_empty() || !n.spine.iter_rev().all(|e| e.is_application()) {
            return false;
        }
        let mut args: Vec<&'v Elim<'v>> = n.spine.iter_rev().collect();
        args.reverse();
        let mut ev = Eval::new(FAMILY_FUEL, Defs::transparent(self.psi), CtxBase::Nil, self.arena);
        let mut family = Family { ev: &mut ev, arena: self.arena, nodes: FAMILY_NODES };
        let mut head = family.ev.global(*var, subst.clone());
        let mut fresh = depth;
        for e in args {
            let Elim::App { ann, .. } = e else { return false };
            let x = self.arena.tm(TmClo::val(self.arena.val(Val::var(fresh))));
            fresh += 1;
            let Ok(next) = family.ev.elim(head, Elim::App { ann: ann.clone(), arg: x }) else { return false };
            head = next;
        }
        let at = self.arena.ty_el(level.clone(), self.arena.tm(TmClo::val(head)));
        let Ok(ty) = family.ev.force_ty(at) else { return false };
        family.never(ty, fresh)
    }

    /// A one-binder type closure under a fresh variable at level `depth`.
    fn under(&mut self, clo: &'v TyClo<'v>, depth: u32) -> Option<&'v VTy<'v>> {
        let x = self.arena.tm(TmClo::val(self.arena.val(Val::var(depth))));
        self.ev.apply_ty(clo, &[x]).ok()
    }
}

/// [`Walk::never_data`]'s walk: whether a type at variables is one no
/// instance of which carries data. Only formers that carry nothing at any
/// instance answer yes, and a `match` stuck on a variable answers yes when
/// every arm does — the arms are all the instance can become. Anything else,
/// fuel and nodes included, is a no.
struct Family<'e, 'a, 'v> {
    ev: &'e mut Eval<'a, 'v>,
    arena: &'v ValueArena<'v>,
    nodes: u32,
}

impl<'v> Family<'_, '_, 'v> {
    fn never(&mut self, ty: &'v VTy<'v>, depth: u32) -> bool {
        let Some(nodes) = self.nodes.checked_sub(1) else { return false };
        self.nodes = nodes;
        let Ok(ty) = self.ev.delta_whnf_ty(ty) else { return false };
        match &*ty {
            VTy::Id { .. } | VTy::SEq { .. } | VTy::SEmpty { .. } | VTy::Squash { .. } => true,
            VTy::Unit { .. } | VTy::Empty { .. } => true,
            VTy::Neutral(VNeTy::El { level, tm }) => {
                let Val::Neutral(n) = &**tm else { return false };
                let Some(Elim::Case { case_l, case_r, .. }) = n.spine.last() else { return false };
                [*case_l, *case_r].into_iter().all(|arm| {
                    let x = self.arena.tm(TmClo::val(self.arena.val(Val::var(depth))));
                    let Ok(code) = self.ev.apply(arm, &[x]) else { return false };
                    let at = self.arena.ty_el(level.clone(), self.arena.tm(TmClo::val(code)));
                    match self.ev.force_ty(at) {
                        Ok(arm) => self.never(arm, depth + 1),
                        Err(_) => false,
                    }
                })
            }
            _ => false,
        }
    }
}
