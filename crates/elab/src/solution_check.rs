//! The unifier's one check on a write (docs/elaborator-principles-survey.md
//! P1, issues/unifier-checked-assignment.md): a solution must inhabit its
//! slot's declared type.
//!
//! The congruence aligns a flexible spine against any rigid one of its
//! length, so `?≈(l, r)` against `Rat::Same(x, y)` offers `?≈ := Rat::Same`
//! where `?≈ : Int → Int → Type` is already fixed. The unifier's first write
//! wins, so a solution of the wrong type is never replaced by a later right
//! one: the call fails at the kernel, or the instance search is handed a goal
//! no instance can be (issues/index-inference-through-unfolding.md). Held at
//! the write, the slot stays open and a later read can still fill it.
//!
//! What is judged, and what is not:
//!
//! - A slot past the end of `doms` is not judged: a caller with no
//!   declared types for its slots (the tactic host's holes) converts its
//!   whole pattern afterwards.
//! - A sort-typed slot (`Ty`) is not judged: its solutions are codes the
//!   `El` rule read off a type, and a code's universe is the kernel's
//!   question.
//! - A slot whose type still mentions an open slot is judged when the read
//!   ends ([`SolutionCheck::settle`]), once that slot is known, and undone
//!   then if it does not fit. Nothing else learned from it: the congruence
//!   records, it does not propagate.
//! - A solution the kernel cannot type, and a conversion out of fuel, keep
//!   the write. Still learn-only, and the kernel still judges the call.

use std::cell::{Cell, OnceCell, RefCell};

use heather_kernel::conv::ConvError;
use heather_kernel::layer::Layer;
use heather_kernel::term::{GlobalCtx, Term, Type};
use heather_kernel::typing;

use crate::oracle::SemanticOracle;
use crate::unification::{Sol, zonked};
use crate::{Cx, Elaborator, stats};
use crate::app_unify::AppUnify;

/// One unifier root's check: the slots' declared types in the call's
/// scratch world (`n` metas), the world the solutions are typed in (read
/// once, on the first judged write), the slots left for the end, and
/// whether anything was refused.
pub(crate) struct SolutionCheck<'e> {
    elab: &'e Elaborator,
    cx: &'e Cx,
    doms: &'e [Type],
    n: u32,
    world: OnceCell<(GlobalCtx, SemanticOracle)>,
    deferred: RefCell<Vec<usize>>,
    refused: Cell<bool>,
}

impl<'e> SolutionCheck<'e> {
    pub(crate) fn new(elab: &'e Elaborator, cx: &'e Cx, doms: &'e [Type], n: u32) -> Self {
        SolutionCheck {
            elab,
            cx,
            doms,
            n,
            world: OnceCell::new(),
            deferred: RefCell::new(Vec::new()),
            refused: Cell::new(false),
        }
    }

    /// May `slot` take `s` now? `sols` is the world as the read has it, so a
    /// type that mentions an earlier solution is judged at it.
    pub(crate) fn admit(&self, slot: usize, s: &Term, sols: &[Sol]) -> bool {
        let Some(dom) = self.doms.get(slot) else { return true };
        if matches!(dom, Type::Ty(_)) {
            return true;
        }
        let Some(dom) = zonked(dom, self.n, sols) else {
            self.deferred.borrow_mut().push(slot);
            return true;
        };
        let fits = self.fits(s, &dom);
        if !fits {
            self.refused.set(true);
        }
        fits
    }

    /// Judge the writes whose slot type was still open when they happened,
    /// and undo those that do not fit. `true` when any write of this read
    /// was refused or undone.
    pub(crate) fn settle(&self, sols: &mut [Sol]) -> bool {
        let deferred = std::mem::take(&mut *self.deferred.borrow_mut());
        for slot in deferred {
            let Some(s) = sols[slot].solved().cloned() else { continue };
            let Some(dom) = zonked(&self.doms[slot], self.n, sols) else { continue };
            if !self.fits(&s, &dom) {
                sols[slot] = Sol::Unsolved;
                self.refused.set(true);
            }
        }
        self.refused.get()
    }

    /// Does `s` inhabit `dom`? Only a clean "not convertible" says no.
    fn fits(&self, s: &Term, dom: &Type) -> bool {
        stats::count(stats::Counter::SolutionChecks);
        let fuel = self.elab.policy.fuel;
        let (psi, oracle) = self.world.get_or_init(|| {
            let psi = self.elab.goal_psi();
            let oracle = SemanticOracle::in_world(psi.clone(), fuel);
            (psi, oracle)
        });
        let gamma = &self.cx.gamma;
        let Ok((ty, level)) = stats::time_kernel(|| typing::infer_term(psi, 0, Layer::Prog, gamma, s, fuel)) else {
            return true;
        };
        !matches!(
            stats::time_kernel(|| oracle.convert_type(gamma, Layer::Prog, &ty, dom, &level)),
            Err(ConvError::NotConvertible)
        )
    }
}

impl Elaborator {
    /// A solved slot's **own type** teaches the slots its declared type
    /// still waits on (issues/generic-theorem-implicit-points.md). A class
    /// theorem's points are typed at its carrier, `{x, y: K}`, and a
    /// hypothesis `h: a < b` solves `?x := a` and `?< := <` while `?K`, which
    /// only those slots' types mention, stays open, so the class goal never
    /// becomes meta-free and instance search never runs. Reading `a : K`
    /// against `?x : El ?K` is what pins it.
    ///
    /// Learn-only, as every read: a solution the kernel cannot type teaches
    /// nothing, and the kernel still judges the call. Run only while a slot
    /// is open, over the solved slots whose declared type is still open, so
    /// a call every argument already pinned pays nothing. `true` when it
    /// solved at least one slot.
    ///
    /// A slot written while its type was open is judged once that type
    /// closes, as [`SolutionCheck::settle`] does at the end of a read, and
    /// undone if it does not fit: `?z := d` read off `h2: c < d` at `CReal`,
    /// once `?K` is `Rat`, is the call naming `z` as not inferred, not the
    /// kernel refusing a term with no spelling.
    pub(crate) fn learn_from_solution_types(
        &self,
        cx: &Cx,
        meta_doms: &[Type],
        n: u32,
        sols: &mut [Sol],
        span: heather_syntax::Span,
    ) -> bool {
        let open = |sols: &[Sol]| sols.iter().filter(|s| matches!(s, Sol::Unsolved)).count();
        let mut learned = false;
        let mut world: Option<GlobalCtx> = None;
        // Each round solves a slot, and an undone slot is not taken again
        // (its type is closed, so the read's own check refuses it), so the
        // slot count bounds the rounds; the bound is only a backstop.
        for _ in 0..=sols.len() {
            let before = open(sols);
            if before == 0 {
                return learned;
            }
            // The solved slots whose type is open now: judged below once it
            // closes.
            let opened: Vec<usize> = (0..sols.len().min(meta_doms.len()))
                .filter(|&slot| {
                    sols[slot].solved().is_some()
                        && !matches!(meta_doms[slot], Type::Ty(_))
                        && zonked(&meta_doms[slot], n, sols).is_none()
                })
                .collect();
            for slot in 0..sols.len().min(meta_doms.len()) {
                let Some(s) = sols[slot].solved().cloned() else { continue };
                let dom = &meta_doms[slot];
                if matches!(dom, Type::Ty(_)) || zonked(dom, n, sols).is_some() {
                    continue;
                }
                let psi = world.get_or_insert_with(|| self.goal_psi());
                let fuel = self.policy.fuel;
                let Ok((ty, _)) = stats::time_kernel(|| typing::infer_term(psi, 0, Layer::Prog, &cx.gamma, &s, fuel)) else {
                    continue;
                };
                AppUnify(self).unify_arg_ty(cx, dom, &ty, n, sols, meta_doms, crate::unification::Guesses::Take, span);
            }
            if open(sols) == before {
                return learned;
            }
            learned = true;
            let check = SolutionCheck::new(self, cx, meta_doms, n);
            for slot in 0..sols.len().min(meta_doms.len()) {
                if !opened.contains(&slot) || zonked(&meta_doms[slot], n, sols).is_none() {
                    continue;
                }
                let Some(s) = sols[slot].solved().cloned() else { continue };
                if !check.admit(slot, &s, sols) {
                    sols[slot] = Sol::Unsolved;
                }
            }
        }
        learned
    }
}
