//! Folds over runs, by the class of their step
//! (`issues/nat-run-algebra-primitives.md`).
//!
//! `elim_Nat(M; b; s; Succ^c(t))` with `s` classified (`probe.rs`):
//!
//! - **affine**, uniformly: `T^c[elim(t)]` — the tree iterated over the
//!   run's program (`value/algebra.rs`), instantiated at the fold at the
//!   tail. Peeled (`T` holds only at successor `k`): `T^{c-1}[s(t, elim(t))]`,
//!   the innermost step taken as written.
//! - **synchronous**: a [`Val::NatSync`], which cancels its run against the
//!   run it is applied to (`eval.rs`, the application case).
//! - **opaque**: `None` — the ordinary one-step path, after the
//!   bit-transducer class is asked; **direct** (`ih` does not occur in the
//!   step): `None` straight away, the one step being the whole fold.
//!
//! An affine result is a value shaped like the tree: successors on a
//! projection of the base, or pairs of those. Projections and pairs carry
//! the annotations the calculus gives them, read from the motive at the
//! tail and at the scrutinee respectively, so a value built here is one the
//! fold would have built; nothing from the probe survives into it.
//!
//! That each value built here is convertible with the unary fold is proved
//! against the reference model, with increments as counts and iteration one
//! composition per step: `lib/kernel_model/kernel_runs.hthr`
//! (`Tm::fold_affine`, `Tm::fold_affine_peeled`, `Tm::fold_sync`;
//! `docs/kernel/kernel-model-design.md` §7). Programs and binary powering against
//! that iteration rest on `value/algebra.rs`'s reference test.

use crate::rc::Rc;

use crate::value::algebra::{AffineTree, FoldClass, Increment, Proj};
use crate::value::program::ContextProgram;
use crate::value::{Elim, SigAnn, TmClo, VTy, Val};

use super::{Eval, Frame, Res, Work};

impl<'a, 'v> Eval<'a, 'v> {
    /// The fold of `e` (a `Nat` eliminator) over `head = Succ^program(tail)`
    /// by its step's class, or the ordinary step when the class has no
    /// shortcut.
    #[inline(never)]
    pub(super) fn fold_run(
        &mut self,
        head: &'v Val<'v>,
        program: &Rc<ContextProgram<()>>,
        tail: &'v TmClo<'v>,
        e: &Elim<'v>,
    ) -> Res<Work<'v>> {
        let Elim::ElimNat { step, .. } = e else {
            unreachable!("fold_run is given a Nat eliminator")
        };
        let class = self.classify_step(step)?;
        self.fold_by_class(head, program, tail, e, &class)
    }

    /// [`Eval::fold_run`] once the step is classified: kept apart so the
    /// classification, which re-enters the machine, stands on a small frame
    /// (docs/kernel/native-depth-budget-design.md §8).
    #[inline(never)]
    fn fold_by_class(
        &mut self,
        head: &'v Val<'v>,
        program: &Rc<ContextProgram<()>>,
        tail: &'v TmClo<'v>,
        e: &Elim<'v>,
        class: &FoldClass,
    ) -> Res<Work<'v>> {
        let Elim::ElimNat { step, .. } = e else {
            unreachable!("fold_by_class is given a Nat eliminator")
        };
        let work = match class {
            // Not a `Nat` algebra — which is what every fold over a *width*
            // is, its step returning a function. The bit-transducer class
            // (`eval/transduce.rs`) is asked next, and `None` from it is the
            // ordinary one-step path as before.
            FoldClass::Opaque => self.fold_transduce(program, tail, e),
            FoldClass::Direct => Ok(None),
            FoldClass::Sync { .. } => Ok(Some(Work::Val(self.arena.val(Val::NatSync {
                program: Rc::clone(program),
                tail,
                elim: self.arena.elim_cell(e.clone()),
            })))),
            FoldClass::Affine { tree, uniform } => {
                self.fold_affine(head, program, tail, e, tree, *uniform)
            }
        }?;
        Ok(match work {
            Some(work) => work,
            None => self.nat_run_step(program, tail, step, e),
        })
    }

    #[inline(never)]
    fn fold_affine(
        &mut self,
        head: &'v Val<'v>,
        program: &Rc<ContextProgram<()>>,
        tail: &'v TmClo<'v>,
        e: &Elim<'v>,
        tree: &AffineTree,
        uniform: bool,
    ) -> Res<Option<Work<'v>>> {
        let Elim::ElimNat { step, motive, .. } = e else { unreachable!() };
        let fold_at_tail = self.arena.tm(TmClo::elim(tail, self.arena.elim_cell(e.clone())));
        // What the iterate is applied to, its type's index, and how many
        // times the tree is applied.
        let (base, base_at, count) = if uniform {
            (fold_at_tail, tail, Some(Rc::clone(program)))
        } else {
            let (_, rest) = ContextProgram::uncons(program);
            let inner = self.drive(Work::Apply(*step, vec![tail, fold_at_tail]))?;
            (self.vclo(inner), self.vclo(self.arena.val(Val::Succ(tail))), rest)
        };
        let Some(count) = count else {
            // One successor, peeled: the innermost step is the whole fold.
            return Ok(Some(Work::Force(base)));
        };
        let Some(iterated) = tree.iterate(&count) else { return Ok(None) };

        if let AffineTree::Leaf { inc, path } = &iterated {
            if path.is_empty() {
                // The successor algebra: the fold at the tail is forced
                // through the merging frame, so a run it produces joins this
                // one and a glued tail is unfolded rather than left pending.
                if let Some(inc) = inc {
                    self.frames.push(Frame::NatRunTail { program: Rc::clone(inc), glued: None });
                }
                return Ok(Some(Work::Force(base)));
            }
        }
        if let AffineTree::Lit { inc } = &iterated {
            return Ok(Some(Work::Force(self.literal(inc))));
        }

        // A tuple, or a projection: annotate from the motive.
        let base_ty = self.apply_ty(motive, &[base_at])?;
        let base_ty = self.delta_whnf_ty(base_ty)?;
        let scrut = self.vclo(head);
        let out_ty = self.apply_ty(motive, &[scrut])?;
        let out_ty = self.delta_whnf_ty(out_ty)?;
        Ok(self.build(&iterated, base, &base_ty, out_ty)?.map(Work::Force))
    }

    /// `Succ^{inc}(Zero)`.
    pub(super) fn literal(&self, inc: &Increment) -> &'v TmClo<'v> {
        let zero = self.vclo(self.arena.val(Val::Zero));
        match inc {
            None => zero,
            Some(program) => {
                self.vclo(self.arena.val(Val::NatRun { program: Rc::clone(program), tail: zero }))
            }
        }
    }

    /// `tree[ih := base]` as a closure, `None` if a type expected to be a
    /// pair is not one (ill-typed input; declined, not guessed).
    fn build(
        &mut self,
        tree: &AffineTree,
        base: &'v TmClo<'v>,
        base_ty: &'v VTy<'v>,
        out_ty: &'v VTy<'v>,
    ) -> Res<Option<&'v TmClo<'v>>> {
        Ok(Some(match tree {
            AffineTree::Lit { inc } => self.literal(inc),
            AffineTree::Leaf { inc, path } => {
                let Some(component) = self.project(base, base_ty, path)? else {
                    return Ok(None);
                };
                match inc {
                    None => component,
                    Some(program) => self.vclo(self.arena.val(Val::NatRun {
                        program: Rc::clone(program),
                        tail: component,
                    })),
                }
            }
            AffineTree::Pair(fst, snd) => {
                let VTy::Sigma { fst_level, snd_level, fst: fst_ty, snd: snd_ty } = &*out_ty
                else {
                    return Ok(None);
                };
                let (fst_level, snd_level, fst_ty, snd_ty) =
                    (fst_level.clone(), snd_level.clone(), *fst_ty, *snd_ty);
                let fst_out = self.force_ty(fst_ty)?;
                let fst_out = self.delta_whnf_ty(fst_out)?;
                let Some(fst_v) = self.build(fst, base, base_ty, fst_out)? else {
                    return Ok(None);
                };
                let snd_out = self.apply_ty(snd_ty, &[fst_v])?;
                let snd_out = self.delta_whnf_ty(snd_out)?;
                let Some(snd_v) = self.build(snd, base, base_ty, snd_out)? else {
                    return Ok(None);
                };
                self.vclo(self.arena.val(Val::Pair {
                    ann: Some(SigAnn { fst_level, snd_level, fst_ty, snd_ty }),
                    fst: fst_v,
                    snd: snd_v,
                }))
            }
        }))
    }

    /// `base.path` as a chain of projection closures, each annotated from
    /// the pair type it projects out of. A pair-valued base reduces them
    /// when forced; a neutral one keeps them as its spine.
    fn project(
        &mut self,
        base: &'v TmClo<'v>,
        base_ty: &'v VTy<'v>,
        path: &[Proj],
    ) -> Res<Option<&'v TmClo<'v>>> {
        let mut cur = base;
        let mut ty = base_ty;
        for step in path {
            let VTy::Sigma { fst_level, snd_level, fst, snd } = &*ty else { return Ok(None) };
            let (fst_level, snd_level, fst_ty, snd_ty) =
                (fst_level.clone(), snd_level.clone(), *fst, *snd);
            let fst_elim = Elim::Fst {
                ann: Some(SigAnn {
                    fst_level: fst_level.clone(),
                    snd_level: snd_level.clone(),
                    fst_ty,
                    snd_ty,
                }),
            };
            let next_ty = match step {
                Proj::Fst => self.force_ty(fst_ty)?,
                Proj::Snd => {
                    let fst_thunk = self.arena.tm(TmClo::elim(cur, self.arena.elim_cell(fst_elim.clone())));
                    self.apply_ty(snd_ty, &[fst_thunk])?
                }
            };
            let elim = match step {
                Proj::Fst => fst_elim,
                Proj::Snd => Elim::Snd {
                    ann: Some(SigAnn { fst_level, snd_level, fst_ty, snd_ty }),
                },
            };
            cur = self.arena.tm(TmClo::elim(cur, self.arena.elim_cell(elim)));
            ty = self.delta_whnf_ty(next_ty)?;
        }
        Ok(Some(cur))
    }
}
