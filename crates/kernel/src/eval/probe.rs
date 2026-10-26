//! Semantic classification of a `Nat` fold's step
//! (`issues/nat-run-algebra-primitives.md`).
//!
//! A run (`Val::NatRun`) is `Succ^c(tail)` without `c` nodes, and a fold over
//! it can be done without `c` steps exactly when its step is an algebra the
//! run arithmetic (`value/algebra.rs`) can iterate. Which steps those are is
//! decided here **by evaluating the step**, not by reading its spelling: the
//! step closure is applied to fresh neutral variables `k` and `ih`, and the
//! value that comes back is read as one of
//!
//! - an [`AffineTree`]: pairs of `Succ^q(ih.π)` and closed literals, the only
//!   neutral in sight being `ih` itself under projections;
//! - a function that, applied to `Succ x`, is `Succ^q(ih x)` — the
//!   synchronous two-counter algebra of `Le`, `leb`, `sub`, `min`, `max`;
//! - anything else, which is opaque and folds one step at a time.
//!
//! Soundness is the substitution property of reduction: a value with no
//! stuck case split on `k`, `ih`, or `x` was reached by a reduction that
//! holds for every instantiation of them. So the class is a fact about the
//! algebra as a function on runs, generic over how the definition was
//! written — `nat::Nat::sub`'s spelling never matched the old syntactic pattern
//! and classifies here by what it does.
//!
//! That property, and the fuel claim below, are proved for ch. 06's
//! weak-head reduction on a λ + `Nat` fragment in
//! `lib/kernel_model/kernel_reduction.hthr` (`Tm::whnf_inst_settled`:
//! an unblocked run is, at the same fuel, the run of every instance;
//! `docs/kernel-model-design.md`). What is not proved is that this evaluator
//! implements that reduction.
//!
//! Each reading is tried **uniformly** (`k` neutral: the class holds at every
//! step) and, if that is stuck on `k`, **peeled** (`k := Succ x`: the class
//! holds at every step but the innermost, which the fold takes ordinarily —
//! `half`'s window matches on `k`).
//!
//! The probe's variables are `Head::Var` at reserved top levels. No real
//! context reaches them, and a probe value is read and dropped: the only
//! thunks it can memoize are ones it created (unreachable afterwards) and
//! environment thunks that predate it (closed with respect to it). Its
//! reductions charge the ordinary fuel — they are the ones the fold's own
//! first step would perform — so a probe never manufactures a verdict fuel
//! would have refused.
//!
//! ## Steps that never read `ih`
//!
//! A step in which `ih` does not occur is not probed
//! (`issues/kernel-fold-probe-evaluates-recursive-arms.md`): the fold's one
//! ordinary step is then the whole fold at any run, so no class could do
//! better, and the probes would only evaluate the step again. That is the
//! shape of a `match` on a literal inside an enclosing recursion,
//! `At(before, name) => match name { Zero => walk(before), Succ(_) => … }`,
//! whose arms are the enclosing recursion's calls: probing it evaluated each
//! level's call once per probe as well as once for the fold, exponentially
//! in the walk's depth. The test is on syntax (`bounds::ignores_innermost`),
//! but it decides only whether to probe, never a class's verdict: the
//! ordinary step is the fold's definition.

use std::sync::Arc as Rc;

use crate::level::Level;
use crate::term::Type;
use crate::value::algebra::{add_increments, AffineTree, FoldClass, Increment, Path, Proj};
use crate::value::program::ContextProgram;
use crate::value::{Elim, Env, Head, PiAnn, TmClo, TyClo, Val};

use super::{Eval, Res, Work};

/// The reserved levels. Γ is never this deep; the gap between them keeps a
/// misread impossible even if it were off by one.
const PROBE_IH: u32 = u32::MAX - 8;
const PROBE_K: u32 = u32::MAX - 16;
const PROBE_X: u32 = u32::MAX - 24;

impl<'a, 'v> Eval<'a, 'v> {
    /// The class of `step`, probed once per closure and memoized in the
    /// arena.
    pub(super) fn classify_step(&mut self, step: &'v TmClo<'v>) -> Res<Rc<FoldClass>> {
        if let Some(class) = self.arena.fold_class(step) {
            return Ok(class);
        }
        // `ih` is the step's innermost binder (the module doc's last
        // section).
        if let Some((_, body)) = step.as_syn() {
            if crate::bounds::ignores_innermost(body, 1) {
                let class = Rc::new(FoldClass::Direct);
                self.arena.cache_fold_class(step, Rc::clone(&class));
                return Ok(class);
            }
        }
        let class = Rc::new(self.probe_step(step)?);
        self.arena.cache_fold_class(step, Rc::clone(&class));
        Ok(class)
    }

    fn probe_var(&self, level: u32) -> &'v TmClo<'v> {
        self.vclo(Rc::new(Val::var(level)))
    }

    /// `step k ih`, driven to its δ-transparent weak head value.
    #[inline(never)]
    fn probe_apply(&mut self, step: &'v TmClo<'v>, k: &'v TmClo<'v>) -> Res<Rc<Val<'v>>> {
        let ih = self.probe_var(PROBE_IH);
        let v = self.drive(Work::Apply(step, vec![k, ih]))?;
        self.delta_whnf(v)
    }

    #[inline(never)]
    fn probe_step(&mut self, step: &'v TmClo<'v>) -> Res<FoldClass> {
        let value = self.probe_apply(step, self.probe_var(PROBE_K))?;
        if let Val::Lam { .. } | Val::WfIh { .. } | Val::WIh { .. } | Val::IWfIh { .. } = &*value {
            return self.probe_sync(value);
        }
        if let Some(tree) = self.read_affine(&value)? {
            return Ok(FoldClass::Affine { tree, uniform: true });
        }
        let peeled = self.vclo(Rc::new(Val::Succ(self.probe_var(PROBE_X))));
        let value = self.probe_apply(step, peeled)?;
        Ok(match self.read_affine(&value)? {
            Some(tree) => FoldClass::Affine { tree, uniform: false },
            None => FoldClass::Opaque,
        })
    }

    /// The function-valued algebra applied to `Succ x`: synchronous when
    /// that is `Succ^q(ih x)`. The application's annotations are dummies —
    /// the result is read for its head and spine and never kept.
    #[inline(never)]
    fn probe_sync(&mut self, fun: Rc<Val<'v>>) -> Res<FoldClass> {
        let nat = self.arena.ty(TyClo::new(Env::empty(), Rc::new(Type::Nat)));
        let arg = self.vclo(Rc::new(Val::Succ(self.probe_var(PROBE_X))));
        let app = Elim::App {
            ann: Some(PiAnn {
                dom_level: Level::Zero,
                cod_level: Level::Zero,
                dom: nat,
                cod: nat,
            }),
            arg,
        };
        let value = self.drive(Work::Elim(fun, app))?;
        let value = self.delta_whnf(value)?;
        let (inc, tail) = self.strip_successors(value)?;
        let Val::Neutral(n) = &*tail else { return Ok(FoldClass::Opaque) };
        if !matches!(n.head, Head::Var(PROBE_IH)) {
            return Ok(FoldClass::Opaque);
        }
        let mut spine = n.spine.iter_rev();
        let (Some(Elim::App { arg, .. }), None) = (spine.next(), spine.next()) else {
            return Ok(FoldClass::Opaque);
        };
        let arg = self.force(arg)?;
        let arg = self.delta_whnf(arg)?;
        let is_x = matches!(&*arg,
            Val::Neutral(x) if matches!(x.head, Head::Var(PROBE_X)) && x.spine.is_empty());
        Ok(if is_x { FoldClass::Sync { inc } } else { FoldClass::Opaque })
    }

    /// Read a probe value as an affine tree; `None` is "not one".
    #[inline(never)]
    fn read_affine(&mut self, value: &Rc<Val<'v>>) -> Res<Option<AffineTree>> {
        if let Val::Pair { fst, snd, .. } = &**value {
            let fst = self.force(fst)?;
            let fst = self.delta_whnf(fst)?;
            let Some(fst) = self.read_affine(&fst)? else { return Ok(None) };
            let snd = self.force(snd)?;
            let snd = self.delta_whnf(snd)?;
            let Some(snd) = self.read_affine(&snd)? else { return Ok(None) };
            return Ok(Some(AffineTree::Pair(Box::new(fst), Box::new(snd))));
        }
        let (inc, tail) = self.strip_successors(Rc::clone(value))?;
        Ok(match &*tail {
            Val::Zero => Some(AffineTree::Lit { inc }),
            Val::Neutral(n) if matches!(n.head, Head::Var(PROBE_IH)) => {
                projection_path(n.spine.iter_rev()).map(|path| AffineTree::Leaf { inc, path })
            }
            _ => None,
        })
    }

    /// `Succ^q(t)` as `(q, t)`, with `t` forced past every successor and
    /// glued definition; `t` is whatever the successors sit on.
    fn strip_successors(&mut self, value: Rc<Val<'v>>) -> Res<(Increment, Rc<Val<'v>>)> {
        let mut inc: Increment = None;
        let mut cur = value;
        loop {
            let next = match &*cur {
                Val::Succ(pred) => {
                    inc = add_increments(&inc, &Some(ContextProgram::run((), ONE)));
                    *pred
                }
                Val::NatRun { program, tail } => {
                    inc = add_increments(&inc, &Some(Rc::clone(program)));
                    *tail
                }
                _ => return Ok((inc, cur)),
            };
            let forced = self.force(next)?;
            cur = self.delta_whnf(forced)?;
        }
    }
}

const ONE: std::num::NonZeroU64 = match std::num::NonZeroU64::new(1) {
    Some(one) => one,
    None => unreachable!(),
};

/// The projection path a spine of `fst`/`snd` eliminations denotes,
/// innermost first; `None` if anything else was applied.
fn projection_path<'v>(spine: impl Iterator<Item = &'v Elim<'v>>) -> Option<Path> {
    let mut path: Path = spine
        .map(|e| match e {
            Elim::Fst { .. } => Some(Proj::Fst),
            Elim::Snd { .. } => Some(Proj::Snd),
            _ => None,
        })
        .collect::<Option<_>>()?;
    path.reverse();
    Some(path)
}
