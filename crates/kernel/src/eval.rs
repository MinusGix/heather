//! The **evaluator**: (syntax, environment) → weak head normal value
//! (docs/nbe-conversion-design.md §§3–6).
//!
//! This is the environment machine that replaces the term rewriter's
//! substitute-and-re-reduce loop on the conversion path. It decides the same
//! relation `reduce.rs` transcribes — ch. 06's untyped weak-head reduction
//! plus δ — but an eliminator's β **extends an environment** instead of
//! copying a branch, which is what changes the exponent of
//! `issues/whnf-sharing-term-growth.md`.
//!
//! It is **not wired into `conv.rs`**: stage 1 of the round lands the domain
//! and the machine, differentially tested against the rewriter
//! (`tests/eval_differential.rs`); stage 2b switches conversion over.
//!
//! What it shares rather than transcribes:
//!
//! - [`crate::reduce::beta_elim_ty`] / [`beta_elim_tm`] — the ~1300-line code
//!   recursor β. The evaluator hands the box's payload to the *existing*
//!   function, receives the fired branch as **syntax**, and evaluates it. The
//!   65 branch telescopes are not written down a sixth time.
//! - [`crate::term::nth`] and the `elim_W`/`elim_Wf` ih λs, which are built
//!   from the same syntax `reduce.rs` builds — see [`Eval::fire_elim_w`].
//! - [`crate::reduce::step_type_delta`], for the one annotation that lives in
//!   a *different* local scope: `elim^Trm`'s type annotation, scoped in Δ
//!   (ch. 06 fixes the type-then-term reduction order).
//!
//! ## Laziness, and where it stops
//!
//! Sub-structures are [`TmClo`]/[`TyClo`] — environment plus syntax, forced
//! on demand and memoized. That is deliberate and it is what keeps the
//! machine faithful to ch. 06: weak-head reduction does not look inside
//! `su t`, an unfired branch, or an unread annotation, and neither does this.
//! A strict (children-are-values) domain would agree on every value and still
//! reduce a never-forced induction hypothesis — the shape §12 of the design
//! measured as family C.
//!
//! **Forcing is fallible everywhere** ([`Eval::force`], [`Eval::force_ty`],
//! [`Eval::apply`]): no `Deref`, no infallible accessor, no `unwrap`. And a
//! thunk that fails memoizes **nothing**, so re-forcing the same value graph
//! under a larger budget succeeds (design §6).
//!
//! ## Fuel
//!
//! One unit per evaluation step ch. 06 would have counted: every closure
//! application (β at `Lam`/`ULam`/`CtxLam`/`TyLam`), every eliminator fire,
//! every `El` decode, every `Vec`/`Fin` unfold, every δ-unfold. Exhaustion is
//! [`OutOfFuel`] and is never a verdict.

use std::sync::Arc as Rc;

use crate::level::Level;
use crate::reduce::{
    beta_elim_ty, beta_elim_tm, step_type_delta, Defs, OutOfFuel, Rec, NATIVE_DEPTH_LIMIT,
};
use crate::subst::{GlobalEntry, GlobalSubst};
use crate::term::{
    iwf_ih, m_out_corec, nth, Branches, IWfSig, MSig, CtxBase, CtxEntries, CtxEntry, GlobalVar, LocalCtx, LocalSubst, LocalVar,
    Motives, Term, Type,
};
use crate::value::{
    Elim, ElimSpine, Env, Head, Lookup, PiAnn, VCorec, VIWfSig, VMSig, VTmIWf, VTmM, SigAnn, SumAnn, TmClo, TyClo, VNeTy, VNeutral,
    VSubst, VTail, VTy, Val, ValueArena, WIhSyntax,
};
use crate::value::algebra::{AffineTree, FoldClass};
use crate::value::program::ContextProgram;

mod bits;
mod probe;
mod runs;
mod transduce;
mod withheld;

type Res<T> = Result<T, OutOfFuel>;

// ---------------------------------------------------------------------------
// Small constructors
// ---------------------------------------------------------------------------

fn neutral<'v>(
    arena: &'v ValueArena<'v>,
    head: Head<'v>,
    spine: ElimSpine<'v>,
    unfold: Option<&'v TmClo<'v>>,
) -> &'v Val<'v> {
    arena.val(Val::Neutral(arena.neutral(VNeutral { head, spine, unfold })))
}

// -- materializing a closure's pending global offset -------------------------
//
// A syntactic closure evaluates an **unshifted** body under the global offset
// its environment carries (`docs/lazy-global-offset-design.md`). The offset
// stays pending on the value path; these four helpers spend it where syntax
// *leaves* that path — into a box, a `ctx`, an annotation, a recursor table —
// and where a closure body sits under a global binder, which is the one place
// a pending (cutoff-free) offset could not be applied later.

fn amb_tm(env: &Env<'_>, t: &Rc<Term>) -> Rc<Term> {
    match env.gshift() {
        0 => Rc::clone(t),
        k => Rc::new(t.shift_global(k)),
    }
}

fn amb_ty(env: &Env<'_>, t: &Rc<Type>) -> Rc<Type> {
    match env.gshift() {
        0 => Rc::clone(t),
        k => Rc::new(t.shift_global(k)),
    }
}

fn amb_ctx(env: &Env<'_>, c: &LocalCtx) -> LocalCtx {
    match env.gshift() {
        0 => c.clone(),
        k => c.shift_global(k),
    }
}

/// A term closure whose body sits **under a global binder** (design §4): the
/// offset is spent now, above that binder, and the closure is ambient.
fn under_binder_tm<'v>(
    arena: &'v ValueArena<'v>,
    env: &Env<'v>,
    body: &Rc<Term>,
) -> &'v TmClo<'v> {
    match env.gshift() {
        0 => arena.tm(TmClo::syn(*env, Rc::clone(body))),
        k => arena.tm(TmClo::syn(
            env.with_gshift(0),
            Rc::new(body.shift_global_above(k, 1)),
        )),
    }
}

/// The recursor's motive and branch telescopes, materialized: they are read
/// as syntax by `reduce.rs`'s β, which knows nothing of offsets.
fn amb_tables(
    env: &Env<'_>,
    motives: &Rc<Motives>,
    branches: &Rc<Branches>,
) -> (Rc<Motives>, Rc<Branches>) {
    match env.gshift() {
        0 => (Rc::clone(motives), Rc::clone(branches)),
        k => {
            let (m, b) = crate::subst::shift_global_tables(motives, branches, k);
            (Rc::new(m), Rc::new(b))
        }
    }
}

/// [`under_binder_tm`] at the type level.
fn under_binder_ty<'v>(
    arena: &'v ValueArena<'v>,
    env: &Env<'v>,
    body: &Rc<Type>,
) -> &'v TyClo<'v> {
    match env.gshift() {
        0 => arena.ty(TyClo::new(*env, Rc::clone(body))),
        k => arena.ty(TyClo::new(
            env.with_gshift(0),
            Rc::new(body.shift_global_above(k, 1)),
        )),
    }
}

/// An eliminator applied to something it cannot eliminate. Unreachable on
/// well-typed input — `reduce.rs` is equally stuck there — but represented
/// rather than panicked on, so no input reaches undefined behaviour.
fn stuck<'v>(arena: &'v ValueArena<'v>, head: &'v Val<'v>, e: &Elim<'v>) -> &'v Val<'v> {
    let spine = arena.elim(ElimSpine::empty(), e.clone());
    neutral(arena, Head::Stuck(head), spine, None)
}

// ---------------------------------------------------------------------------
// The machine
// ---------------------------------------------------------------------------

/// A pending reduction, in the tail position of [`Eval::drive`]'s loop.
enum Work<'v> {
    /// Already a weak head value.
    Val(&'v Val<'v>),
    /// `eval(t, ρ)`.
    Eval(Rc<Term>, Env<'v>),
    /// Force a 0-binder sub-structure.
    Force(&'v TmClo<'v>),
    /// Apply a closure to its pending binders' values.
    Apply(&'v TmClo<'v>, Vec<&'v TmClo<'v>>),
    /// [`Work::Apply`] at one binder — β's commonest shape, and the one that
    /// must not allocate a vector to say so.
    Apply1(&'v TmClo<'v>, &'v TmClo<'v>),
    /// Eliminate a weak head value.
    Elim(&'v Val<'v>, Elim<'v>),
}

/// What [`Eval::fire_instantiate`] substitutes into a binder's body.
enum Instantiate {
    /// The universe levels, innermost first.
    Univ(Vec<Level>),
    Global(GlobalEntry),
}

/// What a value flows back into: a thunk waiting to memoize it, or an
/// elimination waiting for its head.
enum Frame<'v> {
    /// A thunk being forced: its value is memoized when it arrives
    /// (`ValueArena::cache_tm`).
    Memo(&'v TmClo<'v>),
    /// An elimination that already has a region cell (a glued unfolding's,
    /// an eliminator's own recursion).
    Elim(&'v Elim<'v>),
    /// An elimination made for this frame alone. Held by value rather than
    /// given a region cell: the frame is popped long before the query ends,
    /// and a cell would keep it until then.
    Owned(Elim<'v>),
    /// A successor program waiting for the value its fold produced at the
    /// run's tail. A run there is merged into one program rather than left
    /// as the next fragment of a chain, so that `add`-shaped folds over
    /// literals — `p + p`, `mul(p, 2)` — build one saturated run and not
    /// one fragment per logical addition.
    ///
    /// Under conversion's δ-lazy evaluation the tail's fold is usually a
    /// *glued* neutral (`mul(2, k)` unfolded once is `add(mul(2, k-1), 2)`,
    /// whose tail is the still-glued `mul(2, k-1)`), so the frame unfolds
    /// glued heads at the tail until a run, a constructor, or a stuck
    /// neutral appears — each unfolding charged as a δ-step. `glued` keeps
    /// the first glued neutral: if the unfoldings end stuck, that is the
    /// tail conversion keeps, so an open wrapper is not normalized away.
    NatRunTail {
        program: Rc<ContextProgram<()>>,
        glued: Option<&'v Val<'v>>,
    },
    /// A synchronous fold (`head`, a `NatSync`) waiting for its unfolded
    /// right-hand counter; the application `app` is retried with the value
    /// that flows back in place of its argument.
    SyncArg {
        head: &'v Val<'v>,
        app: &'v Elim<'v>,
    },
}

/// An evaluation run: the shared fuel budget, the δ-environment, and the
/// **base** of the ambient local context.
///
/// The base is the one piece of Γ the machine needs beyond the environment:
/// de Bruijn indices past the environment's concrete entries name variables
/// of the abstract prefix `g` (see [`Head::BaseVar`]), and the shared β
/// helpers materialize `id_Γ`, which reads Γ's length and base and nothing
/// else. It never changes during a run: a universe or global instantiation
/// renumbers the *outer* scope back down, so the captured environment is
/// already in the post-instantiation scope, and a context variable
/// substituted by `Λ(g). t` is always freshly bound and therefore never Γ's
/// base.
pub struct Eval<'a, 'v> {
    fuel: u64,
    defs: Defs<'a>,
    base: CtxBase,
    arena: &'v ValueArena<'v>,
    /// [`Eval::drive`]'s continuation stack, kept across drives so that the
    /// common reduction step allocates nothing for it. Nested drives (a
    /// scrutinee evaluated before its elimination is built) use it as a
    /// stack of stacks: each records the height it entered at.
    frames: Vec<Frame<'v>>,
    /// Native frames already standing under this machine: one per live
    /// re-entry of [`Eval::drive`], plus whatever the caller reserved with
    /// [`Eval::reserve_depth`]. Bounded by
    /// [`crate::reduce::NATIVE_DEPTH_LIMIT`]
    /// (docs/native-depth-budget-design.md).
    depth: u32,
    /// Set while a caller has asked for the **δ-transparent** weak head
    /// value ([`Eval::delta_whnf`]). An eliminator stuck on a glued
    /// scrutinee then unfolds the scrutinee and retries, instead of
    /// stalling as a spine for the caller to δ-step from the outside —
    /// each such outside step replays the whole pending spine, which made
    /// a structural consumer over a computed producer cubic in the width
    /// (and, once the replays' throwaway memos evicted the shared ones,
    /// exponential). The unfoldings performed are exactly those the outside
    /// loop would perform, in the same order, each charged one δ-step; only
    /// the replays are gone. Off by default: opaque evaluation is what the
    /// δ-lazy rendezvous in conversion needs (see `step_elim`).
    transparent: bool,
    /// Work done, for `crate::stats` (`docs/instrumentation-design.md` §2).
    /// Plain fields rather than thread-locals: the fuel decrement is the
    /// kernel's hottest line and a counter beside `fuel` costs what `fuel -=
    /// 1` costs. Flushed to the thread-local totals when the run is dropped.
    /// Nothing in the kernel reads them.
    steps: u64,
    delta_steps: u64,
    drives: u64,
}

impl Drop for Eval<'_, '_> {
    fn drop(&mut self) {
        crate::stats::eval_steps(self.steps);
        crate::stats::eval_delta_steps(self.delta_steps);
        crate::stats::eval_drives(self.drives);
    }
}

/// An `M` signature's closures, all built in `env` (see [`VMSig`]).
fn vm_sig<'v>(arena: &'v ValueArena<'v>, env: &Env<'v>, sig: &MSig) -> Rc<VMSig<'v>> {
    Rc::new(VMSig {
        level: sig.level.clone(),
        pos_level: sig.pos_level.clone(),
        idx_level: sig.idx_level.clone(),
        idx: arena.ty(TyClo::new(*env, Rc::clone(&sig.idx))),
        shape: arena.ty(TyClo::new(*env, Rc::clone(&sig.shape))),
        pos: arena.ty(TyClo::new(*env, Rc::clone(&sig.pos))),
        next: arena.tm(TmClo::syn(*env, Rc::clone(&sig.next))),
    })
}

impl<'a, 'v> Eval<'a, 'v> {
    /// A run with `fuel` units, unfolding the definitions of `defs`, over a Γ
    /// whose base is `base`.
    pub fn new(
        fuel: u64,
        defs: Defs<'a>,
        base: CtxBase,
        arena: &'v ValueArena<'v>,
    ) -> Eval<'a, 'v> {
        Eval {
            fuel,
            defs,
            base,
            arena,
            frames: Vec::new(),
            depth: 0,
            transparent: false,
            steps: 0,
            delta_steps: 0,
            drives: 0,
        }
    }

    /// The unspent budget.
    pub fn fuel(&self) -> u64 {
        self.fuel
    }

    /// Declare the native frames the *caller* is already standing on, so that
    /// the depth budget bounds the whole stack and not this machine's share
    /// of it. Conversion runs the evaluator from inside its own recursion
    /// (`conv/dom/values.rs`), and the two interleave on one native stack.
    pub fn reserve_depth(&mut self, frames: u32) {
        self.depth = frames;
    }

    fn vclo(&self, value: &'v Val<'v>) -> &'v TmClo<'v> {
        self.arena.tm(TmClo::val(value))
    }

    fn nat_residual(
        &self,
        program: Option<Rc<ContextProgram<()>>>,
        tail: &'v TmClo<'v>,
    ) -> &'v TmClo<'v> {
        match program {
            None => tail,
            Some(program) => self.vclo(self.arena.val(Val::NatRun { program, tail })),
        }
    }

    fn spend(&mut self) -> Res<()> {
        if self.fuel == 0 {
            return Err(OutOfFuel);
        }
        self.fuel -= 1;
        self.steps += 1;
        Ok(())
    }

    /// [`Eval::spend`] in bulk: one unit per bit a native step consumed or
    /// produced (`docs/native-bitvector-values-design.md` §8). Charging
    /// *something* proportional to the data keeps `eval_steps` an
    /// interpretable measure and keeps a pathological width from being free;
    /// charging at most what the structural path charged is what keeps a
    /// verdict fuel allows today from becoming a refusal.
    fn spend_n(&mut self, n: u64) -> Res<()> {
        if self.fuel < n {
            self.fuel = 0;
            return Err(OutOfFuel);
        }
        self.fuel -= n;
        self.steps += n;
        Ok(())
    }

    /// A Γ of the right *shape* for the shared β helpers, which read only its
    /// length and base (`reduce.rs` module doc). The entry types are never
    /// inspected, so a filler suffices — and building one is confined to the
    /// code-recursor path, which is not the hot one.
    fn scope(&self, env: &Env<'v>) -> LocalCtx {
        LocalCtx {
            base: self.base,
            entries: CtxEntries::repeat(
                CtxEntry { ty: Rc::new(Type::Nat), level: Level::Zero },
                env.len() as usize,
            ),
        }
    }

    // -- the trampoline -----------------------------------------------------

    /// Drive a piece of work to a value, keeping the machine's **tail calls
    /// off the native stack**.
    ///
    /// Every link in a reduction chain — evaluate an application, fire its β,
    /// apply the closure, evaluate the body, meet the next application — is a
    /// tail call, and a rewriter spends them in a `while` loop
    /// (`reduce.rs`'s `whnf_*`). Written as Rust recursion they would make
    /// the machine's stack depth proportional to the *number of reduction
    /// steps* rather than to the term's depth, and a divergent term would
    /// then abort the process instead of returning [`OutOfFuel`] — turning
    /// the fuel policy, which exists to make the checker total on ill-typed
    /// input, into a crash. (Measured, 2026-07-31: Ω under a 500-step budget
    /// overflowed an 8 MiB stack.)
    ///
    /// So the tail positions are *returned* as [`Work`] and spent here, and
    /// the two places a result has to flow back into something — a thunk
    /// waiting for its memo, an elimination waiting for its head — become
    /// explicit [`Frame`]s on the heap. Non-tail recursion (a scrutinee, an
    /// application's function, a type annotation) stays on the native stack,
    /// where its depth is the syntax's and the rewriter's own — *except* when
    /// a value nests scrutinees, which is why each re-entry is counted
    /// against [`NATIVE_DEPTH_LIMIT`] (docs/native-depth-budget-design.md).
    /// A head that is a bound variable, the commonest way a value nests, is
    /// the exception's exception: it is forced on this loop with the
    /// elimination waiting on the heap ([`Eval::await_bound`], §9).
    fn drive(&mut self, start: Work<'v>) -> Res<&'v Val<'v>> {
        let floor = self.frames.len();
        self.drive_above(start, floor)
    }

    /// [`Eval::drive`] with the frames above `floor` already its own.
    fn drive_above(&mut self, start: Work<'v>, floor: usize) -> Res<&'v Val<'v>> {
        if self.depth >= NATIVE_DEPTH_LIMIT {
            self.frames.truncate(floor);
            return Err(OutOfFuel);
        }
        self.depth += 1;
        self.drives += 1;
        let out = self.drive_from(start, floor);
        self.depth -= 1;
        // An error unwinds whatever this drive had pending; a thunk that
        // never reached its frame keeps no memo (design §6).
        self.frames.truncate(floor);
        out
    }

    /// The loop is the machine's whole native frame on a value-nested chain
    /// (docs/native-depth-budget-design.md §8): every arm but the trivial
    /// ones is a call to a function kept out of line, so this frame holds
    /// only `work` and what the next call needs, and a re-entry costs that
    /// rather than the union of every arm's locals.
    fn drive_from(&mut self, start: Work<'v>, floor: usize) -> Res<&'v Val<'v>> {
        let mut work = start;
        loop {
            // Every arm writes the one `next`, so the frame holds one `Work`
            // in flight rather than a result slot per callee.
            let next = match work {
                Work::Eval(t, env) => self.step_eval(&t, &env),
                Work::Elim(head, e) => self.step_elim(head, e),
                Work::Apply1(c, arg) => Ok(self.step_apply(c, &[arg])),
                Work::Apply(c, args) => Ok(self.step_apply(c, &args)),
                Work::Force(c) => Ok(self.step_force(c)),
                Work::Val(v) => {
                    if self.frames.len() == floor {
                        return Ok(v);
                    }
                    match self.frames.pop() {
                        None => return Ok(v),
                        Some(frame) => self.step_return(frame, v),
                    }
                }
            };
            work = next?;
        }
    }

    /// [`Work::Apply`] and [`Work::Apply1`]: the closure's body in its
    /// environment extended by `args`.
    #[inline(never)]
    fn step_apply(&mut self, c: &'v TmClo<'v>, args: &[&'v TmClo<'v>]) -> Work<'v> {
        match c {
            TmClo::Syn { env, body, .. } => Work::Eval(Rc::clone(body), env.extend(self.arena, args)),
            // A closure position holding a computed value has no pending
            // binders; it ignores them.
            _ => Work::Force(c),
        }
    }

    /// [`Work::Force`]: a memo hit, a computed value, or the thunk's body
    /// under a [`Frame::Memo`].
    #[inline(never)]
    fn step_force(&mut self, c: &'v TmClo<'v>) -> Work<'v> {
        if let Some(at) = self.arena.sealed_glue(c) {
            crate::unseal::note(at);
        }
        if let Some(v) = self.arena.memo_tm(c) {
            return Work::Val(v);
        }
        match c {
            TmClo::Val(v) => Work::Val(*v),
            TmClo::Syn { env, body, .. } => {
                if let Some(v) = self.arena.memo_closed(c) {
                    return Work::Val(v);
                }
                let w = Work::Eval(Rc::clone(body), *env);
                self.frames.push(Frame::Memo(c));
                w
            }
            TmClo::Elim { head, elim, .. } => {
                let w = Work::Force(head);
                self.frames.push(Frame::Memo(c));
                self.frames.push(Frame::Elim(*elim));
                w
            }
        }
    }

    /// A value flowing back into the frame it was popped from.
    #[inline(never)]
    fn step_return(&mut self, frame: Frame<'v>, v: &'v Val<'v>) -> Res<Work<'v>> {
        Ok(match frame {
            // A thunk records its value only on success.
            Frame::Memo(c) => {
                self.arena.cache_tm(c, &v);
                self.arena.cache_closed(c, v);
                Work::Val(v)
            }
            Frame::Elim(e) => Work::Elim(v, e.clone()),
            Frame::Owned(e) => Work::Elim(v, e),
            Frame::SyncArg { head, app } => {
                let Elim::App { ann, .. } = &*app else {
                    unreachable!("SyncArg stores an application")
                };
                let app = Elim::App { ann: ann.clone(), arg: self.vclo(v) };
                Work::Elim(head, app)
            }
            Frame::NatRunTail { program, glued } => match &*v {
                Val::NatRun { program: inner, tail } => {
                    Work::Val(self.arena.val(Val::NatRun {
                        program: ContextProgram::append(program, Rc::clone(inner)),
                        tail: *tail,
                    }))
                }
                Val::Neutral(n) if n.unfold.is_some() => {
                    self.spend()?;
                    let unfold = n.unfold.unwrap();
                    let glued = glued.or_else(|| Some(v));
                    self.frames.push(Frame::NatRunTail { program, glued });
                    Work::Force(unfold)
                }
                Val::Neutral(_) => {
                    let tail = glued.unwrap_or(v);
                    Work::Val(self.arena.val(Val::NatRun { program, tail: self.vclo(tail) }))
                }
                _ => Work::Val(self.arena.val(Val::NatRun { program, tail: self.vclo(v) })),
            },
        })
    }

    // -- forcing and application -------------------------------------------

    /// Force a 0-binder sub-structure to its weak head value. Memoizes on
    /// success only.
    pub fn force(&mut self, c: &'v TmClo<'v>) -> Res<&'v Val<'v>> {
        self.drive(Work::Force(c))
    }

    /// [`Eval::force`] for types.
    pub fn force_ty(&mut self, c: &'v TyClo<'v>) -> Res<&'v VTy<'v>> {
        if let Some(v) = self.arena.memo_ty(c) {
            return Ok(v);
        }
        let v = match c {
            TyClo::Val(v) => *v,
            TyClo::Syn { env, body, .. } => {
                let (env, body) = (*env, Rc::clone(body));
                self.eval_ty(&body, &env)?
            }
            TyClo::Vec { level, elem, len, .. } => {
                let (level, elem, len) = (*level, *elem, *len);
                let lv = self.force(len)?;
                self.vec_ty(level, elem, &lv)?
            }
            TyClo::El { level, tm, .. } => {
                let (level, tm) = (*level, *tm);
                let v = self.force(tm)?;
                self.decode(level, &v)?
            }
        };
        self.arena.cache_ty(c, &v);
        Ok(v)
    }

    /// Apply a closure to its pending binders' values, `args[0]` outermost.
    /// This is the operation that replaces `apply_local`: it allocates one
    /// environment cell per binder and copies nothing.
    pub fn apply(&mut self, c: &'v TmClo<'v>, args: &[&'v TmClo<'v>]) -> Res<&'v Val<'v>> {
        let w = match args {
            [a] => Work::Apply1(c, *a),
            _ => Work::Apply(c, args.to_vec()),
        };
        self.drive(w)
    }

    /// [`Eval::apply`] for type closures. A closure that is not syntactic has
    /// no pending binders and ignores them (`TyClo::Val` is a *constant*
    /// closure — the shape conversion's weakened annotations take).
    pub fn apply_ty(&mut self, c: &'v TyClo<'v>, args: &[&'v TmClo<'v>]) -> Res<&'v VTy<'v>> {
        if args.is_empty() {
            return self.force_ty(c);
        }
        match c {
            TyClo::Syn { env, body, .. } => {
                let (env, body) = (env.extend(self.arena, args), Rc::clone(body));
                self.eval_ty(&body, &env)
            }
            _ => self.force_ty(c),
        }
    }

    // -- δ ------------------------------------------------------------------

    /// Force exactly one glued definition at the head, leaving a newly
    /// exposed defined head glued. Conversion uses this to interleave
    /// unfolding with spine comparison: a transparent wrapper may reveal the
    /// same head as the other side without requiring either body to normalize
    /// completely.
    pub fn delta_step(&mut self, v: &'v Val<'v>) -> Res<&'v Val<'v>> {
        let unfold = match &*v {
            Val::Neutral(n) => n.unfold,
            _ => None,
        };
        match unfold {
            None => Ok(v),
            Some(u) => {
                self.spend()?;
                self.delta_steps += 1;
                self.force(u)
            }
        }
    }

    /// [`Eval::delta_step`] run **transparently**, as [`Eval::delta_whnf`]'s
    /// steps are: a single step that looks ahead (conversion's
    /// `meet_on_the_way`) forces the glued unfoldings the transparent run
    /// that follows will read, and forced opaquely they hold eliminators
    /// stuck on glued scrutinees that the run must replay. That costs work,
    /// not correctness, and enough of it to run `rt_lower_tests`'s
    /// `spread_agrees` out of fuel. #459 found the step refusing a
    /// convertible pair instead: the cause was a withheld call judged open
    /// at a lazily forced argument and memoized unglued, fixed where the
    /// verdict is made ([`Eval::closed`],
    /// `docs/kernel-implicit-state-review.md` §1).
    pub fn delta_step_transparent(&mut self, v: &'v Val<'v>) -> Res<&'v Val<'v>> {
        let saved = std::mem::replace(&mut self.transparent, true);
        let out = self.delta_step(v);
        self.transparent = saved;
        out
    }

    /// Force the glued unfoldings at the head until the value is not a
    /// definition's spine — i.e. the δ-transparent weak head value.
    ///
    /// Conversion's δ-lazy stage deliberately does *not* call this until the
    /// opaque comparison has failed (design §5); it is the second stage, and
    /// the differential oracle's counterpart to `whnf_term_delta`.
    ///
    /// Runs **transparently** (`Eval::transparent`): a stuck eliminator met
    /// while replaying the spine unfolds its glued scrutinee in place. The
    /// loop is still needed — an application spine over a glued head is
    /// left glued by the replay — and it terminates because every round
    /// unfolds at least the innermost definition.
    pub fn delta_whnf(&mut self, mut v: &'v Val<'v>) -> Res<&'v Val<'v>> {
        let saved = std::mem::replace(&mut self.transparent, true);
        let out = loop {
            let next = match self.delta_step(v) {
                Ok(next) => next,
                Err(e) => break Err(e),
            };
            if Val::ptr_eq(next, v) {
                break Ok(v);
            }
            v = next;
        };
        self.transparent = saved;
        out
    }

    /// [`Eval::delta_step`] for types: advance exactly one definition in the
    /// term at which an `El`, `Vec`, `Fin` or `DVec` is δ-stuck, then perform the
    /// newly enabled non-δ type computation.
    /// Unfold a type value's definitions until its head is a former, or it
    /// is stuck on something δ cannot move.
    ///
    /// The evaluator-side spelling of `Conv::delta_to_head_ty`, and it exists
    /// for exactly one customer: the checked spellings
    /// (`docs/intro-by-type-design.md`), whose single annotation is the
    /// *un-reduced* type the elaborator had. Evaluating one means exposing
    /// that type's head former and reading the component closures off it —
    /// which is where the sharing this round is about comes from, because the
    /// components are closures over an environment and are never copied.
    pub fn ty_to_former(&mut self, mut v: &'v VTy<'v>) -> Res<&'v VTy<'v>> {
        while matches!(&*v, VTy::Neutral(_)) {
            let d = self.delta_step_ty(v)?;
            if VTy::ptr_eq(d, v) {
                break;
            }
            v = d;
        }
        Ok(v)
    }

    pub fn delta_step_ty(&mut self, v: &'v VTy<'v>) -> Res<&'v VTy<'v>> {
        enum Next<'v> {
            Done,
            El(Level, &'v Val<'v>),
            Vec(Level, &'v TyClo<'v>, &'v Val<'v>),
            Fin(&'v Val<'v>),
            DVec(Level, &'v TyClo<'v>, &'v Val<'v>),
        }
        let next = match &*v {
            VTy::Neutral(VNeTy::El { level, tm }) => Next::El(level.clone(), *tm),
            VTy::Vec { level, elem, len } => Next::Vec(level.clone(), *elem, *len),
            VTy::Fin { len } => Next::Fin(*len),
            VTy::DVec { level, len, fam } => Next::DVec(level.clone(), *fam, *len),
            _ => Next::Done,
        };
        match next {
            Next::Done => Ok(v),
            Next::El(level, tm) => {
                let d = self.delta_step(tm)?;
                if Val::ptr_eq(d, tm) {
                    Ok(v)
                } else {
                    self.decode(&level, &d)
                }
            }
            Next::Vec(level, elem, len) => {
                let d = self.delta_step(len)?;
                if Val::ptr_eq(d, len) {
                    Ok(v)
                } else {
                    self.vec_ty(&level, elem, &d)
                }
            }
            Next::Fin(len) => {
                let d = self.delta_step(len)?;
                if Val::ptr_eq(d, len) {
                    Ok(v)
                } else {
                    self.fin_ty(&d)
                }
            }
            Next::DVec(level, fam, len) => {
                let d = self.delta_step(len)?;
                if Val::ptr_eq(d, len) {
                    Ok(v)
                } else {
                    self.dvec_ty(&level, fam, &d)
                }
            }
        }
    }

    /// Force the glued unfoldings at a type's δ-stuck term until none
    /// remains.
    pub fn delta_whnf_ty(&mut self, mut v: &'v VTy<'v>) -> Res<&'v VTy<'v>> {
        let saved = std::mem::replace(&mut self.transparent, true);
        let out = loop {
            let next = match self.delta_step_ty(v) {
                Ok(next) => next,
                Err(e) => break Err(e),
            };
            if VTy::ptr_eq(next, v) {
                break Ok(v);
            }
            v = next;
        };
        self.transparent = saved;
        out
    }

    // -- types --------------------------------------------------------------

    /// Evaluate a type to a weak head normal type value.
    pub fn eval_ty(&mut self, t: &Type, env: &Env<'v>) -> Res<&'v VTy<'v>> {
        let yclo = |env: &Env<'v>, body: &Rc<Type>| {
            self.arena.ty(TyClo::new(*env, Rc::clone(body)))
        };
        let tclo = |env: &Env<'v>, body: &Rc<Term>| {
            self.arena.tm(TmClo::syn(*env, Rc::clone(body)))
        };
        let v = match t {
            Type::Nat => VTy::Nat,
            Type::Ty(l) => VTy::Ty(l.clone()),
            Type::Unit { level } => VTy::Unit { level: level.clone() },
            Type::Empty { level } => VTy::Empty { level: level.clone() },
            Type::SEmpty { level } => VTy::SEmpty { level: level.clone() },
            Type::Pi { dom_level, cod_level, dom, cod } => VTy::Pi {
                dom_level: dom_level.clone(),
                cod_level: cod_level.clone(),
                dom: yclo(env, dom),
                cod: yclo(env, cod),
            },
            Type::Sigma { fst_level, snd_level, fst, snd } => VTy::Sigma {
                fst_level: fst_level.clone(),
                snd_level: snd_level.clone(),
                fst: yclo(env, fst),
                snd: yclo(env, snd),
            },
            Type::W { shape_level, pos_level, shape, pos } => VTy::W {
                shape_level: shape_level.clone(),
                pos_level: pos_level.clone(),
                shape: yclo(env, shape),
                pos: yclo(env, pos),
            },
            Type::Wf { level, shape, arity } => VTy::Wf {
                level: level.clone(),
                shape: yclo(env, shape),
                arity: tclo(env, arity),
            },
            Type::IWf { sig, index } => VTy::IWf {
                sig: Rc::new(VIWfSig {
                    level: sig.level.clone(),
                    idx_level: sig.idx_level.clone(),
                    idx: yclo(env, &sig.idx),
                    shape: yclo(env, &sig.shape),
                    arity: tclo(env, &sig.arity),
                    out: tclo(env, &sig.out),
                    child: tclo(env, &sig.child),
                }),
                index: tclo(env, index),
            },
            Type::M { sig, index } => VTy::M { sig: vm_sig(self.arena, env, sig), index: tclo(env, index) },
            Type::Sum { lhs_level, rhs_level, lhs, rhs } => VTy::Sum {
                lhs_level: lhs_level.clone(),
                rhs_level: rhs_level.clone(),
                lhs: yclo(env, lhs),
                rhs: yclo(env, rhs),
            },
            Type::Id { level, ty, lhs, rhs } => VTy::Id {
                level: level.clone(),
                ty: yclo(env, ty),
                lhs: tclo(env, lhs),
                rhs: tclo(env, rhs),
            },
            Type::SEq { level, ty, lhs, rhs } => VTy::SEq {
                level: level.clone(),
                ty: yclo(env, ty),
                lhs: tclo(env, lhs),
                rhs: tclo(env, rhs),
            },
            Type::Squash { level, ty } => VTy::Squash {
                level: level.clone(),
                ty: yclo(env, ty),
            },
            Type::UPi { num_vars, level, body } => VTy::UPi {
                num_vars: *num_vars,
                level: level.clone(),
                body: yclo(env, body),
            },
            Type::CtxPi { level, body } => VTy::CtxPi {
                level: level.clone(),
                body: under_binder_ty(self.arena, env, body),
            },
            Type::TyPi { ctx, arg_level, body_level, body } => VTy::TyPi {
                ctx: amb_ctx(env, ctx),
                arg_level: arg_level.clone(),
                body_level: body_level.clone(),
                body: under_binder_ty(self.arena, env, body),
            },
            Type::CodeTy { ctx, level } => {
                VTy::CodeTy { ctx: amb_ctx(env, ctx), level: level.clone() }
            }
            Type::CodeTm { ctx, ty, level } => VTy::CodeTm {
                ctx: amb_ctx(env, ctx),
                ty: amb_ty(env, ty),
                level: level.clone(),
            },
            Type::GlobalTy { var, subst } => {
                let var = GlobalVar(var.0 + env.gshift());
                let subst = self.eval_subst(subst, env)?;
                VTy::Neutral(VNeTy::Global { var, subst })
            }
            // `El` is a redex-or-neutral and has no canonical value.
            Type::El { level, tm } => {
                let v = self.eval_tm(tm, env)?;
                return self.decode(level, &v);
            }
            // `Vec`/`Fin` step at a canonical length; the value exists only
            // over a stuck one.
            Type::Vec { level, elem, len } => {
                let lv = self.eval_tm(len, env)?;
                return self.vec_ty(level, yclo(env, elem), &lv);
            }
            Type::Fin { len } => {
                let lv = self.eval_tm(len, env)?;
                return self.fin_ty(&lv);
            }
            Type::DVec { level, len, fam } => {
                let lv = self.eval_tm(len, env)?;
                return self.dvec_ty(level, yclo(env, fam), &lv);
            }
        };
        Ok(self.arena.vty(v))
    }

    /// `El^l v` — decode an encoding *value*, or leave the neutral `El`.
    ///
    /// The decoded children are built as `El` **syntax** over the encoding
    /// child's own closure, so the decode stays one step deep: a `Π` is weak
    /// head normal and its domain is not reduced until someone asks.
    fn decode(&mut self, level: &Level, v: &'v Val<'v>) -> Res<&'v VTy<'v>> {
        // `El^l c` as a lazy type. When `c` has syntax the `El` is built as
        // syntax over the child's own closure — one step deep, so a decoded
        // `Π`'s domain is not reduced until someone asks; otherwise the
        // domain's own lazy `El` says the same thing about a value.
        let arena = self.arena;
        let el = |l: &Level, c: &'v TmClo<'v>| -> Option<&'v TyClo<'v>> {
            Some(match c.as_syn() {
                Some((env, body)) => arena.ty(TyClo::new(
                    *env,
                    Rc::new(Type::El { level: l.clone(), tm: Rc::clone(body) }),
                )),
                None => arena.ty_el(l.clone(), c),
            })
        };
        let stuck_el =
            || Ok(arena.vty(VTy::Neutral(VNeTy::El { level: level.clone(), tm: v })));

        let decoded = match &*v {
            Val::TmNat => VTy::Nat,
            Val::TmTy(l) => VTy::Ty(l.clone()),
            Val::TmUnit { level } => VTy::Unit { level: level.clone() },
            Val::TmEmpty { level } => VTy::Empty { level: level.clone() },
            Val::TmSEmpty { level } => VTy::SEmpty { level: level.clone() },
            Val::TmSquash { level, ty } => {
                let Some(ty) = el(level, ty) else { return stuck_el() };
                VTy::Squash { level: level.clone(), ty }
            }
            Val::TmPi { dom_level, cod_level, dom, cod } => {
                let (Some(d), Some(c)) = (el(dom_level, dom), el(cod_level, cod)) else {
                    return stuck_el();
                };
                VTy::Pi {
                    dom_level: dom_level.clone(),
                    cod_level: cod_level.clone(),
                    dom: d,
                    cod: c,
                }
            }
            Val::TmSigma { fst_level, snd_level, fst, snd } => {
                let (Some(a), Some(b)) = (el(fst_level, fst), el(snd_level, snd)) else {
                    return stuck_el();
                };
                VTy::Sigma {
                    fst_level: fst_level.clone(),
                    snd_level: snd_level.clone(),
                    fst: a,
                    snd: b,
                }
            }
            Val::TmW { shape_level, pos_level, shape, pos } => {
                let (Some(s), Some(p)) = (el(shape_level, shape), el(pos_level, pos)) else {
                    return stuck_el();
                };
                VTy::W {
                    shape_level: shape_level.clone(),
                    pos_level: pos_level.clone(),
                    shape: s,
                    pos: p,
                }
            }
            Val::TmSum { lhs_level, rhs_level, lhs, rhs } => {
                let (Some(a), Some(b)) = (el(lhs_level, lhs), el(rhs_level, rhs)) else {
                    return stuck_el();
                };
                VTy::Sum {
                    lhs_level: lhs_level.clone(),
                    rhs_level: rhs_level.clone(),
                    lhs: a,
                    rhs: b,
                }
            }
            Val::TmId { level: l, ty, lhs, rhs } => {
                let Some(t) = el(l, ty) else { return stuck_el() };
                VTy::Id {
                    level: l.clone(),
                    ty: t,
                    lhs: *lhs,
                    rhs: *rhs,
                }
            }
            Val::TmSEq { level: l, ty, lhs, rhs } => {
                let Some(t) = el(l, ty) else { return stuck_el() };
                VTy::SEq {
                    level: l.clone(),
                    ty: t,
                    lhs: *lhs,
                    rhs: *rhs,
                }
            }
            // The arity rides across unchanged: it is a term under the same
            // binder, and only the shape decodes.
            Val::TmWf { level: l, shape, arity } => {
                let Some(s) = el(l, shape) else { return stuck_el() };
                VTy::Wf { level: l.clone(), shape: s, arity: *arity }
            }
            // `El(TmM …) ⇝ M(El idx; El shape; El pos; next)(index)`
            // (docs/kernel-m-codes-design.md §1): `next` and the index are
            // terms of the decoded index type and ride across unchanged.
            Val::TmM(m) => {
                let VTmM { level: l, pos_level, idx_level, idx, shape, pos, next, index } = &**m;
                let (Some(i), Some(s), Some(p)) = (el(idx_level, idx), el(l, shape), el(pos_level, pos)) else {
                    return stuck_el();
                };
                VTy::M {
                    sig: Rc::new(VMSig {
                        level: l.clone(),
                        pos_level: pos_level.clone(),
                        idx_level: idx_level.clone(),
                        idx: i,
                        shape: s,
                        pos: p,
                        next: *next,
                    }),
                    index: *index,
                }
            }
            // `El(TmIWf …) ⇝ IWf(El idx; El shape; arity; out; child)(index)`
            // (docs/iwf-former-design.md §6): the arity, output and child
            // index and the index are terms and ride across unchanged.
            Val::TmIWf(w) => {
                let VTmIWf { level: l, idx_level, idx, shape, arity, out, child, index } = &**w;
                let (Some(i), Some(s)) = (el(idx_level, idx), el(l, shape)) else {
                    return stuck_el();
                };
                VTy::IWf {
                    sig: Rc::new(VIWfSig {
                        level: l.clone(),
                        idx_level: idx_level.clone(),
                        idx: i,
                        shape: s,
                        arity: *arity,
                        out: *out,
                        child: *child,
                    }),
                    index: *index,
                }
            }
            // `El (DVec k i. f) ⇝ DVec k (i. El f)`, which then steps at a
            // canonical length, as `Vec`'s decode does below.
            Val::TmDVec { level: l, len, fam } => {
                let Some(f) = el(l, fam) else { return stuck_el() };
                self.spend()?;
                let lv = self.force(len)?;
                let l = l.clone();
                return self.dvec_ty(&l, f, &lv);
            }
            // `El (Vec s k) ⇝ Vec (El s) k`, which then steps at a canonical
            // length — so the decode continues into the `Vec` rule.
            Val::TmVec { level: l, elem, len } => {
                let Some(e) = el(l, elem) else { return stuck_el() };
                self.spend()?;
                let lv = self.force(len)?;
                let l = l.clone();
                return self.vec_ty(&l, e, &lv);
            }
            Val::TmFin { len } => {
                self.spend()?;
                let lv = self.force(len)?;
                return self.fin_ty(&lv);
            }
            _ => return stuck_el(),
        };
        self.spend()?;
        Ok(self.arena.vty(decoded))
    }

    /// `Vec^l(T; k)`: `0 ⇝ Unit^l`, `S k ⇝ Σ(_ : T). Vec^l(T; k)`, stuck
    /// otherwise.
    ///
    /// The Σ-tail is the **unforced** `Vec` of [`TyClo::Vec`], not syntax: the
    /// predecessor is a value with no syntax of its own, the element type need
    /// not have any either (conversion synthesizes `Vec`s over element types
    /// that are values), and evaluating the tail eagerly would unroll the
    /// whole tuple type at a literal length. Neither the tail nor the element
    /// mentions the Σ's own binder, and a non-syntactic closure ignores it.
    pub(crate) fn vec_ty(
        &mut self,
        level: &Level,
        elem: &'v TyClo<'v>,
        len: &'v Val<'v>,
    ) -> Res<&'v VTy<'v>> {
        let out = match &*len {
            Val::Zero => {
                self.spend()?;
                VTy::Unit { level: level.clone() }
            }
            Val::Succ(pred) => {
                self.spend()?;
                VTy::Sigma {
                    fst_level: level.clone(),
                    snd_level: level.clone(),
                    fst: elem,
                    snd: self.arena.ty_vec(level.clone(), elem, pred),
                }
            }
            Val::NatRun { program, tail } => {
                self.spend()?;
                let pred = Val::nat_run_pred(self.arena, program, tail);
                VTy::Sigma {
                    fst_level: level.clone(),
                    snd_level: level.clone(),
                    fst: elem,
                    snd: self.arena.ty_vec(level.clone(), elem, pred),
                }
            }
            _ => VTy::Vec {
                level: level.clone(),
                elem,
                len: len,
            },
        };
        Ok(self.arena.vty(out))
    }

    /// `DVec^l(k; i. F)`: `0 ⇝ Unit^l`,
    /// `S k ⇝ Σ^{l,l}(_ : F[inl ⟨⟩/i]). DVec^l(k; j. F[inr j/i])`, stuck
    /// otherwise (docs/iwf-former-design.md §1.1).
    ///
    /// Both components are syntactic closures over the family's own
    /// environment, so nothing is forced: the head is the family with `i`
    /// bound to `inl ⟨⟩` — one environment cell — and the tail is `DVec`
    /// syntax read with the predecessor `k` pushed (the predecessor is a
    /// value with no syntax, and the tail's family must name it in its `inr`
    /// annotation). Only the tail's family is rewritten, by
    /// [`Type::inst_top`]: `F[inr j/i]` is not an environment extension.
    ///
    /// A family that is not syntactic (a constant closure) has no body to
    /// rewrite. The evaluator builds every `DVec` from syntax, so that does
    /// not arise; if it did the type would stay stuck, which costs
    /// completeness and not soundness.
    fn dvec_ty(
        &mut self,
        level: &Level,
        fam: &'v TyClo<'v>,
        len: &'v Val<'v>,
    ) -> Res<&'v VTy<'v>> {
        let stuck = || Ok(self.arena.vty(VTy::DVec { level: level.clone(), len: len, fam }));
        let pred = match &*len {
            Val::Zero => {
                self.spend()?;
                return Ok(self.arena.vty(VTy::Unit { level: level.clone() }));
            }
            Val::Succ(pred) => *pred,
            Val::NatRun { program, tail } => Val::nat_run_pred(self.arena, program, tail),
            _ => return stuck(),
        };
        let TyClo::Syn { env: fenv, body } = fam else { return stuck() };
        let (fenv, body) = (*fenv, Rc::clone(body));
        self.spend()?;
        let k = Env::empty().push(self.arena, pred);
        let first = self.arena.tm(TmClo::syn(
            k,
            Rc::new(crate::term::fin_first(Rc::new(Term::Var(LocalVar(0))))),
        ));
        let fst = self.arena.ty(TyClo::new(fenv.push(self.arena, first), Rc::clone(&body)));
        // In (Γ_F, k, x), the family in (Γ_F, k, x, j).
        let tail = Type::DVec {
            level: level.clone(),
            len: Rc::new(Term::Var(LocalVar(1))),
            fam: Rc::new(body.inst_top(
                3,
                &crate::term::fin_next(Rc::new(Term::Var(LocalVar(2))), Rc::new(Term::Var(LocalVar(0)))),
            )),
        };
        let snd = self.arena.ty(TyClo::new(fenv.push(self.arena, pred), Rc::new(tail)));
        Ok(self.arena.vty(VTy::Sigma { fst_level: level.clone(), snd_level: level.clone(), fst, snd }))
    }

    /// `Fin(k)`: `0 ⇝ Empty^0`, `S k ⇝ Unit^0 +^{0,0} Fin(k)`, stuck
    /// otherwise. Both reducts are closed apart from the predecessor, which
    /// again rides in the environment.
    fn fin_ty(&mut self, len: &'v Val<'v>) -> Res<&'v VTy<'v>> {
        let out = match &*len {
            Val::Zero => {
                self.spend()?;
                VTy::Empty { level: Level::Zero }
            }
            Val::Succ(pred) => {
                self.spend()?;
                let rhs_env = Env::empty().push(self.arena, pred);
                VTy::Sum {
                    lhs_level: Level::Zero,
                    rhs_level: Level::Zero,
                    lhs: self.arena.ty(TyClo::new(
                        Env::empty(),
                        Rc::new(Type::Unit { level: Level::Zero }),
                    )),
                    rhs: self.arena.ty(TyClo::new(
                        rhs_env,
                        Rc::new(Type::Fin { len: Rc::new(Term::Var(LocalVar(0))) }),
                    )),
                }
            }
            Val::NatRun { program, tail } => {
                self.spend()?;
                let pred = Val::nat_run_pred(self.arena, program, tail);
                let rhs_env = Env::empty().push(self.arena, pred);
                VTy::Sum {
                    lhs_level: Level::Zero,
                    rhs_level: Level::Zero,
                    lhs: self.arena.ty(TyClo::new(
                        Env::empty(),
                        Rc::new(Type::Unit { level: Level::Zero }),
                    )),
                    rhs: self.arena.ty(TyClo::new(
                        rhs_env,
                        Rc::new(Type::Fin { len: Rc::new(Term::Var(LocalVar(0))) }),
                    )),
                }
            }
            _ => VTy::Fin { len: len },
        };
        Ok(self.arena.vty(out))
    }

    /// A local substitution inside a neutral: its terms become **values**,
    /// evaluated pointwise here. An unforced `δ` would be the defect class
    /// reintroduced by the domain (design §3.4).
    fn eval_subst(&mut self, d: &LocalSubst, env: &Env<'v>) -> Res<VSubst<'v>> {
        let mut terms = Vec::with_capacity(d.terms.len());
        for t in &d.terms {
            terms.push(self.eval_tm(t, env)?);
        }
        Ok(VSubst { tail: VTail::of(d.tail, env.gshift()), terms })
    }

    // -- terms --------------------------------------------------------------

    /// Evaluate a term to a weak head normal value.
    pub fn eval_tm(&mut self, t: &Rc<Term>, env: &Env<'v>) -> Res<&'v Val<'v>> {
        self.eval_tm_ref(t, env)
    }

    /// [`Eval::eval_tm`] on a node the caller does not own — the **root** of a
    /// conversion, which is syntax lent to the checker. Wrapping it in an
    /// `Rc` just to start the machine cost 1.3× on `nat/check-numeral`, whose
    /// every conversion is one `Nat ≈ Nat`.
    pub fn eval_tm_ref(&mut self, t: &Term, env: &Env<'v>) -> Res<&'v Val<'v>> {
        // The first step may leave its elimination waiting on the frame
        // stack ([`Eval::await_bound`]), so the drive's floor is taken
        // before it.
        let floor = self.frames.len();
        let w = match self.step_eval(t, env) {
            Ok(w) => w,
            Err(e) => {
                self.frames.truncate(floor);
                return Err(e);
            }
        };
        self.drive_above(w, floor)
    }

    /// The pair a projection eliminates. When it is an application of a
    /// bound variable to a bound variable, `fst(k y)` or `snd(k y)`, its value
    /// is shared through the arena by the closures the two variables are
    /// bound to, so the sibling projection of the same application reads it
    /// instead of evaluating it again.
    ///
    /// This is the shape of a tier-2 function child, whose tree and proof
    /// are `λy. fst(k y)` and `λy. snd(k y)` over one `k`
    /// (docs/inductive-tier2-w-lowering.md §6): without the sharing, every
    /// read of a child evaluated `k y` twice, and a `bind` nested `d` deep to
    /// the left evaluated its innermost tree `2^d` times
    /// (issues/tier2-left-nested-bind-cost.md). Sound because evaluation is
    /// pure: the same closures applied give the same value, and only a
    /// success is remembered. Only a `k` that is a λ is shared: its
    /// application is β and reads nothing of the site's Π annotation, where
    /// a stuck application would keep the first site's annotation in its
    /// spine.
    fn eval_projected(&mut self, pair: &Rc<Term>, env: &Env<'v>) -> Res<&'v Val<'v>> {
        let (fun, arg) = match &**pair {
            Term::App { fun, arg, .. } | Term::AppAt { fun, arg } => (fun, arg),
            _ => return self.eval_tm(pair, env),
        };
        let (Some(k), Some(y)) = (bound_root(env, fun), bound_root(env, arg)) else {
            return self.eval_tm(pair, env);
        };
        if !matches!(&*self.force(k)?, Val::Lam { .. }) {
            return self.eval_tm(pair, env);
        }
        let key = (k as *const TmClo<'v> as usize, y as *const TmClo<'v> as usize);
        if let Some(v) = self.arena.shared_app(key) {
            crate::stats::shared_apps(1);
            return Ok(v);
        }
        let v = self.eval_tm(pair, env)?;
        self.arena.cache_shared_app(key, &v);
        Ok(v)
    }

    /// One step of [`Eval::eval_tm`], with its **tail positions returned**
    /// rather than called: see [`Eval::drive`]. An elimination evaluates its
    /// head here and builds its eliminator in [`Eval::elim_of`]; every other former is
    /// [`Eval::step_intro`]'s. The split is for the native stack: the head's
    /// evaluation is the recursion, and only this small frame stands under
    /// it (docs/native-depth-budget-design.md §8).
    fn step_eval(&mut self, t: &Term, env: &Env<'v>) -> Res<Work<'v>> {
        let v = match t {
            Term::Var(x) => match env.lookup(x.0) {
                Lookup::Bound(c) => return Ok(Work::Force(c)),
                Lookup::Base(d) => Val::base_var(self.arena, d),
            },
            // -- eliminations: the head here, the eliminator out of line --
            Term::App { fun, .. }
            | Term::AppAt { fun, .. }
            | Term::UApp { fun, .. }
            | Term::CtxApp { fun, .. }
            | Term::TyApp { fun, .. } => {
                if let Some(w) = self.await_bound(fun, t, env) {
                    return Ok(w);
                }
                let f = self.eval_tm(fun, env)?;
                return Ok(Work::Elim(f, self.elim_of(t, env)));
            }
            Term::Fst { pair, .. }
            | Term::Snd { pair, .. }
            | Term::FstAt { pair }
            | Term::SndAt { pair } => {
                if let Some(w) = self.await_bound(pair, t, env) {
                    return Ok(w);
                }
                let p = self.eval_projected(pair, env)?;
                return Ok(Work::Elim(p, self.elim_of(t, env)));
            }
            Term::ElimNat { scrut, .. }
            | Term::ElimEmpty { scrut, .. }
            | Term::ElimSEmpty { scrut, .. }
            | Term::ElimSquash { scrut, .. }
            | Term::Case { scrut, .. }
            | Term::ElimW { scrut, .. }
            | Term::ElimWf { scrut, .. }
            | Term::ElimIWf { scrut, .. }
            | Term::Out { scrut, .. }
            | Term::LetBoxTy { scrut, .. }
            | Term::LetBoxTm { scrut, .. }
            | Term::ElimCodeTy { scrut, .. } => {
                if let Some(w) = self.await_bound(scrut, t, env) {
                    return Ok(w);
                }
                let s = self.eval_tm(scrut, env)?;
                return Ok(Work::Elim(s, self.elim_of(t, env)));
            }
            Term::J { proof, .. } => {
                if let Some(w) = self.await_bound(proof, t, env) {
                    return Ok(w);
                }
                let p = self.eval_tm(proof, env)?;
                return Ok(Work::Elim(p, self.elim_of(t, env)));
            }
            Term::ElimCodeTm { .. } => return self.step_elim_code_tm(t, env),
            Term::VecLit { .. } => return self.step_vec_lit(t, env),
            // Its one-step view, a pair whose tail is the same array one
            // element on: one pair per element demanded, never the chain.
            Term::VecItems { level, elem, items, from } => {
                let unfolded = crate::term::vec_items_unfold(level, elem, items, *from).ok_or(OutOfFuel)?;
                return self.step_eval(&unfolded, env);
            }
            _ => return self.step_intro(t, env),
        };
        Ok(Work::Val(self.arena.val(v)))
    }

    /// An elimination `t` whose head (an application's function, a
    /// projection's pair, a scrutinee, `J`'s proof) is a variable bound to a
    /// closure: the head is forced on this machine's own loop, with the
    /// elimination waiting for it in a [`Frame::Owned`], instead of by a
    /// nested [`Eval::drive`].
    ///
    /// A chain of such heads is a chain in the *value*, not the syntax: each
    /// variable stands for a thunk whose body eliminates the next one
    /// (docs/native-depth-budget-design.md §1). The commonest is a tier-2
    /// value's proof read through a run of `match` aliases, `c y` with `c`
    /// the previous alias's `c y` (docs/inductive-tier2-w-lowering.md §7),
    /// one link per request a tactic answers under a `bind`
    /// (issues/grind-unrelated-lemma-fuel.md). Forced natively, every link
    /// re-entered `drive` and the chain was capped at `NATIVE_DEPTH_LIMIT`
    /// links; waiting on the heap, its depth is the frame stack's. A head
    /// that is any other term still recurses natively, where its depth is
    /// the syntax's.
    fn await_bound(&mut self, head: &Rc<Term>, t: &Term, env: &Env<'v>) -> Option<Work<'v>> {
        let Term::Var(x) = &**head else { return None };
        let Lookup::Bound(c) = env.lookup(x.0) else { return None };
        let e = self.elim_of(t, env);
        self.frames.push(Frame::Owned(e));
        Some(Work::Force(c))
    }

    /// [`Eval::step_eval`] at a former that is not an elimination.
    #[inline(never)]
    fn step_intro(&mut self, t: &Term, env: &Env<'v>) -> Res<Work<'v>> {
        let yclo = |env: &Env<'v>, body: &Rc<Type>| {
            self.arena.ty(TyClo::new(*env, Rc::clone(body)))
        };
        let tclo = |env: &Env<'v>, body: &Rc<Term>| {
            self.arena.tm(TmClo::syn(*env, Rc::clone(body)))
        };
        let v = match t {

            // -- encodings --
            Term::TmNat => Val::TmNat,
            Term::TmTy(l) => Val::TmTy(l.clone()),
            Term::TmUnit { level } => Val::TmUnit { level: level.clone() },
            Term::TmEmpty { level } => Val::TmEmpty { level: level.clone() },
            Term::TmSEmpty { level } => Val::TmSEmpty { level: level.clone() },
            Term::TmSquash { level, ty } => Val::TmSquash {
                level: level.clone(),
                ty: tclo(env, ty),
            },
            Term::TmPi { dom_level, cod_level, dom, cod } => Val::TmPi {
                dom_level: dom_level.clone(),
                cod_level: cod_level.clone(),
                dom: tclo(env, dom),
                cod: tclo(env, cod),
            },
            Term::TmSigma { fst_level, snd_level, fst, snd } => Val::TmSigma {
                fst_level: fst_level.clone(),
                snd_level: snd_level.clone(),
                fst: tclo(env, fst),
                snd: tclo(env, snd),
            },
            Term::TmW { shape_level, pos_level, shape, pos } => Val::TmW {
                shape_level: shape_level.clone(),
                pos_level: pos_level.clone(),
                shape: tclo(env, shape),
                pos: tclo(env, pos),
            },
            Term::TmWf { level, shape, arity } => Val::TmWf {
                level: level.clone(),
                shape: tclo(env, shape),
                arity: tclo(env, arity),
            },
            Term::TmDVec { level, len, fam } => Val::TmDVec {
                level: level.clone(),
                len: tclo(env, len),
                fam: tclo(env, fam),
            },
            Term::TmIWf { level, idx_level, idx, shape, arity, out, child, index } => {
                Val::TmIWf(Rc::new(VTmIWf {
                    level: level.clone(),
                    idx_level: idx_level.clone(),
                    idx: tclo(env, idx),
                    shape: tclo(env, shape),
                    arity: tclo(env, arity),
                    out: tclo(env, out),
                    child: tclo(env, child),
                    index: tclo(env, index),
                }))
            }
            Term::TmM { level, pos_level, idx_level, idx, shape, pos, next, index } => Val::TmM(Rc::new(VTmM {
                level: level.clone(),
                pos_level: pos_level.clone(),
                idx_level: idx_level.clone(),
                idx: tclo(env, idx),
                shape: tclo(env, shape),
                pos: tclo(env, pos),
                next: tclo(env, next),
                index: tclo(env, index),
            })),
            Term::TmId { level, ty, lhs, rhs } => Val::TmId {
                level: level.clone(),
                ty: tclo(env, ty),
                lhs: tclo(env, lhs),
                rhs: tclo(env, rhs),
            },
            Term::TmSEq { level, ty, lhs, rhs } => Val::TmSEq {
                level: level.clone(),
                ty: tclo(env, ty),
                lhs: tclo(env, lhs),
                rhs: tclo(env, rhs),
            },
            Term::TmSum { lhs_level, rhs_level, lhs, rhs } => Val::TmSum {
                lhs_level: lhs_level.clone(),
                rhs_level: rhs_level.clone(),
                lhs: tclo(env, lhs),
                rhs: tclo(env, rhs),
            },
            Term::TmVec { level, elem, len } => Val::TmVec {
                level: level.clone(),
                elem: tclo(env, elem),
                len: tclo(env, len),
            },
            Term::TmFin { len } => Val::TmFin { len: tclo(env, len) },

            // -- data --
            Term::Zero => Val::Zero,
            Term::NatLit(n) if n.is_zero() => Val::Zero,
            Term::NatLit(n) => Val::NatRun {
                program: nat_lit_program(n),
                tail: self.arena.tm(TmClo::val(self.arena.val(Val::Zero))),
            },
            Term::Succ(p) => Val::Succ(tclo(env, p)),
            Term::Refl { level, ty, tm } => Val::Refl {
                level: level.clone(),
                ty: yclo(env, ty),
                tm: tclo(env, tm),
            },
            Term::SRefl { level, ty, tm } => Val::SRefl {
                level: level.clone(),
                ty: yclo(env, ty),
                tm: tclo(env, tm),
            },
            Term::Squash { level, ty, tm } => Val::Squash {
                level: level.clone(),
                ty: yclo(env, ty),
                tm: tclo(env, tm),
            },
            Term::Pair { fst_level, snd_level, fst_ty, snd_ty, fst, snd } => Val::Pair {
                ann: Some(SigAnn {
                    fst_level: fst_level.clone(),
                    snd_level: snd_level.clone(),
                    fst_ty: yclo(env, fst_ty),
                    snd_ty: yclo(env, snd_ty),
                }),
                fst: tclo(env, fst),
                snd: tclo(env, snd),
            },
            Term::Triv { level } => Val::Triv { level: level.clone() },
            Term::Inl { lhs_level, rhs_level, lhs, rhs, val } => Val::Inl {
                ann: Some(SumAnn {
                    lhs_level: lhs_level.clone(),
                    rhs_level: rhs_level.clone(),
                    lhs: yclo(env, lhs),
                    rhs: yclo(env, rhs),
                }),
                val: tclo(env, val),
            },
            Term::Inr { lhs_level, rhs_level, lhs, rhs, val } => Val::Inr {
                ann: Some(SumAnn {
                    lhs_level: lhs_level.clone(),
                    rhs_level: rhs_level.clone(),
                    lhs: yclo(env, lhs),
                    rhs: yclo(env, rhs),
                }),
                val: tclo(env, val),
            },

            // -- the checked spellings (docs/intro-by-type-design.md) -------
            //
            // These do not get value forms of their own. The evaluator
            // exposes the annotation's head former and builds the *existing*
            // `Val::Pair` / `Val::Inl` / `Val::Inr` from the component
            // closures it finds there. Three consequences, all of them the
            // point: `value.rs`, `value/shift.rs` and the native fast paths
            // (`eval/bits.rs`, `eval/transduce.rs`, `eval/runs.rs`) never
            // learn the spelling exists; `pair@(T;a;b)` and
            // `pair(x:S.U;a;b)` are the same value, so they convert with no
            // new arm; and the components are the Σ value's own closures, so
            // the object the elaborator used to *write out* is now shared
            // rather than copied.
            //
            // An annotation whose head is not the expected former is
            // ill-typed. `eval` has one failure and it is `OutOfFuel` — "no
            // answer", never a verdict — so that is what it returns. The
            // rejection belongs to the typing rule, which does its own whnf
            // and reports `HeadMismatch`.
            // The **unannotated** spelling is the one the elaborator writes
            // at every inner layer, and it is the whole of the round's win:
            // there is no type to evaluate, no Σ to force, and the value is
            // the two field closures and nothing else.
            Term::PairAt { ty: None, fst, snd } => {
                Val::Pair { ann: None, fst: tclo(env, fst), snd: tclo(env, snd) }
            }
            Term::PairAt { ty: Some(ty), fst, snd } => {
                let t = self.eval_ty(ty, env)?;
                let t = self.ty_to_former(t)?;
                let VTy::Sigma { fst_level, snd_level, fst: fty, snd: sty } = &*t else {
                    return Err(OutOfFuel);
                };
                Val::Pair {
                    ann: Some(SigAnn {
                        fst_level: fst_level.clone(),
                        snd_level: snd_level.clone(),
                        fst_ty: *fty,
                        snd_ty: *sty,
                    }),
                    fst: tclo(env, fst),
                    snd: tclo(env, snd),
                }
            }
            Term::InlAt { ty, val } | Term::InrAt { ty, val } => {
                let right = matches!(t, Term::InrAt { .. });
                let ann = match ty {
                    None => None,
                    Some(ty) => {
                        let s = self.eval_ty(ty, env)?;
                        let s = self.ty_to_former(s)?;
                        let VTy::Sum { lhs_level, rhs_level, lhs, rhs } = &*s else {
                            return Err(OutOfFuel);
                        };
                        Some(SumAnn {
                            lhs_level: lhs_level.clone(),
                            rhs_level: rhs_level.clone(),
                            lhs: *lhs,
                            rhs: *rhs,
                        })
                    }
                };
                let val = tclo(env, val);
                if right { Val::Inr { ann, val } } else { Val::Inl { ann, val } }
            }

            Term::Sup { shape_level, pos_level, shape_ty, pos_ty, label, children } => {
                Val::Sup {
                    shape_level: shape_level.clone(),
                    pos_level: pos_level.clone(),
                    shape_ty: yclo(env, shape_ty),
                    pos_ty: yclo(env, pos_ty),
                    label: tclo(env, label),
                    children: tclo(env, children),
                }
            }
            Term::Supf { level, shape, arity, label, children } => Val::Supf {
                level: level.clone(),
                shape: yclo(env, shape),
                arity: tclo(env, arity),
                label: tclo(env, label),
                children: tclo(env, children),
            },
            Term::Supi { sig, label, children } => Val::Supi {
                sig: Rc::new(VIWfSig {
                    level: sig.level.clone(),
                    idx_level: sig.idx_level.clone(),
                    idx: yclo(env, &sig.idx),
                    shape: yclo(env, &sig.shape),
                    arity: tclo(env, &sig.arity),
                    out: tclo(env, &sig.out),
                    child: tclo(env, &sig.child),
                }),
                label: tclo(env, label),
                children: tclo(env, children),
            },

            Term::Corec { sig, carrier_level, carrier, step, index, seed } => Val::Corec {
                sig: vm_sig(self.arena, env, sig),
                coalg: Rc::new(VCorec {
                    carrier_level: carrier_level.clone(),
                    carrier: yclo(env, carrier),
                    step: tclo(env, step),
                    env: *env,
                }),
                index: tclo(env, index),
                seed: tclo(env, seed),
            },

            // -- functions --
            Term::Lam { dom_level, cod_level, dom, body } => Val::Lam {
                dom_level: dom_level.clone(),
                cod_level: cod_level.clone(),
                dom: yclo(env, dom),
                body: tclo(env, body),
            },
            Term::ULam { num_vars, level, body } => Val::ULam {
                num_vars: *num_vars,
                level: level.clone(),
                body: tclo(env, body),
            },
            Term::CtxLam { level, body } => Val::CtxLam {
                level: level.clone(),
                body: under_binder_tm(self.arena, env, body),
            },
            Term::TyLam { ctx, arg_level, body_level, body } => Val::TyLam {
                ctx: amb_ctx(env, ctx),
                arg_level: arg_level.clone(),
                body_level: body_level.clone(),
                body: under_binder_tm(self.arena, env, body),
            },

            // -- code: inert, and carrying no environment --
            //
            // A box holds raw syntax with no environment and compares
            // syntactically (ch. 06), so it is the sharpest of the sites
            // where a pending offset must be spent: an ambient box is what
            // keeps `letbox`'s β substituting ambient code into the ambient
            // body of design §4.
            Term::BoxTy(c) => Val::BoxTy(amb_ty(env, c)),
            Term::BoxTm(c) => Val::BoxTm(amb_tm(env, c)),

            // -- globals: glued neutrals --
            Term::GlobalTm { var, subst } => {
                let var = GlobalVar(var.0 + env.gshift());
                let subst = self.eval_subst(subst, env)?;
                return Ok(Work::Val(self.global_tm(var, subst)));
            }

            _ => unreachable!("step_eval evaluates variables and eliminations itself"),
        };
        Ok(Work::Val(self.arena.val(v)))
    }

    /// The eliminator of the elimination `t`, its closures over `env`; the
    /// head is [`Eval::step_eval`]'s.
    #[inline(never)]
    fn elim_of(&self, t: &Term, env: &Env<'v>) -> Elim<'v> {
        let yclo = |env: &Env<'v>, body: &Rc<Type>| {
            self.arena.ty(TyClo::new(*env, Rc::clone(body)))
        };
        let tclo = |env: &Env<'v>, body: &Rc<Term>| {
            self.arena.tm(TmClo::syn(*env, Rc::clone(body)))
        };
        match t {
            Term::App { dom_level, cod_level, dom, cod, arg, .. } => {
                let e = Elim::App {
                    ann: Some(PiAnn {
                        dom_level: dom_level.clone(),
                        cod_level: cod_level.clone(),
                        dom: yclo(env, dom),
                        cod: yclo(env, cod),
                    }),
                    arg: tclo(env, arg),
                };
                e
            }
            // app@ stores no Π, and the evaluator does not view the head's
            // type to invent one (docs/app-by-head-type-design.md §5).
            Term::AppAt { arg, .. } => {
                Elim::App { ann: None, arg: tclo(env, arg) }
            }
            Term::UApp { levels, .. } => {
                Elim::UApp { levels: levels.clone() }
            }
            Term::CtxApp { ctx, .. } => {
                Elim::CtxApp { ctx: amb_ctx(env, ctx) }
            }
            Term::TyApp { arg, .. } => {
                Elim::TyApp { arg: amb_ty(env, arg) }
            }
            Term::Fst { fst_level, snd_level, fst_ty, snd_ty, .. } => {
                let e = Elim::Fst {
                    ann: Some(SigAnn {
                        fst_level: fst_level.clone(),
                        snd_level: snd_level.clone(),
                        fst_ty: yclo(env, fst_ty),
                        snd_ty: yclo(env, snd_ty),
                    }),
                };
                e
            }
            Term::Snd { fst_level, snd_level, fst_ty, snd_ty, .. } => {
                let e = Elim::Snd {
                    ann: Some(SigAnn {
                        fst_level: fst_level.clone(),
                        snd_level: snd_level.clone(),
                        fst_ty: yclo(env, fst_ty),
                        snd_ty: yclo(env, snd_ty),
                    }),
                };
                e
            }
            // The checked projections push the *existing* elims with no
            // annotation at all — they carry none (design §2.1). A neutral
            // `fst@` is therefore indistinguishable from a neutral `fst` at
            // the value domain except for the stored levels, which
            // `conv.rs`'s typed projection arm already treats as optional:
            // it reads the Σ inferred for the pair, never the annotation.
            Term::FstAt { .. } | Term::SndAt { .. } => {
                let second = matches!(t, Term::SndAt { .. });
                let e = if second {
                    Elim::Snd { ann: None }
                } else {
                    Elim::Fst { ann: None }
                };
                e
            }
            Term::ElimNat { level, motive, base, step, .. } => {
                let e = Elim::ElimNat {
                    level: level.clone(),
                    motive: yclo(env, motive),
                    base: tclo(env, base),
                    step: tclo(env, step),
                };
                e
            }
            Term::ElimEmpty { level, scrut_level, motive, .. } => {
                let e = Elim::ElimEmpty {
                    level: level.clone(),
                    scrut_level: scrut_level.clone(),
                    motive: yclo(env, motive),
                };
                e
            }
            Term::ElimSEmpty { level, scrut_level, motive, .. } => {
                let e = Elim::ElimSEmpty {
                    level: level.clone(),
                    scrut_level: scrut_level.clone(),
                    motive: yclo(env, motive),
                };
                e
            }
            Term::ElimSquash { src_level, dst_level, src_ty, motive, case, .. } => {
                let e = Elim::ElimSquash {
                    src_level: src_level.clone(),
                    dst_level: dst_level.clone(),
                    src_ty: yclo(env, src_ty),
                    motive: yclo(env, motive),
                    case: tclo(env, case),
                };
                e
            }
            Term::Case {
                lhs_level,
                rhs_level,
                motive_level,
                lhs,
                rhs,
                motive,
                case_l,
                case_r,
                ..
            } => {
                let e = Elim::Case {
                    lhs_level: lhs_level.clone(),
                    rhs_level: rhs_level.clone(),
                    motive_level: motive_level.clone(),
                    lhs: yclo(env, lhs),
                    rhs: yclo(env, rhs),
                    motive: yclo(env, motive),
                    case_l: tclo(env, case_l),
                    case_r: tclo(env, case_r),
                };
                e
            }
            Term::ElimW {
                shape_level,
                pos_level,
                motive_level,
                shape,
                pos,
                motive,
                step,
                ..
            } => {
                let e = Elim::ElimW {
                    shape_level: shape_level.clone(),
                    pos_level: pos_level.clone(),
                    motive_level: motive_level.clone(),
                    shape: yclo(env, shape),
                    pos: yclo(env, pos),
                    motive: yclo(env, motive),
                    step: tclo(env, step),
                    env: env.clone(),
                };
                e
            }
            Term::ElimWf { level, motive_level, shape, arity, motive, step, .. } => {
                let e = Elim::ElimWf {
                    level: level.clone(),
                    motive_level: motive_level.clone(),
                    shape: yclo(env, shape),
                    arity: tclo(env, arity),
                    motive: yclo(env, motive),
                    step: tclo(env, step),
                    env: env.clone(),
                };
                e
            }
            Term::ElimIWf { sig, motive_level, motive, step, index, .. } => {
                let e = Elim::ElimIWf {
                    sig: Rc::new(VIWfSig {
                        level: sig.level.clone(),
                        idx_level: sig.idx_level.clone(),
                        idx: yclo(env, &sig.idx),
                        shape: yclo(env, &sig.shape),
                        arity: tclo(env, &sig.arity),
                        out: tclo(env, &sig.out),
                        child: tclo(env, &sig.child),
                    }),
                    motive_level: motive_level.clone(),
                    motive: yclo(env, motive),
                    step: tclo(env, step),
                    index: tclo(env, index),
                    env: env.clone(),
                };
                e
            }
            Term::Out { sig, index, .. } => {
                let e = Elim::Out { sig: vm_sig(self.arena, env, sig), index: tclo(env, index) };
                e
            }
            Term::J { ty_level, motive_level, ty, lhs, motive, case, rhs, .. } => {
                let e = Elim::J {
                    ty_level: ty_level.clone(),
                    motive_level: motive_level.clone(),
                    ty: yclo(env, ty),
                    lhs: tclo(env, lhs),
                    motive: yclo(env, motive),
                    case: tclo(env, case),
                    rhs: tclo(env, rhs),
                };
                e
            }
            Term::LetBoxTy { motive_level, code_level, ctx, motive, body, .. } => {
                let e = Elim::LetBoxTy {
                    motive_level: motive_level.clone(),
                    code_level: code_level.clone(),
                    ctx: amb_ctx(env, ctx),
                    motive: yclo(env, motive),
                    body: under_binder_tm(self.arena, env, body),
                };
                e
            }
            Term::LetBoxTm { motive_level, code_level, ctx, ty, motive, body, .. } => {
                let e = Elim::LetBoxTm {
                    motive_level: motive_level.clone(),
                    code_level: code_level.clone(),
                    ctx: amb_ctx(env, ctx),
                    ty: amb_ty(env, ty),
                    motive: yclo(env, motive),
                    body: under_binder_tm(self.arena, env, body),
                };
                e
            }
            Term::ElimCodeTy {
                ty_motive_level,
                tm_motive_level,
                motives,
                branches,
                code_level,
                ctx,
                ..
            } => {
                let (motives, branches) = amb_tables(env, motives, branches);
                let e = Elim::ElimCodeTy {
                    ty_motive_level: ty_motive_level.clone(),
                    tm_motive_level: tm_motive_level.clone(),
                    motives,
                    branches,
                    code_level: code_level.clone(),
                    ctx: amb_ctx(env, ctx),
                    // Tables, `ctx` and the box the β meets are all ambient,
                    // so the fired branch is too.
                    env: env.with_gshift(0),
                };
                e
            }
            _ => unreachable!("elim_of is given an elimination"),
        }
    }

    /// `elim^Trm`, whose fixed order puts a step before the scrutinee.
    #[inline(never)]
    fn step_elim_code_tm(&mut self, t: &Term, env: &Env<'v>) -> Res<Work<'v>> {
        match t {
            Term::ElimCodeTm {
                ty_motive_level,
                tm_motive_level,
                motives,
                branches,
                code_level,
                ctx,
                ty,
                scrut,
            } => {
                // Fixed order (ch. 06): the type annotation — scoped in Δ,
                // not Γ — reaches WHNF before the scrutinee is touched. It
                // stays syntax, so it is the rewriter that reduces it.
                let ctx = amb_ctx(env, ctx);
                let wty = self.whnf_ty_syntax(&amb_ty(env, ty), &ctx)?;
                let s = self.eval_tm(scrut, env)?;
                let (motives, branches) = amb_tables(env, motives, branches);
                let e = Elim::ElimCodeTm {
                    ty_motive_level: ty_motive_level.clone(),
                    tm_motive_level: tm_motive_level.clone(),
                    motives,
                    branches,
                    code_level: code_level.clone(),
                    ctx,
                    ty: wty,
                    // See `elim^Typ` above.
                    env: env.with_gshift(0),
                };
                return Ok(Work::Elim(s, e));
            }
            _ => unreachable!("step_elim_code_tm is given elim^Trm"),
        }
    }

    /// `u^δ` as a glued neutral: `unfold` is `Some` exactly when `Defs` says
    /// `u` is a definition here, and it evaluates the (already rescoped) body
    /// under δ's **value** environment.
    ///
    /// That environment is δ's payload values alone: `wk^k_g` maps the
    /// abstract prefix of Δ to the abstract prefix of Γ identically, and
    /// `·_{g?}` targets an empty Δ, so past the payloads the lookup falls
    /// through to the same [`Head::BaseVar`] numbering either way.
    /// `u^δ` alone, glued to its body when it has one: what evaluating
    /// `Term::GlobalTm` produces, for a reader that holds the head of a
    /// neutral and wants to apply it to arguments of its own.
    pub fn global(&mut self, var: GlobalVar, subst: VSubst<'v>) -> &'v Val<'v> {
        self.global_tm(var, subst)
    }

    fn global_tm(&mut self, var: GlobalVar, subst: VSubst<'v>) -> &'v Val<'v> {
        // An occurrence whose δ does not fit the definition's context is
        // ill-typed and stays an unglued neutral (`Defs::fits`).
        let body = self.defs.body_unshifted(var).filter(|_| self.defs.fits(var, subst.terms.len())).map(Rc::clone);
        let unfold = body.map(|body| self.glue(var, &subst, body));
        neutral(self.arena, Head::Global { var, subst }, ElimSpine::empty(), unfold)
    }

    /// `body[δ]` for the global `var` as a closure: δ's payload values over
    /// the body's own Ψ-prefix (the `global_tm` convention).
    fn glue(&mut self, var: GlobalVar, subst: &VSubst<'v>, body: Rc<Term>) -> &'v TmClo<'v> {
        let mut denv = Env::at(var.0 + 1);
        for v in &subst.terms {
            denv = denv.push(self.arena, self.vclo(*v));
        }
        self.arena.tm(TmClo::syn(denv, body))
    }

    /// `u a⃗` with `u` a sealed theorem, met by an elimination that unseals
    /// (`Elim::unseals`): the same neutral, now glued to the proof applied to
    /// `a⃗`, so that the elimination about to be pushed extends a pending
    /// unfolding exactly as it would a definition's
    /// (`issues/theorem-witness-unfolding.md`, option D). Until this moment
    /// the neutral carried no unfolding at all, so no comparison could open
    /// the proof of a bare `u a⃗`; and the proof counts as opened only once
    /// the glue is forced ([`ValueArena::mark_sealed`]). `None` when `n` is
    /// not such a neutral.
    #[inline(never)]
    fn unseal(&mut self, n: &VNeutral<'v>) -> Option<&'v VNeutral<'v>> {
        if n.unfold.is_some() {
            return None;
        }
        let Head::Global { var, subst } = &n.head else { return None };
        if !self.defs.is_sealed(*var) || !self.defs.fits(*var, subst.terms.len()) {
            return None;
        }
        let (at, body) = self.defs.sealed_proof_unshifted(*var)?;
        let mut unfold = self.glue(*var, subst, Rc::clone(body));
        // Recorded when forced, not here: an elimination is about to be
        // pushed, but conversion may still decide on the spine.
        self.arena.mark_sealed(unfold, at);
        let mut spine: Vec<&'v Elim<'v>> = n.spine.iter_rev().collect();
        spine.reverse();
        for e in spine {
            unfold = self.arena.tm(TmClo::elim(unfold, e));
        }
        Some(self.arena.neutral(VNeutral { head: n.head.clone(), spine: n.spine, unfold: Some(unfold) }))
    }

    /// `T ⇝* W` on **syntax**, in a local context that is not the ambient
    /// one. The single customer is `elim^Trm`'s type annotation (scoped in
    /// Δ); it is off the hot path and the design keeps Δ syntactic (§3.4).
    fn whnf_ty_syntax(&mut self, t: &Rc<Type>, gamma: &LocalCtx) -> Res<Rc<Type>> {
        let mut cur = Rc::clone(t);
        while let Some(next) = step_type_delta(&cur, gamma, self.defs)? {
            self.spend()?;
            cur = Rc::new(next);
        }
        Ok(cur)
    }

    // -- elimination --------------------------------------------------------

    /// Apply one elimination to a weak head value: fire its β, or extend the
    /// neutral's spine (and, when the neutral is glued, its unfolding).
    pub fn elim(&mut self, head: &'v Val<'v>, e: Elim<'v>) -> Res<&'v Val<'v>> {
        self.drive(Work::Elim(head, e))
    }

    /// One step of [`Eval::elim`]; see [`Eval::drive`].
    ///
    /// A dispatcher, and deliberately nothing more: the arms that can
    /// re-enter the machine natively (a fold classified, a counter forced,
    /// an ih applied) each have a function of their own, and the β arms
    /// that never re-enter share [`Eval::step_fire`]. What stands on the
    /// native stack during a re-entry is then this frame and the one arm's,
    /// never the union of every arm's locals (design §8).
    #[inline(never)]
    fn step_elim(&mut self, head: &'v Val<'v>, e: Elim<'v>) -> Res<Work<'v>> {
        match (&*head, &e) {
            (Val::Neutral(_), _) => self.step_neutral(head, e),
            // A width fold waiting for the arguments its class fires at
            // (`docs/native-bitvector-values-design.md` §4).
            (Val::BitFold { .. }, Elim::App { .. }) => self.bit_fold_app(&head, e),
            (Val::NatSync { .. }, Elim::App { .. }) => self.fire_nat_sync(head, e),
            (Val::NatRun { .. }, Elim::ElimNat { .. }) => self.fire_nat_run(head, e),
            (Val::WfIh { elim, label, children }, Elim::App { .. }) => {
                let (elim, label, children) = (*elim, *label, *children);
                self.wf_ih_apply(&head, &elim, label, children, e)
            }
            (Val::WIh { elim, label, children }, Elim::App { .. }) => {
                let (elim, label, children) = (*elim, *label, *children);
                self.w_ih_apply(&head, &elim, label, children, e)
            }
            (Val::IWfIh { elim, label, children }, Elim::App { .. }) => {
                let (elim, label, children) = (*elim, *label, *children);
                self.iwf_ih_apply(&head, &elim, label, children, e)
            }
            _ => self.step_fire(head, e),
        }
    }

    /// [`Eval::step_elim`] at a neutral head: unfold a glued scrutinee the
    /// fold machinery or a transparent request wants, or extend the spine.
    #[inline(never)]
    fn step_neutral(&mut self, head: &'v Val<'v>, e: Elim<'v>) -> Res<Work<'v>> {
        let Val::Neutral(n) = &*head else { unreachable!("step_neutral is given a neutral") };
        let unsealed = if e.unseals() { self.unseal(n) } else { None };
        let n = unsealed.as_ref().unwrap_or(n);
        // A Nat fold the run machinery accelerates — one whose step
        // classifies as an affine or synchronous algebra (`probe.rs`,
        // memoized per closure) — whose scrutinee
        // is a *glued* definition unfolds that scrutinee here rather
        // than stalling as a spine for conversion to δ-step from the
        // outside one definition at a time (each such step replays the
        // whole pending spine, so a chain of `p + p` doublings under a
        // literal consumer was cubic in the chain). Only these folds do
        // so: their scrutinee is closed arithmetic whenever the fold
        // can fire at all, and an open one stops at its variable. A
        // general match or recursor must NOT: the x86 decoder's
        // open-argument unfolding theorems meet at a *folded* scrutinee
        // (`match decode_opcode_direct(…)` on both sides), and unfolding
        // it eagerly exhausts fuel on the dispatch it hides.
        // Only the `Nat` classes ask this: their scrutinee is closed
        // arithmetic whenever the fold can fire at all. A width fold's
        // scrutinee is the *width*, which reaches the eliminator as a
        // literal; probing every glued-scrutinee fold for a transducer
        // costs a motive walk per occurrence and buys nothing.
        if let (Some(unfold), Elim::ElimNat { step, .. }) = (n.unfold, &e) {
            if matches!(&*self.classify_step(step)?, FoldClass::Affine { .. } | FoldClass::Sync { .. }) {
                self.spend()?;
                self.frames.push(Frame::Owned(e));
                return Ok(Work::Force(unfold));
            }
        }
        // Under a δ-transparent request (`Eval::delta_whnf`) every
        // eliminator that would be stuck on a glued scrutinee unfolds
        // it instead. Applications are not stuck — they extend the
        // spine, keeping the glued `f a⃗` shape — and the transparent
        // loop unfolds that spine's head next if it has to.
        if self.transparent && !e.is_application() {
            if let Some(unfold) = n.unfold {
                self.spend()?;
                self.frames.push(Frame::Owned(e));
                return Ok(Work::Force(unfold));
            }
        }
        let n = *n;
        let applies = matches!(e, Elim::App { .. });
        let v = self.push_elim(n, e);
        // A call of a withheld definition that this application saturates at
        // closed arguments is glued here, and computes from now on
        // (`eval/withheld.rs`).
        if applies && matches!(&n.head, Head::Global { var, .. } if self.defs.withheld(*var).is_some()) {
            if let Val::Neutral(m) = v {
                if let Some(glued) = self.glue_withheld(m) {
                    return Ok(Work::Val(glued));
                }
            }
        }
        Ok(Work::Val(v))
    }

    /// [`Eval::step_elim`] at a canonical head whose β does not re-enter
    /// the machine: fire it, or be stuck.
    #[inline(never)]
    fn step_fire(&mut self, head: &'v Val<'v>, e: Elim<'v>) -> Res<Work<'v>> {
        match (&*head, &e) {
            (Val::Lam { body, .. }, Elim::App { arg, .. }) => {
                self.spend()?;
                let (body, arg) = (*body, *arg);
                Ok(Work::Apply1(body, arg))
            }
            (Val::ULam { num_vars, body, .. }, Elim::UApp { levels })
                if *num_vars as usize == levels.len() =>
            {
                let body = *body;
                // The written vectors pair positionally (outermost first);
                // instantiation wants innermost-first.
                let phi: Vec<Level> = levels.iter().rev().cloned().collect();
                self.fire_instantiate(&head, &e, body, Instantiate::Univ(phi))
            }
            (Val::CtxLam { body, .. }, Elim::CtxApp { ctx }) => {
                let (body, entry) = (*body, GlobalEntry::Ctx(ctx.clone()));
                self.fire_instantiate(&head, &e, body, Instantiate::Global(entry))
            }
            (Val::TyLam { body, .. }, Elim::TyApp { arg }) => {
                let (body, entry) = (*body, GlobalEntry::Ty(Rc::clone(arg)));
                self.fire_instantiate(&head, &e, body, Instantiate::Global(entry))
            }
            (Val::Zero, Elim::ElimNat { base, .. }) => {
                self.spend()?;
                let base = *base;
                Ok(Work::Force(base))
            }
            // `elim_Nat … (su t) ⇝ s'[t/x, elim_Nat … t/y]`: the induction
            // hypothesis is a *pending* elimination, so a step that ignores
            // it costs nothing.
            (Val::Succ(pred), Elim::ElimNat { step, .. }) => {
                self.spend()?;
                let (pred, step) = (*pred, *step);
                let ih = self.arena.tm(TmClo::elim(pred, self.arena.elim_cell(e.clone())));
                Ok(Work::Apply(step, vec![pred, ih]))
            }
            (Val::Refl { .. }, Elim::J { case, .. }) => {
                self.spend()?;
                let case = *case;
                Ok(Work::Force(case))
            }
            (Val::Squash { tm, .. }, Elim::ElimSquash { case, .. }) => {
                self.spend()?;
                Ok(Work::Apply1(*case, *tm))
            }
            // A run's one-step view is the Σ-chain it stands for
            // (`docs/native-bitvector-values-design.md` §3.3): unpack its
            // first bit, with the annotations `Eval::vec_ty` gives that Σ,
            // and let the ordinary pair arms fire on it. Costing one step
            // per projection is what keeps `Fst`/`Snd` on a word O(1).
            (
                Val::BitRun { level, ty, width, bits, tail_len, tail },
                Elim::Fst { .. } | Elim::Snd { .. },
            ) => {
                let pair = Val::bit_run_unpack(
                    self.arena, level, ty, *width, *bits, tail_len, tail,
                );
                Ok(Work::Elim(self.arena.val(pair), e.clone()))
            }
            (Val::Pair { fst, .. }, Elim::Fst { .. }) => {
                self.spend()?;
                let fst = *fst;
                Ok(Work::Force(fst))
            }
            (Val::Pair { snd, .. }, Elim::Snd { .. }) => {
                self.spend()?;
                let snd = *snd;
                Ok(Work::Force(snd))
            }
            (Val::Inl { val, .. }, Elim::Case { case_l, .. }) => {
                self.spend()?;
                let (val, case_l) = (*val, *case_l);
                Ok(Work::Apply1(case_l, val))
            }
            (Val::Inr { val, .. }, Elim::Case { case_r, .. }) => {
                self.spend()?;
                let (val, case_r) = (*val, *case_r);
                Ok(Work::Apply1(case_r, val))
            }
            (Val::Sup { label, children, .. }, Elim::ElimW { .. }) => {
                self.spend()?;
                let (label, children) = (*label, *children);
                match self.fire_elim_w(label, children, &e)? {
                    Some(v) => Ok(v),
                    None => Ok(Work::Val(stuck(self.arena, &head, &e))),
                }
            }
            (Val::Supf { label, children, .. }, Elim::ElimWf { .. }) => {
                self.spend()?;
                let (label, children) = (*label, *children);
                match self.fire_elim_wf(label, children, &e)? {
                    Some(v) => Ok(v),
                    None => Ok(Work::Val(stuck(self.arena, &head, &e))),
                }
            }
            // At any index: β does not look at the index (design §4).
            (Val::Supi { label, children, .. }, Elim::ElimIWf { .. }) => {
                self.spend()?;
                let (label, children) = (*label, *children);
                match self.fire_elim_iwf(label, children, &e)? {
                    Some(v) => Ok(v),
                    None => Ok(Work::Val(stuck(self.arena, &head, &e))),
                }
            }
            // One step, only under `out` (docs/kernel-coinduction-design.md §1.4).
            (Val::Corec { sig, coalg, index, seed }, Elim::Out { .. }) => {
                self.spend()?;
                match self.fire_out(sig, coalg, index, seed) {
                    Some(w) => Ok(w),
                    None => Ok(Work::Val(stuck(self.arena, &head, &e))),
                }
            }
            (Val::BoxTy(code), Elim::LetBoxTy { body, .. }) => {
                let (body, entry) = (*body, GlobalEntry::Ty(Rc::clone(code)));
                self.fire_instantiate(&head, &e, body, Instantiate::Global(entry))
            }
            (Val::BoxTm(code), Elim::LetBoxTm { body, .. }) => {
                let (body, entry) = (*body, GlobalEntry::Tm(Rc::clone(code)));
                self.fire_instantiate(&head, &e, body, Instantiate::Global(entry))
            }
            // `box (U^δ)` blocks the recursor: canonical, but neutral as a
            // whole (ch. 06), which is why the box becomes the head.
            (Val::BoxTy(code), Elim::ElimCodeTy { .. }) => {
                if matches!(&**code, Type::GlobalTy { .. }) {
                    return Ok(Work::Val(neutral(
                        self.arena,
                        Head::BoxedGlobalTy(Rc::clone(code)),
                        self.arena.elim(ElimSpine::empty(), e.clone()),
                        None,
                    )));
                }
                let code = Rc::clone(code);
                match self.fire_code_ty(&code, &e)? {
                    Some(v) => Ok(v),
                    None => Ok(Work::Val(stuck(self.arena, &head, &e))),
                }
            }
            (Val::BoxTm(code), Elim::ElimCodeTm { .. }) => {
                if matches!(&**code, Term::GlobalTm { .. }) {
                    return Ok(Work::Val(neutral(
                        self.arena,
                        Head::BoxedGlobalTm(Rc::clone(code)),
                        self.arena.elim(ElimSpine::empty(), e.clone()),
                        None,
                    )));
                }
                let code = Rc::clone(code);
                match self.fire_code_tm(&code, &e)? {
                    Some(v) => Ok(v),
                    None => Ok(Work::Val(stuck(self.arena, &head, &e))),
                }
            }
            _ => Ok(Work::Val(stuck(self.arena, &head, &e))),
        }
    }

    /// A Nat fold over a run: iterated by its algebra's class when it has
    /// one (`eval/runs.rs`), otherwise one successor step.
    #[inline(never)]
    fn fire_nat_run(&mut self, head: &'v Val<'v>, e: Elim<'v>) -> Res<Work<'v>> {
        let (Val::NatRun { program, tail }, Elim::ElimNat { .. }) = (&*head, &e) else {
            unreachable!("fire_nat_run is given a Nat fold over a run")
        };
        self.spend()?;
        self.fold_run(&head, program, tail, &e)
    }

    /// One successor step of a Nat fold over a run: the step applied to the
    /// run's predecessor and the pending fold over it.
    #[inline(never)]
    fn nat_run_step(
        &mut self,
        program: &Rc<ContextProgram<()>>,
        tail: &'v TmClo<'v>,
        step: &'v TmClo<'v>,
        e: &Elim<'v>,
    ) -> Work<'v> {
        let pred = Val::nat_run_pred(self.arena, program, tail);
        let ih = self.arena.tm(TmClo::elim(pred, self.arena.elim_cell(e.clone())));
        Work::Apply(step, vec![pred, ih])
    }

    /// The β of a binder over a universe, a context, a type or a box: the
    /// body instantiated, then evaluated. Out of line because the
    /// substitution's temporaries are the largest locals of the β arms
    /// (docs/native-depth-budget-design.md §8).
    #[inline(never)]
    fn fire_instantiate(
        &mut self,
        head: &'v Val<'v>,
        e: &Elim<'v>,
        body: &'v TmClo<'v>,
        by: Instantiate,
    ) -> Res<Work<'v>> {
        self.spend()?;
        let Some((benv, bbody)) = body.as_syn() else { return Ok(Work::Val(stuck(self.arena, head, e))) };
        let inst = match by {
            Instantiate::Univ(phi) => bbody.inst_univ(&phi),
            Instantiate::Global(entry) => bbody.apply_global(&GlobalSubst::single(entry)),
        };
        Ok(Work::Eval(Rc::new(inst), benv.clone()))
    }

    /// A synchronous fold applied to its right-hand counter
    /// (`Frame::SyncArg`): cancel the matching prefix of two runs, or
    /// expose one outer successor step.
    #[inline(never)]
    fn fire_nat_sync(&mut self, head: &'v Val<'v>, e: Elim<'v>) -> Res<Work<'v>> {
        let (Val::NatSync { program, tail, elim }, Elim::App { ann, arg }) = (&*head, &e) else {
            unreachable!("fire_nat_sync is given a synchronous fold's application")
        };
        let right = self.force(arg)?;
        if let Val::Neutral(rn) = &*right {
            if let Some(unfold) = rn.unfold {
                // The counter on the right is a glued definition
                // (`sub(x, p)` feeding the next comparison): unfold
                // it and retry, for the reason given at the neutral
                // scrutinee case above.
                self.spend()?;
                self.frames.push(Frame::SyncArg {
                    head: head,
                    app: self.arena.elim_cell(e.clone()),
                });
                return Ok(Work::Force(unfold));
            }
        }
        if let Val::NatRun { program: right_program, tail: right_tail } = &*right {
            let cancelled = ContextProgram::cancel_matching_prefix(
                Rc::clone(program),
                Rc::clone(right_program),
                self.fuel.saturating_sub(1),
            )
            .map_err(|_| {
                self.fuel = 0;
                OutOfFuel
            })?;
            self.fuel -= cancelled.inspected;
            if cancelled.changed {
                self.spend()?;
                // `inc` successors per cancelled pair (`max`):
                // the successor algebra iterated over the cancelled
                // prefix, wrapped around the residual fold.
                let Elim::ElimNat { step, .. } = &**elim else {
                    unreachable!("NatSync stores a Nat eliminator")
                };
                if let FoldClass::Sync { inc: Some(inc) } = &*self.classify_step(step)? {
                    let prefix = cancelled.cancelled.as_ref().expect("changed cancels");
                    let by = AffineTree::Leaf { inc: Some(Rc::clone(inc)), path: Vec::new() };
                    let Some(AffineTree::Leaf { inc: Some(total), .. }) = by.iterate(prefix)
                    else {
                        unreachable!("a successor leaf iterates to one")
                    };
                    self.frames.push(Frame::NatRunTail { program: total, glued: None });
                }
                let left = self.nat_residual(cancelled.left, tail);
                let right = self.nat_residual(cancelled.right, right_tail);
                let folded = self.arena.tm(TmClo::elim(left, *elim));
                let app = Elim::App { ann: ann.clone(), arg: right };
                self.frames.push(Frame::Owned(app));
                return Ok(Work::Force(folded));
            }
        }

        // The right-hand head is not a matching run. Expose exactly
        // the ordinary outer successor step and retry the application
        // on its result; no semantic case is guessed here.
        let pred = Val::nat_run_pred(self.arena, program, tail);
        let ih = self.arena.tm(TmClo::elim(pred, *elim));
        let Elim::ElimNat { step, .. } = &**elim else {
            unreachable!("NatSync stores a Nat eliminator")
        };
        self.frames.push(Frame::Owned(e));
        self.spend()?;
        Ok(Work::Apply(*step, vec![pred, ih]))
    }

    /// Extend a neutral's spine — and, when it is glued, its pending
    /// unfolding by the same elimination, so that forcing the unfolding
    /// replays the spine (design §5).
    #[inline(never)]
    fn push_elim(&mut self, n: &'v VNeutral<'v>, e: Elim<'v>) -> &'v Val<'v> {
        // The unfolding's elimination is the spine node's own: one cell,
        // where the glue used to copy the elimination into a second.
        let spine = self.arena.elim(n.spine, e);
        let unfold = match (n.unfold, spine.last()) {
            (Some(u), Some(e)) => Some(self.arena.tm(TmClo::elim(u, e))),
            _ => None,
        };
        neutral(self.arena, n.head.clone(), spine, unfold)
    }

    /// `elim_W (sup(…; a; f)) ⇝ s[a/a, f/f, (λ y. elim_W …(f y))/ih]`,
    /// with the ih held as [`Val::WIh`] rather than built as that λ's
    /// syntax. The syntax guards are [`w_ih_lam`](Eval::w_ih_lam)'s, kept
    /// here so the β fires exactly when it did while the λ was eager.
    #[inline(never)]
    fn fire_elim_w(
        &mut self,
        label: &'v TmClo<'v>,
        children: &'v TmClo<'v>,
        e: &Elim<'v>,
    ) -> Res<Option<Work<'v>>> {
        let Elim::ElimW { shape, pos, motive, step, .. } = e else {
            return Ok(None);
        };
        if step.as_syn().is_none()
            || shape.as_syn().is_none()
            || pos.as_syn().is_none()
            || motive.as_syn().is_none()
        {
            return Ok(None);
        }
        let ih = self.arena.val(Val::WIh { elim: self.arena.elim_cell(e.clone()), label, children });
        let step = *step;
        Ok(Some(Work::Apply(
            step,
            vec![label, children, self.vclo(ih)],
        )))
    }

    /// The λ a [`Val::WIh`] stands for, built as syntax: an ordinary
    /// syntactic closure over the environment `ρ, a, f`. The recursive
    /// eliminator is *exactly* `reduce.rs`'s term with `a` and `f` named by
    /// de Bruijn slots instead of substituted, which is why its adequacy is
    /// by inspection. The whole-node `shift_local(3)` is `reduce.rs`'s
    /// `shift_local(1)` widened by the two extra slots, and it descends the
    /// annotations' own binders for the same reason. Only the fallback of
    /// [`w_ih_apply`](Eval::w_ih_apply) and the readers that inspect a
    /// function without applying it pay for this.
    pub fn w_ih_lam(
        arena: &'v ValueArena<'v>,
        label: &'v TmClo<'v>,
        children: &'v TmClo<'v>,
        e: &Elim<'v>,
    ) -> Option<&'v Val<'v>> {
        let Elim::ElimW {
            shape_level,
            pos_level,
            motive_level,
            shape,
            pos,
            motive,
            step,
            env,
        } = e
        else {
            return None;
        };
        let (_, step_body) = step.as_syn()?;
        let (_, shape_body) = shape.as_syn()?;
        let (_, pos_body) = pos.as_syn()?;
        let (_, motive_body) = motive.as_syn()?;
        let rho_af = env.push(arena, label).push(arena, children);
        let syntax = arena.w_ih_syntax(
            [shape_level, pos_level, motive_level],
            (shape_body, pos_body, motive_body, step_body),
            || {
                let lmax = Level::max(shape_level.clone(), pos_level.clone());
                let w_syn = Type::W {
                    shape_level: shape_level.clone(),
                    pos_level: pos_level.clone(),
                    shape: Rc::clone(shape_body),
                    pos: Rc::clone(pos_body),
                };
                let template = Term::ElimW {
                    shape_level: shape_level.clone(),
                    pos_level: pos_level.clone(),
                    motive_level: motive_level.clone(),
                    shape: Rc::clone(shape_body),
                    pos: Rc::clone(pos_body),
                    motive: Rc::clone(motive_body),
                    step: Rc::clone(step_body),
                    scrut: Rc::new(Term::Zero),
                }
                .shift_local(3);
                let Term::ElimW { shape: s3, pos: p3, motive: m3, step: st3, .. } = template else {
                    unreachable!("shifting an elim_W yields an elim_W")
                };
                // `f y` in `(Γ, a, f, y)`: `f` is slot 1, `y` slot 0, and the App's
                // codomain annotation binds one more.
                let f_y = Term::App {
                    fun: Rc::new(Term::Var(LocalVar(1))),
                    dom_level: pos_level.clone(),
                    cod_level: lmax.clone(),
                    dom: Rc::new(pos_body.shift_local(2)),
                    cod: Rc::new(w_syn.shift_local(4)),
                    arg: Rc::new(Term::Var(LocalVar(0))),
                };
                let rec = Term::ElimW {
                    shape_level: shape_level.clone(),
                    pos_level: pos_level.clone(),
                    motive_level: motive_level.clone(),
                    shape: s3,
                    pos: p3,
                    motive: m3,
                    step: st3,
                    scrut: Rc::new(f_y),
                };
                WIhSyntax {
                    levels: [shape_level.clone(), pos_level.clone(), motive_level.clone()],
                    _keep: (
                        Rc::clone(shape_body),
                        Rc::clone(pos_body),
                        Rc::clone(motive_body),
                        Rc::clone(step_body),
                    ),
                    rec: Rc::new(rec),
                    // `T[a/x]` in `(Γ, a, f)`: `a` is slot 1.
                    dom: Rc::new(pos_body.shift_local(1)),
                }
            },
        );
        Some(arena.val(Val::Lam {
            dom_level: pos_level.clone(),
            cod_level: motive_level.clone(),
            dom: arena.ty(TyClo::new(rho_af, Rc::clone(&syntax.dom))),
            body: arena.tm(TmClo::syn(rho_af, Rc::clone(&syntax.rec))),
        }))
    }

    /// `ih y` for a [`Val::WIh`]: when `f` is a λ, `f y` is its β and the
    /// eliminator fires on that, the λ's body without its syntax, charged the
    /// two β the λ's application and its body's `f y` charged. Over any other
    /// `f` it applies the λ itself.
    #[inline(never)]
    fn w_ih_apply(
        &mut self,
        head: &'v Val<'v>,
        elim: &'v Elim<'v>,
        label: &'v TmClo<'v>,
        children: &'v TmClo<'v>,
        e: Elim<'v>,
    ) -> Res<Work<'v>> {
        let Elim::App { arg, .. } = &e else {
            return Ok(Work::Val(stuck(self.arena, head, &e)));
        };
        let arg = *arg;
        if let Val::Lam { body, .. } = &*self.force(children)? {
            let body = *body;
            self.spend()?;
            self.spend()?;
            self.frames.push(Frame::Elim(elim));
            return Ok(Work::Apply1(body, arg));
        }
        match Eval::w_ih_lam(self.arena, label, children, elim).as_deref() {
            Some(Val::Lam { body, .. }) => {
                self.spend()?;
                Ok(Work::Apply1(*body, arg))
            }
            _ => Ok(Work::Val(stuck(self.arena, head, &e))),
        }
    }

    /// `elim_Wf (sup_f(…; a; cs)) ⇝ s[a, cs, λ i. elim_Wf(…; nth … cs i)]`,
    /// with the ih held as [`Val::WfIh`] rather than built as that λ's
    /// syntax. The syntax guards are [`wf_ih_lam`](Eval::wf_ih_lam)'s, kept
    /// here so the β fires exactly when it did while the λ was eager.
    #[inline(never)]
    fn fire_elim_wf(
        &mut self,
        label: &'v TmClo<'v>,
        children: &'v TmClo<'v>,
        e: &Elim<'v>,
    ) -> Res<Option<Work<'v>>> {
        let Elim::ElimWf { shape, arity, motive, step, .. } = e else {
            return Ok(None);
        };
        if step.as_syn().is_none()
            || arity.as_syn().is_none()
            || shape.as_syn().is_none()
            || motive.as_syn().is_none()
        {
            return Ok(None);
        }
        let ih = self.arena.val(Val::WfIh { elim: self.arena.elim_cell(e.clone()), label, children });
        let step = *step;
        Ok(Some(Work::Apply(
            step,
            vec![label, children, self.vclo(ih)],
        )))
    }

    /// The λ a [`Val::WfIh`] stands for, built as syntax:
    /// [`fire_elim_w`](Eval::fire_elim_w)'s construction, with the child
    /// reached through the shared [`nth`] schema instead of an application.
    /// Only the fallback of [`wf_ih_apply`](Eval::wf_ih_apply) and the
    /// readers that inspect a function without applying it pay for this.
    fn wf_ih_lam(
        &mut self,
        label: &'v TmClo<'v>,
        children: &'v TmClo<'v>,
        e: &Elim<'v>,
    ) -> Option<&'v Val<'v>> {
        let Elim::ElimWf { level, motive_level, shape, arity, motive, step, env } = e else {
            return None;
        };
        let (_, step_body) = step.as_syn()?;
        let (_, arity_body) = arity.as_syn()?;
        let (_, shape_body) = shape.as_syn()?;
        let (_, motive_body) = motive.as_syn()?;
        let rho_acs = env.push(self.arena, label).push(self.arena, children);
        let wf_syn = Type::Wf {
            level: level.clone(),
            shape: Rc::clone(shape_body),
            arity: Rc::clone(arity_body),
        };
        let template = Term::ElimWf {
            level: level.clone(),
            motive_level: motive_level.clone(),
            shape: Rc::clone(shape_body),
            arity: Rc::clone(arity_body),
            motive: Rc::clone(motive_body),
            step: Rc::clone(step_body),
            scrut: Rc::new(Term::Zero),
        }
        .shift_local(3);
        let Term::ElimWf { shape: s3, arity: n3, motive: m3, step: st3, .. } = template else {
            unreachable!("shifting an elim_Wf yields an elim_Wf")
        };
        // `nth(Wf; n[a/x]; cs; i)` in `(Γ, a, cs, i)`: `a` is slot 2, so the
        // arity's own binder lands on it under a shift of 2.
        let child = nth(
            level,
            &Rc::new(wf_syn.shift_local(3)),
            &Rc::new(arity_body.shift_local(2)),
            Rc::new(Term::Var(LocalVar(1))),
            Rc::new(Term::Var(LocalVar(0))),
        );
        let rec = Term::ElimWf {
            level: level.clone(),
            motive_level: motive_level.clone(),
            shape: s3,
            arity: n3,
            motive: m3,
            step: st3,
            scrut: Rc::new(child),
        };
        Some(self.arena.val(Val::Lam {
            dom_level: Level::Zero,
            cod_level: motive_level.clone(),
            dom: self.arena.ty(TyClo::new(
                rho_acs,
                Rc::new(Type::Fin { len: Rc::new(arity_body.shift_local(1)) }),
            )),
            body: self.arena.tm(TmClo::syn(rho_acs, Rc::new(rec))),
        }))
    }

    /// `elim_IWf(…; m; sup_i(…; a; cs)) ⇝ s[a, cs, iwfIH a cs]`, at any
    /// index (docs/iwf-former-design.md §4), with the ih held as
    /// [`Val::IWfIh`] rather than built as that λ's syntax. The syntax
    /// guards are [`iwf_ih_lam`](Eval::iwf_ih_lam)'s, kept here so the β
    /// fires exactly when it did while the λ was eager.
    #[inline(never)]
    fn fire_elim_iwf(
        &mut self,
        label: &'v TmClo<'v>,
        children: &'v TmClo<'v>,
        e: &Elim<'v>,
    ) -> Res<Option<Work<'v>>> {
        let Elim::ElimIWf { sig, motive, step, .. } = e else {
            return Ok(None);
        };
        let VIWfSig { idx, shape, arity, out, child, .. } = &**sig;
        if idx.as_syn().is_none()
            || shape.as_syn().is_none()
            || arity.as_syn().is_none()
            || out.as_syn().is_none()
            || child.as_syn().is_none()
            || motive.as_syn().is_none()
            || step.as_syn().is_none()
        {
            return Ok(None);
        }
        let ih = self.arena.val(Val::IWfIh { elim: self.arena.elim_cell(e.clone()), label, children });
        let step = *step;
        Ok(Some(Work::Apply(step, vec![label, children, self.vclo(ih)])))
    }

    /// The λ a [`Val::IWfIh`] stands for: `reduce.rs`'s ih, from the one
    /// schema [`iwf_ih`], built as syntax in `(Γ, a, cs)` — the annotations
    /// weakened past the two slots, `a` and `cs` named by them — and closed
    /// over the environment `ρ, a, cs`, as [`Eval::w_ih_lam`] builds
    /// `elim_W`'s. Only the fallback of [`iwf_ih_apply`](Eval::iwf_ih_apply)
    /// and the readers that inspect a function without applying it pay for
    /// this.
    fn iwf_ih_lam(
        &self,
        label: &'v TmClo<'v>,
        children: &'v TmClo<'v>,
        e: &Elim<'v>,
    ) -> Option<&'v Val<'v>> {
        let Elim::ElimIWf { sig, motive_level, motive, step, env, .. } = e else {
            return None;
        };
        let VIWfSig { level, idx_level, idx, shape, arity, out, child } = &**sig;
        let (_, idx_b) = idx.as_syn()?;
        let (_, shape_b) = shape.as_syn()?;
        let (_, arity_b) = arity.as_syn()?;
        let (_, out_b) = out.as_syn()?;
        let (_, child_b) = child.as_syn()?;
        let (_, motive_b) = motive.as_syn()?;
        let (_, step_b) = step.as_syn()?;
        let sig = Rc::new(IWfSig {
            level: level.clone(),
            idx_level: idx_level.clone(),
            idx: Rc::clone(idx_b),
            shape: Rc::clone(shape_b),
            arity: Rc::clone(arity_b),
            out: Rc::clone(out_b),
            child: Rc::clone(child_b),
        })
        .shift_local(2);
        let ih = iwf_ih(
            &sig,
            motive_level,
            &Rc::new(motive_b.shift_local_above(2, 2)),
            &Rc::new(step_b.shift_local_above(2, 3)),
            &Term::Var(LocalVar(1)),
            &Term::Var(LocalVar(0)),
        );
        let Term::Lam { dom_level, cod_level, dom, body } = ih else {
            unreachable!("iwf_ih builds a λ")
        };
        let rho_acs = env.push(self.arena, label).push(self.arena, children);
        Some(self.arena.val(Val::Lam {
            dom_level,
            cod_level,
            dom: self.arena.ty(TyClo::new(rho_acs, dom)),
            body: self.arena.tm(TmClo::syn(rho_acs, body)),
        }))
    }

    /// `ih i` for a [`Val::IWfIh`]: over a canonical index and a canonical
    /// tuple, `dnth(…; cs; i)` is a component, and the eliminator fires on it
    /// at the child's index `c[a, i]` — the λ's body, without its syntax. Over
    /// anything else it applies the λ itself.
    #[inline(never)]
    fn iwf_ih_apply(
        &mut self,
        head: &'v Val<'v>,
        elim: &'v Elim<'v>,
        label: &'v TmClo<'v>,
        children: &'v TmClo<'v>,
        e: Elim<'v>,
    ) -> Res<Work<'v>> {
        let Elim::App { arg, .. } = &e else {
            return Ok(Work::Val(stuck(self.arena, head, &e)));
        };
        let arg = *arg;
        let mut cs = self.force(children)?;
        let mut i = self.force(arg)?;
        loop {
            let Val::Pair { fst, snd, .. } = &*cs else { break };
            let (fst, snd) = (*fst, *snd);
            match &*i {
                Val::Inl { .. } => {
                    let Some(rec) = self.iwf_reindexed(elim, label, arg) else { break };
                    self.spend()?;
                    self.frames.push(Frame::Elim(rec));
                    return Ok(Work::Force(fst));
                }
                Val::Inr { val, .. } => {
                    let val = *val;
                    self.spend()?;
                    cs = self.force(snd)?;
                    i = self.force(val)?;
                }
                _ => break,
            }
        }
        match self.iwf_ih_lam(label, children, elim).as_deref() {
            Some(Val::Lam { body, .. }) => {
                self.spend()?;
                Ok(Work::Apply1(*body, arg))
            }
            _ => Ok(Work::Val(stuck(self.arena, head, &e))),
        }
    }

    /// `elim` at the child index `c[a, i]`: the signature's `child` closure
    /// opened at the label and the position, everything else `elim`'s own.
    fn iwf_reindexed(
        &self,
        elim: &Elim<'v>,
        label: &'v TmClo<'v>,
        position: &'v TmClo<'v>,
    ) -> Option<&'v Elim<'v>> {
        let Elim::ElimIWf { sig, motive_level, motive, step, env, .. } = elim else {
            return None;
        };
        let (rho, child) = sig.child.as_syn()?;
        let rho = rho.push(self.arena, label).push(self.arena, position);
        Some(self.arena.elim_cell(Elim::ElimIWf {
            sig: Rc::clone(sig),
            motive_level: motive_level.clone(),
            motive,
            step,
            index: self.arena.tm(TmClo::syn(rho, Rc::clone(child))),
            env: env.clone(),
        }))
    }

    /// `out(corec^{k}(…; X; c; j; x)) ⇝ m_out_corec(…)`
    /// (docs/kernel-coinduction-design.md §1.4). The reduct is `reduce.rs`'s,
    /// from the one schema [`m_out_corec`]: built as syntax in `(Γ, j, x)` —
    /// the signature and the coalgebra weakened past the two slots, `j` and
    /// `x` named by them — and evaluated in the coalgebra's environment
    /// extended by the index and the seed, so `c[j, x]` is one closure that
    /// both projections share. `None` when a closure is not syntax.
    #[inline(never)]
    fn fire_out(
        &mut self,
        sig: &VMSig<'v>,
        coalg: &VCorec<'v>,
        index: &'v TmClo<'v>,
        seed: &'v TmClo<'v>,
    ) -> Option<Work<'v>> {
        let VMSig { level, pos_level, idx_level, idx, shape, pos, next } = sig;
        let (_, idx_b) = idx.as_syn()?;
        let (_, shape_b) = shape.as_syn()?;
        let (_, pos_b) = pos.as_syn()?;
        let (_, next_b) = next.as_syn()?;
        let (_, carrier_b) = coalg.carrier.as_syn()?;
        let (_, step_b) = coalg.step.as_syn()?;
        let sig = Rc::new(MSig {
            level: level.clone(),
            pos_level: pos_level.clone(),
            idx_level: idx_level.clone(),
            idx: Rc::clone(idx_b),
            shape: Rc::clone(shape_b),
            pos: Rc::clone(pos_b),
            next: Rc::clone(next_b),
        })
        .shift_local(2);
        let reduct = m_out_corec(
            &sig,
            &coalg.carrier_level,
            &Rc::new(carrier_b.shift_local_above(2, 1)),
            &Rc::new(step_b.shift_local_above(2, 2)),
            &Term::Var(LocalVar(1)),
            &Term::Var(LocalVar(0)),
        );
        let rho = coalg.env.push(self.arena, index).push(self.arena, seed);
        Some(Work::Eval(Rc::new(reduct), rho))
    }

    /// `ih i` for a [`Val::WfIh`]: when the index is a canonical `Fin` value
    /// and the tuple a canonical chain of pairs, `nth` is the projections it
    /// reduces to (`inl _` is the head, `inr j` the `j`th of the tail), and
    /// the eliminator fires on that child, the λ's body without its syntax.
    /// Anything else — a neutral index, a stuck or glued tuple — applies the
    /// λ itself, so what `nth` does there (project a neutral tuple, stall on
    /// a neutral index) is exactly what it did. One unit of fuel per
    /// projection, never more than the `nth` reduction charged.
    #[inline(never)]
    fn wf_ih_apply(
        &mut self,
        head: &'v Val<'v>,
        elim: &'v Elim<'v>,
        label: &'v TmClo<'v>,
        children: &'v TmClo<'v>,
        e: Elim<'v>,
    ) -> Res<Work<'v>> {
        let Elim::App { arg, .. } = &e else {
            return Ok(Work::Val(stuck(self.arena, head, &e)));
        };
        let arg = *arg;
        let mut cs = self.force(children)?;
        let mut i = self.force(arg)?;
        loop {
            let Val::Pair { fst, snd, .. } = &*cs else { break };
            let (fst, snd) = (*fst, *snd);
            match &*i {
                Val::Inl { .. } => {
                    self.spend()?;
                    self.frames.push(Frame::Elim(elim));
                    return Ok(Work::Force(fst));
                }
                Val::Inr { val, .. } => {
                    let val = *val;
                    self.spend()?;
                    cs = self.force(snd)?;
                    i = self.force(val)?;
                }
                _ => break,
            }
        }
        match self.wf_ih_lam(label, children, elim).as_deref() {
            Some(Val::Lam { body, .. }) => {
                self.spend()?;
                Ok(Work::Apply1(*body, arg))
            }
            _ => Ok(Work::Val(stuck(self.arena, head, &e))),
        }
    }

    /// `elim^Typ … (box code)`: the fired branch comes from the *shared*
    /// [`beta_elim_ty`] as syntax in the current Γ, and is then evaluated in
    /// the current environment. `None` is `reduce.rs`'s own stuck case (a
    /// layer-m type that cannot be code).
    #[inline(never)]
    fn fire_code_ty(&mut self, code: &Rc<Type>, e: &Elim<'v>) -> Res<Option<Work<'v>>> {
        let Elim::ElimCodeTy {
            ty_motive_level,
            tm_motive_level,
            motives,
            branches,
            ctx,
            env,
            ..
        } = e
        else {
            return Ok(None);
        };
        let rec = Rec::new(ty_motive_level, tm_motive_level, motives, branches);
        let gamma = self.scope(env);
        let Some(fired) = beta_elim_ty(&rec, ctx, code, &gamma) else {
            return Ok(None);
        };
        self.spend()?;
        Ok(Some(Work::Eval(Rc::new(fired), env.clone())))
    }

    /// [`fire_code_ty`](Eval::fire_code_ty) for `elim^Trm`; the type
    /// annotation in the elimination is already in WHNF, as its β requires.
    #[inline(never)]
    fn fire_code_tm(&mut self, code: &Rc<Term>, e: &Elim<'v>) -> Res<Option<Work<'v>>> {
        let Elim::ElimCodeTm {
            ty_motive_level,
            tm_motive_level,
            motives,
            branches,
            code_level,
            ctx,
            ty,
            env,
        } = e
        else {
            return Ok(None);
        };
        let rec = Rec::new(ty_motive_level, tm_motive_level, motives, branches);
        let gamma = self.scope(env);
        let Some(fired) = beta_elim_tm(&rec, ctx, ty, code_level, code, &gamma) else {
            return Ok(None);
        };
        self.spend()?;
        Ok(Some(Work::Eval(Rc::new(fired), env.clone())))
    }
}

// ---------------------------------------------------------------------------
// Entry points
// ---------------------------------------------------------------------------

/// Evaluate a term in the **identity environment** of `gamma` — the root of
/// a conversion, where every local is its own neutral variable — to a
/// δ-transparent weak head value.
pub fn whnf_value<'v>(
    arena: &'v ValueArena<'v>,
    t: &Rc<Term>,
    gamma: &LocalCtx,
    defs: Defs<'_>,
    fuel: u64,
) -> Result<&'v Val<'v>, OutOfFuel> {
    let mut ev = Eval::new(fuel, defs, gamma.base, arena);
    let env = Env::identity(arena, gamma.entries.len() as u32);
    let v = ev.eval_tm(t, &env)?;
    ev.delta_whnf(v)
}

/// The number a natural-number term computes to, read δ-transparently in the
/// identity environment of `gamma` under one `fuel` budget: `Zero`,
/// successors and saturated runs, each tail forced to its δ-transparent head.
/// `None` for anything stuck (open, or waiting on a neutral) or past `u64`.
/// A reader for the elaborator's reflection, not a judgement: whatever it
/// answers is re-checked by conversion when the certificate is.
pub fn nat_value(
    t: &Rc<Term>,
    gamma: &LocalCtx,
    defs: Defs<'_>,
    fuel: u64,
) -> Result<Option<u64>, OutOfFuel> {
    let arena = ValueArena::new();
    let mut ev = Eval::new(fuel, defs, gamma.base, &arena);
    let env = Env::identity(&arena, gamma.entries.len() as u32);
    let mut v = ev.eval_tm(t, &env)?;
    let mut total = 0u64;
    loop {
        v = ev.delta_whnf(v)?;
        let next = match &*v {
            Val::Zero => return Ok(Some(total)),
            Val::Succ(pred) => {
                let Some(t) = total.checked_add(1) else { return Ok(None) };
                total = t;
                *pred
            }
            Val::NatRun { program, tail } => {
                let Some(n) = crate::value::program::ContextProgram::repetition_count_up_to(
                    program,
                    u64::MAX - total,
                ) else {
                    return Ok(None);
                };
                total += n;
                *tail
            }
            _ => return Ok(None),
        };
        v = ev.force(next)?;
    }
}

/// [`whnf_value`] for types.
pub fn whnf_value_ty<'v>(
    arena: &'v ValueArena<'v>,
    t: &Rc<Type>,
    gamma: &LocalCtx,
    defs: Defs<'_>,
    fuel: u64,
) -> Result<&'v VTy<'v>, OutOfFuel> {
    let mut ev = Eval::new(fuel, defs, gamma.base, arena);
    let env = Env::identity(arena, gamma.entries.len() as u32);
    let v = ev.eval_ty(t, &env)?;
    ev.delta_whnf_ty(v)
}

/// The run program a nonzero literal evaluates to
/// (`docs/wide-numerals-design.md` §2): one saturated run up to `u64::MAX`;
/// above it, the value's bits from the top by doubling and incrementing
/// ([`ContextProgram::of_count`]).
fn nat_lit_program(n: &crate::term::Numeral) -> Rc<ContextProgram<()>> {
    ContextProgram::of_count((), n)
}

/// The closure a variable term is bound to in `env`, seen through closures
/// that are themselves only a bound variable (an argument passed on as it
/// is: `λy. ⟨f y, c y⟩` hands `f` and `c` each a closure of `y`). `None` for
/// any other term and for a variable of the base context.
fn bound_root<'v>(env: &Env<'v>, t: &Term) -> Option<&'v TmClo<'v>> {
    let Term::Var(x) = t else { return None };
    let Lookup::Bound(mut c) = env.lookup(x.0) else { return None };
    while let TmClo::Syn { env, body } = c {
        let Term::Var(x) = &**body else { break };
        let Lookup::Bound(next) = env.lookup(x.0) else { break };
        c = next;
    }
    Some(c)
}

#[cfg(test)]
mod tests {
    use super::{Elim, Eval};
    use crate::value::algebra::FoldClass;
    use crate::level::Level;
    use crate::reduce::{Defs, OutOfFuel};
    use crate::term::{CtxBase, LocalVar, Term, Type};
    use crate::value::program::ContextProgram;
    use crate::value::{Env, PiAnn, TmClo, TyClo, Val, ValueArena};
    use std::num::NonZeroU64;
    use std::sync::Arc as Rc;

    fn two_to_64() -> Rc<ContextProgram<()>> {
        let full = ContextProgram::run((), NonZeroU64::new(u64::MAX).unwrap());
        ContextProgram::prepend((), NonZeroU64::new(1).unwrap(), full)
    }

    fn shared_two_to_64() -> Rc<ContextProgram<()>> {
        let mut program = ContextProgram::run((), NonZeroU64::new(1).unwrap());
        for _ in 0..64 {
            program = ContextProgram::compose(Rc::clone(&program), program);
        }
        program
    }

    fn nat_elim<'v>(
        arena: &'v ValueArena<'v>,
        env: Env<'v>,
        step_body: Term,
    ) -> Elim<'v> {
        Elim::ElimNat {
            level: Level::Zero,
            motive: arena.ty(TyClo::new(env, Rc::new(Type::Nat))),
            base: arena.tm(TmClo::val(arena.val(Val::Zero))),
            step: arena.tm(TmClo::syn(env, Rc::new(step_body))),
        }
    }

    fn dummy_lam(body: Term) -> Term {
        Term::Lam {
            dom_level: Level::Zero,
            cod_level: Level::Zero,
            dom: Rc::new(Type::Nat),
            body: Rc::new(body),
        }
    }

    fn synchronous_step() -> Term {
        dummy_lam(Term::ElimNat {
            level: Level::Zero,
            motive: Rc::new(Type::Nat),
            base: Rc::new(Term::Zero),
            step: Rc::new(Term::App {
                fun: Rc::new(Term::Var(LocalVar(3))),
                dom_level: Level::Zero,
                cod_level: Level::Zero,
                dom: Rc::new(Type::Nat),
                cod: Rc::new(Type::Nat),
                arg: Rc::new(Term::Var(LocalVar(1))),
            }),
            scrut: Rc::new(Term::Var(LocalVar(0))),
        })
    }

    fn app_elim<'v>(arena: &'v ValueArena<'v>, arg: &'v TmClo<'v>) -> Elim<'v> {
        let ty = arena.ty(TyClo::new(Env::empty(), Rc::new(Type::Nat)));
        Elim::App {
            ann: Some(PiAnn {
                dom_level: Level::Zero,
                cod_level: Level::Zero,
                dom: ty,
                cod: ty,
            }),
            arg,
        }
    }

    #[test]
    fn saturated_runs_present_two_to_64_as_one_successor_step() {
        let arena = ValueArena::new();
        let tail = arena.tm(TmClo::val(arena.val(Val::Zero)));
        let program = two_to_64();
        let pred = Val::nat_run_pred(&arena, &program, tail);
        assert!(matches!(pred, TmClo::Val(v) if matches!(&**v, Val::NatRun { .. })));
    }

    #[test]
    fn maximum_literal_enters_the_value_domain_as_one_saturated_run() {
        let arena = ValueArena::new();
        let env = Env::empty();
        let mut ev = Eval::new(1, Defs::opaque(), CtxBase::Nil, &arena);
        let value = ev.eval_tm_ref(&Term::NatLit(u64::MAX.into()), &env).unwrap();
        assert!(matches!(&*value,
            Val::NatRun { program, tail }
                if matches!(&**program,
                    ContextProgram::Run { count, .. } if count.get() == u64::MAX)
                && matches!(tail, TmClo::Val(z) if matches!(&**z, Val::Zero))));
    }

    /// A literal past a machine word (docs/wide-numerals-design.md) denotes
    /// exactly its value, in a program of `O(bits)` shared nodes.
    #[test]
    fn a_wide_literal_enters_the_value_domain_as_its_exact_count() {
        let arena = ValueArena::new();
        let env = Env::empty();
        for n in [1u128 << 64, (1u128 << 64) + 1, (1u128 << 100) + 12345, u128::MAX] {
            let mut ev = Eval::new(1, Defs::opaque(), CtxBase::Nil, &arena);
            let value = ev.eval_tm_ref(&Term::NatLit(crate::term::Numeral::from_u128(n)), &env).unwrap();
            let Val::NatRun { program, tail } = &*value else { panic!("{n}: not a run: {value:?}") };
            assert!(matches!(tail, TmClo::Val(z) if matches!(&**z, Val::Zero)), "{n}");
            assert_eq!(exact_count(program), n, "{n}");
        }
    }

    #[test]
    fn successor_algebra_maps_a_shared_run_without_visiting_its_nodes() {
        let arena = ValueArena::new();
        let env = Env::empty();
        let tail = arena.tm(TmClo::val(arena.val(Val::Zero)));
        let program = shared_two_to_64();
        let head = arena.val(Val::NatRun { program: Rc::clone(&program), tail });
        let elim = nat_elim(
            &arena,
            env,
            Term::Succ(Rc::new(Term::Var(LocalVar(0)))),
        );
        let mut ev = Eval::new(2, Defs::opaque(), CtxBase::Nil, &arena);
        let result = ev.elim(head, elim).unwrap();
        assert!(matches!(&*result,
            Val::NatRun { program: mapped, .. } if Rc::ptr_eq(mapped, &program)));
    }

    /// `add`-shaped folds chain: mapping a run onto a tail whose fold is
    /// itself a run must yield one saturated run, not two fragments, or a
    /// doubled literal (`p + p`, and so `pow(2, k)`) is `2^k` fragments.
    #[test]
    fn successor_algebra_merges_the_run_its_tail_produces() {
        let arena = ValueArena::new();
        let env = Env::empty();
        let zero = arena.tm(TmClo::val(arena.val(Val::Zero)));
        let inner = arena.tm(TmClo::val(arena.val(Val::NatRun {
            program: ContextProgram::run((), NonZeroU64::new(4).unwrap()),
            tail: zero,
        })));
        let head = arena.val(Val::NatRun {
            program: ContextProgram::run((), NonZeroU64::new(3).unwrap()),
            tail: inner,
        });
        let elim = nat_elim(
            &arena,
            env,
            Term::Succ(Rc::new(Term::Var(LocalVar(0)))),
        );
        let mut ev = Eval::new(8, Defs::opaque(), CtxBase::Nil, &arena);
        let result = ev.elim(head, elim).unwrap();
        assert!(matches!(&*result,
            Val::NatRun { program, .. }
                if matches!(&**program, ContextProgram::Run { count, .. } if count.get() == 7)));
    }

    /// `twice` is the successor algebra with two constructors per step: a
    /// saturated run's count is scaled, in constant work.
    #[test]
    fn double_successor_algebra_scales_a_saturated_run() {
        let arena = ValueArena::new();
        let env = Env::empty();
        let tail = arena.tm(TmClo::val(arena.val(Val::Zero)));
        let head = arena.val(Val::NatRun {
            program: ContextProgram::run((), NonZeroU64::new(1 << 40).unwrap()),
            tail,
        });
        let elim = nat_elim(
            &arena,
            env,
            Term::Succ(Rc::new(Term::Succ(Rc::new(Term::Var(LocalVar(0)))))),
        );
        let mut ev = Eval::new(4, Defs::opaque(), CtxBase::Nil, &arena);
        let result = ev.elim(head, elim).unwrap();
        assert!(matches!(&*result,
            Val::NatRun { program, .. }
                if matches!(&**program, ContextProgram::Run { count, .. } if count.get() == 1 << 41)));
    }

    /// A count the wider algebra cannot represent in one `u64` run is a
    /// composed program, exact and still constant work: nothing is
    /// materialized and nothing is guessed.
    #[test]
    fn double_successor_algebra_composes_an_overflowing_count() {
        let arena = ValueArena::new();
        let env = Env::empty();
        let tail = arena.tm(TmClo::val(arena.val(Val::Zero)));
        let head = arena.val(Val::NatRun {
            program: ContextProgram::run((), NonZeroU64::new(u64::MAX).unwrap()),
            tail,
        });
        let elim = nat_elim(
            &arena,
            env,
            Term::Succ(Rc::new(Term::Succ(Rc::new(Term::Var(LocalVar(0)))))),
        );
        let mut ev = Eval::new(16, Defs::opaque(), CtxBase::Nil, &arena);
        let result = ev.elim(head, elim).unwrap();
        let Val::NatRun { program, .. } = &*result else { panic!("not a run: {result:?}") };
        assert!(matches!(&**program, ContextProgram::Compose { .. }));
        assert_eq!(ContextProgram::repetition_count_up_to(program, u64::MAX), None);
        assert_eq!(exact_count(program), 2 * (u64::MAX as u128));
    }

    /// The whole count, beyond the kernel's bounded view; a test may hold it.
    fn exact_count(program: &Rc<ContextProgram<()>>) -> u128 {
        fn go(
            program: &Rc<ContextProgram<()>>,
            memo: &mut std::collections::HashMap<*const ContextProgram<()>, u128>,
        ) -> u128 {
            if let Some(n) = memo.get(&Rc::as_ptr(program)) {
                return *n;
            }
            let n = match &**program {
                ContextProgram::Run { count, .. } => count.get() as u128,
                ContextProgram::Compose { outer, inner, .. } => go(outer, memo) + go(inner, memo),
            };
            memo.insert(Rc::as_ptr(program), n);
            n
        }
        go(program, &mut std::collections::HashMap::new())
    }

    #[test]
    fn an_arbitrary_fold_over_a_shared_run_still_obeys_fuel() {
        let arena = ValueArena::new();
        let env = Env::empty();
        let tail = arena.tm(TmClo::val(arena.val(Val::Zero)));
        let head = arena.val(Val::NatRun { program: shared_two_to_64(), tail });
        // Match on the induction hypothesis: observing the result genuinely
        // asks to traverse the logical spine, so compression must not claim
        // a constant-time answer. (Returning `ih` unchanged is the identity
        // algebra, which *is* affine: that fold is the base in one step.)
        let elim = nat_elim(&arena, env, Term::ElimNat {
            level: Level::Zero,
            motive: Rc::new(Type::Nat),
            base: Rc::new(Term::Zero),
            step: Rc::new(Term::Zero),
            scrut: Rc::new(Term::Var(LocalVar(0))),
        });
        let mut ev = Eval::new(32, Defs::opaque(), CtxBase::Nil, &arena);
        assert_eq!(ev.elim(head, elim).unwrap_err(), OutOfFuel);
    }

    #[test]
    fn synchronous_fold_cancels_independent_saturated_runs() {
        let arena = ValueArena::new();
        let env = Env::empty();
        let tail = arena.tm(TmClo::val(arena.val(Val::Zero)));
        let left = arena.val(Val::NatRun {
            program: ContextProgram::run((), NonZeroU64::new(u64::MAX).unwrap()),
            tail,
        });
        let right = arena.tm(TmClo::val(arena.val(Val::NatRun {
            program: ContextProgram::run((), NonZeroU64::new(u64::MAX).unwrap()),
            tail,
        })));
        let elim = Elim::ElimNat {
            level: Level::Zero,
            motive: arena.ty(TyClo::new(env, Rc::new(Type::Nat))),
            base: arena.tm(TmClo::syn(env, Rc::new(dummy_lam(Term::Zero)))),
            step: arena.tm(TmClo::syn(env, Rc::new(synchronous_step()))),
        };
        let mut ev = Eval::new(8, Defs::opaque(), CtxBase::Nil, &arena);
        let folded = ev.elim(left, elim).unwrap();
        let result = ev.elim(folded, app_elim(&arena, right)).unwrap();
        assert!(matches!(&*result, Val::Zero));
    }

    #[test]
    fn synchronous_fold_bisimulates_independent_exponential_dags() {
        let arena = ValueArena::new();
        let env = Env::empty();
        let tail = arena.tm(TmClo::val(arena.val(Val::Zero)));
        let left = arena.val(Val::NatRun { program: shared_two_to_64(), tail });
        let right = arena.tm(TmClo::val(arena.val(Val::NatRun {
            program: shared_two_to_64(),
            tail,
        })));
        let elim = Elim::ElimNat {
            level: Level::Zero,
            motive: arena.ty(TyClo::new(env, Rc::new(Type::Nat))),
            base: arena.tm(TmClo::syn(env, Rc::new(dummy_lam(Term::Zero)))),
            step: arena.tm(TmClo::syn(env, Rc::new(synchronous_step()))),
        };
        let mut ev = Eval::new(80, Defs::opaque(), CtxBase::Nil, &arena);
        let folded = ev.elim(left, elim).unwrap();
        let result = ev.elim(folded, app_elim(&arena, right)).unwrap();
        assert!(matches!(&*result, Val::Zero));
    }

    #[test]
    fn almost_synchronous_algebra_is_not_accelerated() {
        let env = Env::empty();
        let mut step = synchronous_step();
        let Term::Lam { body, .. } = &mut step else { unreachable!() };
        let Term::ElimNat { step: inner, .. } = Rc::make_mut(body) else { unreachable!() };
        // `ih` applied to the λ's own argument rather than its predecessor.
        let Term::App { arg, .. } = Rc::make_mut(inner) else { unreachable!() };
        *arg = Rc::new(Term::Var(LocalVar(2)));
        let arena = ValueArena::new();
        let closure = arena.tm(TmClo::syn(env, Rc::new(step)));
        let mut ev = Eval::new(64, Defs::opaque(), CtxBase::Nil, &arena);
        assert!(matches!(&*ev.classify_step(closure).unwrap(), FoldClass::Opaque));
    }

    /// A weak head `Nat` value's count, walking successors and runs through
    /// their tails; only a test may hold the whole number.
    fn nat_value<'v>(ev: &mut Eval<'_, 'v>, value: &'v Val<'v>) -> u128 {
        let mut total = 0u128;
        let mut cur = value;
        loop {
            let next = match &*cur {
                Val::Zero => return total,
                Val::Succ(pred) => {
                    total += 1;
                    *pred
                }
                Val::NatRun { program, tail } => {
                    total += exact_count(program);
                    *tail
                }
                other => panic!("not a closed natural: {other:?}"),
            };
            cur = ev.force(next).unwrap();
        }
    }

    fn run_over_zero<'v>(arena: &'v ValueArena<'v>, count: u64) -> &'v Val<'v> {
        arena.val(Val::NatRun {
            program: ContextProgram::run((), NonZeroU64::new(count).unwrap()),
            tail: arena.tm(TmClo::val(arena.val(Val::Zero))),
        })
    }

    /// `add(ih, a)` as a step body over binders `k, ih` with `a` the outer
    /// environment's one entry: `elim_Nat(a; ih; λ _ ih'. su ih')`.
    fn add_env_step() -> Term {
        Term::ElimNat {
            level: Level::Zero,
            motive: Rc::new(Type::Nat),
            base: Rc::new(Term::Var(LocalVar(0))),
            step: Rc::new(Term::Succ(Rc::new(Term::Var(LocalVar(0))))),
            scrut: Rc::new(Term::Var(LocalVar(2))),
        }
    }

    /// `mul(a, b)` folds `add(ih, a)` over `b`; the step probes to
    /// `Succ^{|a|}(ih)` through the nested fold, so two runs multiply in one
    /// iteration — here past `u64`, into a composed program, under a fuel
    /// that could not have paid for `2^32` additions.
    #[test]
    fn multiplication_of_two_runs_is_one_iteration() {
        let arena = ValueArena::new();
        let a = arena.tm(TmClo::val(run_over_zero(&arena, 1 << 32)));
        let env = Env::empty().push(&arena, a);
        let elim = nat_elim(&arena, env, add_env_step());
        let mut ev = Eval::new(64, Defs::opaque(), CtxBase::Nil, &arena);
        let result = ev.elim(run_over_zero(&arena, 1 << 32), elim).unwrap();
        let Val::NatRun { program, .. } = &*result else { panic!("not a run: {result:?}") };
        assert_eq!(exact_count(program), 1u128 << 64);
        assert_eq!(nat_value(&mut ev, result), 1u128 << 64);
    }

    /// A step that reads only `k` folds directly, and so does a constant
    /// one: neither is probed, the one ordinary step being the whole fold.
    #[test]
    fn steps_that_ignore_ih_fold_directly() {
        let arena = ValueArena::new();
        let env = Env::empty();
        let step = arena.tm(TmClo::syn(env, Rc::new(Term::Succ(Rc::new(Term::Var(LocalVar(1)))))));
        let mut ev = Eval::new(64, Defs::opaque(), CtxBase::Nil, &arena);
        assert!(matches!(&*ev.classify_step(step).unwrap(), FoldClass::Direct));
        let step = arena.tm(TmClo::syn(env, Rc::new(Term::Succ(Rc::new(Term::Zero)))));
        assert!(matches!(&*ev.classify_step(step).unwrap(), FoldClass::Direct));
        // `(λ_. Succ(k)) ih` reads `ih` and drops it: probed, its result
        // sits on `k` rather than `ih`, and it is not affine.
        let drops_ih = Term::App {
            fun: Rc::new(dummy_lam(Term::Succ(Rc::new(Term::Var(LocalVar(2)))))),
            dom_level: Level::Zero,
            cod_level: Level::Zero,
            dom: Rc::new(Type::Nat),
            cod: Rc::new(Type::Nat),
            arg: Rc::new(Term::Var(LocalVar(0))),
        };
        let step = arena.tm(TmClo::syn(env, Rc::new(drops_ih)));
        assert!(matches!(&*ev.classify_step(step).unwrap(), FoldClass::Opaque));
    }

    /// A step that reads none of its captures is classified once per query,
    /// whatever environment each occurrence closes it over — every unfolding
    /// of a definition holding the fold closes it over that call's arguments
    /// (issues/native-certificate-pieces-remaining-cost.md). One that reads
    /// a capture is a new question under each.
    #[test]
    fn a_step_reading_no_capture_is_probed_once() {
        let arena = ValueArena::new();
        let mut ev = Eval::new(1 << 20, Defs::opaque(), CtxBase::Nil, &arena);
        let zero = arena.tm(TmClo::val(arena.val(Val::Zero)));
        let (here, there) = (Env::empty(), Env::empty().push(&arena, zero).push(&arena, zero));
        let body = Rc::new(Term::Succ(Rc::new(Term::Var(LocalVar(0)))));
        let first = arena.tm(TmClo::syn(here, Rc::clone(&body)));
        assert!(!matches!(&*ev.classify_step(first).unwrap(), FoldClass::Opaque | FoldClass::Direct));
        let spent = ev.fuel();
        let second = arena.tm(TmClo::syn(there, Rc::clone(&body)));
        assert!(!matches!(&*ev.classify_step(second).unwrap(), FoldClass::Opaque | FoldClass::Direct));
        assert_eq!(ev.fuel(), spent);
        assert_eq!(first.ident_under(2), second.ident_under(2));
        // `x₂`, the innermost capture, read beside `ih`: the two closures
        // are two identities.
        let reads = Rc::new(Term::Var(LocalVar(2)));
        let (a, b) = (arena.tm(TmClo::syn(there, Rc::clone(&reads))), arena.tm(TmClo::syn(there.push(&arena, zero), reads)));
        assert_ne!(a.ident_under(2), b.ident_under(2));
    }

    /// A closed subterm is evaluated once per query: forcing it under a
    /// second environment spends nothing.
    #[test]
    fn a_closed_body_is_evaluated_once() {
        let arena = ValueArena::new();
        let mut ev = Eval::new(1 << 20, Defs::opaque(), CtxBase::Nil, &arena);
        let zero = arena.tm(TmClo::val(arena.val(Val::Zero)));
        let redex = Rc::new(Term::App {
            fun: Rc::new(dummy_lam(Term::Succ(Rc::new(Term::Var(LocalVar(0)))))),
            dom_level: Level::Zero,
            cod_level: Level::Zero,
            dom: Rc::new(Type::Nat),
            cod: Rc::new(Type::Nat),
            arg: Rc::new(Term::Zero),
        });
        let first = arena.tm(TmClo::syn(Env::empty(), Rc::clone(&redex)));
        let value = ev.force(first).unwrap();
        assert_eq!(nat_value(&mut ev, value), 1);
        let spent = ev.fuel();
        assert!(spent < 1 << 20);
        let second = arena.tm(TmClo::syn(Env::empty().push(&arena, zero), redex));
        let value = ev.force(second).unwrap();
        assert_eq!(nat_value(&mut ev, value), 1);
        assert_eq!(ev.fuel(), spent);
    }

    /// `(λx. x x)(λx. x x)` as a step body, applied to `ih` when `reads_ih`:
    /// it never reaches a weak head value.
    fn divergent_step(reads_ih: bool) -> Term {
        let app = |f: Term, a: Term| Term::App {
            fun: Rc::new(f),
            dom_level: Level::Zero,
            cod_level: Level::Zero,
            dom: Rc::new(Type::Nat),
            cod: Rc::new(Type::Nat),
            arg: Rc::new(a),
        };
        let omega = dummy_lam(app(Term::Var(LocalVar(0)), Term::Var(LocalVar(0))));
        let diverge = app(omega.clone(), omega);
        if reads_ih { app(diverge, Term::Var(LocalVar(0))) } else { diverge }
    }

    /// A step that never reads `ih` is not probed
    /// (`issues/kernel-fold-probe-evaluates-recursive-arms.md`): classifying
    /// even a divergent one spends nothing, where a step that reads `ih` is
    /// probed and runs the fuel out.
    #[test]
    fn a_step_that_never_reads_ih_is_not_probed() {
        let arena = ValueArena::new();
        let mut ev = Eval::new(1 << 20, Defs::opaque(), CtxBase::Nil, &arena);
        let step = arena.tm(TmClo::syn(Env::empty(), Rc::new(divergent_step(false))));
        assert!(matches!(&*ev.classify_step(step).unwrap(), FoldClass::Direct));
        assert_eq!(ev.fuel(), 1 << 20);
        let step = arena.tm(TmClo::syn(Env::empty(), Rc::new(divergent_step(true))));
        assert_eq!(ev.classify_step(step).unwrap_err(), OutOfFuel);
        // The fold over a long run is the one ordinary step: a constant
        // step, `Succ(Zero)`, folds over `2^32` successors in one.
        let elim = nat_elim(&arena, Env::empty(), Term::Succ(Rc::new(Term::Zero)));
        let mut ev = Eval::new(8, Defs::opaque(), CtxBase::Nil, &arena);
        let result = ev.elim(run_over_zero(&arena, 1 << 32), elim).unwrap();
        assert_eq!(nat_value(&mut ev, result), 1);
    }

    fn pair_nat_ty() -> Type {
        Type::Sigma {
            fst_level: Level::Zero,
            snd_level: Level::Zero,
            fst: Rc::new(Type::Nat),
            snd: Rc::new(Type::Nat),
        }
    }

    fn fst_nat(pair: Term) -> Term {
        Term::Fst {
            fst_level: Level::Zero,
            snd_level: Level::Zero,
            fst_ty: Rc::new(Type::Nat),
            snd_ty: Rc::new(Type::Nat),
            pair: Rc::new(pair),
        }
    }

    fn snd_nat(pair: Term) -> Term {
        Term::Snd {
            fst_level: Level::Zero,
            snd_level: Level::Zero,
            fst_ty: Rc::new(Type::Nat),
            snd_ty: Rc::new(Type::Nat),
            pair: Rc::new(pair),
        }
    }

    fn pair_nat(fst: Term, snd: Term) -> Term {
        Term::Pair {
            fst_level: Level::Zero,
            snd_level: Level::Zero,
            fst_ty: Rc::new(Type::Nat),
            snd_ty: Rc::new(Type::Nat),
            fst: Rc::new(fst),
            snd: Rc::new(snd),
        }
    }

    /// `half` as the elaborator lowers it: a window `(half n, half (n-1))`
    /// whose step is `λ k F. ⟨match k { 0 => 0; su _ => su (π₁ F) }, π₀ F⟩`.
    /// The step matches on `k`, so the class is peeled: a permutation with
    /// an increment at every step but the innermost.
    fn half_elim<'v>(arena: &'v ValueArena<'v>) -> Elim<'v> {
        let env = Env::empty();
        // Binders at the step: k = 1, F = 0; inside the inner step two more.
        let step = pair_nat(
            Term::ElimNat {
                level: Level::Zero,
                motive: Rc::new(Type::Nat),
                base: Rc::new(Term::Zero),
                step: Rc::new(Term::Succ(Rc::new(snd_nat(Term::Var(LocalVar(2)))))),
                scrut: Rc::new(Term::Var(LocalVar(1))),
            },
            fst_nat(Term::Var(LocalVar(0))),
        );
        Elim::ElimNat {
            level: Level::Zero,
            motive: arena.ty(TyClo::new(env, Rc::new(pair_nat_ty()))),
            base: arena.tm(TmClo::syn(env, Rc::new(pair_nat(Term::Zero, Term::Zero)))),
            step: arena.tm(TmClo::syn(env, Rc::new(step))),
        }
    }

    #[test]
    fn a_course_of_values_window_is_iterated_as_a_permutation() {
        let arena = ValueArena::new();
        for count in [1u64, 2, 3, 7, 8, 1 << 40, u64::MAX] {
            let mut ev = Eval::new(96, Defs::opaque(), CtxBase::Nil, &arena);
            let window = ev.elim(run_over_zero(&arena, count), half_elim(&arena)).unwrap();
            let Val::Pair { fst, snd, .. } = &*window else { panic!("not a window: {window:?}") };
            let half = ev.force(fst).unwrap();
            assert_eq!(nat_value(&mut ev, half), (count / 2) as u128, "half({count})");
            let previous = ev.force(snd).unwrap();
            assert_eq!(nat_value(&mut ev, previous), ((count - 1) / 2) as u128, "half({count} - 1)");
        }
    }

    /// The peeled window over an *open* tail: eight peeled steps swap the
    /// window four times, so `half(x + 9)` is four successors on the first
    /// component of the innermost step's window, which is stuck on `x`.
    #[test]
    fn a_peeled_window_over_an_open_tail_stops_at_the_innermost_step() {
        let arena = ValueArena::new();
        let x = arena.tm(TmClo::val(arena.val(Val::var(&arena, 0))));
        let head = arena.val(Val::NatRun {
            program: ContextProgram::run((), NonZeroU64::new(9).unwrap()),
            tail: x,
        });
        let mut ev = Eval::new(96, Defs::opaque(), CtxBase::Nil, &arena);
        let window = ev.elim(head, half_elim(&arena)).unwrap();
        let Val::Pair { fst, .. } = &*window else { panic!("not a window: {window:?}") };
        let half = ev.force(fst).unwrap();
        let Val::NatRun { program, tail } = &*half else { panic!("no successors: {half:?}") };
        assert_eq!(exact_count(program), 4);
        let inner = ev.force(tail).unwrap();
        assert!(matches!(&*inner, Val::Neutral(_)), "{inner:?}");
    }

    /// `max` as a fold: `λ k ih. λ m. elim_Nat(m; su k; λ l _. su (ih l))`
    /// at binders k = 1, ih = 0; m = 0 under the lambda; l = 1, _ = 0 in the
    /// inner step. The synchronous algebra with one successor per
    /// cancelled pair.
    fn max_elim<'v>(arena: &'v ValueArena<'v>) -> Elim<'v> {
        let env = Env::empty();
        let step = dummy_lam(Term::ElimNat {
            level: Level::Zero,
            motive: Rc::new(Type::Nat),
            base: Rc::new(Term::Succ(Rc::new(Term::Var(LocalVar(2))))),
            step: Rc::new(Term::Succ(Rc::new(Term::App {
                fun: Rc::new(Term::Var(LocalVar(3))),
                dom_level: Level::Zero,
                cod_level: Level::Zero,
                dom: Rc::new(Type::Nat),
                cod: Rc::new(Type::Nat),
                arg: Rc::new(Term::Var(LocalVar(1))),
            }))),
            scrut: Rc::new(Term::Var(LocalVar(0))),
        });
        Elim::ElimNat {
            level: Level::Zero,
            motive: arena.ty(TyClo::new(env, Rc::new(Type::Nat))),
            base: arena.tm(TmClo::syn(env, Rc::new(dummy_lam(Term::Var(LocalVar(0)))))),
            step: arena.tm(TmClo::syn(env, Rc::new(step))),
        }
    }

    /// `max(7, 3)`: three pairs cancel under three successors, and the
    /// residual takes the ordinary step. At `u64::MAX` the prefix is
    /// cancelled, not walked.
    #[test]
    fn synchronous_algebra_with_successors_iterates_them_over_the_cancelled_prefix() {
        let arena = ValueArena::new();
        let mut ev = Eval::new(64, Defs::opaque(), CtxBase::Nil, &arena);
        let elim = max_elim(&arena);
        assert!(matches!(&*ev.classify_step(elim_step(&elim)).unwrap(),
            FoldClass::Sync { inc: Some(_) }));
        let three = arena.tm(TmClo::val(run_over_zero(&arena, 3)));
        let folded = ev.elim(run_over_zero(&arena, 7), elim).unwrap();
        let result = ev.elim(folded, app_elim(&arena, three)).unwrap();
        assert_eq!(nat_value(&mut ev, result), 7);

        let mut ev = Eval::new(64, Defs::opaque(), CtxBase::Nil, &arena);
        let big = arena.tm(TmClo::val(run_over_zero(&arena, u64::MAX - 1)));
        let folded = ev.elim(run_over_zero(&arena, u64::MAX), max_elim(&arena)).unwrap();
        let result = ev.elim(folded, app_elim(&arena, big)).unwrap();
        assert_eq!(nat_value(&mut ev, result), u64::MAX as u128);
    }

    /// A uniform window over an *open* tail projects the stuck fold: the
    /// projections are a spine on it, annotated from the motive. The swap
    /// `λ k F. ⟨π₁ F, π₀ F⟩` over nine successors swaps once.
    #[test]
    fn a_window_over_an_open_tail_projects_the_stuck_fold() {
        let arena = ValueArena::new();
        let env = Env::empty();
        let x = arena.tm(TmClo::val(arena.val(Val::var(&arena, 0))));
        let head = arena.val(Val::NatRun {
            program: ContextProgram::run((), NonZeroU64::new(9).unwrap()),
            tail: x,
        });
        let swap = pair_nat(snd_nat(Term::Var(LocalVar(0))), fst_nat(Term::Var(LocalVar(0))));
        let elim = Elim::ElimNat {
            level: Level::Zero,
            motive: arena.ty(TyClo::new(env, Rc::new(pair_nat_ty()))),
            base: arena.tm(TmClo::syn(env, Rc::new(pair_nat(Term::Zero, Term::Zero)))),
            step: arena.tm(TmClo::syn(env, Rc::new(swap))),
        };
        let mut ev = Eval::new(64, Defs::opaque(), CtxBase::Nil, &arena);
        let window = ev.elim(head, elim).unwrap();
        let Val::Pair { fst, .. } = &*window else { panic!("not a window: {window:?}") };
        let first = ev.force(fst).unwrap();
        assert!(matches!(&*first, Val::Neutral(n)
            if matches!(n.spine.last(), Some(Elim::Snd { .. }))), "{first:?}");
    }

    fn elim_step<'v>(elim: &Elim<'v>) -> &'v TmClo<'v> {
        let Elim::ElimNat { step, .. } = elim else { unreachable!() };
        step
    }
}
