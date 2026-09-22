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
//!   56 branch telescopes are not written down a sixth time.
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

use std::num::NonZeroU64;
use std::sync::Arc as Rc;

use crate::level::Level;
use crate::reduce::{
    beta_elim_ty, beta_elim_tm, step_type_delta, Defs, OutOfFuel, Rec, NATIVE_DEPTH_LIMIT,
};
use crate::subst::{GlobalEntry, GlobalSubst};
use crate::term::{
    nth, Branches, CtxBase, CtxEntries, CtxEntry, GlobalVar, LocalCtx, LocalSubst, LocalVar,
    Motives, Term, Type,
};
use crate::value::{
    Elim, ElimSpine, Env, Head, Lookup, SigAnn, SumAnn, TmClo, TyClo, VNeTy, VNeutral,
    VSubst, VTail, VTy, Val, ValueArena,
};
use crate::value::algebra::{AffineTree, FoldClass};
use crate::value::program::ContextProgram;

mod bits;
mod probe;
mod runs;
mod transduce;

type Res<T> = Result<T, OutOfFuel>;

// ---------------------------------------------------------------------------
// Small constructors
// ---------------------------------------------------------------------------

fn neutral<'v>(
    head: Head<'v>,
    spine: ElimSpine<'v>,
    unfold: Option<&'v TmClo<'v>>,
) -> Rc<Val<'v>> {
    Rc::new(Val::Neutral(Rc::new(VNeutral { head, spine, unfold })))
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
fn stuck<'v>(arena: &'v ValueArena<'v>, head: &Rc<Val<'v>>, e: &Elim<'v>) -> Rc<Val<'v>> {
    let spine = arena.elim(ElimSpine::empty(), e.clone());
    neutral(Head::Stuck(Rc::clone(head)), spine, None)
}

// ---------------------------------------------------------------------------
// The machine
// ---------------------------------------------------------------------------

/// A pending reduction, in the tail position of [`Eval::drive`]'s loop.
enum Work<'v> {
    /// Already a weak head value.
    Val(Rc<Val<'v>>),
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
    Elim(Rc<Val<'v>>, Elim<'v>),
}

/// What a value flows back into: a thunk waiting to memoize it, or an
/// elimination waiting for its head.
enum Frame<'v> {
    Memo(&'v TmClo<'v>),
    Elim(Rc<Elim<'v>>),
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
        glued: Option<Rc<Val<'v>>>,
    },
    /// A synchronous fold (`head`, a `NatSync`) waiting for its unfolded
    /// right-hand counter; the application `app` is retried with the value
    /// that flows back in place of its argument.
    SyncArg {
        head: Rc<Val<'v>>,
        app: Rc<Elim<'v>>,
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

    fn vclo(&self, value: Rc<Val<'v>>) -> &'v TmClo<'v> {
        self.arena.tm(TmClo::val(value))
    }

    fn nat_residual(
        &self,
        program: Option<Rc<ContextProgram<()>>>,
        tail: &'v TmClo<'v>,
    ) -> &'v TmClo<'v> {
        match program {
            None => tail,
            Some(program) => self.vclo(Rc::new(Val::NatRun { program, tail })),
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
    fn drive(&mut self, start: Work<'v>) -> Res<Rc<Val<'v>>> {
        if self.depth >= NATIVE_DEPTH_LIMIT {
            return Err(OutOfFuel);
        }
        self.depth += 1;
        self.drives += 1;
        let floor = self.frames.len();
        let out = self.drive_from(start, floor);
        self.depth -= 1;
        // An error unwinds whatever this drive had pending; a thunk that
        // never reached its frame keeps no memo (design §6).
        self.frames.truncate(floor);
        out
    }

    fn drive_from(&mut self, start: Work<'v>, floor: usize) -> Res<Rc<Val<'v>>> {
        let mut work = start;
        loop {
            work = match work {
                Work::Eval(t, env) => self.step_eval(&t, &env)?,
                Work::Elim(head, e) => self.step_elim(head, e)?,
                Work::Apply1(c, arg) => match c {
                    TmClo::Syn { env, body, .. } => {
                        Work::Eval(Rc::clone(body), env.push(self.arena, arg))
                    }
                    _ => Work::Force(c),
                },
                Work::Apply(c, args) => match c {
                    TmClo::Syn { env, body, .. } => {
                        Work::Eval(Rc::clone(body), env.extend(self.arena, &args))
                    }
                    // A closure position holding a computed value has no
                    // pending binders; it ignores them.
                    _ => Work::Force(c),
                },
                Work::Force(c) => {
                    if let Some(v) = self.arena.memo_tm(c) {
                        Work::Val(v)
                    } else {
                        match c {
                            TmClo::Val(v) => Work::Val(Rc::clone(v)),
                            TmClo::Syn { env, body, .. } => {
                                let w = Work::Eval(Rc::clone(body), *env);
                                self.frames.push(Frame::Memo(c));
                                w
                            }
                            TmClo::Elim { head, elim, .. } => {
                                let w = Work::Force(head);
                                self.frames.push(Frame::Memo(c));
                                self.frames.push(Frame::Elim(Rc::clone(elim)));
                                w
                            }
                        }
                    }
                }
                Work::Val(v) => {
                    if self.frames.len() == floor {
                        return Ok(v);
                    }
                    match self.frames.pop() {
                        None => return Ok(v),
                        // A thunk records its value only on success.
                        Some(Frame::Memo(c)) => {
                            self.arena.cache_tm(c, &v);
                            Work::Val(v)
                        }
                        Some(Frame::Elim(e)) => Work::Elim(v, (*e).clone()),
                        Some(Frame::SyncArg { head, app }) => {
                            let Elim::App { dom_level, cod_level, dom, cod, .. } = &*app else {
                                unreachable!("SyncArg stores an application")
                            };
                            let app = Elim::App {
                                dom_level: dom_level.clone(),
                                cod_level: cod_level.clone(),
                                dom: *dom,
                                cod: *cod,
                                arg: self.vclo(v),
                            };
                            Work::Elim(head, app)
                        }
                        Some(Frame::NatRunTail { program, glued }) => match &*v {
                            Val::NatRun { program: inner, tail } => {
                                Work::Val(Rc::new(Val::NatRun {
                                    program: ContextProgram::append(program, Rc::clone(inner)),
                                    tail: *tail,
                                }))
                            }
                            Val::Neutral(n) if n.unfold.is_some() => {
                                self.spend()?;
                                let unfold = n.unfold.unwrap();
                                let glued = glued.or_else(|| Some(Rc::clone(&v)));
                                self.frames.push(Frame::NatRunTail { program, glued });
                                Work::Force(unfold)
                            }
                            Val::Neutral(_) => {
                                let tail = glued.unwrap_or(v);
                                Work::Val(Rc::new(Val::NatRun { program, tail: self.vclo(tail) }))
                            }
                            _ => Work::Val(Rc::new(Val::NatRun { program, tail: self.vclo(v) })),
                        },
                    }
                }
            };
        }
    }

    // -- forcing and application -------------------------------------------

    /// Force a 0-binder sub-structure to its weak head value. Memoizes on
    /// success only.
    pub fn force(&mut self, c: &'v TmClo<'v>) -> Res<Rc<Val<'v>>> {
        self.drive(Work::Force(c))
    }

    /// [`Eval::force`] for types.
    pub fn force_ty(&mut self, c: &'v TyClo<'v>) -> Res<Rc<VTy<'v>>> {
        if let Some(v) = self.arena.memo_ty(c) {
            return Ok(v);
        }
        let v = match c {
            TyClo::Val(v) => Rc::clone(v),
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
    pub fn apply(&mut self, c: &'v TmClo<'v>, args: &[&'v TmClo<'v>]) -> Res<Rc<Val<'v>>> {
        let w = match args {
            [a] => Work::Apply1(c, *a),
            _ => Work::Apply(c, args.to_vec()),
        };
        self.drive(w)
    }

    /// [`Eval::apply`] for type closures. A closure that is not syntactic has
    /// no pending binders and ignores them (`TyClo::Val` is a *constant*
    /// closure — the shape conversion's weakened annotations take).
    pub fn apply_ty(&mut self, c: &'v TyClo<'v>, args: &[&'v TmClo<'v>]) -> Res<Rc<VTy<'v>>> {
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
    pub fn delta_step(&mut self, v: Rc<Val<'v>>) -> Res<Rc<Val<'v>>> {
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
    pub fn delta_whnf(&mut self, mut v: Rc<Val<'v>>) -> Res<Rc<Val<'v>>> {
        let saved = std::mem::replace(&mut self.transparent, true);
        let out = loop {
            let next = match self.delta_step(Rc::clone(&v)) {
                Ok(next) => next,
                Err(e) => break Err(e),
            };
            if Rc::ptr_eq(&next, &v) {
                break Ok(v);
            }
            v = next;
        };
        self.transparent = saved;
        out
    }

    /// [`Eval::delta_step`] for types: advance exactly one definition in the
    /// term at which an `El`, `Vec`, or `Fin` is δ-stuck, then perform the
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
    pub fn ty_to_former(&mut self, mut v: Rc<VTy<'v>>) -> Res<Rc<VTy<'v>>> {
        while matches!(&*v, VTy::Neutral(_)) {
            let d = self.delta_step_ty(Rc::clone(&v))?;
            if Rc::ptr_eq(&d, &v) {
                break;
            }
            v = d;
        }
        Ok(v)
    }

    pub fn delta_step_ty(&mut self, v: Rc<VTy<'v>>) -> Res<Rc<VTy<'v>>> {
        enum Next<'v> {
            Done,
            El(Level, Rc<Val<'v>>),
            Vec(Level, &'v TyClo<'v>, Rc<Val<'v>>),
            Fin(Rc<Val<'v>>),
        }
        let next = match &*v {
            VTy::Neutral(VNeTy::El { level, tm }) => Next::El(level.clone(), Rc::clone(tm)),
            VTy::Vec { level, elem, len } => Next::Vec(level.clone(), *elem, Rc::clone(len)),
            VTy::Fin { len } => Next::Fin(Rc::clone(len)),
            _ => Next::Done,
        };
        match next {
            Next::Done => Ok(v),
            Next::El(level, tm) => {
                let d = self.delta_step(Rc::clone(&tm))?;
                if Rc::ptr_eq(&d, &tm) {
                    Ok(v)
                } else {
                    self.decode(&level, &d)
                }
            }
            Next::Vec(level, elem, len) => {
                let d = self.delta_step(Rc::clone(&len))?;
                if Rc::ptr_eq(&d, &len) {
                    Ok(v)
                } else {
                    self.vec_ty(&level, elem, &d)
                }
            }
            Next::Fin(len) => {
                let d = self.delta_step(Rc::clone(&len))?;
                if Rc::ptr_eq(&d, &len) {
                    Ok(v)
                } else {
                    self.fin_ty(&d)
                }
            }
        }
    }

    /// Force the glued unfoldings at a type's δ-stuck term until none
    /// remains.
    pub fn delta_whnf_ty(&mut self, mut v: Rc<VTy<'v>>) -> Res<Rc<VTy<'v>>> {
        let saved = std::mem::replace(&mut self.transparent, true);
        let out = loop {
            let next = match self.delta_step_ty(Rc::clone(&v)) {
                Ok(next) => next,
                Err(e) => break Err(e),
            };
            if Rc::ptr_eq(&next, &v) {
                break Ok(v);
            }
            v = next;
        };
        self.transparent = saved;
        out
    }

    // -- types --------------------------------------------------------------

    /// Evaluate a type to a weak head normal type value.
    pub fn eval_ty(&mut self, t: &Type, env: &Env<'v>) -> Res<Rc<VTy<'v>>> {
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
        };
        Ok(Rc::new(v))
    }

    /// `El^l v` — decode an encoding *value*, or leave the neutral `El`.
    ///
    /// The decoded children are built as `El` **syntax** over the encoding
    /// child's own closure, so the decode stays one step deep: a `Π` is weak
    /// head normal and its domain is not reduced until someone asks.
    fn decode(&mut self, level: &Level, v: &Rc<Val<'v>>) -> Res<Rc<VTy<'v>>> {
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
            || Ok(Rc::new(VTy::Neutral(VNeTy::El { level: level.clone(), tm: Rc::clone(v) })));

        let decoded = match &**v {
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
        Ok(Rc::new(decoded))
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
        len: &Rc<Val<'v>>,
    ) -> Res<Rc<VTy<'v>>> {
        let out = match &**len {
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
                len: Rc::clone(len),
            },
        };
        Ok(Rc::new(out))
    }

    /// `Fin(k)`: `0 ⇝ Empty^0`, `S k ⇝ Unit^0 +^{0,0} Fin(k)`, stuck
    /// otherwise. Both reducts are closed apart from the predecessor, which
    /// again rides in the environment.
    fn fin_ty(&mut self, len: &Rc<Val<'v>>) -> Res<Rc<VTy<'v>>> {
        let out = match &**len {
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
            _ => VTy::Fin { len: Rc::clone(len) },
        };
        Ok(Rc::new(out))
    }

    /// A local substitution inside a neutral: its terms become **values**,
    /// evaluated pointwise here. An unforced `δ` would be the defect class
    /// reintroduced by the domain (design §3.4).
    fn eval_subst(&mut self, d: &LocalSubst, env: &Env<'v>) -> Res<VSubst<'v>> {
        let mut terms = Vec::with_capacity(d.terms.len());
        for t in &d.terms {
            terms.push(self.eval_tm(t, env)?);
        }
        Ok(VSubst { tail: VTail::of(d.tail, self.base, env.gshift()), terms })
    }

    // -- terms --------------------------------------------------------------

    /// Evaluate a term to a weak head normal value.
    pub fn eval_tm(&mut self, t: &Rc<Term>, env: &Env<'v>) -> Res<Rc<Val<'v>>> {
        self.eval_tm_ref(t, env)
    }

    /// [`Eval::eval_tm`] on a node the caller does not own — the **root** of a
    /// conversion, which is syntax lent to the checker. Wrapping it in an
    /// `Rc` just to start the machine cost 1.3× on `nat/check-numeral`, whose
    /// every conversion is one `Nat ≈ Nat`.
    pub fn eval_tm_ref(&mut self, t: &Term, env: &Env<'v>) -> Res<Rc<Val<'v>>> {
        let w = self.step_eval(t, env)?;
        self.drive(w)
    }

    /// One step of [`Eval::eval_tm`], with its **tail positions returned**
    /// rather than called: see [`Eval::drive`].
    fn step_eval(&mut self, t: &Term, env: &Env<'v>) -> Res<Work<'v>> {
        let yclo = |env: &Env<'v>, body: &Rc<Type>| {
            self.arena.ty(TyClo::new(*env, Rc::clone(body)))
        };
        let tclo = |env: &Env<'v>, body: &Rc<Term>| {
            self.arena.tm(TmClo::syn(*env, Rc::clone(body)))
        };
        let v = match t {
            Term::Var(x) => match env.lookup(x.0) {
                Lookup::Bound(c) => return Ok(Work::Force(c)),
                Lookup::Base(d) => Val::base_var(d),
            },

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
            Term::NatLit(0) => Val::Zero,
            Term::NatLit(n) => Val::NatRun {
                program: ContextProgram::run(
                    (),
                    NonZeroU64::new(*n).expect("nonzero NatLit arm"),
                ),
                tail: self.arena.tm(TmClo::val(Rc::new(Val::Zero))),
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

            // -- eliminations --
            Term::App { fun, dom_level, cod_level, dom, cod, arg } => {
                let f = self.eval_tm(fun, env)?;
                let e = Elim::App {
                    dom_level: dom_level.clone(),
                    cod_level: cod_level.clone(),
                    dom: yclo(env, dom),
                    cod: yclo(env, cod),
                    arg: tclo(env, arg),
                };
                return Ok(Work::Elim(f, e));
            }
            Term::UApp { fun, levels } => {
                let f = self.eval_tm(fun, env)?;
                return Ok(Work::Elim(f, Elim::UApp { levels: levels.clone() }));
            }
            Term::CtxApp { fun, ctx } => {
                let f = self.eval_tm(fun, env)?;
                return Ok(Work::Elim(f, Elim::CtxApp { ctx: amb_ctx(env, ctx) }));
            }
            Term::TyApp { fun, arg } => {
                let f = self.eval_tm(fun, env)?;
                return Ok(Work::Elim(f, Elim::TyApp { arg: amb_ty(env, arg) }));
            }
            Term::Fst { fst_level, snd_level, fst_ty, snd_ty, pair } => {
                let p = self.eval_tm(pair, env)?;
                let e = Elim::Fst {
                    ann: Some(SigAnn {
                        fst_level: fst_level.clone(),
                        snd_level: snd_level.clone(),
                        fst_ty: yclo(env, fst_ty),
                        snd_ty: yclo(env, snd_ty),
                    }),
                };
                return Ok(Work::Elim(p, e));
            }
            Term::Snd { fst_level, snd_level, fst_ty, snd_ty, pair } => {
                let p = self.eval_tm(pair, env)?;
                let e = Elim::Snd {
                    ann: Some(SigAnn {
                        fst_level: fst_level.clone(),
                        snd_level: snd_level.clone(),
                        fst_ty: yclo(env, fst_ty),
                        snd_ty: yclo(env, snd_ty),
                    }),
                };
                return Ok(Work::Elim(p, e));
            }
            // The checked projections push the *existing* elims with no
            // annotation at all — they carry none (design §2.1). A neutral
            // `fst@` is therefore indistinguishable from a neutral `fst` at
            // the value domain except for the stored levels, which
            // `conv.rs`'s typed projection arm already treats as optional:
            // it reads the Σ inferred for the pair, never the annotation.
            Term::FstAt { pair } | Term::SndAt { pair } => {
                let second = matches!(t, Term::SndAt { .. });
                let p = self.eval_tm(pair, env)?;
                let e = if second {
                    Elim::Snd { ann: None }
                } else {
                    Elim::Fst { ann: None }
                };
                return Ok(Work::Elim(p, e));
            }
            Term::ElimNat { level, motive, base, step, scrut } => {
                let s = self.eval_tm(scrut, env)?;
                let e = Elim::ElimNat {
                    level: level.clone(),
                    motive: yclo(env, motive),
                    base: tclo(env, base),
                    step: tclo(env, step),
                };
                return Ok(Work::Elim(s, e));
            }
            Term::ElimEmpty { level, scrut_level, motive, scrut } => {
                let s = self.eval_tm(scrut, env)?;
                let e = Elim::ElimEmpty {
                    level: level.clone(),
                    scrut_level: scrut_level.clone(),
                    motive: yclo(env, motive),
                };
                return Ok(Work::Elim(s, e));
            }
            Term::ElimSEmpty { level, scrut_level, motive, scrut } => {
                let s = self.eval_tm(scrut, env)?;
                let e = Elim::ElimSEmpty {
                    level: level.clone(),
                    scrut_level: scrut_level.clone(),
                    motive: yclo(env, motive),
                };
                return Ok(Work::Elim(s, e));
            }
            Term::ElimSquash { src_level, dst_level, src_ty, motive, case, scrut } => {
                let s = self.eval_tm(scrut, env)?;
                let e = Elim::ElimSquash {
                    src_level: src_level.clone(),
                    dst_level: dst_level.clone(),
                    src_ty: yclo(env, src_ty),
                    motive: yclo(env, motive),
                    case: tclo(env, case),
                };
                return Ok(Work::Elim(s, e));
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
                scrut,
            } => {
                let s = self.eval_tm(scrut, env)?;
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
                return Ok(Work::Elim(s, e));
            }
            Term::ElimW {
                shape_level,
                pos_level,
                motive_level,
                shape,
                pos,
                motive,
                step,
                scrut,
            } => {
                let s = self.eval_tm(scrut, env)?;
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
                return Ok(Work::Elim(s, e));
            }
            Term::ElimWf { level, motive_level, shape, arity, motive, step, scrut } => {
                let s = self.eval_tm(scrut, env)?;
                let e = Elim::ElimWf {
                    level: level.clone(),
                    motive_level: motive_level.clone(),
                    shape: yclo(env, shape),
                    arity: tclo(env, arity),
                    motive: yclo(env, motive),
                    step: tclo(env, step),
                    env: env.clone(),
                };
                return Ok(Work::Elim(s, e));
            }
            Term::J { ty_level, motive_level, ty, lhs, motive, case, rhs, proof } => {
                let p = self.eval_tm(proof, env)?;
                let e = Elim::J {
                    ty_level: ty_level.clone(),
                    motive_level: motive_level.clone(),
                    ty: yclo(env, ty),
                    lhs: tclo(env, lhs),
                    motive: yclo(env, motive),
                    case: tclo(env, case),
                    rhs: tclo(env, rhs),
                };
                return Ok(Work::Elim(p, e));
            }
            Term::Transp { ty_level, motive_level, ty, motive, lhs, rhs, proof, tm } => {
                let p = self.eval_tm(proof, env)?;
                let e = Elim::Transp {
                    ty_level: ty_level.clone(),
                    motive_level: motive_level.clone(),
                    ty: yclo(env, ty),
                    motive: yclo(env, motive),
                    lhs: tclo(env, lhs),
                    rhs: tclo(env, rhs),
                    tm: tclo(env, tm),
                };
                return Ok(Work::Elim(p, e));
            }
            Term::LetBoxTy { motive_level, code_level, ctx, motive, body, scrut } => {
                let s = self.eval_tm(scrut, env)?;
                let e = Elim::LetBoxTy {
                    motive_level: motive_level.clone(),
                    code_level: code_level.clone(),
                    ctx: amb_ctx(env, ctx),
                    motive: yclo(env, motive),
                    body: under_binder_tm(self.arena, env, body),
                };
                return Ok(Work::Elim(s, e));
            }
            Term::LetBoxTm { motive_level, code_level, ctx, ty, motive, body, scrut } => {
                let s = self.eval_tm(scrut, env)?;
                let e = Elim::LetBoxTm {
                    motive_level: motive_level.clone(),
                    code_level: code_level.clone(),
                    ctx: amb_ctx(env, ctx),
                    ty: amb_ty(env, ty),
                    motive: yclo(env, motive),
                    body: under_binder_tm(self.arena, env, body),
                };
                return Ok(Work::Elim(s, e));
            }
            Term::ElimCodeTy {
                ty_motive_level,
                tm_motive_level,
                motives,
                branches,
                code_level,
                ctx,
                scrut,
            } => {
                let s = self.eval_tm(scrut, env)?;
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
                return Ok(Work::Elim(s, e));
            }
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
        };
        Ok(Work::Val(Rc::new(v)))
    }

    /// `u^δ` as a glued neutral: `unfold` is `Some` exactly when `Defs` says
    /// `u` is a definition here, and it evaluates the (already rescoped) body
    /// under δ's **value** environment.
    ///
    /// That environment is δ's payload values alone: `wk^k_g` maps the
    /// abstract prefix of Δ to the abstract prefix of Γ identically, and
    /// `·^k_{g?}` targets an empty Δ, so past the payloads the lookup falls
    /// through to the same [`Head::BaseVar`] numbering either way.
    fn global_tm(&mut self, var: GlobalVar, subst: VSubst<'v>) -> Rc<Val<'v>> {
        let body = self.defs.body_unshifted(var).map(Rc::clone);
        let unfold = body.map(|body| {
            let mut denv = Env::at(var.0 + 1);
            for v in &subst.terms {
                denv = denv.push(self.arena, self.vclo(Rc::clone(v)));
            }
            self.arena.tm(TmClo::syn(denv, body))
        });
        neutral(Head::Global { var, subst }, ElimSpine::empty(), unfold)
    }

    /// `T ⇝* W` on **syntax**, in a local context that is not the ambient
    /// one. The single customer is `elim^Trm`'s type annotation (scoped in
    /// Δ); it is off the hot path and the design keeps Δ syntactic (§3.4).
    fn whnf_ty_syntax(&mut self, t: &Rc<Type>, gamma: &LocalCtx) -> Res<Rc<Type>> {
        let mut cur = Rc::clone(t);
        while let Some(next) = step_type_delta(&cur, gamma, self.defs) {
            self.spend()?;
            cur = Rc::new(next);
        }
        Ok(cur)
    }

    // -- elimination --------------------------------------------------------

    /// Apply one elimination to a weak head value: fire its β, or extend the
    /// neutral's spine (and, when the neutral is glued, its unfolding).
    pub fn elim(&mut self, head: Rc<Val<'v>>, e: Elim<'v>) -> Res<Rc<Val<'v>>> {
        self.drive(Work::Elim(head, e))
    }

    /// One step of [`Eval::elim`]; see [`Eval::drive`].
    fn step_elim(&mut self, head: Rc<Val<'v>>, e: Elim<'v>) -> Res<Work<'v>> {
        if let Val::Neutral(n) = &*head {
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
                if !matches!(&*self.classify_step(step)?, FoldClass::Opaque) {
                    self.spend()?;
                    self.frames.push(Frame::Elim(Rc::new(e)));
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
                    self.frames.push(Frame::Elim(Rc::new(e)));
                    return Ok(Work::Force(unfold));
                }
            }
            let n = Rc::clone(n);
            return Ok(Work::Val(self.push_elim(&n, e)));
        }
        match (&*head, &e) {
            // A width fold waiting for the arguments its class fires at
            // (`docs/native-bitvector-values-design.md` §4).
            (Val::BitFold { .. }, Elim::App { .. }) => {
                return self.bit_fold_app(&head, e);
            }
            (
                Val::NatSync { program, tail, elim },
                Elim::App { dom_level, cod_level, dom, cod, arg },
            ) => {
                let right = self.force(arg)?;
                if let Val::Neutral(rn) = &*right {
                    if let Some(unfold) = rn.unfold {
                        // The counter on the right is a glued definition
                        // (`sub(x, p)` feeding the next comparison): unfold
                        // it and retry, for the reason given at the neutral
                        // scrutinee case above.
                        self.spend()?;
                        self.frames.push(Frame::SyncArg {
                            head: Rc::clone(&head),
                            app: Rc::new(e.clone()),
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
                        let folded = self.arena.tm(TmClo::elim(left, Rc::clone(elim)));
                        let app = Elim::App {
                            dom_level: dom_level.clone(),
                            cod_level: cod_level.clone(),
                            dom,
                            cod,
                            arg: right,
                        };
                        self.frames.push(Frame::Elim(Rc::new(app)));
                        return Ok(Work::Force(folded));
                    }
                }

                // The right-hand head is not a matching run. Expose exactly
                // the ordinary outer successor step and retry the application
                // on its result; no semantic case is guessed here.
                let pred = Val::nat_run_pred(self.arena, program, tail);
                let ih = self.arena.tm(TmClo::elim(pred, Rc::clone(elim)));
                let Elim::ElimNat { step, .. } = &**elim else {
                    unreachable!("NatSync stores a Nat eliminator")
                };
                self.frames.push(Frame::Elim(Rc::new(e)));
                self.spend()?;
                Ok(Work::Apply(*step, vec![pred, ih]))
            }
            (Val::Lam { body, .. }, Elim::App { arg, .. }) => {
                self.spend()?;
                let (body, arg) = (*body, *arg);
                Ok(Work::Apply1(body, arg))
            }
            (Val::ULam { num_vars, body, .. }, Elim::UApp { levels })
                if *num_vars as usize == levels.len() =>
            {
                self.spend()?;
                let Some((benv, bbody)) = body.as_syn() else { return Ok(Work::Val(stuck(self.arena, &head, &e))) };
                // The written vectors pair positionally (outermost first);
                // instantiation wants innermost-first.
                let phi: Vec<Level> = levels.iter().rev().cloned().collect();
                let (benv, inst) = (benv.clone(), Rc::new(bbody.inst_univ(&phi)));
                Ok(Work::Eval(inst, benv))
            }
            (Val::CtxLam { body, .. }, Elim::CtxApp { ctx }) => {
                self.spend()?;
                let Some((benv, bbody)) = body.as_syn() else { return Ok(Work::Val(stuck(self.arena, &head, &e))) };
                let sigma = GlobalSubst::single(GlobalEntry::Ctx(ctx.clone()));
                let (benv, inst) = (benv.clone(), Rc::new(bbody.apply_global(&sigma)));
                Ok(Work::Eval(inst, benv))
            }
            (Val::TyLam { body, .. }, Elim::TyApp { arg }) => {
                self.spend()?;
                let Some((benv, bbody)) = body.as_syn() else { return Ok(Work::Val(stuck(self.arena, &head, &e))) };
                let sigma = GlobalSubst::single(GlobalEntry::Ty(Rc::clone(arg)));
                let (benv, inst) = (benv.clone(), Rc::new(bbody.apply_global(&sigma)));
                Ok(Work::Eval(inst, benv))
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
                let ih = self.arena.tm(TmClo::elim(pred, Rc::new(e.clone())));
                Ok(Work::Apply(step, vec![pred, ih]))
            }
            (Val::NatRun { program, tail }, Elim::ElimNat { step, .. }) => {
                self.spend()?;
                if let Some(work) = self.fold_run(&head, program, tail, &e)? {
                    return Ok(work);
                }
                let pred = Val::nat_run_pred(self.arena, program, tail);
                let ih = self.arena.tm(TmClo::elim(pred, Rc::new(e.clone())));
                Ok(Work::Apply(*step, vec![pred, ih]))
            }
            (Val::Refl { .. }, Elim::J { case, .. }) => {
                self.spend()?;
                let case = *case;
                Ok(Work::Force(case))
            }
            (Val::SRefl { .. }, Elim::Transp { tm, .. }) => {
                self.spend()?;
                let tm = *tm;
                Ok(Work::Force(tm))
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
                Ok(Work::Elim(Rc::new(pair), e.clone()))
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
            (Val::BoxTy(code), Elim::LetBoxTy { body, .. }) => {
                self.spend()?;
                let Some((benv, bbody)) = body.as_syn() else { return Ok(Work::Val(stuck(self.arena, &head, &e))) };
                let sigma = GlobalSubst::single(GlobalEntry::Ty(Rc::clone(code)));
                let (benv, inst) = (benv.clone(), Rc::new(bbody.apply_global(&sigma)));
                Ok(Work::Eval(inst, benv))
            }
            (Val::BoxTm(code), Elim::LetBoxTm { body, .. }) => {
                self.spend()?;
                let Some((benv, bbody)) = body.as_syn() else { return Ok(Work::Val(stuck(self.arena, &head, &e))) };
                let sigma = GlobalSubst::single(GlobalEntry::Tm(Rc::clone(code)));
                let (benv, inst) = (benv.clone(), Rc::new(bbody.apply_global(&sigma)));
                Ok(Work::Eval(inst, benv))
            }
            // `box (U^δ)` blocks the recursor: canonical, but neutral as a
            // whole (ch. 06), which is why the box becomes the head.
            (Val::BoxTy(code), Elim::ElimCodeTy { .. }) => {
                if matches!(&**code, Type::GlobalTy { .. }) {
                    return Ok(Work::Val(neutral(
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

    /// Extend a neutral's spine — and, when it is glued, its pending
    /// unfolding by the same elimination, so that forcing the unfolding
    /// replays the spine (design §5).
    fn push_elim(&mut self, n: &Rc<VNeutral<'v>>, e: Elim<'v>) -> Rc<Val<'v>> {
        let unfold = n
            .unfold
            .as_ref()
            .map(|u| self.arena.tm(TmClo::elim(u, Rc::new(e.clone()))));
        let spine = self.arena.elim(n.spine, e);
        neutral(n.head.clone(), spine, unfold)
    }

    /// `elim_W (sup(…; a; f)) ⇝ s[a/a, f/f, (λ y. elim_W …(f y))/ih]`.
    ///
    /// The ih is the one β that synthesizes a λ. Rather than a native
    /// closure, it is built as an ordinary syntactic closure over the
    /// environment `ρ, a, f`: the recursive eliminator is *exactly*
    /// `reduce.rs`'s term with `a` and `f` named by de Bruijn slots instead
    /// of substituted, which is why its adequacy is by inspection. The
    /// whole-node `shift_local(3)` is `reduce.rs`'s `shift_local(1)` widened
    /// by the two extra slots, and it descends the annotations' own binders
    /// for the same reason.
    fn fire_elim_w(
        &mut self,
        label: &'v TmClo<'v>,
        children: &'v TmClo<'v>,
        e: &Elim<'v>,
    ) -> Res<Option<Work<'v>>> {
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
            return Ok(None);
        };
        let Some((_, step_body)) = step.as_syn() else { return Ok(None) };
        let (Some((_, shape_body)), Some((_, pos_body)), Some((_, motive_body))) =
            (shape.as_syn(), pos.as_syn(), motive.as_syn())
        else {
            return Ok(None);
        };
        let rho_af = env.push(self.arena, label).push(self.arena, children);
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
        let ih = Rc::new(Val::Lam {
            dom_level: pos_level.clone(),
            cod_level: motive_level.clone(),
            // `T[a/x]` in `(Γ, a, f)`: `a` is slot 1.
            dom: self.arena.ty(TyClo::new(rho_af, Rc::new(pos_body.shift_local(1)))),
            body: self.arena.tm(TmClo::syn(rho_af, Rc::new(rec))),
        });
        let step = *step;
        Ok(Some(Work::Apply(
            step,
            vec![label, children, self.vclo(ih)],
        )))
    }

    /// `elim_Wf (sup_f(…; a; cs)) ⇝ s[a, cs, λ i. elim_Wf(…; nth … cs i)]`.
    /// [`fire_elim_w`](Eval::fire_elim_w)'s construction, with the child
    /// reached through the shared [`nth`] schema instead of an application.
    fn fire_elim_wf(
        &mut self,
        label: &'v TmClo<'v>,
        children: &'v TmClo<'v>,
        e: &Elim<'v>,
    ) -> Res<Option<Work<'v>>> {
        let Elim::ElimWf { level, motive_level, shape, arity, motive, step, env } = e else {
            return Ok(None);
        };
        let Some((_, step_body)) = step.as_syn() else { return Ok(None) };
        let Some((_, arity_body)) = arity.as_syn() else { return Ok(None) };
        let (Some((_, shape_body)), Some((_, motive_body))) = (shape.as_syn(), motive.as_syn())
        else {
            return Ok(None);
        };
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
        let ih = Rc::new(Val::Lam {
            dom_level: Level::Zero,
            cod_level: motive_level.clone(),
            dom: self.arena.ty(TyClo::new(
                rho_acs,
                Rc::new(Type::Fin { len: Rc::new(arity_body.shift_local(1)) }),
            )),
            body: self.arena.tm(TmClo::syn(rho_acs, Rc::new(rec))),
        });
        let step = *step;
        Ok(Some(Work::Apply(
            step,
            vec![label, children, self.vclo(ih)],
        )))
    }

    /// `elim^Typ … (box code)`: the fired branch comes from the *shared*
    /// [`beta_elim_ty`] as syntax in the current Γ, and is then evaluated in
    /// the current environment. `None` is `reduce.rs`'s own stuck case (a
    /// layer-m type that cannot be code).
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
) -> Result<Rc<Val<'v>>, OutOfFuel> {
    let mut ev = Eval::new(fuel, defs, gamma.base, arena);
    let env = Env::identity(arena, gamma.entries.len() as u32);
    let v = ev.eval_tm(t, &env)?;
    ev.delta_whnf(v)
}

/// [`whnf_value`] for types.
pub fn whnf_value_ty<'v>(
    arena: &'v ValueArena<'v>,
    t: &Rc<Type>,
    gamma: &LocalCtx,
    defs: Defs<'_>,
    fuel: u64,
) -> Result<Rc<VTy<'v>>, OutOfFuel> {
    let mut ev = Eval::new(fuel, defs, gamma.base, arena);
    let env = Env::identity(arena, gamma.entries.len() as u32);
    let v = ev.eval_ty(t, &env)?;
    ev.delta_whnf_ty(v)
}

#[cfg(test)]
mod tests {
    use super::{Elim, Eval};
    use crate::value::algebra::FoldClass;
    use crate::level::Level;
    use crate::reduce::{Defs, OutOfFuel};
    use crate::term::{CtxBase, LocalVar, Term, Type};
    use crate::value::program::ContextProgram;
    use crate::value::{Env, TmClo, TyClo, Val, ValueArena};
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
            base: arena.tm(TmClo::val(Rc::new(Val::Zero))),
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
            dom_level: Level::Zero,
            cod_level: Level::Zero,
            dom: ty,
            cod: ty,
            arg,
        }
    }

    #[test]
    fn saturated_runs_present_two_to_64_as_one_successor_step() {
        let arena = ValueArena::new();
        let tail = arena.tm(TmClo::val(Rc::new(Val::Zero)));
        let program = two_to_64();
        let pred = Val::nat_run_pred(&arena, &program, tail);
        assert!(matches!(pred, TmClo::Val(v) if matches!(&**v, Val::NatRun { .. })));
    }

    #[test]
    fn maximum_literal_enters_the_value_domain_as_one_saturated_run() {
        let arena = ValueArena::new();
        let env = Env::empty();
        let mut ev = Eval::new(1, Defs::opaque(), CtxBase::Nil, &arena);
        let value = ev.eval_tm_ref(&Term::NatLit(u64::MAX), &env).unwrap();
        assert!(matches!(&*value,
            Val::NatRun { program, tail }
                if matches!(&**program,
                    ContextProgram::Run { count, .. } if count.get() == u64::MAX)
                && matches!(tail, TmClo::Val(z) if matches!(&**z, Val::Zero))));
    }

    #[test]
    fn successor_algebra_maps_a_shared_run_without_visiting_its_nodes() {
        let arena = ValueArena::new();
        let env = Env::empty();
        let tail = arena.tm(TmClo::val(Rc::new(Val::Zero)));
        let program = shared_two_to_64();
        let head = Rc::new(Val::NatRun { program: Rc::clone(&program), tail });
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
        let zero = arena.tm(TmClo::val(Rc::new(Val::Zero)));
        let inner = arena.tm(TmClo::val(Rc::new(Val::NatRun {
            program: ContextProgram::run((), NonZeroU64::new(4).unwrap()),
            tail: zero,
        })));
        let head = Rc::new(Val::NatRun {
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
        let tail = arena.tm(TmClo::val(Rc::new(Val::Zero)));
        let head = Rc::new(Val::NatRun {
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
        let tail = arena.tm(TmClo::val(Rc::new(Val::Zero)));
        let head = Rc::new(Val::NatRun {
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
                ContextProgram::Compose { outer, inner } => go(outer, memo) + go(inner, memo),
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
        let tail = arena.tm(TmClo::val(Rc::new(Val::Zero)));
        let head = Rc::new(Val::NatRun { program: shared_two_to_64(), tail });
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
        let tail = arena.tm(TmClo::val(Rc::new(Val::Zero)));
        let left = Rc::new(Val::NatRun {
            program: ContextProgram::run((), NonZeroU64::new(u64::MAX).unwrap()),
            tail,
        });
        let right = arena.tm(TmClo::val(Rc::new(Val::NatRun {
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
        let tail = arena.tm(TmClo::val(Rc::new(Val::Zero)));
        let left = Rc::new(Val::NatRun { program: shared_two_to_64(), tail });
        let right = arena.tm(TmClo::val(Rc::new(Val::NatRun {
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
        let Term::App { fun, .. } = Rc::make_mut(inner) else { unreachable!() };
        *fun = Rc::new(Term::Var(LocalVar(0)));
        let arena = ValueArena::new();
        let closure = arena.tm(TmClo::syn(env, Rc::new(step)));
        let mut ev = Eval::new(64, Defs::opaque(), CtxBase::Nil, &arena);
        assert!(matches!(&*ev.classify_step(closure).unwrap(), FoldClass::Opaque));
    }

    /// A weak head `Nat` value's count, walking successors and runs through
    /// their tails; only a test may hold the whole number.
    fn nat_value<'v>(ev: &mut Eval<'_, 'v>, value: Rc<Val<'v>>) -> u128 {
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

    fn run_over_zero<'v>(arena: &'v ValueArena<'v>, count: u64) -> Rc<Val<'v>> {
        Rc::new(Val::NatRun {
            program: ContextProgram::run((), NonZeroU64::new(count).unwrap()),
            tail: arena.tm(TmClo::val(Rc::new(Val::Zero))),
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

    /// A step whose result sits on `k` rather than `ih` is not affine.
    #[test]
    fn a_step_returning_the_predecessor_is_opaque() {
        let arena = ValueArena::new();
        let env = Env::empty();
        let step = arena.tm(TmClo::syn(env, Rc::new(Term::Succ(Rc::new(Term::Var(LocalVar(1)))))));
        let mut ev = Eval::new(64, Defs::opaque(), CtxBase::Nil, &arena);
        assert!(matches!(&*ev.classify_step(step).unwrap(), FoldClass::Opaque));
        // A constant step is affine (a literal at every step): the fold is
        // that literal in one step.
        let step = arena.tm(TmClo::syn(env, Rc::new(Term::Succ(Rc::new(Term::Zero)))));
        assert!(matches!(&*ev.classify_step(step).unwrap(),
            FoldClass::Affine { tree: crate::value::algebra::AffineTree::Lit { .. }, uniform: true }));
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
        let x = arena.tm(TmClo::val(Rc::new(Val::var(0))));
        let head = Rc::new(Val::NatRun {
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
        let x = arena.tm(TmClo::val(Rc::new(Val::var(0))));
        let head = Rc::new(Val::NatRun {
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
