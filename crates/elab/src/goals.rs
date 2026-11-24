//! Declaration-local goals and their stable Ψ coordinates.
//!
//! A goal is both diagnostic state and a temporary global binding. Keeping
//! allocation, capacity discovery, speculative rollback, and world building
//! together makes their shared numbering invariant structural.

use std::cell::{Cell, RefCell};
use std::collections::HashMap;
use heather_kernel::rc::Rc;

use heather_kernel::layer::Layer;
use heather_kernel::level::Level;
use heather_kernel::subst::{GlobalEntry, GlobalSubst};
use heather_kernel::term::{
    CtxBase, GlobalBinding, GlobalCtx, GlobalVar, LocalCtx, LocalSubst, Term, Type,
};
use heather_syntax::Span;

use crate::{Cx, GoalReport, GoalSource, R, err};

/// Whether an application may turn its remaining implicit slots into goals.
pub(super) enum PromotionCapacity {
    Disabled,
    Ready,
    Restart,
}

#[derive(Clone)]
struct Goal {
    name: String,
    cx: Cx,
    ty: Type,
    level: Level,
    span: Span,
    origin: Option<(String, String)>,
    source: Option<GoalSource>,
    // Optional diagnostic spelling supplied from the original, unreduced type.
    // Never parsed or used for checking; the kernel goal remains `ty`.
    statement_spelling: Option<String>,
    state: GoalState,
}

impl Goal {
    /// Only an open hole is solved: `named` refuses a second discharge and
    /// `outstanding` lists only open slots, so a lifted slot never gets here.
    fn solve(&mut self, term: Term) {
        debug_assert!(self.state.is_open(), "goal `?{}` solved twice", self.name);
        self.state = GoalState::Solved(Rc::new(term));
    }
}

/// What a slot holds. The last two are *lifted*: solved when allocated,
/// never reported, and committed at the gate as globals of their own
/// (`GoalArena::lifted`) rather than substituted in.
#[derive(Clone)]
enum GoalState {
    /// A hole still waiting for its solution, reported if it stays so.
    Open,
    /// A hole solved by an `on` clause or a goal oracle, substituted into
    /// the declaration at the gate.
    Solved(Rc<Term>),
    /// A tactic's proof lifted into a lemma of its own
    /// (`docs/tactics/bv-omega-design.md` §6).
    Proved(Rc<Term>),
    /// A value a tactic names instead of spelling it at every use
    /// (`omega`'s atom list): a *definition* both while the declaration
    /// elaborates and once lifted, so conversion sees through it. The term is
    /// the value in the goal world; the [`Transparent`] holds it scoped in
    /// committed Ψ.
    Transparent(Rc<Term>, Transparent),
}

impl GoalState {
    /// The slot's term, whichever way it was solved.
    fn solution(&self) -> Option<&Rc<Term>> {
        match self {
            GoalState::Open => None,
            GoalState::Solved(term) | GoalState::Proved(term) | GoalState::Transparent(term, _) => Some(term),
        }
    }

    fn is_open(&self) -> bool {
        matches!(self, GoalState::Open)
    }

    fn transparent(&self) -> Option<&Transparent> {
        match self {
            GoalState::Transparent(_, named) => Some(named),
            _ => None,
        }
    }
}

/// A transparent slot's value scoped in committed Ψ, with its context and
/// type there.
#[derive(Clone)]
struct Transparent {
    psi_cx: LocalCtx,
    psi_ty: Rc<Type>,
    psi_body: Rc<Term>,
}

/// Where [`GoalArena::allocate_transparent`] put a value.
pub(super) enum Named {
    /// The slot's reference.
    Slot(Term),
    /// Nowhere: the caller keeps it inline.
    Inline,
    /// Nowhere, and the declaration will restart with more capacity.
    Restart,
}

/// A slot committed at the gate as a global of its own (`GoalArena::lifted`).
pub(super) struct Lifted {
    pub(super) slot: usize,
    pub(super) gamma: LocalCtx,
    pub(super) ty: Type,
    pub(super) level: Level,
    pub(super) body: Rc<Term>,
    /// A definition (`true`) rather than an opaque lemma.
    pub(super) transparent: bool,
}

/// All goal state whose lifetime is one ordinary declaration.
#[derive(Clone, Default)]
pub(super) struct GoalArena {
    base: u32,
    written_base: u32,
    promoted_seen: Cell<u32>,
    entries: RefCell<Vec<Goal>>,
    spans: RefCell<HashMap<(usize, usize, Option<String>), usize>>,
    requested_base: Cell<u32>,
    restart_enabled: Cell<bool>,
    frozen: Cell<bool>,
    /// The padded δ world with every transparent slot's body in place, built
    /// on demand from the elaborator's padded Ψ and dropped whenever a slot
    /// or that Ψ changes (`Self::delta_world`).
    delta_world: RefCell<Option<GlobalCtx>>,
    /// Each slot's binding as [`Self::world`] places it, for the slots
    /// `0..len` with a goal: slot `k`'s depends only on goal `k`, which never
    /// changes once pushed, so the cache grows with the goals and is cut back
    /// with them. Without it every goal oracle shifted every transparent
    /// slot's context, type and body again (a long `let` chain of `linarith`
    /// steps paid that per step, `issues/library-gate-module-cold-rail.md`).
    slot_bindings: RefCell<Vec<GlobalBinding>>,
    /// While a [`GoalCheckpoint`] is open: each in-place change to a goal
    /// that already existed (a solution, a statement spelling), with what it
    /// overwrote, so [`Self::restore`] can put it back. Goals pushed after
    /// the checkpoint need no entry — they are cut off whole.
    undo: RefCell<Vec<(usize, GoalState, Option<String>)>>,
    /// How many checkpoints are open; nothing is logged at zero.
    checkpoints: Cell<u32>,
    /// The copies of one block being elaborated, outermost first: a
    /// `split_all` leaf's case, an `induct` case's name. A written hole there
    /// is keyed by them as well as by its span, so one `?` under
    /// `all_goals` is one goal per case, each in its own context
    /// (issues/induct-case-goal-report.md).
    leaves: RefCell<Vec<String>>,
}

/// [`GoalArena::checkpoint`]'s answer: how many goals there were, how long
/// the undo log was, and every cell's value.
pub(super) struct GoalCheckpoint {
    len: usize,
    undo: usize,
    promoted_seen: u32,
    requested_base: u32,
    restart_enabled: bool,
    frozen: bool,
}

/// The one goal effect expression leaves may perform.
///
/// Keeping this as a view prevents expression elaboration from freezing,
/// rolling back, solving, or otherwise managing the declaration arena.
#[derive(Clone, Copy)]
pub(crate) struct GoalAllocator<'a> {
    arena: &'a GoalArena,
}

impl GoalAllocator<'_> {
    /// Allocate one source-written hole in the current local context.
    pub(crate) fn written_hole(
        self,
        cx: &Cx,
        name: Option<&str>,
        hint: Option<(&str, &str)>,
        ty: Type,
        level: Level,
        span: Span,
    ) -> R<Term> {
        self.arena
            .allocate(cx, name, hint, ty, level, span, None, None)
    }
}

impl GoalArena {
    /// Elaborate `f` as the copy of a block for one case, `key`: the written
    /// holes it meets are that case's goals ([`Self::leaves`]).
    pub(crate) fn in_leaf<T>(&self, key: String, f: impl FnOnce() -> T) -> T {
        self.leaves.borrow_mut().push(key);
        let out = f();
        self.leaves.borrow_mut().pop();
        out
    }

    pub(crate) fn allocator(&self) -> GoalAllocator<'_> {
        GoalAllocator { arena: self }
    }

    pub(super) fn prepare(&mut self) {
        self.requested_base.set(0);
        self.promoted_seen.set(0);
    }

    pub(super) fn clear(&mut self) {
        self.entries.get_mut().clear();
        self.spans.get_mut().clear();
        self.frozen.set(false);
        self.delta_world.get_mut().take();
        self.slot_bindings.get_mut().clear();
        self.undo.get_mut().clear();
    }

    /// The elaborator's padded Ψ moved: the δ world is rebuilt from the new
    /// one on next use.
    pub(super) fn invalidate_delta_world(&mut self) {
        self.delta_world.get_mut().take();
    }

    pub(super) fn finish(&mut self) {
        self.restart_enabled.set(false);
        self.base = 0;
        self.written_base = 0;
        self.clear();
    }

    pub(super) fn enable_restarts(&self) {
        self.restart_enabled.set(true);
    }

    pub(super) fn configure(&mut self, written: u32, reserved: u32) {
        self.written_base = written;
        self.base = written.max(reserved);
    }

    pub(super) fn base(&self) -> u32 {
        self.base
    }

    /// The capacity a restart has been asked for so far (0 for none).
    pub(super) fn requested_base(&self) -> u32 {
        self.requested_base.get()
    }

    /// Ask for a restart at `base` slots at least: how a probe that failed
    /// for want of capacity hands its request past its own rollback, which
    /// forgets it.
    pub(super) fn request_base(&self, base: u32) {
        if self.restart_enabled.get() {
            self.requested_base.set(self.requested_base.get().max(base));
        }
    }

    pub(super) fn take_requested_base(&self) -> u32 {
        self.requested_base.replace(0)
    }

    pub(super) fn reserve_promoted(&self, count: u32) -> PromotionCapacity {
        if !self.restart_enabled.get() {
            return PromotionCapacity::Disabled;
        }
        let total = self.promoted_seen.get() + count;
        self.promoted_seen.set(total);
        let needed = self.written_base + total;
        if needed > self.base {
            self.requested_base.set(self.requested_base.get().max(needed));
            PromotionCapacity::Restart
        } else {
            PromotionCapacity::Ready
        }
    }

    /// A rollback point for expression mechanisms that probe by elaborating.
    pub(super) fn mark(&self) -> usize {
        self.entries.borrow().len()
    }

    /// The rollback point of a speculative probe ([`crate::Elaborator::probe`]):
    /// [`Self::mark`], plus everything else a probe holding `&self` can
    /// change — a solution or spelling written into an existing goal, a
    /// restart request, the freeze. Must be [`Self::restore`]d, innermost
    /// first.
    pub(super) fn checkpoint(&self) -> GoalCheckpoint {
        self.checkpoints.set(self.checkpoints.get() + 1);
        GoalCheckpoint {
            len: self.mark(),
            undo: self.undo.borrow().len(),
            promoted_seen: self.promoted_seen.get(),
            requested_base: self.requested_base.get(),
            restart_enabled: self.restart_enabled.get(),
            frozen: self.frozen.get(),
        }
    }

    /// Put the arena back as it was at `checkpoint`. Whether the probe
    /// allocated a goal, which frees its slot for another one.
    pub(super) fn restore(&self, checkpoint: GoalCheckpoint) -> bool {
        let undone: Vec<_> = self.undo.borrow_mut().drain(checkpoint.undo..).collect();
        {
            let mut entries = self.entries.borrow_mut();
            for (index, state, spelling) in undone.into_iter().rev() {
                if let Some(goal) = entries.get_mut(index) {
                    goal.state = state;
                    goal.statement_spelling = spelling;
                }
            }
        }
        let allocated = self.entries.borrow().len() > checkpoint.len;
        if allocated {
            self.rollback(checkpoint.len);
        }
        self.promoted_seen.set(checkpoint.promoted_seen);
        self.requested_base.set(checkpoint.requested_base);
        self.restart_enabled.set(checkpoint.restart_enabled);
        self.frozen.set(checkpoint.frozen);
        self.checkpoints.set(self.checkpoints.get() - 1);
        allocated
    }

    /// Close `checkpoint` keeping everything done since it: the changes
    /// stay logged for a checkpoint still open outside it.
    pub(super) fn keep(&self, checkpoint: GoalCheckpoint) {
        let _ = checkpoint;
        self.checkpoints.set(self.checkpoints.get() - 1);
        if self.checkpoints.get() == 0 {
            self.undo.borrow_mut().clear();
        }
    }

    /// Log goal `index`'s state and spelling before it is changed in place,
    /// if a checkpoint is open.
    fn log_change(&self, goal: &Goal, index: usize) {
        if self.checkpoints.get() > 0 {
            self.undo.borrow_mut().push((index, goal.state.clone(), goal.statement_spelling.clone()));
        }
    }

    /// Discard every goal allocated after `mark`, including its source key.
    pub(super) fn rollback(&self, mark: usize) {
        let mut entries = self.entries.borrow_mut();
        if entries[mark.min(entries.len())..].iter().any(|goal| goal.state.transparent().is_some()) {
            self.delta_world.borrow_mut().take();
        }
        entries.truncate(mark);
        self.slot_bindings.borrow_mut().truncate(mark);
        self.spans.borrow_mut().retain(|_, index| *index < mark);
    }

    #[allow(clippy::too_many_arguments)]
    pub(super) fn allocate(
        &self,
        cx: &Cx,
        name: Option<&str>,
        hint: Option<(&str, &str)>,
        ty: Type,
        level: Level,
        span: Span,
        key: Option<&str>,
        promoted_parameter: Option<usize>,
    ) -> R<Term> {
        if self.frozen.get() {
            return err(
                "a hole may not appear in an `on` right-hand side — give it its own `on`",
                span,
            );
        }
        let leaf = self.leaves.borrow().join("/");
        let key = match key {
            None if !leaf.is_empty() => Some(format!("leaf:{leaf}")),
            key => key.map(str::to_string),
        };
        let in_leaf = !leaf.is_empty();
        let mut goals = self.entries.borrow_mut();
        let mut spans = self.spans.borrow_mut();
        let span_key = (span.start, span.end, key);
        let k = match spans.get(&span_key) {
            Some(&k) => {
                if goals[k].cx.gamma.entries.len() != cx.gamma.entries.len() {
                    return err(
                        "internal: a hole was re-elaborated in a different context",
                        span,
                    );
                }
                k
            }
            None => {
                let k = goals.len();
                if k as u32 >= self.base {
                    // A hole in a block copied to several cases is counted
                    // once; each further case asks for a slot by restarting
                    // the declaration, as a promoted parameter does.
                    if in_leaf && self.restart_enabled.get() {
                        self.request_base(k as u32 + 1);
                        return err("internal: restarting declaration to reserve a goal for each case of a copied block", span);
                    }
                    return err("internal: more goals than the pre-count reserved", span);
                }
                debug_assert!(
                    matches!(cx.gamma.base, CtxBase::Nil),
                    "a goal context must be closed"
                );
                let name = match name {
                    Some(name) => {
                        if in_leaf && goals.iter().any(|goal| goal.name == name) {
                            // The same named hole in another case: `?step`,
                            // `?step.1`, … in case order.
                            let mut ordinal = 1;
                            while goals.iter().any(|goal| goal.name == format!("{name}.{ordinal}")) {
                                ordinal += 1;
                            }
                            format!("{name}.{ordinal}")
                        } else if goals.iter().any(|goal| goal.name == name) {
                            return err(
                                format!(
                                    "hole `?{name}` is already used in this block; \
                                     each named hole is a distinct goal"
                                ),
                                span,
                            );
                        } else {
                            name.to_string()
                        }
                    }
                    None => {
                        let base = hint
                            .map(|(_, parameter)| parameter.to_string())
                            .unwrap_or_else(|| format!("g{}", k + 1));
                        let mut candidate = base.clone();
                        let mut ordinal = 0;
                        while goals.iter().any(|goal| goal.name == candidate) {
                            ordinal += 1;
                            candidate = format!("{base}.{ordinal}");
                        }
                        candidate
                    }
                };
                let origin =
                    hint.map(|(callee, parameter)| (callee.to_string(), parameter.to_string()));
                let source = hint.map(|(callee, parameter)| match promoted_parameter {
                    Some(parameter_index) => GoalSource::ApplyImplicit {
                        callee: callee.to_string(),
                        parameter: parameter.to_string(),
                        parameter_index,
                        apply_span: span,
                    },
                    None => GoalSource::Argument {
                        callee: callee.to_string(),
                        parameter: parameter.to_string(),
                    },
                });
                goals.push(Goal {
                    name,
                    cx: cx.clone(),
                    ty,
                    level,
                    span,
                    origin,
                    source,
                    statement_spelling: None,
                    state: GoalState::Open,
                });
                spans.insert(span_key, k);
                k
            }
        };
        Ok(Term::GlobalTm {
            var: GlobalVar::index(self.base - 1 - k as u32),
            subst: LocalSubst::id(&cx.gamma),
        })
    }

    /// Lift `proof : ty` in `cx` into a slot of its own, returning the slot's
    /// reference. `None` keeps the proof inline: no capacity reserved, a
    /// frozen arena, an open context, or the same site met again in another
    /// context.
    pub(super) fn allocate_proved(&self, tactic: &str, cx: &Cx, ty: Type, level: Level, proof: Term, span: Span) -> Option<Term> {
        if self.frozen.get() || !matches!(cx.gamma.base, CtxBase::Nil) {
            return None;
        }
        let mut goals = self.entries.borrow_mut();
        let mut spans = self.spans.borrow_mut();
        // One site can prove several statements (a `simp_only` discharger,
        // once per side condition): each its own slot, keyed by the slot.
        let same = goals.iter().position(|goal| {
            goal.span == span && matches!(goal.state, GoalState::Proved(_)) && goal.cx.gamma == cx.gamma && goal.ty == ty
        });
        let k = match same {
            Some(k) => k,
            None => {
                let key = (span.start, span.end, Some(format!("#proved{}", goals.len())));
                let k = goals.len();
                if k as u32 >= self.base {
                    return None;
                }
                goals.push(Goal {
                    // The tactic after the slot, for the reader
                    // ([`Self::slot_spelling`]).
                    name: format!("#proved{k}/{tactic}"),
                    cx: cx.clone(),
                    ty,
                    level,
                    span,
                    origin: None,
                    source: None,
                    statement_spelling: None,
                    state: GoalState::Proved(Rc::new(proof)),
                });
                spans.insert(key, k);
                k
            }
        };
        Some(Term::GlobalTm {
            var: GlobalVar::index(self.base - 1 - k as u32),
            subst: LocalSubst::id(&cx.gamma),
        })
    }

    /// Name `value : ty` in `cx` by a transparent slot of its own, returning
    /// the slot's reference; the same value in the same context is named
    /// once. `Inline` keeps the value where it is: a frozen arena, an open
    /// context, a value or context that mentions a goal (a definition's body
    /// must be scoped in committed Ψ), or no capacity left where restarts
    /// are off. Where they are on, running out requests one with more.
    pub(super) fn allocate_transparent(&self, cx: &Cx, ty: Type, level: Level, value: Term) -> Named {
        if self.frozen.get() || !matches!(cx.gamma.base, CtxBase::Nil) {
            return Named::Inline;
        }
        let mut goals = self.entries.borrow_mut();
        if let Some(k) = goals.iter().position(|goal| {
            matches!(&goal.state, GoalState::Transparent(named, _) if **named == value)
                && goal.ty == ty
                && goal.cx.gamma == cx.gamma
        }) {
            return Named::Slot(self.reference(k, &cx.gamma));
        }
        let k = goals.len();
        if k as u32 >= self.base {
            if !self.restart_enabled.get() {
                return Named::Inline;
            }
            // Doubling: the attempt stops at the first slot it cannot have,
            // so the ones after it are not counted yet.
            self.requested_base.set(self.requested_base.get().max(2 * self.base + 1));
            return Named::Restart;
        }
        // Out of the goal world into committed Ψ: any goal reference would
        // tell the two dummies apart.
        let out = |dummy: Term| GlobalSubst { entries: (0..self.base).map(|_| GlobalEntry::Tm(Rc::new(dummy.clone()))).collect() };
        let (zero, one) = (out(Term::Zero), out(Term::Succ(Rc::new(Term::Zero))));
        let into = |sigma: &GlobalSubst| (cx.gamma.apply_global(sigma), ty.apply_global(sigma), value.apply_global(sigma));
        let (psi_cx, psi_ty, psi_body) = into(&zero);
        if (psi_cx.clone(), psi_ty.clone(), psi_body.clone()) != into(&one) {
            return Named::Inline;
        }
        goals.push(Goal {
            name: format!("#named{k}"),
            cx: cx.clone(),
            ty,
            level,
            span: Span { start: 0, end: 0 },
            origin: None,
            source: None,
            statement_spelling: None,
            state: GoalState::Transparent(
                Rc::new(value),
                Transparent { psi_cx, psi_ty: Rc::new(psi_ty), psi_body: Rc::new(psi_body) },
            ),
        });
        self.delta_world.borrow_mut().take();
        Named::Slot(self.reference(k, &cx.gamma))
    }

    /// A restart has been requested: this attempt is discarded whatever it
    /// returns, so it need not reach the kernel.
    pub(super) fn restart_requested(&self) -> bool {
        self.requested_base.get() > self.base
    }

    fn reference(&self, k: usize, gamma: &LocalCtx) -> Term {
        Term::GlobalTm { var: GlobalVar::index(self.base - 1 - k as u32), subst: LocalSubst::id(gamma) }
    }

    /// Slot `k`'s binding as a definition, scoped in committed Ψ followed by
    /// the `k` slots before it.
    fn definition(&self, k: usize, level: &Level, named: &Transparent) -> GlobalBinding {
        GlobalBinding::Tm {
            ctx: named.psi_cx.shift_global(k as u32),
            layer: Layer::Code,
            ty: Rc::new(named.psi_ty.shift_global(k as u32)),
            level: level.clone(),
            body: Some(Rc::new(named.psi_body.shift_global(k as u32))),
        }
    }

    /// `padded` (committed Ψ followed by one placeholder per slot) with each
    /// transparent slot's definition in place, or `None` when there is none.
    pub(super) fn delta_world(&self, padded: &GlobalCtx) -> Option<GlobalCtx> {
        if let Some(world) = self.delta_world.borrow().as_ref() {
            return Some(world.clone());
        }
        let goals = self.entries.borrow();
        if goals.iter().all(|goal| goal.state.transparent().is_none()) {
            return None;
        }
        let committed = padded.bindings.len() - self.base as usize;
        let world = padded.prefix(committed).extended((0..self.base as usize).map(|k| match goals.get(k) {
            Some(Goal { state: GoalState::Transparent(_, named), level, .. }) => self.definition(k, level, named),
            _ => padded.bindings[committed + k].clone(),
        }));
        *self.delta_world.borrow_mut() = Some(world.clone());
        Some(world)
    }

    /// The slots committed at the gate as globals of their own, in slot
    /// order: the lifted proofs and the transparent values. Everything is
    /// scoped in the goal world.
    pub(super) fn lifted(&self) -> Vec<Lifted> {
        self.entries
            .borrow()
            .iter()
            .enumerate()
            .filter_map(|(slot, goal)| {
                let (body, transparent) = match &goal.state {
                    GoalState::Proved(body) => (body, false),
                    GoalState::Transparent(body, _) => (body, true),
                    GoalState::Open | GoalState::Solved(_) => return None,
                };
                Some(Lifted {
                    slot,
                    gamma: goal.cx.gamma.clone(),
                    ty: goal.ty.clone(),
                    level: goal.level.clone(),
                    body: body.clone(),
                    transparent,
                })
            })
            .collect()
    }

    pub(super) fn freeze(&self) {
        self.frozen.set(true);
    }

    pub(super) fn named(&self, name: &str, span: Span) -> R<(Cx, Type, Level)> {
        let goals = self.entries.borrow();
        let Some(goal) = goals.iter().find(|goal| goal.name == name) else {
            let known: Vec<&str> = goals.iter().map(|goal| goal.name.as_str()).collect();
            return err(
                if known.is_empty() {
                    format!("no goal `?{name}` — this block raises none")
                } else {
                    format!(
                        "no goal `?{name}` in this block; it raises: ?{}",
                        known.join(", ?")
                    )
                },
                span,
            );
        };
        if !goal.state.is_open() {
            return err(format!("goal `?{name}` is discharged twice"), span);
        }
        Ok((goal.cx.clone(), goal.ty.clone(), goal.level.clone()))
    }

    /// How a reader is shown a reference to slot `k`
    /// (`display::Speller::goal_slot`): a lifted proof by the tactic that
    /// found it (`bv_omega` and a written `omega` lift theirs, `checking.rs`), a goal by its
    /// name. A named value (`omega`'s atom list) and the padding past the
    /// allocated slots have no spelling.
    pub(super) fn slot_spelling(&self, k: usize) -> Option<String> {
        if k as u32 >= self.base {
            return None;
        }
        let goals = self.entries.try_borrow().ok()?;
        let goal = goals.get(k)?;
        match &goal.state {
            GoalState::Proved(_) => goal.name.rsplit_once('/').map(|(_, tactic)| tactic.to_string()),
            GoalState::Open | GoalState::Solved(_) => Some(format!("?{}", goal.name)),
            GoalState::Transparent(..) => None,
        }
    }

    pub(super) fn outstanding(&self) -> Vec<(usize, Cx, Type, Level)> {
        self.entries
            .borrow()
            .iter()
            .enumerate()
            .filter(|(_, goal)| goal.state.is_open())
            .map(|(index, goal)| (index, goal.cx.clone(), goal.ty.clone(), goal.level.clone()))
            .collect()
    }

    pub(super) fn solve_named(&self, name: &str, term: Term) {
        let mut goals = self.entries.borrow_mut();
        let index = goals
            .iter()
            .position(|goal| goal.name == name)
            .expect("goal was selected before its solution was elaborated");
        self.log_change(&goals[index], index);
        goals[index].solve(term);
    }

    pub(super) fn solve(&self, index: usize, term: Term) {
        let mut goals = self.entries.borrow_mut();
        self.log_change(&goals[index], index);
        goals[index].solve(term);
    }

    pub(super) fn set_statement_spelling(&self, span: Span, key: &str, spelling: String) {
        let spans = self.spans.borrow();
        if let Some(&index) = spans.get(&(span.start, span.end, Some(key.to_owned()))) {
            let mut goals = self.entries.borrow_mut();
            self.log_change(&goals[index], index);
            goals[index].statement_spelling = Some(spelling);
        }
    }

    pub(super) fn reports(&self, mut display: impl FnMut(&Cx, &Type) -> String) -> Vec<GoalReport> {
        self.entries
            .borrow()
            .iter()
            .filter(|goal| goal.state.is_open())
            .map(|goal| {
                let statement = goal
                    .statement_spelling
                    .clone()
                    .unwrap_or_else(|| display(&goal.cx, &goal.ty));
                // What each name means at the goal: a binder or alias that a
                // later one of the same name shadows is not listed, so a
                // local a split or a case re-bound shows once, at its
                // re-bound type. Aliases are listed after the binders.
                let names: Vec<&str> = goal.cx.names.iter().collect();
                let aliases: Vec<_> = goal.cx.aliases.iter().collect();
                let mut context: Vec<(String, String)> = Vec::new();
                for (i, (name, entry)) in names.iter().zip(&goal.cx.gamma.entries).enumerate() {
                    let shadowed = names[i + 1..].contains(name)
                        || aliases.iter().any(|a| a.name == *name && a.depth > i);
                    if !name.starts_with('#') && !shadowed {
                        let mut shown = display(&goal.cx.prefix(i), &entry.ty);
                        // A hypothesis an enclosing match refined is usable
                        // at its type as written too, which is said here or
                        // nowhere (docs/language/matching/arm-readings-design.md).
                        if let Some(from) = crate::readings::Readings::written_position(&goal.cx, i)
                            && let Some(outer) = goal.cx.gamma.entries.get(from)
                        {
                            let written = display(&goal.cx.prefix(from), &outer.ty);
                            if written != shown {
                                shown = format!("{shown}   (or as written: {written})");
                            }
                        }
                        context.push((name.to_string(), shown));
                    }
                }
                for (k, alias) in aliases.iter().enumerate() {
                    let shadowed = aliases[k + 1..].iter().any(|b| b.name == alias.name)
                        || names.iter().skip(alias.depth).any(|n| *n == alias.name);
                    if !alias.name.starts_with('#') && !shadowed {
                        context.push((
                            alias.name.clone(),
                            display(&goal.cx.prefix(alias.depth), &alias.ty),
                        ));
                    }
                }
                GoalReport {
                    name: goal.name.clone(),
                    statement,
                    context,
                    origin: goal.origin.as_ref().map(|(callee, parameter)| {
                        format!("the `{parameter}` parameter of `{callee}`")
                    }),
                    source: goal.source.clone(),
                    span: goal.span,
                }
            })
            .collect()
    }

    /// Ψ as goal statements see it, including reserved-but-unused slots.
    pub(super) fn world(&self, psi: &GlobalCtx, meta_pushed: &[GlobalBinding]) -> GlobalCtx {
        if !meta_pushed.is_empty() {
            return psi.extended(meta_pushed.iter().cloned());
        }
        if self.base == 0 {
            return psi.clone();
        }
        let goals = self.entries.borrow();
        let mut slots = self.slot_bindings.borrow_mut();
        for k in slots.len()..goals.len() {
            let goal = &goals[k];
            slots.push(match goal.state.transparent() {
                Some(named) => self.definition(k, &goal.level, named),
                None => GlobalBinding::Tm {
                    ctx: goal.cx.gamma.clone(),
                    layer: Layer::Code,
                    ty: Rc::new(goal.ty.clone()),
                    level: goal.level.clone(),
                    body: None,
                },
            });
        }
        psi.extended((0..self.base as usize).map(|k| slots.get(k).cloned().unwrap_or_else(placeholder)))
    }

    /// One entry per slot: a discharged goal's solution strengthened out of
    /// the goal world ([`crate::strengthen_global`]), a lifted slot's term
    /// as it stands (the gate replaces it by a reference to the global it
    /// commits), and `0` for the padding. A discharge that mentions a lifted
    /// slot is re-scoped by the gate from [`Self::discharged`].
    pub(super) fn substitution(&self) -> GlobalSubst {
        let goals = self.entries.borrow();
        let entries = (0..self.base as usize)
            .map(|k| {
                GlobalEntry::Tm(match goals.get(k).map(|goal| &goal.state) {
                    Some(GoalState::Solved(t)) => Rc::new(crate::strengthen_global(t, self.base)),
                    Some(state) => state.solution().cloned().unwrap_or_else(|| Rc::new(Term::Zero)),
                    None => Rc::new(Term::Zero),
                })
            })
            .collect();
        GlobalSubst { entries }
    }

    /// The discharged goals, each with its solution in the goal world.
    pub(super) fn discharged(&self) -> Vec<(usize, Term)> {
        self.entries
            .borrow()
            .iter()
            .enumerate()
            .filter_map(|(slot, goal)| match &goal.state {
                GoalState::Solved(t) => Some((slot, (**t).clone())),
                _ => None,
            })
            .collect()
    }
}

fn placeholder() -> GlobalBinding {
    GlobalBinding::Tm {
        ctx: LocalCtx::nil(),
        layer: Layer::Code,
        ty: Rc::new(Type::Nat),
        level: Level::Zero,
        body: None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const SPAN: Span = Span { start: 2, end: 3 };

    #[test]
    fn promoted_capacity_requests_one_stable_prefix() {
        let mut arena = GoalArena::default();
        arena.enable_restarts();
        arena.configure(2, 2);

        assert!(matches!(
            arena.reserve_promoted(3),
            PromotionCapacity::Restart
        ));
        assert_eq!(arena.take_requested_base(), 5);

        arena.clear();
        arena.prepare();
        arena.configure(2, 5);
        assert!(matches!(
            arena.reserve_promoted(3),
            PromotionCapacity::Ready
        ));
        assert_eq!(arena.take_requested_base(), 0);
    }

    #[test]
    fn rollback_removes_goal_and_its_stable_source_identity() {
        let mut arena = GoalArena::default();
        arena.configure(2, 0);
        let cx = Cx::empty();
        let first = arena
            .allocate(
                &cx,
                Some("first"),
                None,
                Type::Nat,
                Level::Zero,
                SPAN,
                None,
                None,
            )
            .unwrap();
        let mark = arena.mark();
        arena
            .allocate(
                &cx,
                Some("discarded"),
                None,
                Type::Nat,
                Level::Zero,
                Span { start: 4, end: 5 },
                None,
                None,
            )
            .unwrap();

        arena.rollback(mark);
        let replacement = arena
            .allocate(
                &cx,
                Some("replacement"),
                None,
                Type::Nat,
                Level::Zero,
                Span { start: 4, end: 5 },
                None,
                None,
            )
            .unwrap();

        assert!(matches!(
            first,
            Term::GlobalTm { var, .. } if var == GlobalVar::index(1)
        ));
        assert!(matches!(
            replacement,
            Term::GlobalTm { var, .. } if var == GlobalVar::index(0)
        ));
    }

    #[test]
    fn checkpoint_restores_solutions_allocations_and_cells() {
        let mut arena = GoalArena::default();
        arena.configure(3, 0);
        let cx = Cx::empty();
        let hole = |name: &str, start: usize| {
            arena
                .allocate(&cx, Some(name), None, Type::Nat, Level::Zero, Span { start, end: start + 1 }, None, None)
                .unwrap()
        };
        hole("kept", 0);
        let outer = arena.checkpoint();
        arena.solve(0, Term::Zero);
        hole("probed", 2);
        let inner = arena.checkpoint();
        arena.solve(1, Term::Zero);
        arena.freeze();
        assert!(!arena.restore(inner));
        assert_eq!(arena.outstanding().len(), 1, "the inner solution is undone, the outer one stays");
        assert!(arena.restore(outer));
        assert_eq!(arena.mark(), 1);
        assert_eq!(arena.outstanding().len(), 1, "the outer solution is undone");
        assert!(arena.undo.borrow().is_empty());
        assert_eq!(arena.checkpoints.get(), 0);
        // Unfrozen, and the probed hole's source key is free again.
        hole("again", 2);
        assert_eq!(arena.mark(), 2);
    }
}
