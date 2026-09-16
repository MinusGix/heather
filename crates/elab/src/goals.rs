//! Declaration-local goals and their stable Ψ coordinates.
//!
//! A goal is both diagnostic state and a temporary global binding. Keeping
//! allocation, capacity discovery, speculative rollback, and world building
//! together makes their shared numbering invariant structural.

use std::cell::{Cell, RefCell};
use std::collections::HashMap;
use std::sync::Arc as Rc;

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
    solution: Option<Rc<Term>>,
    // Optional diagnostic spelling supplied from the original, unreduced type.
    // Never parsed or used for checking; the kernel goal remains `ty`.
    statement_spelling: Option<String>,
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
            self.requested_base.set(needed);
            PromotionCapacity::Restart
        } else {
            PromotionCapacity::Ready
        }
    }

    /// A rollback point for expression mechanisms that probe by elaborating.
    pub(super) fn mark(&self) -> usize {
        self.entries.borrow().len()
    }

    /// Discard every goal allocated after `mark`, including its source key.
    pub(super) fn rollback(&self, mark: usize) {
        self.entries.borrow_mut().truncate(mark);
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
        let mut goals = self.entries.borrow_mut();
        let mut spans = self.spans.borrow_mut();
        let span_key = (span.start, span.end, key.map(str::to_string));
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
                    return err("internal: more goals than the pre-count reserved", span);
                }
                debug_assert!(
                    matches!(cx.gamma.base, CtxBase::Nil),
                    "a goal context must be closed"
                );
                let name = match name {
                    Some(name) => {
                        if goals.iter().any(|goal| goal.name == name) {
                            return err(
                                format!(
                                    "hole `?{name}` is already used in this block; \
                                     each named hole is a distinct goal"
                                ),
                                span,
                            );
                        }
                        name.to_string()
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
                    solution: None,
                    statement_spelling: None,
                });
                spans.insert(span_key, k);
                k
            }
        };
        Ok(Term::GlobalTm {
            var: GlobalVar(self.base - 1 - k as u32),
            subst: LocalSubst::id(&cx.gamma),
        })
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
        if goal.solution.is_some() {
            return err(format!("goal `?{name}` is discharged twice"), span);
        }
        Ok((goal.cx.clone(), goal.ty.clone(), goal.level.clone()))
    }

    pub(super) fn outstanding(&self) -> Vec<(usize, Cx, Type, Level)> {
        self.entries
            .borrow()
            .iter()
            .enumerate()
            .filter(|(_, goal)| goal.solution.is_none())
            .map(|(index, goal)| (index, goal.cx.clone(), goal.ty.clone(), goal.level.clone()))
            .collect()
    }

    pub(super) fn solve_named(&self, name: &str, term: Term) {
        let mut goals = self.entries.borrow_mut();
        let goal = goals
            .iter_mut()
            .find(|goal| goal.name == name)
            .expect("goal was selected before its solution was elaborated");
        goal.solution = Some(Rc::new(term));
    }

    pub(super) fn solve(&self, index: usize, term: Term) {
        self.entries.borrow_mut()[index].solution = Some(Rc::new(term));
    }

    pub(super) fn set_statement_spelling(&self, span: Span, key: &str, spelling: String) {
        let spans = self.spans.borrow();
        if let Some(&index) = spans.get(&(span.start, span.end, Some(key.to_owned()))) {
            self.entries.borrow_mut()[index].statement_spelling = Some(spelling);
        }
    }

    pub(super) fn reports(&self, mut display: impl FnMut(&Cx, &Type) -> String) -> Vec<GoalReport> {
        self.entries
            .borrow()
            .iter()
            .filter(|goal| goal.solution.is_none())
            .map(|goal| {
                let statement = goal
                    .statement_spelling
                    .clone()
                    .unwrap_or_else(|| display(&goal.cx, &goal.ty));
                let mut context = Vec::new();
                for (i, (name, entry)) in
                    goal.cx.names.iter().zip(&goal.cx.gamma.entries).enumerate()
                {
                    if !name.starts_with('#') {
                        context.push((name.clone(), display(&goal.cx.prefix(i), &entry.ty)));
                    }
                }
                for alias in &goal.cx.aliases {
                    context.push((
                        alias.name.clone(),
                        display(&goal.cx.prefix(alias.depth), &alias.ty),
                    ));
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
    pub(super) fn world(
        &self,
        psi: &GlobalCtx,
        meta_pushed: &[GlobalBinding],
        mints: &[GlobalBinding],
    ) -> GlobalCtx {
        if !meta_pushed.is_empty() {
            let mut bindings = psi.bindings.to_vec();
            bindings.extend(meta_pushed.iter().cloned());
            return GlobalCtx::new(bindings);
        }
        if self.base == 0 && mints.is_empty() {
            return psi.clone();
        }
        let goals = self.entries.borrow();
        let mut bindings = psi.bindings.to_vec();
        // The mint block, **below** the goal block: with it there, goal `k` is
        // still `GlobalVar(goal_base − 1 − k)` and only the padding total
        // moves (`crate::mint`).
        bindings.extend(mints.iter().cloned());
        for k in 0..self.base as usize {
            bindings.push(match goals.get(k) {
                Some(goal) => GlobalBinding::Tm {
                    ctx: goal.cx.gamma.clone(),
                    layer: Layer::Code,
                    ty: Rc::new(goal.ty.clone()),
                    level: goal.level.clone(),
                    body: None,
                },
                None => placeholder(),
            });
        }
        GlobalCtx::new(bindings)
    }

    pub(super) fn substitution(&self) -> GlobalSubst {
        let goals = self.entries.borrow();
        let entries = (0..self.base as usize)
            .map(|k| {
                GlobalEntry::Tm(
                    goals
                        .get(k)
                        .and_then(|goal| goal.solution.clone())
                        .unwrap_or_else(|| Rc::new(Term::Zero)),
                )
            })
            .collect();
        GlobalSubst { entries }
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
            Term::GlobalTm {
                var: GlobalVar(1),
                ..
            }
        ));
        assert!(matches!(
            replacement,
            Term::GlobalTm {
                var: GlobalVar(0),
                ..
            }
        ));
    }
}
