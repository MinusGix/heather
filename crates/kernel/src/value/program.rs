//! Succinct programs for repeated one-hole constructor contexts.
//!
//! A program denotes a context, not a materialized constructor tree.  `Run`
//! stores at most `u64::MAX` repetitions; overflowing adjacent runs remain a
//! shared `Compose` instead of growing an unbounded counter.  Nothing here
//! knows which inductive or constructor a context belongs to.

use std::collections::HashMap;
use std::fmt;
use std::num::NonZeroU64;
use std::rc::Rc;

use crate::fmt::node;

/// A shared straight-line program for one-hole constructor contexts.
pub enum ContextProgram<C> {
    Run { context: C, count: NonZeroU64 },
    /// `outer(inner[-])`.
    Compose { outer: Rc<ContextProgram<C>>, inner: Rc<ContextProgram<C>> },
}

/// Residual programs after cancelling an equal outer prefix.
pub struct CancelledPrefix<C> {
    pub left: Option<Rc<ContextProgram<C>>>,
    pub right: Option<Rc<ContextProgram<C>>>,
    pub changed: bool,
    /// Unique program-pair and cursor nodes inspected. Callers charge this
    /// against their ordinary reduction/conversion budget.
    pub inspected: u64,
}

/// The caller's bound was reached before cancellation could justify a
/// residual. This is exhaustion, not evidence that the programs differ.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CancellationExhausted;

struct InspectionBudget {
    remaining: u64,
    inspected: u64,
}

impl InspectionBudget {
    fn new(limit: u64) -> Self {
        Self { remaining: limit, inspected: 0 }
    }

    fn spend(&mut self) -> Result<(), CancellationExhausted> {
        if self.remaining == 0 {
            return Err(CancellationExhausted);
        }
        self.remaining -= 1;
        self.inspected += 1;
        Ok(())
    }
}

type ProgramPair = (usize, usize);

/// A bounded sufficient equivalence test for two independently allocated
/// program DAGs with the same sharing construction. Pair memoization makes a
/// depth-N doubling DAG cost O(N), not O(2^N). A shape mismatch is merely
/// `false`: the cursor can still find denotationally equal prefixes across
/// different associations and run boundaries.
struct Bisimulation<C> {
    memo: HashMap<ProgramPair, bool>,
    retained: Vec<Rc<ContextProgram<C>>>,
}

impl<C: Clone + Eq> Bisimulation<C> {
    fn new() -> Self {
        Self { memo: HashMap::new(), retained: Vec::new() }
    }

    fn key(left: &Rc<ContextProgram<C>>, right: &Rc<ContextProgram<C>>) -> ProgramPair {
        // The memo retains both nodes for every inserted key, so allocator
        // reuse cannot alias it. Addresses are identity tokens only; they are
        // never dereferenced.
        (Rc::as_ptr(left) as usize, Rc::as_ptr(right) as usize)
    }

    fn equivalent(
        &mut self,
        left: &Rc<ContextProgram<C>>,
        right: &Rc<ContextProgram<C>>,
        budget: &mut InspectionBudget,
    ) -> Result<bool, CancellationExhausted> {
        if ContextProgram::equivalent_fast(left, right) {
            return Ok(true);
        }

        enum Visit<C> {
            Enter(Rc<ContextProgram<C>>, Rc<ContextProgram<C>>),
            Finish(ProgramPair, ProgramPair, ProgramPair),
        }

        let root = Self::key(left, right);
        if let Some(result) = self.memo.get(&root) {
            return Ok(*result);
        }
        let mut work = vec![Visit::Enter(Rc::clone(left), Rc::clone(right))];
        while let Some(visit) = work.pop() {
            match visit {
                Visit::Enter(left, right) => {
                    let key = Self::key(&left, &right);
                    if self.memo.contains_key(&key) {
                        continue;
                    }
                    if ContextProgram::equivalent_fast(&left, &right) {
                        self.retained.extend([Rc::clone(&left), Rc::clone(&right)]);
                        self.memo.insert(key, true);
                        continue;
                    }
                    budget.spend()?;
                    self.retained.extend([Rc::clone(&left), Rc::clone(&right)]);
                    match (&*left, &*right) {
                        (
                            ContextProgram::Run { context: lc, count: ln },
                            ContextProgram::Run { context: rc, count: rn },
                        ) => {
                            self.memo.insert(key, lc == rc && ln == rn);
                        }
                        (
                            ContextProgram::Compose { outer: lo, inner: li },
                            ContextProgram::Compose { outer: ro, inner: ri },
                        ) => {
                            let outer = Self::key(lo, ro);
                            let inner = Self::key(li, ri);
                            work.push(Visit::Finish(key, outer, inner));
                            if !self.memo.contains_key(&inner) {
                                work.push(Visit::Enter(Rc::clone(li), Rc::clone(ri)));
                            }
                            if !self.memo.contains_key(&outer) {
                                work.push(Visit::Enter(Rc::clone(lo), Rc::clone(ro)));
                            }
                        }
                        _ => {
                            self.memo.insert(key, false);
                        }
                    }
                }
                Visit::Finish(key, outer, inner) => {
                    let result = self.memo.get(&outer).copied().unwrap_or(false)
                        && self.memo.get(&inner).copied().unwrap_or(false);
                    self.memo.insert(key, result);
                }
            }
        }
        Ok(self.memo.get(&root).copied().unwrap_or(false))
    }
}

struct Cursor<C> {
    pending: Vec<Rc<ContextProgram<C>>>,
    run: Option<(C, NonZeroU64)>,
}

impl<C: Clone + Eq> Cursor<C> {
    fn new(program: Rc<ContextProgram<C>>) -> Self {
        Self { pending: vec![program], run: None }
    }

    fn front(&self) -> Option<&Rc<ContextProgram<C>>> {
        if self.run.is_none() { self.pending.last() } else { None }
    }

    fn pop_front(&mut self) {
        debug_assert!(self.run.is_none());
        self.pending.pop();
    }

    fn step(&mut self, budget: &mut InspectionBudget) -> Result<(), CancellationExhausted> {
        if self.run.is_some() {
            return Ok(());
        }
        let Some(program) = self.pending.pop() else { return Ok(()) };
        budget.spend()?;
        match &*program {
            ContextProgram::Run { context, count } => {
                self.run = Some((context.clone(), *count));
            }
            ContextProgram::Compose { outer, inner } => {
                self.pending.push(Rc::clone(inner));
                self.pending.push(Rc::clone(outer));
            }
        }
        Ok(())
    }

    fn consume(&mut self, count: u64) {
        let (_, old) = self.run.as_ref().expect("consume follows next");
        self.run = NonZeroU64::new(old.get() - count)
            .map(|rest| (self.run.as_ref().unwrap().0.clone(), rest));
    }

    fn remainder(mut self) -> Option<Rc<ContextProgram<C>>> {
        let mut pieces = Vec::with_capacity(self.pending.len() + usize::from(self.run.is_some()));
        if let Some((context, count)) = self.run.take() {
            pieces.push(ContextProgram::run(context, count));
        }
        while let Some(piece) = self.pending.pop() {
            pieces.push(piece);
        }
        let mut pieces = pieces.into_iter().rev();
        let mut result = pieces.next()?;
        for outer in pieces {
            result = ContextProgram::compose(outer, result);
        }
        Some(result)
    }

    fn exhausted(&self) -> bool {
        self.run.is_none() && self.pending.is_empty()
    }
}

impl<C: fmt::Debug> fmt::Debug for ContextProgram<C> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        node(f, |f| match self {
            ContextProgram::Run { context, count } => {
                write!(f, "run({context:?}; {count})")
            }
            ContextProgram::Compose { outer, inner } => {
                write!(f, "compose({outer:?}; {inner:?})")
            }
        })
    }
}

impl<C: Clone + Eq> ContextProgram<C> {
    pub fn run(context: C, count: NonZeroU64) -> Rc<Self> {
        Rc::new(ContextProgram::Run { context, count })
    }

    /// Put `count` copies of `context` outside `inner`, merging one adjacent
    /// run only when its `u64` count does not overflow.
    pub fn prepend(context: C, count: NonZeroU64, inner: Rc<Self>) -> Rc<Self> {
        if let ContextProgram::Run { context: next, count: n } = &*inner {
            if *next == context {
                if let Some(sum) = count.get().checked_add(n.get()) {
                    return Self::run(context, NonZeroU64::new(sum).unwrap());
                }
            }
        }
        Rc::new(ContextProgram::Compose {
            outer: Self::run(context, count),
            inner,
        })
    }

    pub fn compose(outer: Rc<Self>, inner: Rc<Self>) -> Rc<Self> {
        Rc::new(ContextProgram::Compose { outer, inner })
    }

    /// A cheap sufficient test that two programs denote the same context.
    /// Object identity remains the broadest constant-time case; independently
    /// allocated runs are just as easy because their whole denotation is the
    /// pair `(context, count)`. The composed case deliberately stops at shared
    /// children rather than walking a potentially exponential DAG.
    pub fn equivalent_fast(left: &Rc<Self>, right: &Rc<Self>) -> bool {
        Rc::ptr_eq(left, right)
            || match (&**left, &**right) {
                (
                    ContextProgram::Run { context: lc, count: ln },
                    ContextProgram::Run { context: rc, count: rn },
                ) => lc == rc && ln == rn,
                (
                    ContextProgram::Compose { outer: lo, inner: li },
                    ContextProgram::Compose { outer: ro, inner: ri },
                ) => Rc::ptr_eq(lo, ro) && Rc::ptr_eq(li, ri),
                _ => false,
            }
    }

    /// Cancel an equal sequence of outer contexts without visiting its
    /// represented constructor nodes. Bisimilar DAG fronts are skipped by
    /// unique node pairs; the fallback walk is over run/composition fragments.
    /// Residual fragments retain the original shared subprograms. A differing
    /// context is a hard boundary, not a claim about it. All structural work
    /// shares `inspection_limit`; exhaustion returns no verdict or residual.
    pub fn cancel_matching_prefix(
        left: Rc<Self>,
        right: Rc<Self>,
        inspection_limit: u64,
    ) -> Result<CancelledPrefix<C>, CancellationExhausted> {
        let mut budget = InspectionBudget::new(inspection_limit);
        if Self::equivalent_fast(&left, &right) {
            return Ok(CancelledPrefix {
                left: None,
                right: None,
                changed: true,
                inspected: 0,
            });
        }
        let mut left = Cursor::new(left);
        let mut right = Cursor::new(right);
        let mut bisimulation = Bisimulation::new();
        let mut changed = false;
        loop {
            while left.run.is_none() && right.run.is_none() {
                let (Some(l), Some(r)) = (left.front(), right.front()) else {
                    break;
                };
                if !bisimulation.equivalent(l, r, &mut budget)? {
                    break;
                }
                left.pop_front();
                right.pop_front();
                changed = true;
            }
            if left.run.is_none() && !left.exhausted() {
                left.step(&mut budget)?;
            }
            if right.run.is_none() && !right.exhausted() {
                right.step(&mut budget)?;
            }
            if (left.run.is_none() && !left.exhausted())
                || (right.run.is_none() && !right.exhausted())
            {
                continue;
            }
            let (Some((lc, ln)), Some((rc, rn))) = (left.run.clone(), right.run.clone()) else {
                break;
            };
            if lc != rc {
                break;
            }
            let count = ln.get().min(rn.get());
            left.consume(count);
            right.consume(count);
            changed = true;
        }
        Ok(CancelledPrefix {
            left: left.remainder(),
            right: right.remainder(),
            changed,
            inspected: budget.inspected,
        })
    }

    /// The outer constructor and a shared program for everything beneath it.
    /// `None` for the remainder means the caller has reached the program's
    /// hole. The rebuilding walk is iterative so a hostile composition spine
    /// does not consume the native stack.
    pub fn uncons(program: &Rc<Self>) -> (&C, Option<Rc<Self>>) {
        let mut current = program;
        let mut inners = Vec::new();
        loop {
            match &**current {
                ContextProgram::Run { context, count } => {
                    let mut rest = NonZeroU64::new(count.get() - 1)
                        .map(|n| Self::run(context.clone(), n));
                    while let Some(inner) = inners.pop() {
                        rest = Some(match rest {
                            Some(outer) => Self::compose(outer, inner),
                            None => inner,
                        });
                    }
                    return (context, rest);
                }
                ContextProgram::Compose { outer, inner } => {
                    inners.push(Rc::clone(inner));
                    current = outer;
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::ContextProgram;
    use std::num::NonZeroU64;
    use std::rc::Rc;

    fn n(value: u64) -> NonZeroU64 {
        NonZeroU64::new(value).unwrap()
    }

    fn doubling(context: char, depth: u32) -> Rc<ContextProgram<char>> {
        let mut program = ContextProgram::run(context, n(1));
        for _ in 0..depth {
            program = ContextProgram::compose(Rc::clone(&program), program);
        }
        program
    }

    #[test]
    fn adjacent_runs_merge_until_the_u64_boundary() {
        let two = ContextProgram::run('s', n(2));
        let five = ContextProgram::prepend('s', n(3), two);
        assert!(matches!(&*five, ContextProgram::Run { count, .. } if count.get() == 5));

        let full = ContextProgram::run('s', n(u64::MAX));
        let two_to_64 = ContextProgram::prepend('s', n(1), Rc::clone(&full));
        assert!(matches!(&*two_to_64, ContextProgram::Compose { inner, .. }
            if Rc::ptr_eq(inner, &full)));
    }

    #[test]
    fn shared_composition_exposes_virtual_constructors_without_expansion() {
        let mut program = ContextProgram::run('s', n(1));
        for _ in 0..64 {
            program = ContextProgram::compose(Rc::clone(&program), program);
        }
        let (context, rest) = ContextProgram::uncons(&program);
        assert_eq!(*context, 's');
        assert!(rest.is_some());
    }

    #[test]
    fn independently_allocated_saturated_runs_compare_without_expansion() {
        let left = ContextProgram::run('s', n(u64::MAX));
        let right = ContextProgram::run('s', n(u64::MAX));
        assert!(!Rc::ptr_eq(&left, &right));
        assert!(ContextProgram::equivalent_fast(&left, &right));
        assert!(!ContextProgram::equivalent_fast(
            &left,
            &ContextProgram::run('s', n(u64::MAX - 1)),
        ));
    }

    #[test]
    fn matching_run_prefixes_cancel_arithmetically() {
        let left = ContextProgram::run('s', n(u64::MAX));
        let right = ContextProgram::run('s', n(u64::MAX - 7));
        let cancelled = ContextProgram::cancel_matching_prefix(left, right, 16).unwrap();
        assert!(cancelled.changed);
        assert!(cancelled.right.is_none());
        assert!(matches!(cancelled.left.as_deref(),
            Some(ContextProgram::Run { count, .. }) if count.get() == 7));
    }

    #[test]
    fn cancellation_crosses_composed_saturated_runs_and_stops_at_mismatch() {
        let full = ContextProgram::run('s', n(u64::MAX));
        let left = ContextProgram::compose(ContextProgram::run('s', n(3)), Rc::clone(&full));
        let right = ContextProgram::compose(ContextProgram::run('s', n(1)), full);
        let cancelled = ContextProgram::cancel_matching_prefix(left, right, 32).unwrap();
        assert!(cancelled.changed);
        assert!(cancelled.right.is_none());
        assert!(matches!(cancelled.left.as_deref(),
            Some(ContextProgram::Run { count, .. }) if count.get() == 2));

        let left = ContextProgram::compose(
            ContextProgram::run('s', n(2)),
            ContextProgram::run('x', n(4)),
        );
        let right = ContextProgram::compose(
            ContextProgram::run('s', n(1)),
            ContextProgram::run('y', n(4)),
        );
        let cancelled = ContextProgram::cancel_matching_prefix(left, right, 32).unwrap();
        assert!(cancelled.changed);
        assert!(cancelled.left.is_some());
        assert!(cancelled.right.is_some());
    }

    #[test]
    fn one_shared_exponential_program_cancels_without_traversal() {
        let mut program = ContextProgram::run('s', n(1));
        for _ in 0..64 {
            program = ContextProgram::compose(Rc::clone(&program), program);
        }
        let cancelled =
            ContextProgram::cancel_matching_prefix(Rc::clone(&program), program, 1).unwrap();
        assert!(cancelled.changed);
        assert!(cancelled.left.is_none());
        assert!(cancelled.right.is_none());
    }

    #[test]
    fn independently_allocated_exponential_dags_cancel_by_bisimulation() {
        let left = doubling('s', 64);
        let right = doubling('s', 64);
        assert!(!Rc::ptr_eq(&left, &right));
        let cancelled = ContextProgram::cancel_matching_prefix(left, right, 64).unwrap();
        assert!(cancelled.changed);
        assert!(cancelled.left.is_none());
        assert!(cancelled.right.is_none());
        assert_eq!(cancelled.inspected, 64);
    }

    #[test]
    fn exponential_prefix_leaves_compact_unequal_residuals() {
        let left = ContextProgram::compose(
            doubling('s', 64),
            ContextProgram::run('x', n(u64::MAX)),
        );
        let right = ContextProgram::compose(
            doubling('s', 64),
            ContextProgram::run('y', n(u64::MAX)),
        );
        let cancelled = ContextProgram::cancel_matching_prefix(left, right, 80).unwrap();
        assert!(cancelled.inspected <= 72, "{}", cancelled.inspected);
        assert!(cancelled.changed);
        assert!(matches!(cancelled.left.as_deref(),
            Some(ContextProgram::Run { context: 'x', count }) if count.get() == u64::MAX));
        assert!(matches!(cancelled.right.as_deref(),
            Some(ContextProgram::Run { context: 'y', count }) if count.get() == u64::MAX));
    }

    #[test]
    fn hostile_near_match_exhausts_its_bound_without_a_verdict() {
        let left = doubling('s', 64);
        let right = doubling('x', 64);
        assert!(matches!(
            ContextProgram::cancel_matching_prefix(left, right, 16),
            Err(super::CancellationExhausted),
        ));
    }

}
