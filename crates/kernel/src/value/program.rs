//! Succinct programs for repeated one-hole constructor contexts.
//!
//! A program denotes a context, not a materialized constructor tree.  `Run`
//! stores at most `u64::MAX` repetitions; overflowing adjacent runs remain a
//! shared `Compose` instead of growing an unbounded counter.  Nothing here
//! knows which inductive or constructor a context belongs to.

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
}

struct Cursor<C> {
    pending: Vec<Rc<ContextProgram<C>>>,
    run: Option<(C, NonZeroU64)>,
}

impl<C: Clone + Eq> Cursor<C> {
    fn new(program: Rc<ContextProgram<C>>) -> Self {
        Self { pending: vec![program], run: None }
    }

    fn next(&mut self) -> Option<(C, NonZeroU64)> {
        loop {
            if let Some((context, count)) = &self.run {
                return Some((context.clone(), *count));
            }
            match &*self.pending.pop()? {
                ContextProgram::Run { context, count } => {
                    self.run = Some((context.clone(), *count));
                }
                ContextProgram::Compose { outer, inner } => {
                    self.pending.push(Rc::clone(inner));
                    self.pending.push(Rc::clone(outer));
                }
            }
        }
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
    /// represented constructor nodes. The walk is over run/composition
    /// fragments; residual fragments retain the original shared subprograms.
    /// A differing context is a hard boundary, not a claim about it.
    pub fn cancel_matching_prefix(left: Rc<Self>, right: Rc<Self>) -> CancelledPrefix<C> {
        if Self::equivalent_fast(&left, &right) {
            return CancelledPrefix { left: None, right: None, changed: true };
        }
        let mut left = Cursor::new(left);
        let mut right = Cursor::new(right);
        let mut changed = false;
        loop {
            let (Some((lc, ln)), Some((rc, rn))) = (left.next(), right.next()) else {
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
        CancelledPrefix {
            left: left.remainder(),
            right: right.remainder(),
            changed,
        }
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
        let cancelled = ContextProgram::cancel_matching_prefix(left, right);
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
        let cancelled = ContextProgram::cancel_matching_prefix(left, right);
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
        let cancelled = ContextProgram::cancel_matching_prefix(left, right);
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
        let cancelled = ContextProgram::cancel_matching_prefix(Rc::clone(&program), program);
        assert!(cancelled.changed);
        assert!(cancelled.left.is_none());
        assert!(cancelled.right.is_none());
    }

}
