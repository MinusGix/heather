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

}
