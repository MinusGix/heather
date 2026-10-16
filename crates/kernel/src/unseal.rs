//! Which sealed proofs a computation opened
//! (`issues/theorem-witness-unfolding.md`, option D).
//!
//! A theorem's proof is kept *sealed* beside its opaque binding
//! ([`crate::term::GlobalCtx::sealed`]) and unsealed only where an
//! elimination is stuck on it ([`crate::reduce::Defs::sealed_body`]). A
//! judgment that unsealed a proof depends on that proof's body, not only on
//! the theorem's statement, so whoever caches the judgment must key it on
//! the body too. This module is how they find out: [`record`] runs a closure
//! and returns, beside its result, the absolute Ψ indices of every sealed
//! proof unsealed on this thread while it ran.
//!
//! Like `crate::stats`, it is observational: nothing in the kernel reads a
//! recording, so a recording can never change an answer. Unlike `stats`, a
//! caller *must* consult it before reusing a judgment — that is its purpose.
//! Recordings nest; an inner recording's indices are also the outer one's.

use std::cell::RefCell;
use std::collections::BTreeSet;

thread_local! {
    static FRAMES: RefCell<Vec<BTreeSet<usize>>> = const { RefCell::new(Vec::new()) };
}

/// Run `f`, and return the absolute Ψ indices of the sealed proofs it
/// unsealed on this thread, ascending and without repeats.
pub fn record<T>(f: impl FnOnce() -> T) -> (T, Vec<usize>) {
    let recording = Recording::start();
    let out = f();
    (out, recording.finish())
}

/// [`record`] as a guard, for a span that is not one closure: everything
/// unsealed on this thread between [`Recording::start`] and
/// [`Recording::finish`]. Dropping it unfinished (a panic unwinding through
/// the span) still closes it, so a later recording does not inherit it.
pub struct Recording {
    depth: usize,
}

impl Recording {
    pub fn start() -> Recording {
        let depth = FRAMES.with(|frames| {
            let mut frames = frames.borrow_mut();
            frames.push(BTreeSet::new());
            frames.len()
        });
        Recording { depth }
    }

    /// Close the recording and return what it saw, which also reaches every
    /// recording it is nested in.
    pub fn finish(self) -> Vec<usize> {
        let opened = close(self.depth);
        std::mem::forget(self);
        opened.into_iter().collect()
    }
}

impl Drop for Recording {
    fn drop(&mut self) {
        close(self.depth);
    }
}

/// Pop the frame at `depth` — and any left open inside it, merging them in
/// first — handing its indices to the frame outside it too.
fn close(depth: usize) -> BTreeSet<usize> {
    FRAMES.with(|frames| {
        let mut frames = frames.borrow_mut();
        let mut mine = BTreeSet::new();
        while frames.len() >= depth && depth > 0 {
            mine.extend(frames.pop().unwrap_or_default());
        }
        if let Some(outer) = frames.last_mut() {
            outer.extend(mine.iter().copied());
        }
        mine
    })
}

/// Report, to whatever is recording on this thread, unsealings a judgment
/// made elsewhere — a verdict computed on another thread and reused here.
/// Nothing is counted: the unsealing itself was counted where it happened.
pub fn observe(opened: &[usize]) {
    FRAMES.with(|frames| {
        if let Some(top) = frames.borrow_mut().last_mut() {
            top.extend(opened.iter().copied());
        }
    });
}

/// The sealed proof at absolute Ψ index `at` is being unsealed.
pub(crate) fn note(at: usize) {
    crate::stats::sealed_unfolds(1);
    FRAMES.with(|frames| {
        if let Some(top) = frames.borrow_mut().last_mut() {
            top.insert(at);
        }
    });
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn recordings_nest_and_an_inner_one_reaches_the_outer() {
        let ((inner, ()), outer) = record(|| {
            note(3);
            let inner = record(|| note(1)).1;
            note(3);
            (inner, ())
        });
        assert_eq!(inner, vec![1]);
        assert_eq!(outer, vec![1, 3]);
        // Nothing is recording now: a note goes nowhere.
        note(7);
        assert_eq!(record(|| ()).1, Vec::<usize>::new());
    }
}
