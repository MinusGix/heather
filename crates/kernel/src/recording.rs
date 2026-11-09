//! Nested recordings of Ψ indices a computation observed, shared by
//! `crate::unseal` (sealed proofs opened) and `crate::withheld` (withheld
//! definitions glued). Each keeps its own thread-local stack of frames; this
//! module is the one protocol over it, so both close a frame the same way
//! when a span ends early (docs/kernel-implicit-state-review.md §6).
//!
//! Observational: nothing in the kernel reads a recording, so a recording
//! can never change an answer. Recordings nest; an inner recording's
//! indices are also the outer one's.

use std::cell::RefCell;
use std::collections::BTreeSet;
use std::thread::LocalKey;

/// One kind of recording's frames on this thread, innermost last.
pub(crate) type Frames = RefCell<Vec<BTreeSet<usize>>>;

/// A recording in progress: everything noted on `frames` between
/// [`Recording::start`] and [`Recording::finish`]. Dropping it unfinished
/// (a panic unwinding through the span, caught further out) still closes
/// it, so the recording outside it does not pop it as its own and lose what
/// it saw.
pub(crate) struct Recording {
    frames: &'static LocalKey<Frames>,
    depth: usize,
}

impl Recording {
    pub(crate) fn start(frames: &'static LocalKey<Frames>) -> Recording {
        let depth = frames.with(|frames| {
            let mut frames = frames.borrow_mut();
            frames.push(BTreeSet::new());
            frames.len()
        });
        Recording { frames, depth }
    }

    /// Close the recording and return what it saw, ascending and without
    /// repeats, which also reaches every recording it is nested in.
    pub(crate) fn finish(self) -> Vec<usize> {
        let seen = close(self.frames, self.depth);
        std::mem::forget(self);
        seen.into_iter().collect()
    }
}

impl Drop for Recording {
    fn drop(&mut self) {
        close(self.frames, self.depth);
    }
}

/// Pop the frame at `depth`, and any left open inside it, merging them in
/// first, handing its indices to the frame outside it too.
fn close(frames: &'static LocalKey<Frames>, depth: usize) -> BTreeSet<usize> {
    frames.with(|frames| {
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

/// Add `indices` to the innermost recording on `frames`, if one is open.
pub(crate) fn note(frames: &'static LocalKey<Frames>, indices: impl IntoIterator<Item = usize>) {
    frames.with(|frames| {
        if let Some(top) = frames.borrow_mut().last_mut() {
            top.extend(indices);
        }
    });
}
