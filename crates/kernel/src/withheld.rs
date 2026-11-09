//! Which withheld definitions a computation unfolded
//! (`docs/interface-definitions-design.md` §3, §8).
//!
//! A world's interface boundary ([`crate::term::GlobalCtx::withheld`])
//! keeps a definition opaque until a call of it is saturated at closed
//! arguments; from there it unfolds as any definition does. A judgment made
//! in such a world observed a withheld body only where that happened, so the
//! set of those definitions is what the judgment depends on beyond the
//! statements it read. [`record`] runs a closure and returns, beside its
//! result, the absolute Ψ indices of every withheld definition unfolded on
//! this thread while it ran.
//!
//! Observational, like `crate::unseal`: nothing in the kernel reads a
//! recording, so a recording can never change an answer. Only an
//! elaborator world ever withholds, so the trusted check records nothing.

use crate::recording::{self, Frames, Recording};
use crate::reduce::Defs;
use crate::term::GlobalVar;

thread_local! {
    static FRAMES: Frames = const { Frames::new(Vec::new()) };
}

/// Run `f`, and return the absolute Ψ indices of the withheld definitions it
/// unfolded on this thread, ascending and without repeats. A panic out of
/// `f` that is caught further out still closes this recording
/// ([`Recording`]), as `crate::unseal`'s does.
pub fn record<T>(f: impl FnOnce() -> T) -> (T, Vec<usize>) {
    let recording = Recording::start(&FRAMES);
    let out = f();
    (out, recording.finish())
}

/// Note that the withheld definition `var` of `defs`' world was unfolded.
pub(crate) fn note(defs: Defs<'_>, var: GlobalVar) {
    let Some(at) = defs.absolute(var) else { return };
    recording::note(&FRAMES, [at]);
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A panic inside an inner recording, caught inside the outer one,
    /// leaves the outer recording its own frame: what the outer saw before
    /// and after is kept, and the inner's notes reach it too.
    #[test]
    fn a_caught_panic_inside_a_recording_does_not_strand_its_frame() {
        let (_, outer) = record(|| {
            recording::note(&FRAMES, [3]);
            let caught = std::panic::catch_unwind(|| {
                record(|| {
                    recording::note(&FRAMES, [1]);
                    panic!("inside the inner recording");
                })
            });
            assert!(caught.is_err());
            recording::note(&FRAMES, [5]);
        });
        assert_eq!(outer, vec![1, 3, 5]);
        // Nothing is left open.
        FRAMES.with(|frames| assert!(frames.borrow().is_empty()));
    }
}
