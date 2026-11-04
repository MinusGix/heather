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

use std::cell::RefCell;
use std::collections::BTreeSet;

use crate::reduce::Defs;
use crate::term::GlobalVar;

thread_local! {
    static FRAMES: RefCell<Vec<BTreeSet<usize>>> = const { RefCell::new(Vec::new()) };
}

/// Run `f`, and return the absolute Ψ indices of the withheld definitions it
/// unfolded on this thread, ascending and without repeats.
pub fn record<T>(f: impl FnOnce() -> T) -> (T, Vec<usize>) {
    FRAMES.with(|frames| frames.borrow_mut().push(BTreeSet::new()));
    let out = f();
    let mine = FRAMES.with(|frames| {
        let mut frames = frames.borrow_mut();
        let mine = frames.pop().unwrap_or_default();
        if let Some(outer) = frames.last_mut() {
            outer.extend(mine.iter().copied());
        }
        mine
    });
    (out, mine.into_iter().collect())
}

/// Note that the withheld definition `var` of `defs`' world was unfolded.
pub(crate) fn note(defs: Defs<'_>, var: GlobalVar) {
    let Some(at) = defs.absolute(var) else { return };
    FRAMES.with(|frames| {
        if let Some(top) = frames.borrow_mut().last_mut() {
            top.insert(at);
        }
    });
}
