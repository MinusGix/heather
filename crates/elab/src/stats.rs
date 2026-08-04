//! Phase attribution: how much of a file's check time was spent inside the
//! **kernel gate** (`issues/frontend-benchmarks.md`).
//!
//! The frontend suite has to be able to say which layer a regression is in —
//! parse, elaborate, or kernel-check — and only one of those three can be
//! measured from outside. Parsing is a pure function the bench can call on
//! its own; the kernel gate is *inside* [`crate::Elaborator::elab_decl`], one
//! `check_type` and one `check_term` per declaration, so the elaborator has
//! to report it.
//!
//! What counts is deliberately narrow: the `typing::check_*` calls that gate
//! a finished declaration (and the meta layer's equivalents in `quote.rs`).
//! The elaborator's *other* trips into the kernel — `whnf`, `conv_type`,
//! every unification step — stay on the elaborate side of the split, because
//! they are elaboration deciding something, not the kernel re-checking a
//! result. So `elaborate = total − parse − kernel-gate` is "the elaborator's
//! own work, including the conversion it does while working", which is the
//! quantity a frontend regression would move.
//!
//! Cost when nobody is measuring: two `Instant::now()` per checked
//! declaration, tens of nanoseconds against a declaration that costs
//! microseconds at the very least. Always on rather than behind a feature,
//! so the benchmarked build is the shipped build.
//!
//! Not thread-safe by design and not meant to be: the counter is a
//! thread-local, so a caller measures the elaborator it drives on its own
//! thread and nothing else.

use std::cell::Cell;
use std::time::Instant;

thread_local! {
    static KERNEL_NS: Cell<u64> = const { Cell::new(0) };
}

/// Nanoseconds spent in the kernel gate on this thread since the last
/// [`reset_kernel_ns`].
pub fn kernel_ns() -> u64 {
    KERNEL_NS.with(|c| c.get())
}

/// Zero the counter. Call before the elaboration you want to attribute.
pub fn reset_kernel_ns() {
    KERNEL_NS.with(|c| c.set(0));
}

/// Run `f`, adding its duration to this thread's kernel-gate total.
pub(crate) fn time_kernel<T>(f: impl FnOnce() -> T) -> T {
    let start = Instant::now();
    let out = f();
    let ns = start.elapsed().as_nanos() as u64;
    KERNEL_NS.with(|c| c.set(c.get().saturating_add(ns)));
    out
}
