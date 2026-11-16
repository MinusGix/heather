//! Runtime levels for the kernel's *slow* self-checks.
//!
//! Some checks re-derive a claim the kernel already acted on — so far, that
//! a subtree a node's bounds let a substitution skip really was untouched
//! (`subst.rs`, `sub_ty`/`sub_tm`). They exist to catch a trusted-base
//! optimization disagreeing with the traversal it short-circuits, which no
//! typing rule would notice: the term would simply be wrong. They are also
//! the whole cost of the walk being skipped, paid again, so running every one
//! of them on every skip roughly doubles substitution-heavy elaboration
//! (`issues/certgen-harness-cost.md`).
//!
//! The checks are compiled only under `debug_assertions`; release builds
//! carry none of this and the level is irrelevant there. In debug builds a
//! process-wide level chooses how often they run:
//!
//! - [`SkipVerification::Full`] — every skip. The kernel's own property
//!   tests choose this: random well-scoped terms are the corpus the memo's
//!   scoping rules are meant to be exhaustive over, and a disagreement is a
//!   `law!`-shaped failure.
//! - [`SkipVerification::Sampled`] — one skip in [`SAMPLE_EVERY`], the
//!   default. A memo defect is systematic (a node kind's scoping, not a rare
//!   term), so a sample over the millions of skips a library check makes
//!   finds it with near certainty at a few percent of the cost, and every
//!   elaborator acceptance suite keeps sweeping real term shapes.
//! - [`SkipVerification::Off`] — never.
//!
//! A check is one derivation ([`rederive`]): nothing is checked inside it and
//! it moves no counter, so checking every claim costs about what the claims
//! saved, and a debug build counts what a release build counts.
//!
//! The `long-checks` feature makes `Full` the default for a deliberately
//! slow lane. The kernel reads no environment variable: a policy is set by
//! whoever owns the process (a test binary, a harness), never guessed here.

use std::cell::Cell;
use std::sync::atomic::{AtomicU8, Ordering};

/// How often a skip is re-verified in debug builds.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SkipVerification {
    Off,
    Sampled,
    Full,
}

/// Under [`SkipVerification::Sampled`], the interval between verified skips.
pub const SAMPLE_EVERY: u32 = 16;

const OFF: u8 = 0;
const SAMPLED: u8 = 1;
const FULL: u8 = 2;
const DEFAULT: u8 = if cfg!(feature = "long-checks") { FULL } else { SAMPLED };

static LEVEL: AtomicU8 = AtomicU8::new(DEFAULT);

thread_local! {
    static SAMPLE: Cell<u32> = const { Cell::new(0) };
}

#[cfg(debug_assertions)]
thread_local! {
    /// Which claim this thread is deriving again, if any ([`rederive`]).
    static AGAIN: Cell<u8> = const { Cell::new(NOT_AGAIN) };
}

#[cfg(debug_assertions)]
const NOT_AGAIN: u8 = 0;
#[cfg(debug_assertions)]
const AGAIN_KEPT: u8 = 1;
#[cfg(debug_assertions)]
const AGAIN_SKIP: u8 = 2;

/// The claim a check derives again.
#[cfg(debug_assertions)]
#[derive(Clone, Copy)]
pub(crate) enum Claim {
    /// A node's bounds said a traversal would not change it. Derived again
    /// by the traversal with no bounds consulted anywhere under the node
    /// ([`unskipped`]), so one walk checks the claim for the node and for
    /// everything in it, at the cost the traversal had before there were
    /// bounds: a shared node once (the traversal's own memo), a deep spine
    /// by the traversal's own loop.
    Skip,
    /// Something kept is what deriving it gives: a memo's answer for a
    /// shared node (a mapped node, a judgment, an equal pair), a table's
    /// verdict, a stored precondition. Derived again once, over whatever is
    /// kept for the parts.
    Kept,
}

/// Run `derive`, which derives again what the kernel already acted on, with
/// nothing of it showing: no check nested inside it, no counter moved
/// ([`crate::stats::unobserved`]), and for [`Claim::Skip`] no skip taken.
///
/// A check that checks inside itself costs the paths of what it checks, not
/// the nodes, and costs them on the native stack: a skipped child verified
/// inside its parent's verification, and a hit under a re-judged node
/// re-judged in turn, turn a shared chain of `k` links into `2^k` paths and a
/// deep closed chain into a stack overflow, and the substitution counters
/// would read the checks' own walks (`issues/self-checks-nest.md`). Sampling
/// one check in [`SAMPLE_EVERY`] hides all three, so it is not a defence.
#[cfg(debug_assertions)]
pub(crate) fn rederive<T>(claim: Claim, derive: impl FnOnce() -> T) -> T {
    struct Restore(u8);
    impl Drop for Restore {
        fn drop(&mut self) {
            AGAIN.with(|w| w.set(self.0));
        }
    }
    let kind = match claim {
        Claim::Skip => AGAIN_SKIP,
        Claim::Kept => AGAIN_KEPT,
    };
    let _restore = Restore(AGAIN.with(|w| w.replace(kind)));
    crate::stats::unobserved(derive)
}

/// Whether this thread is walking a skipped subtree again
/// ([`Claim::Skip`]): a traversal that can verify its skips takes none
/// while it is.
#[cfg(debug_assertions)]
#[inline]
pub(crate) fn unskipped() -> bool {
    AGAIN.with(|w| w.get()) == AGAIN_SKIP
}

/// Release builds verify nothing, so nothing is ever walked again.
#[cfg(not(debug_assertions))]
#[inline(always)]
pub(crate) fn unskipped() -> bool {
    false
}

/// Set the process-wide level. Idempotent and cheap; a test may call it at
/// the top of every case.
pub fn set_skip_verification(level: SkipVerification) {
    let raw = match level {
        SkipVerification::Off => OFF,
        SkipVerification::Sampled => SAMPLED,
        SkipVerification::Full => FULL,
    };
    LEVEL.store(raw, Ordering::Relaxed);
}

pub fn skip_verification() -> SkipVerification {
    match LEVEL.load(Ordering::Relaxed) {
        OFF => SkipVerification::Off,
        FULL => SkipVerification::Full,
        _ => SkipVerification::Sampled,
    }
}

/// Whether the skip being taken right now should be re-verified. One relaxed
/// load on the skip path, which already pays a thread-local memo probe per
/// node; under sampling, one thread-local counter as well.
#[cfg(debug_assertions)]
pub(crate) fn verify_this_skip() -> bool {
    // A check checks one claim. The claims met inside it are not checked
    // in turn (`rederive`), and they do not move the sampling stride
    // either: which claims a run checks is a function of the claims it
    // makes.
    if AGAIN.with(|w| w.get()) != NOT_AGAIN {
        return false;
    }
    match LEVEL.load(Ordering::Relaxed) {
        OFF => false,
        FULL => true,
        _ => SAMPLE.with(|n| {
            let next = n.get().wrapping_add(1) % SAMPLE_EVERY;
            n.set(next);
            next == 0
        }),
    }
}
