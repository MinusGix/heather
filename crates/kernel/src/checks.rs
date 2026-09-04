//! Runtime levels for the kernel's *slow* self-checks.
//!
//! Some checks re-derive a claim the kernel already acted on — today, that a
//! subtree the bounds memo let a substitution skip really was untouched
//! (`subst.rs`, `sub_ty`/`sub_tm`). They exist to catch a trusted-base
//! optimization disagreeing with the traversal it short-circuits, which no
//! typing rule would notice: the term would simply be wrong. They are also
//! the whole cost of the walk being skipped, paid again, so running every one
//! of them on every skip roughly doubles substitution-heavy elaboration
//! (2026-09-04: the Omega closure went 61 s → 138 s in the test profile,
//! `issues/certgen-harness-cost.md`).
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
