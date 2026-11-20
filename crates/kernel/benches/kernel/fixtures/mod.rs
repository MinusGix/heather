//! The fixtures: one module per area, each exporting families.
//!
//! Two rules every fixture here follows.
//!
//! **Setup is not timed.** Building the term, the context and the expected
//! answer happens when the family is constructed; `Case::run` does the
//! kernel call and nothing else.
//!
//! **A fixture validates before it is timed.** `Case::expect` is a cheap
//! checksum the harness verifies once per case, and the heavier structural
//! assertions (this really checks, this really reduces to that) run at setup.
//! The failure mode this guards is specific and has happened elsewhere: a
//! fixture that stops doing its work gets *faster*, so an unvalidated
//! benchmark reports a win for a bug.

pub mod code;
pub mod conv;
pub mod delta;
pub mod level;
pub mod nat;
pub mod simulate;
pub mod subst;
pub mod terms;
pub mod wf;

use crate::harness::Family;

/// Every family, in report order. Areas are ordered bottom-up through the
/// kernel: levels, substitution, reduction, conversion, then checking.
pub fn all() -> Vec<Family> {
    let mut v = vec![];
    v.extend(level::families());
    v.extend(subst::families());
    v.extend(nat::families());
    v.extend(conv::families());
    v.extend(delta::families());
    v.extend(simulate::families());
    v.extend(wf::families());
    v.extend(code::families());
    v
}

/// Fuel for fixture reductions. Generous: every fixture terminates, so
/// exhaustion is a bug, not a limit — and fuel is a step count, not a time
/// budget, so a large value costs nothing when the work is small.
pub const FUEL: u64 = 1 << 24;
