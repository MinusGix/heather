//! Inert observational counters (`docs/instrumentation-design.md` §2).
//!
//! Thread-local `Cell<u64>`s that say how much work the checker did — how
//! many conversion queries the syntactic shortcut answered, how many the gate
//! memo answered, how many paid for a value-domain comparison and how each of
//! those failed, how many steps and δ-unfoldings the evaluator spent.
//!
//! Two properties are load-bearing and must stay true of anything added here:
//!
//! 1. **Nothing in the kernel ever reads a counter.** `typing`, `conv`, `eval`
//!    and `reduce` bump; only a caller outside the kernel snapshots. A counter
//!    can therefore never influence a judgment, and deleting this module would
//!    change no answer.
//! 2. **Every bump is a one-liner**, and every counter is declared, bumped and
//!    rendered through the one macro below, so the set is auditable by reading
//!    the list.
//!
//! Always compiled, never feature-gated: the build that ships is the build
//! that was measured. The expensive samplers — the `Tc::conv_ty` miss table,
//! its excerpts, `HEATHER_CONV_MISS_TRACE` — stay behind `value-metrics`,
//! because those format terms and these do not.
//!
//! Thread-local by design: a caller measures the checker it drives on its own
//! thread and nothing else.

use std::cell::Cell;

macro_rules! counters {
    ($($(#[$m:meta])* $name:ident),* $(,)?) => {
        #[derive(Default)]
        struct Cells { $($name: Cell<u64>,)* }

        thread_local! {
            static CELLS: Cells = Cells::default();
        }

        /// A copyable reading of every counter on this thread.
        #[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
        pub struct Snapshot { $($(#[$m])* pub $name: u64,)* }

        $(
            $(#[$m])*
            #[inline]
            pub fn $name(n: u64) {
                CELLS.with(|c| c.$name.set(c.$name.get().wrapping_add(n)));
            }
        )*

        /// Read every counter on this thread.
        pub fn snapshot() -> Snapshot {
            CELLS.with(|c| Snapshot { $($name: c.$name.get(),)* })
        }

        /// Zero every counter on this thread.
        pub fn reset() {
            CELLS.with(|c| { $(c.$name.set(0);)* });
        }

        /// Add another thread's reading into this thread's counters.
        ///
        /// What a deferred kernel gate's join does with a worker's delta
        /// (`docs/parallel-kernel-gate-design.md` §7), so that a scope still
        /// open on the joining thread accounts for work done off it. Still
        /// inert: this module writes counters and reads them only through
        /// `snapshot`.
        pub fn merge(delta: &Snapshot) {
            CELLS.with(|c| { $(c.$name.set(c.$name.get().wrapping_add(delta.$name));)* });
        }

        impl Snapshot {
            /// The counters' column names, in the order [`Snapshot::values`]
            /// reports them.
            pub const NAMES: &'static [&'static str] = &[$(stringify!($name),)*];

            /// This snapshot minus an earlier one: what happened in between.
            pub fn since(&self, earlier: &Snapshot) -> Snapshot {
                Snapshot { $($name: self.$name.wrapping_sub(earlier.$name),)* }
            }

            /// Two readings added column-wise — one row's own numbers plus
            /// what a worker did for it.
            pub fn plus(&self, other: &Snapshot) -> Snapshot {
                Snapshot { $($name: self.$name.wrapping_add(other.$name),)* }
            }

            /// The counters in [`Snapshot::NAMES`] order.
            pub fn values(&self) -> Vec<u64> {
                vec![$(self.$name,)*]
            }
        }
    };
}

counters! {
    /// Calls to the gate entry point `typing::check_term` (and its profiled
    /// twin) — one per proof obligation the kernel was actually asked to
    /// judge. The one counter here that is about the *caller's* schedule
    /// rather than the checker's internals: a verdict the serial replay
    /// reused (`docs/parallel-kernel-gate-design.md` §5.2) is a call that did
    /// not happen, and this column is how a test says so.
    check_terms,
    /// `Tc::conv_ty` queries answered by the syntactic reflexivity test.
    conv_shortcut_hits,
    /// `Tc::conv_ty` queries answered by the gate's cross-head memo.
    conv_memo_hits,
    /// `Tc::conv_ty` queries that paid for a value-domain comparison.
    conv_misses,
    /// Misses that failed for **exhausted fuel or depth** rather than for a
    /// real mismatch. Kept apart from `conv_not_convertible` because the two
    /// call for opposite responses: more budget against a better spelling
    /// (`issues/generated-proof-cost-diagnostics.md`).
    conv_out_of_fuel,
    /// Misses that failed on a genuine mismatch.
    conv_not_convertible,
    /// Fuel units the evaluator spent — one per reduction step.
    eval_steps,
    /// Definition unfoldings (δ-steps) the evaluator performed.
    eval_delta_steps,
    /// Re-entries of the evaluator's trampoline.
    eval_drives,
    /// Nodes the `shift_global` traversal visited — every rescoping of a
    /// global's body, type or context into the ambient Ψ pays one per node
    /// (`issues/refl-theorem-step-cost.md`: the copying a fuel pin cannot
    /// see).
    shift_global_nodes,
    /// Definition bodies rescoped by `Defs::body` — one per `GlobalCache`
    /// body fill, i.e. per (definition, gate call) pair that unfolded it.
    delta_body_rescopes,
    /// Occurrences of `u^δ` / `U^δ` whose typing or conversion rule read the
    /// binding's declared context and type rescoped into the ambient Ψ. One
    /// per **occurrence**: the rescoping itself is memoized per (Ψ,
    /// `GlobalVar`) in `reduce::GlobalCache`, so this is demand and
    /// `shift_global_nodes` is the work it caused.
    global_ref_rescopes,
    /// Binding signatures actually rescoped — one per `GlobalCache` signature
    /// fill, i.e. per (binding, Ψ) pair some occurrence demanded. The work
    /// behind `global_ref_rescopes`, which is the demand.
    global_sig_rescopes,
}
