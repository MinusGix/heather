//! Inert observational counters (`docs/infrastructure/instrumentation-design.md` §2).
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
        /// (`docs/kernel/parallel-kernel-gate-design.md` §7), so that a scope still
        /// open on the joining thread accounts for work done off it. Still
        /// inert: this module writes counters and reads them only through
        /// `snapshot`.
        pub fn merge(delta: &Snapshot) {
            CELLS.with(|c| { $(c.$name.set(c.$name.get().wrapping_add(delta.$name));)* });
        }

        /// Run `f` with none of its bumps reaching this thread's counters:
        /// for the kernel's debug-only re-verification of a memo hit
        /// (`typing.rs` §The typing memo), which judges again what the hit
        /// skipped. Without it a debug build would count that work, and
        /// which hits are sampled (a thread-local stride, `crate::checks`)
        /// would move the counts. Still inert: the counters are restored,
        /// never read by a judgment.
        #[cfg(debug_assertions)]
        pub(crate) fn unobserved<T>(f: impl FnOnce() -> T) -> T {
            let saved = snapshot();
            let out = f();
            CELLS.with(|c| { $(c.$name.set(saved.$name);)* });
            out
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
    /// reused (`docs/kernel/parallel-kernel-gate-design.md` §5.2) is a call that did
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
    /// Projections of an application `k y` answered by the value a sibling
    /// projection of the same application already computed
    /// (`Eval::eval_projected`): a tier-2 function child's tree and proof
    /// sharing one evaluation of the child.
    shared_apps,
    /// Nodes the `shift_global` traversal visited — every rescoping of a
    /// global's body, type or context into the ambient Ψ pays one per node
    /// (`issues/refl-theorem-step-cost.md`: the copying a fuel pin cannot
    /// see).
    shift_global_nodes,
    /// Nodes the local shift and the local substitutions (`shift_local`,
    /// `apply_local`, `inst_top`) visited, skipped and memoized ones
    /// included. Its growth against the shared size of what they were given
    /// is the tree/DAG gap `issues/subst-shared-node-memo.md` closes.
    local_subst_nodes,
    /// Shared nodes a substitution traversal answered from its per-call memo
    /// (`subst.rs` §Keeping a shared DAG shared): one per second (or later)
    /// path into the same node at the same depths.
    subst_memo_hits,
    /// Pairs of distinct nodes that `==` on `Term`/`Type` compared
    /// (`syntax_eq.rs`): the structural equality behind the conversion
    /// shortcut and the elaborator's `refl` test, pointer-equal children
    /// not counted. Its growth against the shared size of the two sides is
    /// the tree/DAG gap `issues/kernel-equality-walks-dags-as-trees.md`
    /// closes.
    syntax_eq_nodes,
    /// Second (or later) paths into a pair of shared nodes that one `==`
    /// call had already found equal, answered from its memo (`syntax_eq.rs`).
    syntax_eq_memo_hits,
    /// Judgments the kernel checker answered from its typing memo
    /// (`typing.rs` §The typing memo): one per second (or later) path into
    /// the same node in the same scope, the node's whole subtree unvisited.
    typing_memo_hits,
    /// Definition bodies rescoped by `Defs::body` — one per `GlobalCache`
    /// body fill, i.e. per (definition, gate call) pair that unfolded it.
    delta_body_rescopes,
    /// Sealed proofs unsealed at a stuck elimination (`crate::unseal`): one
    /// per unsealing, so a theorem a check projects twice counts twice.
    sealed_unfolds,
    /// Lazily kept sealed proofs loaded from their source (a module image's
    /// encoding: `term::SealedProof`): one per proof per run, on the thread
    /// that first needed it.
    sealed_loads,
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
    /// `pair@` / `inl@` / `inr@` / `fst@` / `snd@` nodes the checker judged —
    /// the **checked spellings** of `docs/elaborator/intro-by-type-design.md`, whose
    /// annotation is the un-reduced type the elaborator had rather than the
    /// reduct's components. One per typing rule fired, so it counts the
    /// forms a gate actually met and not the ones a source happens to
    /// contain.
    ///
    /// The round's marker column (design §8): it is **zero by construction**
    /// before the elaborator emits the forms, so `scripts/perf ab --marker
    /// intro_at_nodes` can assert the after binary emits it and the before
    /// one does not.
    intro_at_nodes,
    /// `ITy::Sel` nodes the value machine evaluated
    /// (`docs/elaborator/intro-by-type-design.md` §3.3, §3.7). Every conversion miss
    /// and every view of a selection re-evaluates the description's chain in
    /// a fresh per-query arena — linear in the nesting, against the
    /// rewriter's `3.5ⁿ` per query, but paid again per query. Whether that
    /// re-evaluation dominates is the number stage 2 reads out of this
    /// column beside `conv_misses`; the fix, if it does, is a
    /// declaration-scoped memo, which is a design of its own and not a thing
    /// to slip in.
    sel_evals,
    /// Selections **spelled** — `Tc::materialize` calls
    /// (`docs/elaborator/intro-by-type-design.md` §3.5). This is the rewriter running
    /// on an `@`-derived type, i.e. exactly the exponential object the round
    /// exists to stop building, and it is a counter rather than a comment so
    /// that a workload reaching it is seen and not guessed. The four λ
    /// inference arms and the non-Π/Σ/sum branch of `Tc::view` are its only
    /// callers.
    ity_materialized,
}
