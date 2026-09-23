//! Elaboration determinism (issues/elaboration-determinism.md).
//!
//! For most compilers, byte-identical output is hygiene. For Heather it is a
//! semantic commitment: `.code` quotes the *elaborated* term and meta-programs
//! branch on it, and the content-addressed cache of
//! issues/parallel-checking-and-caching.md keys on hashes of elaborated
//! output. Two elaborations of one source that differ at all are two
//! programs, not two spellings of one. So it gets a regression test rather
//! than a comment.
//!
//! The two guarantees are different, so they are separate tests:
//!
//! - `same_source_elaborates_identically` — stability *within* this build.
//!   It is what catches an accidentally-iterated `HashMap`.
//! - `nat_suite_golden_hash` — stability *across* builds. A failure is not a
//!   bug report, it is a notification: the elaborator's output changed, and
//!   someone has to decide that was intended.
//!
//! plus `the_hash_sees_past_the_debug_budget`, which keeps the second one
//! honest.

use heather_elab::Elaborator;
use heather_kernel::term::GlobalCtx;

mod support;
use support::{NAT_SUITE, psi_hash};

/// Elaborate the prelude + the Nat suite from scratch, returning Ψ.
fn elaborate() -> GlobalCtx {
    let mut e = Elaborator::with_prelude().expect("prelude");
    e.elab_source(NAT_SUITE).expect("Nat suite must elaborate and kernel-check");
    e.psi().clone()
}

/// Fresh `Elaborator`s, same source, same terms — repeatedly.
///
/// The repetition is the test, not padding. Every `HashMap`/`HashSet` in the
/// elaborator is built with std's `RandomState`, which draws **new keys per
/// map instance** (a per-process seed plus a per-instance counter), so each
/// fresh `Elaborator` in this one process already hashes its names to
/// different buckets and would iterate them in a different order. A single
/// pair of runs could get lucky on a small map; several rounds make an
/// order-sensitive path a near-certain failure instead of a flake. It also
/// means this test needs no environment variable, no subprocess, and no
/// second `cargo test` invocation to vary the seed — the standard library
/// varies it for us.
///
/// `PartialEq` on `GlobalCtx` is derived and structural, so this compares
/// every binding, type, body and level — not a summary of them.
#[test]
fn same_source_elaborates_identically() {
    const ROUNDS: usize = 8;
    let first = elaborate();
    for round in 1..ROUNDS {
        let again = elaborate();
        assert!(
            again == first,
            "elaboration round {round} produced a different Ψ from round 0 — \
             elaboration is not deterministic. The usual cause is a \
             HashMap/HashSet iterated somewhere its order reaches the emitted \
             term; see crates/elab/src/lib.rs's determinism note. \
             (round 0 hash {:#018x}, round {round} hash {:#018x})",
            psi_hash(&first),
            psi_hash(&again),
        );
    }
}

/// The elaborated Nat suite hashes to a fixed value.
///
/// **A failure here is not necessarily a bug.** It says one thing: the
/// elaborator no longer emits the terms it emitted when this constant was
/// written. That is a visible event to confirm deliberately — read the
/// change, decide it is the improvement you meant, then paste the printed
/// hash in below. What it exists to prevent is the *silent* version, where a
/// refactor quietly reshapes every emitted term and nothing says so.
///
/// Set 2026-08-06, over the prelude's 4 theorems + the suite's `fn add` and
/// 4 theorems; re-taken 2026-09-10 over the 10 Ψ bindings that are those plus
/// the prelude's `CollectionLiteral#tycode_fn`
/// (docs/per-instantiation-type-codes-design.md §2).
///
/// Unmoved by the same day's fix to the kernel's `Debug` for `Branches`,
/// which went from printing 37 of the 52 recursor branches to all 52 and
/// reordered the rendering (issues/branches-debug-partial.md). The hash is
/// taken over the printed form, so *any* recursor in Ψ would have moved it:
/// that it did not is the measurement that this suite — and today's
/// elaborator at all, which constructs no `ElimCodeTy`/`ElimCodeTm` — emits
/// no code recursor. The golden's blind spot was real but unexercised.
/// Moved 2026-09-15 by `docs/telescoped-record-projections-design.md`'s
/// device: `CollectionLiteral<C>(n)` is telescoped and its spine is dependent
/// (`fromLiteral` mentions `element`), so its projections are now named and Ψ
/// carries `3·nfields + 1 = 7` more bindings. The hash is over Ψ's printed
/// form, so it moves whenever Ψ does.
/// Moved 2026-09-22 by `docs/app-by-head-type-design.md`: every emitted
/// application is `app@(f; a)` now, with no annotations.
const NAT_SUITE_GOLDEN: u64 = 0x67f02d6ccda1f6af;

#[test]
fn nat_suite_golden_hash() {
    let got = psi_hash(&elaborate());
    assert_eq!(
        got, NAT_SUITE_GOLDEN,
        "the elaborated Nat suite changed shape.\n\
         If that was intended, update NAT_SUITE_GOLDEN in \
         crates/elab/tests/determinism.rs to:\n    \
         const NAT_SUITE_GOLDEN: u64 = {got:#018x};"
    );
}

/// The hash is a hash *of the whole term*, not of a bounded prefix.
///
/// Kernel `Debug` elides past a node budget (crates/kernel/src/fmt.rs), so
/// hashing `{:?}` would make any two large Ψs that agree on their first 512
/// nodes indistinguishable — a golden hash that cannot fail is worse than
/// none. `psi_hash` goes through `write_exact` instead; this pins that it
/// really does see past the budget, by hashing a Ψ against the same Ψ with a
/// deeply-buried difference.
#[test]
fn the_hash_sees_past_the_debug_budget() {
    use heather_kernel::level::Level;
    use heather_kernel::term::{GlobalBinding, LocalCtx, Term, Type};
    use std::sync::Arc as Rc;

    fn deep(n: usize, tip: Term) -> GlobalCtx {
        let mut t = tip;
        for _ in 0..n {
            t = Term::Succ(Rc::new(t));
        }
        GlobalCtx::new(vec![GlobalBinding::defined_tm(
            LocalCtx::nil(),
            heather_kernel::layer::Layer::Prog,
            Rc::new(Type::Nat),
            Level::Zero,
            Rc::new(t),
        )])
    }

    // 2000 `Succ`s deep: far past the 512-node budget, so the two differ
    // only where a bounded printer would have stopped looking.
    let a = deep(2000, Term::Zero);
    let b = deep(2000, Term::Succ(Rc::new(Term::Zero)));
    assert_ne!(a, b, "the fixtures must actually differ");
    assert_ne!(
        psi_hash(&a),
        psi_hash(&b),
        "psi_hash is only seeing a bounded prefix of the term"
    );
}
