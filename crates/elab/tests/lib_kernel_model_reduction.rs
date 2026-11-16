//! `lib/kernel_model/kernel_reduction.hthr` — a reference model of the
//! kernel's weak-head reduction and the substitution property the fold
//! classifier (`crates/kernel/src/eval/probe.rs`) relies on
//! (`docs/kernel/kernel-model-design.md`, milestone `hih-kernel-model`): the
//! refusal that needs the checker. The model run at literals, the probe lemma
//! at open values, and the `¬` theorems that each hypothesis is needed are
//! `lib/_tests/kernel_model/kernel_reduction_tests.hthr`, which the
//! whole-library gate checks (`crates/cli/tests/library.rs`;
//! docs/test-value-audit.md §3.4).

use crate::support::{self, Refusal};

const MODULES: &[(&str, &str)] = &[
    ("logic", include_str!("../../../lib/std/core/logic.hthr")),
    ("bool", include_str!("../../../lib/std/core/bool.hthr")),
    ("nat", include_str!("../../../lib/std/num/nat.hthr")),
    ("option", include_str!("../../../lib/std/core/option.hthr")),
    ("kernel_reduction", include_str!("../../../lib/kernel_model/kernel_reduction.hthr")),
];

/// The probe lemma cannot be applied to a blocked probe: its `Unblocked`
/// premise is a computed `False` at `split_step`, which cases on `k`, so the
/// citation is refused by conversion and not by a missing `Ground` witness
/// (the `Ground` premise is supplied and holds).
#[test]
fn the_lemma_needs_an_unblocked_probe() {
    let msg = support::assert_refused(
        &mut support::semantic_test_base(MODULES),
        "kernel_reduction_blocked",
        "import logic; import bool; import nat; import option; import kernel_reduction;
        fn split_step() → Tm { Lam(Lam(NRec(NZero, Lam(Lam(NZero)), Bv(1)))) }
        theorem bad():
                Tm::whnf(4, App(App(split_step(), NZero), NZero))
                    = Tm::whnf(4, Tm::probe(split_step())).map(λ (v: Tm) => v.inst(Tm::probe_sub(NZero, NZero))) {
            Tm::probe_step(split_step(), And(trivial, And(trivial, trivial)), 4, NZero, trivial, trivial, NZero, trivial, trivial, refl)
        }",
        Refusal::Kernel,
    );
    assert!(!msg.contains("Ground"), "{msg}");
}
