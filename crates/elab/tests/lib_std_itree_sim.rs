//! `lib/std/itree/itree_sim.hthr` (`docs/itree-simulation-design.md`): the
//! simulation's vacuity controls. The simulations themselves are
//! `lib/_tests/std/itree/itree_sim_tests.hthr`, which the whole-library gate
//! checks (`crates/cli/tests/library.rs`; docs/test-value-audit.md §3.4):
//! silent passes refining a loop that leaves at once, a calling pass
//! simulated call for call, and a pass of two calls as two spec passes.
//!
//! What is left are refusals by the kernel: a spec that leaves with another
//! value, a source call the spec does not make, and a mutation of the
//! probes' two-call proof whose spec leaves with another value.

use std::sync::OnceLock;

use heather_elab::{Elaborator, SemanticImage};

use crate::support::{self, Refusal};

const MODULES: &[(&str, &str)] = &[
    ("logic", include_str!("../../../lib/std/core/logic.hthr")),
    ("bool", include_str!("../../../lib/std/core/bool.hthr")),
    ("nat", include_str!("../../../lib/std/num/nat.hthr")),
    ("option", include_str!("../../../lib/std/core/option.hthr")),
    ("pair", include_str!("../../../lib/std/core/pair.hthr")),
    ("list", include_str!("../../../lib/std/data/list.hthr")),
    ("itree", include_str!("../../../lib/std/itree/itree.hthr")),
    ("itree_trace", include_str!("../../../lib/std/itree/itree_trace.hthr")),
    ("itree_sim", include_str!("../../../lib/std/itree/itree_sim.hthr")),
];

static BASE: OnceLock<SemanticImage> = OnceLock::new();

fn base() -> Elaborator {
    BASE.get_or_init(|| support::semantic_test_base(MODULES).semantic_image()).elaborator()
}

fn refused(name: &str, src: &str) {
    support::assert_refused(&mut base(), name, src, Refusal::Kernel);
}

const IMPORTS: &str = "import logic; import nat; import itree; import itree_trace; import itree_sim;\n";

const DOWN: &str = "
fn down_body(E: Events, a: Nat) → ITree<Step<Nat, Nat>>(E) {
    match a { Zero => Ret(Break(0)), Succ(m) => Ret(Continue(m)) }
}
fn now_body(E: Events, u: True) → ITree<Step<True, Nat>>(E) { Ret(Break(0)) }
";

/// A pass that leaves with 1 is not simulated by a spec that leaves with 0.
#[test]
fn a_spec_that_leaves_with_another_value_is_refused() {
    refused(
        "itree_sim_down_wrong",
        &format!(
            "{IMPORTS}{DOWN}
            fn one_body(E: Events, u: True) → ITree<Step<True, Nat>>(E) {{ Ret(Break(1)) }}
            theorem bad(E: Events): ITree::PassSim<Nat, True, Nat>(E, E, TraceMap::id(E), Contract::none(E), λ x y => True,
                λ x => down_body(E, x), λ y => one_body(E, y), 0, trivial)
            {{
                Inl(SimRet(Break(1), refl, refl))
            }}"
        ),
    );}

const CALL: &str = "
fn call_body(E: Events, c: E.Cmd, a: Nat) → ITree<Step<Nat, Nat>>(E) {
    ITree::bind(E, ITree::trigger(E, c), λ x => Ret(Break(a)))
}
";

/// A source call the spec does not make is refused.
#[test]
fn a_call_the_spec_does_not_make_is_refused() {
    refused(
        "itree_sim_call_wrong",
        &format!(
            "{IMPORTS}{CALL}
            theorem bad(E: Events, c: E.Cmd, a: Nat):
                ITree::Sim<Step<Nat, Nat>, Step<Nat, Nat>>(E, E, TraceMap::id(E), Contract::none(E), λ x y => x = y,
                    call_body(E, c, a), Ret(Break(a)))
            {{
                SimVis(trivial, λ x => Ret(Break(a)), refl, λ x v => SimRet(Break(a), refl, refl))
            }}"
        ),
    );}

/// The probes' two-call simulation with its spec leaving with 1 where the
/// source leaves with 0: a mutation that goes through the proof.
#[test]
fn a_pass_of_two_calls_leaving_with_another_value_is_refused() {
    let probes = include_str!("../../../lib/_tests/std/itree/itree_sim_tests.hthr");
    let right = "λ y v => SimRet(0, refl, refl)";
    assert_eq!(probes.matches(right).count(), 1, "the mutation's target moved in itree_sim_tests.hthr");
    refused("itree_sim_twice_wrong", &probes.replace(right, "λ y v => SimRet(1, refl, refl)"));
}
