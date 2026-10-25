//! `lib/std/itree/coitree_bridge.hthr`: what needs the checker. The
//! embedding's observations and the loops, cuts and binds carrying traces
//! both ways are `lib/_tests/std/itree/coitree_bridge_tests.hthr`, which the
//! whole-library gate checks (`crates/cli/tests/library.rs`;
//! docs/test-value-audit.md §3.4). What is left are the fuel and depth
//! controls: one less of either than the probes' `fuelled` and `fuel_free`
//! leaves a `Cut` where the return was.

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
    ("coitree", include_str!("../../../lib/std/itree/coitree.hthr")),
    ("coitree_eutt", include_str!("../../../lib/std/itree/coitree_eutt.hthr")),
    ("coitree_bridge", include_str!("../../../lib/std/itree/coitree_bridge.hthr")),
];

static BASE: OnceLock<SemanticImage> = OnceLock::new();

fn base() -> Elaborator {
    BASE.get_or_init(|| support::semantic_test_base(MODULES).semantic_image()).elaborator()
}

const IMPORTS: &str = "import logic; import nat; import itree; import itree_trace; import coitree; import coitree_eutt; \
     import coitree_bridge;\n";

// A literal loop: each pass is a silent step and then a `Continue`, so two
// passes and the `Break` take fuel 3 and depth 5.
const DOWN: &str = "
    fn down(E: Events, a: Nat) → ITree<Step<Nat, Nat>>(E) {
        match a { Zero => Ret(Break(0)), Succ(m) => Tau(Ret(Continue(m))) }
    }
    fn co_down(E: Events, a: Nat) → CoTree<Nat>(E) { CoTree::iter(E, λ x => CoTree::of_tree(E, down(E, x)), a) }
";

#[test]
fn one_less_fuel_or_depth_returns_nothing() {
    for (name, case) in [
        ("coitree_bridge_short_fuel", "theorem bad(E: Events): Program::Produces<Nat>(E, Program::iter<Nat, Nat>(E, λ x => down(E, x), 2), TRet(0)) {
            Converges(2, Returned(refl))
        }"),
        ("coitree_bridge_short_depth", "theorem bad(E: Events): Program::Produces<Nat>(E, CoTree::program(E, co_down(E, 2)), TRet(0)) {
            Converges(4, Returned(refl))
        }"),
    ] {
        support::assert_refused(&mut base(), name, &format!("{IMPORTS}{DOWN}{case}"), Refusal::Says("constructor of `RetTrace`"));
    }
}
