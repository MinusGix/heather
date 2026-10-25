//! `lib/std/itree/coitree_eutt.hthr`: what needs the checker. The counts and
//! a client's equivalences are `lib/_tests/std/itree/coitree_eutt_tests.hthr`,
//! which the whole-library gate checks (`crates/cli/tests/library.rs`;
//! docs/test-value-audit.md §3.4). What is left: a count too small to reach
//! the leaf and different leaves refused, and a goal over `Eutt` naming it
//! with its trees.

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
];

static BASE: OnceLock<SemanticImage> = OnceLock::new();

fn base() -> Elaborator {
    BASE.get_or_init(|| support::semantic_test_base(MODULES).semantic_image()).elaborator()
}

fn refused(name: &str, src: &str, why: Refusal) {
    support::assert_refused(&mut base(), name, &format!("{IMPORTS}{src}"), why);
}

const IMPORTS: &str =
    "import logic; import nat; import itree; import itree_trace; import coitree; import coitree_eutt;\n";

/// One silent step dropped of two does not reach the leaf (`two_taus` in the
/// probes drops both), and different leaves are not equivalent.
#[test]
fn a_short_count_or_a_different_leaf_is_refused() {
    refused("coitree_eutt_short", "fn bad(E: Events) → Eutt<Nat>(E, CTau(CTau(CRet(1))), CRet(1)) { ERet(1, 0, 1, refl, refl) }", Refusal::Kernel);
    refused("coitree_eutt_wrong", "fn bad(E: Events) → Eutt<Nat>(E, CRet(1), CRet(2)) { ERet(0, 0, 1, refl, refl) }", Refusal::Kernel);
}

/// A goal over `Eutt` names it with its trees.
#[test]
fn goals_name_equivalence() {
    refused(
        "coitree_eutt_goal",
        "theorem g<R>(E: Events, t: CoTree<R>(E), e: Eutt<R>(E, t, CoTree::spin(E))): t = t { ?g }",
        Refusal::Says("e : Eutt<R>(E, t, spin(E))"),
    );
}
