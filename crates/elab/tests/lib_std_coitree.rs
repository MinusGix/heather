//! `lib/std/itree/coitree.hthr` (`docs/itrees/coitree-design.md`): what needs the
//! checker. The observations and a client's own bisimilarities are
//! `lib/_tests/std/itree/coitree_tests.hthr`, which the whole-library gate
//! checks (`crates/cli/tests/library.rs`; docs/test-value-audit.md §3.4).
//! What is left: a bisimilarity between different leaves refused, and a goal
//! over `Bisim` naming it with its trees.

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
];

static BASE: OnceLock<SemanticImage> = OnceLock::new();

fn base() -> Elaborator {
    BASE.get_or_init(|| support::semantic_test_base(MODULES).semantic_image()).elaborator()
}

fn refused(name: &str, src: &str, why: Refusal) {
    support::assert_refused(&mut base(), name, &format!("{IMPORTS}{src}"), why);
}

const IMPORTS: &str = "import logic; import nat; import itree; import itree_trace; import coitree;\n";

/// Different leaves are not bisimilar.
#[test]
fn different_leaves_are_not_bisimilar() {
    refused("coitree_bisim_wrong", "fn bad(E: Events) → Bisim<Nat>(E, CRet(1), CRet(2)) { BRet(1, refl, refl) }", Refusal::Kernel);
}

// A goal over `Bisim` names it with its trees, through the named signature
// (`docs/inductives/codata-named-signature-design.md`).
#[test]
fn goals_name_bisimilarity() {
    refused(
        "coitree_goal",
        "theorem g<R>(E: Events, t: CoTree<R>(E), b: Bisim<R>(E, t, CoTree::spin(E))): t = t { ?g }",
        Refusal::Says("b : Bisim<R>(E, t, spin(E))"),
    );
}
