//! `lib/std/itree/itree.hthr` (`docs/itree-core-round.md`): definitional
//! facts that do not hold, which the language cannot state as `¬` theorems
//! because they fail only up to conversion. What it can state is
//! `lib/_tests/std/itree/itree_tests.hthr`, which the whole-library gate
//! checks (`crates/cli/tests/library.rs`): the loop unrolling at a literal
//! and a successor fuel, right identity up to `Same`, and the `¬` theorems
//! that no fuel does not return and that `Same` tells different trees apart.
//! The client showcase is a CLI-tier row of `docs/showcase/showcases.tsv`
//! (docs/test-value-audit.md §3.4, §3.5).
//!
//! Both tests here are incompleteness pins (§4.6): each claim is refused by
//! conversion, and a stronger conversion (funext, unfolding at a variable)
//! would make it hold.

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
];

static BASE: OnceLock<SemanticImage> = OnceLock::new();

fn base() -> Elaborator {
    BASE.get_or_init(|| support::semantic_test_base(MODULES).semantic_image()).elaborator()
}

const IMPORTS: &str = "import logic; import nat; import itree;\n";

fn refused(name: &str, src: &str) {
    support::assert_refused(&mut base(), name, &format!("{IMPORTS}{src}"), Refusal::Kernel);
}

/// Incompleteness pin: the loop is stuck at a bare variable fuel, so it is
/// not `Cut` by conversion.
#[test]
fn iter_is_stuck_at_a_variable() {
    refused(
        "itree_iter_neutral",
        "theorem bad<A, B>(E: Events, n: Nat, body: A → ITree<Step<A, B>>(E), a: A): ITree::iter(E, n, body, a) = Cut { refl }",
    );
}

/// Incompleteness pin: right identity through `Vis` is not an equation by
/// conversion, at a neutral tree or at one `Vis` with an open continuation,
/// where a pointwise fact would need funext. It holds up to `Same`
/// (`roundtrip` and `vis_ret_r` in the probes).
#[test]
fn right_identity_is_same_not_equal() {
    refused("itree_ret_r_eq", "theorem bad<R>(E: Events, t: ITree<R>(E)): ITree::bind(E, t, λ r => Ret(r)) = t { refl }");
    refused(
        "itree_ret_r_vis_eq",
        "theorem bad<R>(E: Events, c: E.Cmd, k: E.Resp(c) → ITree<R>(E)): ITree::bind<R, R>(E, Vis(c, k), λ r => Ret(r)) = Vis(c, k) { refl }",
    );
}
