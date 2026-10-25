//! `lib/std/data/tree.hthr` — the branching half of the explicit
//! recursion-algebra experiment (`issues/datatype-container-algebras.md`):
//! the refusals that need the checker. What the language can state is
//! `lib/_tests/std/data/tree_tests.hthr`, which the whole-library gate checks
//! (`crates/cli/tests/library.rs`): fusion through a fold that uses both
//! `Node` results at an open leaf type, the fold and the mirror computing,
//! and the `¬` theorem that the mirror moves leaves (docs/test-value-audit.md
//! §3.4).

use crate::support::{self, Refusal};
use heather_elab::Elaborator;

const LOGIC: &str = include_str!("../../../lib/std/core/logic.hthr");
const BOOL: &str = include_str!("../../../lib/std/core/bool.hthr");
const NAT: &str = include_str!("../../../lib/std/num/nat.hthr");
const OPTION: &str = include_str!("../../../lib/std/core/option.hthr");
const PAIR: &str = include_str!("../../../lib/std/core/pair.hthr");
const LIST: &str = include_str!("../../../lib/std/data/list.hthr");
const TREE: &str = include_str!("../../../lib/std/data/tree.hthr");

fn elaborated() -> Elaborator {
    support::library(&[
        ("logic", LOGIC),
        ("bool", BOOL),
        ("nat", NAT),
        ("option", OPTION),
        ("pair", PAIR),
        ("list", LIST),
        ("tree", TREE),
    ])
}

fn refused(src: &str, why: Refusal) {
    support::assert_refused(&mut elaborated(), "probe", &format!("import list;\nimport nat;\nimport tree;\n{src}"), why);
}

/// `ih_left` knows only that the left subtree kept its size; it cannot
/// certify dropping the whole right branch at the `Node` obligation. The
/// obligation is a computed type, so the kernel is what refuses it.
#[test]
fn a_wrong_node_clause_cannot_be_certified() {
    refused(
        r#"
fn drop_right_alg<A>() -> TreeAlg<A, Tree<A>> {
    TreeAlg<A, Tree<A>> {
        leaf: λ (value: A) => Leaf(value),
        node: λ (left: Tree<A>) (right: Tree<A>) => left,
    }
}

fn bad_size_laws<A>() -> TreePassLaws<A>(TreeSameSize<A>, drop_right_alg<A>()) {
    TreePassLaws {
        leaf: λ (value: A) => refl,
        node: λ (left: Tree<A>) (left_r: Tree<A>) ih_left
                (right: Tree<A>) (right_r: Tree<A>) ih_right => ih_left,
    }
}
"#,
        Refusal::Kernel,
    );
}

/// The left IH is indexed by `left`, not by `Node(left, right)`.
#[test]
fn a_node_obligation_cannot_return_one_childs_proof() {
    refused(
        r#"
fn wrong<A>() -> TreeElim<A>(λ (tree: Tree<A>) => tree = tree) {
    TreeElim {
        leaf: λ (value: A) => refl,
        node: λ (left: Tree<A>) (right: Tree<A>) ih_left ih_right => ih_left,
    }
}
"#,
        Refusal::Says("this has type `left = left`, but `Node(left, right) = Node(left, right)` is expected here"),
    );
}
