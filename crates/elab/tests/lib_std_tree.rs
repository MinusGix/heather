//! `lib/std/tree.hthr` — the branching half of the explicit recursion-algebra
//! experiment (`issues/datatype-container-algebras.md`).
//!
//! The headline test folds a tree into a list with `append`, then fuses `len`
//! through that fold into a Nat algebra. Both Node results are used, the leaf
//! type stays open, and the tree is neutral. That is the control a linear list
//! fold cannot provide.

use heather_elab::{ElabError, Elaborator};

const LOGIC: &str = include_str!("../../../lib/std/logic.hthr");
const BOOL: &str = include_str!("../../../lib/std/bool.hthr");
const NAT: &str = include_str!("../../../lib/std/nat.hthr");
const OPTION: &str = include_str!("../../../lib/std/option.hthr");
const PAIR: &str = include_str!("../../../lib/std/pair.hthr");
const LIST: &str = include_str!("../../../lib/std/list.hthr");
const TREE: &str = include_str!("../../../lib/std/tree.hthr");

fn run(extra: &str) -> Result<Elaborator, String> {
    let mut e = Elaborator::with_prelude().expect("prelude");
    for (name, src) in [
        ("logic", LOGIC),
        ("bool", BOOL),
        ("nat", NAT),
        ("option", OPTION),
        ("pair", PAIR),
        ("list", LIST),
        ("tree", TREE),
    ] {
        if let Err(err) = e.elab_module_source(name, src) {
            return Err(match err {
                ElabError::Elab { msg, .. } => format!("{name}: {msg}"),
                other => format!("{name}: {other}"),
            });
        }
    }
    if !extra.is_empty() {
        let src = format!("import list;\nimport nat;\nimport tree;\n{extra}");
        if let Err(err) = e.elab_module_source("probe", &src) {
            return Err(match err {
                ElabError::Elab { msg, .. } => msg,
                other => format!("{other}"),
            });
        }
    }
    Ok(e)
}

fn ok(extra: &str) -> Elaborator {
    run(extra).unwrap_or_else(|e| panic!("expected this to check, got: {e}"))
}

fn bad(extra: &str) -> String {
    match run(extra) {
        Err(e) => e,
        Ok(_) => panic!("expected a refusal, but it checked"),
    }
}

#[test]
fn the_tree_module_checks() {
    ok("");
}

#[test]
fn fusion_uses_both_branches_at_an_open_leaf_type() {
    ok(r#"
fn leaves_alg<A>() -> TreeAlg<A, List<A>> {
    TreeAlg<A, List<A>> {
        leaf: λ (a: A) => Cons(a, Nil),
        node: append,
    }
}

fn leaf_count_alg<A>() -> TreeAlg<A, Nat> {
    TreeAlg<A, Nat> {
        leaf: λ (a: A) => 1,
        node: add,
    }
}

theorem leaf_count_fusion<A>(tree: Tree<A>):
    len(tree_fold(leaves_alg<A>(), tree)) = tree_fold(leaf_count_alg<A>(), tree)
{
    tree_fold_fusion(
        leaves_alg<A>(), leaf_count_alg<A>(), λ (xs: List<A>) => len(xs),
        λ (a: A) => refl,
        λ (left: List<A>) (right: List<A>) => len_append(left, right), tree)
}
"#);
}

#[test]
fn the_branching_fold_computes() {
    ok(r#"
fn sample() -> Tree<Nat> { Node(Leaf(2), Node(Leaf(3), Leaf(5))) }

theorem leaves_compute():
    tree_fold(TreeAlg<Nat, List<Nat>> {
        leaf: λ (n: Nat) => Cons(n, Nil),
        node: append,
    }, sample()) = Cons(2, Cons(3, Cons(5, Nil)))
{ refl }

// Three leaves plus two internal nodes.
theorem size_computes(): tree_size(sample()) = 5 { refl }
theorem rebuild_computes(): tree_fold(tree_rebuild_alg<Nat>(), sample()) = sample() {
    tree_rebuild_id(sample())
}
"#);
}

#[test]
fn the_dependent_tree_algebra_accepts_an_open_motive() {
    ok(r#"
theorem e_use<A>(P: Tree<A> -> Type, alg: TreeElim<A>(P), tree: Tree<A>): P(tree) {
    tree_elim(P, alg, tree)
}

theorem e_leaf<A>(P: Tree<A> -> Type, alg: TreeElim<A>(P), value: A):
    tree_elim(P, alg, Leaf(value)) = alg.leaf(value)
{ tree_elim_leaf(P, alg, value) }

theorem e_node<A>(P: Tree<A> -> Type, alg: TreeElim<A>(P), left, right: Tree<A>):
    tree_elim(P, alg, Node(left, right)) =
        alg.node(left, right, tree_elim(P, alg, left), tree_elim(P, alg, right))
{ tree_elim_node(P, alg, left, right) }

theorem e_rebuild<A>(tree: Tree<A>): tree_fold(tree_rebuild_alg<A>(), tree) = tree {
    tree_rebuild_id(tree)
}
"#);
}

#[test]
fn a_node_obligation_cannot_return_one_childs_proof() {
    let msg = bad(r#"
fn wrong<A>() -> TreeElim<A>(λ (tree: Tree<A>) => tree = tree) {
    TreeElim {
        leaf: λ (value: A) => refl,
        // The left IH is indexed by `left`, not by `Node(left, right)`.
        node: λ (left: Tree<A>) (right: Tree<A>) ih_left ih_right => ih_left,
    }
}
"#);
    assert!(msg.contains("left = left") && msg.contains("expected"), "{msg}");
}
