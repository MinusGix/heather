//! Acceptance for tier-1 branching inductives (issues/wf-former.md phase 5,
//! `issues/tier1-branching-constructors.md`), against the checklist of
//! `docs/inductive-tier1-wf-lowering.md` §10.
//!
//! The point of the tier, as at tier 0: every declaration below is lowered —
//! here onto `Wf`/`sup_f`/`elim_Wf` — and then re-checked by the *real
//! kernel*, so a wrong encoding shows up as a rejection. The test that
//! matters most is `mirror_of_mirror`, which is `crates/kernel/tests/wf.rs`'s
//! hand-built acceptance written at the surface instead.

use heather_elab::{ElabError, Elaborator};

fn elab(src: &str) -> Elaborator {
    let mut e = Elaborator::with_prelude().expect("prelude");
    e.elab_source(src).unwrap_or_else(|err| panic!("{}", err.render(src)));
    e
}

fn elab_err(src: &str) -> String {
    let mut e = Elaborator::with_prelude().expect("prelude");
    match e.elab_source(src) {
        Err(ElabError::Elab { msg, .. }) => msg,
        Err(other) => format!("{other}"),
        Ok(()) => panic!("expected an error, but this elaborated:\n{src}"),
    }
}

const TREE: &str = r#"
inductive Tree { Leaf, Node(Tree, Tree) }
"#;

// §10.1–2 — the declaration lowers to a `Wf`, and its constructors check,
// including at *open* children (the property every finitary encoding lacks).
#[test]
fn tree_declares_and_builds() {
    elab(&format!(
        "{TREE}
         fn leaf() -> Tree {{ Leaf }}
         fn one() -> Tree {{ Node(Leaf, Leaf) }}
         fn under(l: Tree, r: Tree) -> Tree {{ Node(l, r) }}
         fn deep(t: Tree) -> Tree {{ Node(Node(t, Leaf), t) }}"
    ));
}

// §10.3 — `match` lowers to `elim_Wf`, self-calls become the `Fin`-indexed
// ih, and the result *computes*: `refl` proves a closed evaluation.
#[test]
fn mirror_computes() {
    elab(&format!(
        "{TREE}
         fn mirror(t: Tree) -> Tree {{
             match t {{
                 Leaf => Leaf,
                 Node(l, r) => Node(mirror(r), mirror(l)),
             }}
         }}
         theorem m_leaf(): mirror(Leaf) = Leaf {{ refl }}
         theorem m_one(): mirror(Node(Leaf, Leaf)) = Node(Leaf, Leaf) {{ refl }}
         theorem m_two(): mirror(Node(Node(Leaf, Leaf), Leaf))
                        = Node(Leaf, Node(Leaf, Leaf)) {{ refl }}"
    ));
}

// β fires on a constructor form whatever the children are, so `mirror` of an
// *open* node reduces — the route-A property that the finitary encodings
// cannot have and that the whole `Wf` design is for.
#[test]
fn beta_fires_on_open_children() {
    elab(&format!(
        "{TREE}
         fn mirror(t: Tree) -> Tree {{
             match t {{
                 Leaf => Leaf,
                 Node(l, r) => Node(mirror(r), mirror(l)),
             }}
         }}
         theorem open_node(l: Tree, r: Tree):
             mirror(Node(l, r)) = Node(mirror(r), mirror(l)) {{ refl }}"
    ));
}

// §10.5 — arities 0/1/2 in one declaration, with a payload field alongside
// the recursive ones. The payload and the children are separated by the
// lowering and have to come back in declaration order.
#[test]
fn mixed_arities_and_payloads() {
    elab(
        r#"
        inductive T { Tip(Nat), One(T), Two(T, T) }

        fn label(t: T) -> Nat {
            match t {
                Tip(n) => n,
                One(s) => label(s),
                Two(a, b) => label(a),
            }
        }

        theorem l0(): label(Tip(3)) = 3 { refl }
        theorem l1(): label(One(Tip(4))) = 4 { refl }
        theorem l2(): label(Two(Tip(5), Tip(6))) = 5 { refl }
        "#,
    );
}

// §10.6 — the linear tier folds in: `List` is an arity-≤1 declaration on the
// same path, with no exact-height fording anywhere.
#[test]
fn linear_declarations_fold_in() {
    elab(
        r#"
        inductive List { Nil, Cons(head: Nat, tail: List) }

        fn len(xs: List) -> Nat {
            match xs {
                Nil => 0,
                Cons(h, t) => Succ(len(t)),
            }
        }

        theorem len0(): len(Nil) = 0 { refl }
        theorem len2(): len(Cons(1, Cons(2, Nil))) = 2 { refl }
        "#,
    );
}

// §10.4 — **the acceptance**. `mirror (mirror t) = t` by a surface recursive
// `theorem`, which is what `crates/kernel/tests/wf.rs` proves by hand. The
// dependent motive means the ih really is `M[child/z]` at each index, and the
// constructor-form gap route A bridges with funext is closed by conversion,
// so it never appears in the proof.
#[test]
fn mirror_of_mirror() {
    elab(&format!(
        "{TREE}
         fn mirror(t: Tree) -> Tree {{
             match t {{
                 Leaf => Leaf,
                 Node(l, r) => Node(mirror(r), mirror(l)),
             }}
         }}

         theorem cong_node_l(l1: Tree, l2: Tree, r: Tree, p: l1 = l2):
             Node(l1, r) = Node(l2, r)
         {{ j(p, (y, q) -> Node(l1, r) = Node(y, r), refl) }}

         theorem cong_node_r(l: Tree, r1: Tree, r2: Tree, p: r1 = r2):
             Node(l, r1) = Node(l, r2)
         {{ j(p, (y, q) -> Node(l, r1) = Node(l, y), refl) }}

         theorem trans_tree({{a: Tree}}, {{b: Tree}}, {{c: Tree}}, p: a = b, q: b = c): a = c
         {{ j(q, (y, r) -> a = y, p) }}

         theorem mirror_mirror(t: Tree): mirror(mirror(t)) = t {{
             match t {{
                 Leaf => refl,
                 Node(l, r) => trans_tree(
                     @cong_node_l(mirror(mirror(l)), l, mirror(mirror(r)),
                                  mirror_mirror(l)),
                     @cong_node_r(l, mirror(mirror(r)), r, mirror_mirror(r))),
             }}
         }}"
    ));
}

// §10.8 — the rejections stay rejections, with their own messages.
#[test]
fn nested_recursion_is_diagnosed() {
    let msg = elab_err(
        r#"
        inductive List { Nil, Cons(head: Nat, tail: List) }
        inductive Rose { Node(kids: List<Rose>) }
        "#,
    );
    assert!(msg.contains("nested"), "{msg}");
}

#[test]
fn a_recursive_field_is_not_in_scope_later() {
    // §2: a recursive field is a child, not a component of the shape, so
    // nothing later can depend on it.
    let msg = elab_err(
        r#"
        inductive T { Mk(t: T, p: t = t) }
        fn use_it(x: T) -> Nat { 0 }
        "#,
    );
    assert!(msg.contains("unbound name `t`"), "{msg}");
}
