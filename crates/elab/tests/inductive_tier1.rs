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
         {{ j(p, λ y q => Node(l1, r) = Node(y, r), refl) }}

         theorem cong_node_r(l: Tree, r1: Tree, r2: Tree, p: r1 = r2):
             Node(l, r1) = Node(l, r2)
         {{ j(p, λ y q => Node(l, r1) = Node(l, y), refl) }}

         theorem trans_tree({{a: Tree}}, {{b: Tree}}, {{c: Tree}}, p: a = b, q: b = c): a = c
         {{ j(q, λ y r => a = y, p) }}

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

// §10.7 — no-confusion, both halves, on a tier-1 declaration. Disjointness
// is `elim_Wf` at the motive `Ty 0` (large elimination over a `Wf`, which
// needs no new kernel power); injectivity is `elim_Wf` at a constant motive,
// projecting a payload field with `fst`/`snd` and a recursive one with `nth`.
#[test]
fn no_confusion() {
    elab(&format!(
        "{TREE}
         theorem leaf_is_not_node(l: Tree, r: Tree, p: Leaf = Node(l, r)): Leaf = l {{
             absurd(p)
         }}

         theorem node_injective_left(a: Tree, b: Tree, c: Tree, d: Tree,
                                     p: Node(a, b) = Node(c, d)): a = c {{
             inj(p)
         }}

         theorem node_injective_right(a: Tree, b: Tree, c: Tree, d: Tree,
                                      p: Node(a, b) = Node(c, d)): b = d {{
             inj(p, 1)
         }}"
    ));
}

// Disjointness in an arm needs only the label's injection path. Its children
// vector is neutral there and deliberately need not be decoded merely to see
// that `Cons` and `Nil` are different
// (issues/absurd-on-branch-scrutinee.md).
#[test]
fn absurd_reads_a_recursive_match_arms_own_scrutinee() {
    elab(
        r#"
        inductive List<A> { Nil, Cons(A, List<A>) }
        theorem branch<A>(xs: List<A>): xs = Nil -> Nat {
            match xs {
                Nil => λ p => 0,
                Cons(h, t) => λ p => absurd(p),
            }
        }
        "#,
    );
}

// The payload half of injectivity, at a constructor that carries both a
// payload field and children: the two halves are projected by different
// mechanisms and both have to land on the declared field order.
#[test]
fn injectivity_across_payload_and_children() {
    elab(
        r#"
        inductive T { Tip(Nat), Two(n: Nat, l: T, r: T) }

        theorem tip_inj(a: Nat, b: Nat, p: Tip(a) = Tip(b)): a = b { inj(p) }

        theorem two_payload(a: Nat, b: Nat, l: T, r: T, l2: T, r2: T,
                            p: Two(a, l, r) = Two(b, l2, r2)): a = b { inj(p) }

        theorem two_left(a: Nat, b: Nat, l: T, r: T, l2: T, r2: T,
                         p: Two(a, l, r) = Two(b, l2, r2)): l = l2 { inj(p, 1) }

        theorem two_right(a: Nat, b: Nat, l: T, r: T, l2: T, r2: T,
                          p: Two(a, l, r) = Two(b, l2, r2)): r = r2 { inj(p, 2) }

        theorem tip_is_not_two(a: Nat, b: Nat, l: T, r: T,
                               p: Tip(a) = Two(b, l, r)): a = b { absurd(p) }
        "#,
    );
}

// §6.4 — the guardedness analysis is untrusted and can only *reject*, but it
// still has to reject: the argument in the decreasing position must be one of
// the recursive fields the arm binds, not the scrutinee and not a payload.
#[test]
fn a_self_call_must_descend() {
    let msg = elab_err(&format!(
        "{TREE}
         fn loop_forever(t: Tree) -> Tree {{
             match t {{ Leaf => Leaf, Node(l, r) => loop_forever(t) }}
         }}"
    ));
    assert!(msg.contains("must descend"), "{msg}");

    let msg = elab_err(
        r#"
        inductive T { Tip(Nat), One(n: Nat, s: T) }
        fn f(t: T) -> Nat {
            match t { Tip(n) => n, One(n, s) => f(t) }
        }
        "#,
    );
    assert!(msg.contains("must descend"), "{msg}");
}

#[test]
fn a_self_call_outside_a_match_is_rejected() {
    let msg = elab_err(&format!(
        "{TREE}
         fn f(t: Tree) -> Tree {{ f(t) }}"
    ));
    assert!(msg.contains("not structurally guarded"), "{msg}");
}

// Both children are reachable as ihs, at their own indices — the `Fin`-indexed
// ih is what distinguishes them, and getting the index wrong would still
// typecheck for a *symmetric* motive, so the asymmetric one is the test.
#[test]
fn each_child_has_its_own_ih() {
    elab(
        r#"
        inductive T { Tip(Nat), Two(T, T) }

        fn left_spine(t: T) -> Nat {
            match t { Tip(n) => n, Two(a, b) => left_spine(a) }
        }
        fn right_spine(t: T) -> Nat {
            match t { Tip(n) => n, Two(a, b) => right_spine(b) }
        }

        theorem l(): left_spine(Two(Tip(1), Tip(2))) = 1 { refl }
        theorem r(): right_spine(Two(Tip(1), Tip(2))) = 2 { refl }
        "#,
    );
}

// The shift observer (issues/tyvar-scoping-in-lowered-fields.md). Every
// declaration above is monomorphic, so `⟦D⟧` is *closed* and every
// `shift_local` in the lowering — `d_ty` in `wf.rs`, the children tuple's
// `snd_ty`, the spine shifts in `inject` — is a no-op. Instantiating a
// parameter at a context-dependent type (`n = n`) puts a free local inside
// `⟦D⟧` and makes all of them load-bearing at once, through the same
// acceptance the closed version goes through.
#[test]
fn the_lowering_shifts_are_exercised_by_a_dependent_parameter() {
    // `Node` carries a payload of the parameter's type as well as its two
    // children: that is what lets a constructor inside an `=` type recover
    // `A`, and it also puts a context-dependent type in the *shape* rather
    // than only in the leaves.
    elab(
        r#"
        inductive Tree<A> { Leaf(A), Node(A, Tree<A>, Tree<A>) }

        fn mirror(n: Nat, t: Tree<n = n>) -> Tree<n = n> {
            match t {
                Leaf(a) => Leaf(a),
                Node(a, l, r) => Node(a, mirror(n, r), mirror(n, l)),
            }
        }

        theorem cong_l(n: Nat, a: n = n, l1: Tree<n = n>, l2: Tree<n = n>,
                       r: Tree<n = n>, p: l1 = l2): Node(a, l1, r) = Node(a, l2, r)
        { j(p, λ y q => Node(a, l1, r) = Node(a, y, r), refl) }

        theorem cong_r(n: Nat, a: n = n, l: Tree<n = n>, r1: Tree<n = n>,
                       r2: Tree<n = n>, p: r1 = r2): Node(a, l, r1) = Node(a, l, r2)
        { j(p, λ y q => Node(a, l, r1) = Node(a, l, y), refl) }

        theorem tr(n: Nat, {x: Tree<n = n>}, {y: Tree<n = n>}, {z: Tree<n = n>},
                   p: x = y, q: y = z): x = z
        { j(q, λ w r => x = w, p) }

        theorem mirror_mirror(n: Nat, t: Tree<n = n>): mirror(n, mirror(n, t)) = t {
            match t {
                Leaf(a) => refl,
                Node(a, l, r) => tr(n,
                    @cong_l(n, a, mirror(n, mirror(n, l)), l, mirror(n, mirror(n, r)),
                            mirror_mirror(n, l)),
                    @cong_r(n, a, l, mirror(n, mirror(n, r)), r,
                            mirror_mirror(n, r))),
            }
        }
        "#,
    );
}

// The `Wf` case tree's **inner** injection annotations — axis 6 of
// `docs/testing-generated-terms.md`, swept by
// `issues/dependent-motive-crossing-sweep.md` (2026-08-05).
//
// `wf_case_tree`'s inner `Inr` is annotated `shift_local(d + 2)`, because it
// lands in `(cx, y, z')` — the `#rest` binder *and* the inner `Case`'s own
// motive binder, which is what the `embed(…, 2)` on the next line says. That
// is the shift the 2026-08-04 round fixed; nothing in *this* file pinned it,
// because every declaration here with an open payload has **two**
// constructors (`Tree<A>`, above) and every three-constructor one is
// monomorphic, so the annotations mention no ambient variable. What did pin
// it, measured by re-introducing the `d + 1`, was three tests in
// `indexed_route_2b_gen.rs` — the *fording* file, four layers up, whose
// `Tree<A>` happens to be three-constructor and polymorphic. That is
// `docs/container-fields.md` §10.1's rule going unpaid: the emitter is here,
// so its control belongs here, or the search for the next one starts from the
// wrong end.
//
// Unlike tier 0's, this emitter's motive is dependent *by construction* — a
// `Wf` step's motive is `Π(cs : Vec(⟦D⟧; arity a)). Π(ih). M[sup_f(a; cs)]`,
// whose domains mention the tag `a` whatever the surface motive is — so the
// 2026-08-05 third condition costs nothing here. The `as λ z` motive below is
// written dependent anyway, so the test keeps its meaning if that ever stops
// being true.
//
// `Tip` is the *middle* constructor deliberately: it is the one whose arm sits
// under the inner node.
#[test]
fn an_inner_wf_injection_is_scoped_two_binders_deep() {
    elab(
        r#"
        inductive Tr3<A> { Leaf, Tip(v: A), Node(l: Tr3<A>, r: Tr3<A>) }
        fn idt<A>(t: Tr3<A>) -> Tr3<A> { t }
        theorem idt_id<A>(t: Tr3<A>): idt(t) = t {
            match t as λ z => idt(z) = z {
                Leaf => refl,
                Tip(v) => refl,
                Node(l, r) => refl,
            }
        }
        // The equation binding drives the same tree through the convoy, whose
        // motive `Π(t = z). M` is dependent by construction.
        fn idt2<A>(t: Tr3<A>) -> Tr3<A> { t }
        theorem idt2_id<A>(t: Tr3<A>): idt2(t) = t {
            match h : t as λ z => idt2(z) = z {
                Leaf => refl,
                Tip(v) => refl,
                Node(l, r) => refl,
            }
        }
        "#,
    );
    // The controls, blind to the shift by construction: three constructors at
    // a **closed** payload (no ambient variable in any annotation)…
    elab(
        r#"
        inductive Tr3n { Leaf, Tip(v: Nat), Node(l: Tr3n, r: Tr3n) }
        fn idn(t: Tr3n) -> Tr3n { t }
        theorem idn_id(t: Tr3n): idn(t) = t {
            match t as λ z => idn(z) = z { Leaf => refl, Tip(v) => refl, Node(l, r) => refl }
        }
        "#,
    );
    // …and an open payload at **two** constructors, where there is no inner
    // `Case` at all.
    elab(
        r#"
        inductive Tr2<A> { Tip(v: A), Node(l: Tr2<A>, r: Tr2<A>) }
        fn id2<A>(t: Tr2<A>) -> Tr2<A> { t }
        theorem id2_id<A>(t: Tr2<A>): id2(t) = t {
            match t as λ z => id2(z) = z { Tip(v) => refl, Node(l, r) => refl }
        }
        "#,
    );
}
