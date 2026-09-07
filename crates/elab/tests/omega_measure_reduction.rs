//! Acceptance for issues/omega-measure-at-constructor-pattern.md
//! (docs/omega-measure-reduction-design.md): at `omega`'s atom fallback a
//! measure applied to a constructor value is reduced, kept only when its head
//! became arithmetic, and its leaves named by conversion against candidates
//! built from the original's own spelling. The obligation this closes is
//! `list_len(t) < list_len(Cons(h, t))` — the most common `decreases` there
//! is, refused before this round and discharged by hand everywhere else.
//!
//! What the positives vary (docs/testing-generated-terms.md): one measure in
//! two spellings (`list_len(xs)` and `xs.len()`), a **branching** measure
//! whose reduct has two leaves, a two-successor measure that needs §2.1's
//! second naming, and an **open element type**. The controls pin what
//! reduction must *not* change: a non-decreasing site is still refused with
//! its wording, an opaque head still interns unreduced, and the `lift = false`
//! re-lowering is no longer reached on the reproducer.
//!
//! The kept-by-hand sites (`runs`'s `drop_eq_le`, `gcd`'s `nat::mod_lt`) and
//! the removed ones (`merge`'s two `on`s) live in `termination_measures.rs`,
//! and the group's in `mutual_recursion.rs`.

use heather_elab::{ElabError, Elaborator};

const LOGIC: &str = include_str!("../../../lib/std/logic.hthr");
const BOOL: &str = include_str!("../../../lib/std/bool.hthr");
const NAT: &str = include_str!("../../../lib/std/nat.hthr");
const OPTION: &str = include_str!("../../../lib/std/option.hthr");
const PAIR: &str = include_str!("../../../lib/std/pair.hthr");
const LIST: &str = include_str!("../../../lib/std/list.hthr");
const ALGEBRA: &str = include_str!("../../../lib/std/algebra.hthr");
const INT: &str = include_str!("../../../lib/std/int.hthr");
const OMEGA: &str = include_str!("../../../lib/std/omega.hthr");

fn base() -> Elaborator {
    let mut e = Elaborator::with_prelude().expect("prelude");
    for (name, src) in [
        ("logic", LOGIC),
        ("bool", BOOL),
        ("nat", NAT),
        ("option", OPTION),
        ("pair", PAIR),
        ("list", LIST),
        ("algebra", ALGEBRA),
        ("int", INT),
        ("omega", OMEGA),
    ] {
        if let Err(err) = e.elab_module_source(name, src) {
            panic!("{name} did not check: {err}");
        }
    }
    e
}

const IMPORTS: &str = "import logic;\nimport nat;\nimport list;\nimport int;\nimport omega;\n";

fn ok(src: &str) {
    let mut e = base();
    e.elab_module_source("m", &format!("{IMPORTS}{src}"))
        .unwrap_or_else(|err| panic!("expected this to check, got: {err}"));
}

fn elab_err(src: &str) -> String {
    let mut e = base();
    match e.elab_module_source("m", &format!("{IMPORTS}{src}")) {
        Err(ElabError::Elab { msg, .. }) => msg,
        other => panic!("expected a surface elaboration error, got {other:?}"),
    }
}

const DROP1: &str = r#"
fn drop1(xs: List<Nat>) -> Nat decreases list_len(xs) {
    match xs { Nil => 0, Cons(h, t) => Succ(drop1(t)) }
}
"#;

#[test]
fn a_list_tail_closes_by_omega_alone() {
    ok(&format!(
        "{DROP1}\n\
         theorem drop1_two(): drop1([7, 8]) = 2 {{ refl }}\n\
         // the non-`decreases` occurrence of the same defect (design §1.1)\n\
         theorem at_ctor(h: Nat, xs: List<Nat>): nat::Lt(list_len(xs), list_len(Cons(h, xs))) {{ omega }}"
    ));
}

#[test]
fn the_member_spelling_of_the_same_measure_closes_too() {
    // `xs.len()` is `list::List::len`, a wrapper the reducer walks through
    // before it reaches the `Succ` — a second spelling of one measure, which
    // is what design §3 says a syntactic unfolding would not cover.
    ok(r#"
        fn drop1_len(xs: List<Nat>) -> Nat decreases xs.len() {
            match xs { Nil => 0, Cons(h, t) => Succ(drop1_len(t)) }
        }
        theorem drop1_len_two(): drop1_len([7, 8]) = 2 { refl }
    "#);
}

#[test]
fn a_tree_measure_names_both_leaves() {
    // The reduct is `Succ(nat::add(u₁, u₂))`: two unspellable leaves, two
    // recursive fields, two candidates (design §2's table, row 3).
    ok(r#"
        inductive Tree { Leaf, Node(left: Tree, right: Tree) }

        fn tnodes(t: Tree) -> Nat {
            match t { Leaf => 0, Node(l, r) => Succ(nat::add(tnodes(l), tnodes(r))) }
        }

        fn tsum(t: Tree) -> Nat decreases tnodes(t) {
            match t { Leaf => 1, Node(l, r) => nat::add(tsum(l), tsum(r)) }
        }

        theorem tsum_leaf(): tsum(Leaf) = 1 { refl }
        theorem tsum_node(): tsum(Node(Leaf, Leaf)) = 2 { refl }
    "#);
}

#[test]
fn a_two_successor_measure_closes_through_the_second_reduction() {
    // The §2.1 note: `dlen(Cons(h, t))` unfolds to `Succ(Succ(dlen(t)))`, so
    // the leaf of the first reduct is itself a successor no candidate converts
    // against. Naming that leaf under the *same* candidates reaches `dlen(t)`.
    ok(r#"
        fn dlen(xs: List<Nat>) -> Nat {
            match xs { Nil => 0, Cons(h, t) => Succ(Succ(dlen(t))) }
        }

        fn dwalk(xs: List<Nat>) -> Nat decreases dlen(xs) {
            match xs { Nil => 0, Cons(h, t) => Succ(dwalk(t)) }
        }

        theorem dwalk_two(): dwalk([7, 8]) = 2 { refl }
    "#);
}

#[test]
fn the_measure_closes_at_an_open_element_type() {
    // docs/testing-generated-terms.md's open-element axis: `List<A>`, where
    // the constructor value's fields are not `Nat`s and nothing about the
    // element computes.
    ok(r#"
        fn drop1_open<A>(xs: List<A>) -> Nat decreases list_len(xs) {
            match xs { Nil => 0, Cons(h, t) => Succ(drop1_open<A>(t)) }
        }
        theorem drop1_open_two(a, b: Nat): drop1_open<Nat>([a, b]) = 2 { refl }
        theorem drop1_open_nil<A>(): drop1_open<A>(Nil) = 0 { refl }
    "#);
}

#[test]
fn the_lifted_obligation_is_accepted_so_the_retry_is_not_reached() {
    // Design §7's fifth control. `elab_measure_decl` re-lowers with
    // `lift = false` only when the checker refuses a lifted `f#obl_N`, and it
    // records the reason against `f_unfold` and declines the companions. A
    // citation of `drop1_unfold` therefore reports the retry — unless the
    // lifted attempt was accepted, which is the claim.
    let mut e = base();
    let msg = match e.elab_module_source(
        "m",
        &format!(
            "{IMPORTS}{DROP1}\n\
             theorem cite(xs: List<Nat>): drop1(xs) = drop1(xs) {{ drop1_unfold(xs) }}"
        ),
    ) {
        Ok(()) => String::new(),
        Err(err) => format!("{err}"),
    };
    assert!(!msg.contains("no unfolding equation"), "{msg}");
    assert!(!msg.contains("was refused"), "{msg}");
}

// -- negative controls --------------------------------------------------------

#[test]
fn a_non_decreasing_measure_at_a_constructor_pattern_is_still_refused() {
    // Design §7 control 1. Both sides reduce to `Succ(list_len(t))`, so
    // reduction must not turn a refusal into an acceptance — and must not
    // lose §2-of-the-measures-doc's wording.
    let msg = elab_err(
        r#"
        fn stall(xs: List<Nat>) -> Nat decreases list_len(xs) {
            match xs { Nil => 0, Cons(h, t) => Succ(stall(xs)) }
        }
        "#,
    );
    assert!(msg.contains("must decrease the measure"), "{msg}");
    assert!(msg.contains("Discharge it by hand"), "{msg}");
    assert!(msg.contains("on ?dec1"), "{msg}");
}

#[test]
fn a_neutral_measure_head_still_interns_under_its_own_spelling() {
    // Design §7 control 2, and control 4's neutral site beside the literal
    // one: `runs`'s call is on a suffix a *callee* returned, so the measure
    // head is opaque under any reduction and the atom is spelled by the term
    // the writer wrote. Without the `on` the report names it unreduced.
    let msg = elab_err(
        r#"
        fn drop_eq(t: Nat, ts: List<Nat>) -> List<Nat> {
            match ts {
                Nil => Nil,
                Cons(h, rest) => match nat::eq_dec(t, h) { Inl(_) => drop_eq(t, rest), Inr(_) => Cons(h, rest) },
            }
        }

        fn runs(ts: List<Nat>) -> Nat decreases ts.len() {
            match ts {
                Nil => 0,
                Cons(t, rest) => Succ(runs(drop_eq(t, rest))),
            }
        }
        "#,
    );
    assert!(msg.contains("must decrease the measure"), "{msg}");
    assert!(msg.contains("drop_eq(t, rest)"), "{msg}");
    assert!(!msg.contains("elim"), "{msg}");
}
