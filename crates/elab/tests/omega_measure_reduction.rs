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
//! The kept-by-hand sites (`runs`'s `drop_eq_le`, `gcd`'s `nat::Nat::mod_lt`) and
//! the removed ones (`merge`'s two `on`s) live in `termination_measures.rs`,
//! and the group's in `mutual_recursion.rs`.
//!
//! The last section is the same design's filed-separately gap
//! (issues/tier1-arm-binder-has-no-spelling.md): a `match` arm's binders
//! spell by name, so an `omega` goal inside an arm can mention them.

use std::cell::OnceCell;
use std::sync::Mutex;

use heather_elab::{ElabError, Elaborator, SemanticImage};

use crate::support;

const LOGIC: &str = include_str!("../../../lib/std/logic.hthr");
const BOOL: &str = include_str!("../../../lib/std/bool.hthr");
const NAT: &str = include_str!("../../../lib/std/nat.hthr");
const OPTION: &str = include_str!("../../../lib/std/option.hthr");
const PAIR: &str = include_str!("../../../lib/std/pair.hthr");
const LIST: &str = include_str!("../../../lib/std/list.hthr");
const ALGEBRA: &str = include_str!("../../../lib/std/algebra.hthr");
const INT: &str = include_str!("../../../lib/std/int.hthr");
const OMEGA: &str = include_str!("../../../lib/std/omega.hthr");

/// The same prefix, in the same order, as `semantic_omega_warmup.rs`, so the
/// on-disk image keys this file reads are the ones the warmup wrote.
const MODULES: &[(&str, &str)] = &[
    ("logic", LOGIC),
    ("bool", BOOL),
    ("nat", NAT),
    ("option", OPTION),
    ("pair", PAIR),
    ("list", LIST),
    ("algebra", ALGEBRA),
    ("int", INT),
    ("omega", OMEGA),
];

static PREFIX_LOAD: Mutex<()> = Mutex::new(());

thread_local! {
    static BASE: OnceCell<SemanticImage> = const { OnceCell::new() };
}

fn load_image() -> SemanticImage {
    // Two libtest workers otherwise miss the cold image store together and
    // each spends the process's CPU rail checking the same arithmetic
    // prefix. The first worker fills it; the second waits and replays it.
    let _serial = PREFIX_LOAD.lock().unwrap_or_else(|poisoned| poisoned.into_inner());
    support::semantic_test_base(MODULES).semantic_image()
}

/// A fresh elaborator over the checked library prefix. The semantic image is
/// the committed-state boundary: every call forks its own attempt, report and
/// gate state, so a test's module never leaks into the next one's base.
fn base() -> Elaborator {
    BASE.with(|base| base.get_or_init(load_image).elaborator())
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
fn drop1(xs: List<Nat>) -> Nat decreases xs.len() {
    match xs { Nil => 0, Cons(h, t) => Succ(drop1(t)) }
}
"#;

#[test]
fn a_list_tail_closes_by_omega_alone() {
    ok(&format!(
        "{DROP1}\n\
         theorem drop1_two(): drop1([7, 8]) = 2 {{ refl }}\n\
         // the non-`decreases` occurrence of the same defect (design §1.1)\n\
         theorem at_ctor(h: Nat, xs: List<Nat>): nat::Nat::Lt(xs.len(), Cons(h, xs).len()) {{ omega }}"
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
    // The reduct is `Succ(nat::Nat::add(u₁, u₂))`: two unspellable leaves, two
    // recursive fields, two candidates (design §2's table, row 3).
    ok(r#"
        inductive Tree { Leaf, Node(left: Tree, right: Tree) }

        fn tnodes(t: Tree) -> Nat {
            match t { Leaf => 0, Node(l, r) => Succ(nat::Nat::add(tnodes(l), tnodes(r))) }
        }

        fn tsum(t: Tree) -> Nat decreases tnodes(t) {
            match t { Leaf => 1, Node(l, r) => nat::Nat::add(tsum(l), tsum(r)) }
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
        fn drop1_open<A>(xs: List<A>) -> Nat decreases xs.len() {
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
        fn stall(xs: List<Nat>) -> Nat decreases xs.len() {
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
                Cons(h, rest) => match nat::Nat::eq_dec(t, h) { Inl(_) => drop_eq(t, rest), Inr(_) => Cons(h, rest) },
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

// -- arm binders --------------------------------------------------------------
//
// issues/tier1-arm-binder-has-no-spelling.md: a `match` arm binds its
// constructor's fields as aliases for projections out of the arm's neutral
// payload and children tuples, and those projections have no spelling of
// their own. The display walk spells such a term by the alias's written name,
// only while that name still means it. A payload field and the recursive
// binder, a concrete and an open element type, a fact from the motive and a
// goal in checking position; the control re-binds the name first.

const SHORT: &str = r#"
fn Short(chunks: List<List<Nat>>) → Type {
    match chunks { Nil => True, Cons(chunk, rest) => (chunk.len() <= 4096) ∧ Short(rest) }
}
"#;

#[test]
fn a_payload_binder_spells_by_its_name() {
    // `lib/elf64_read_pieces.hthr`'s `eof_room` shape: a fact about the payload
    // field from the arm's motive, used by `omega` in the arm.
    ok(&format!(
        "{SHORT}\n\
         theorem short_room(chunks: List<List<Nat>>, carry: Nat, room: carry + 4096 < 10000): Short(chunks) → Nat {{\n\
             match chunks as λ cs => Short(cs) → Nat {{\n\
                 Nil => λ ok => 0,\n\
                 Cons(chunk, _) => λ ok => {{\n\
                     let capped: (chunk.len() <= 4096) = ok.left;\n\
                     let here: (carry + chunk.len() < 10000) = {{ omega }};\n\
                     0\n\
                 }}\n\
             }}\n\
         }}"
    ));
}

#[test]
fn the_recursive_binder_spells_at_an_open_element_type() {
    ok(r#"
        theorem rest_open<A>(xs: List<A>, carry: Nat): Nat {
            match xs {
                Nil => 0,
                Cons(_, rest) => {
                    let here: ((rest.len() <= 5) → carry + rest.len() < carry + 6) = λ small => { omega };
                    0
                }
            }
        }
    "#);
}

#[test]
fn a_rebound_arm_binder_is_not_spelled_by_its_old_name() {
    // After `let chunk: Nat = …` the fact `capped` is about the *field*, and
    // `chunk` now names a number: spelling the field `chunk` would hand the
    // certificate a different term. Mis-spelling `capped` would assert
    // `5000 <= 4096` and let omega prove this impossible goal.
    let msg = elab_err(&format!(
        "{SHORT}\n\
         theorem shadow(chunks: List<List<Nat>>, carry: Nat, room: carry + 4096 < 10000): Short(chunks) → Nat {{\n\
             match chunks as λ cs => Short(cs) → Nat {{\n\
                 Nil => λ ok => 0,\n\
                 Cons(chunk, _) => λ ok => {{\n\
                     let capped = ok.left;\n\
                     let chunk: Nat = 5000;\n\
                     let here: (carry < 0) = {{ omega }};\n\
                     0\n\
                 }}\n\
             }}\n\
         }}"
    ));
    assert!(msg.contains("skipped unspellable facts") && msg.contains("capped"), "{msg}");
}

// -- omega inside match arms --------------------------------------------------

#[test]
fn a_neutral_constructor_in_an_arithmetic_fact_spells_its_fields() {
    ok(r#"
        theorem ctor_fact(xs: List<Nat>, f: List<Nat> → Nat):
            (f(xs) = 7) → Nat {
            match xs as λ ys => (f(ys) = 7) → Nat {
                Nil => λ counted => 0,
                Cons(x, rest) => λ counted => {
                    let same: (f(Cons(x, rest)) <= 7) = omega;
                    0
                }
            }
        }
    "#);
}

#[test]
fn an_arm_measure_finds_its_recursive_child() {
    ok(r#"
        theorem tail_bound(xs: List<Nat>): (xs.len() <= 4096) → Nat {
            match xs as λ ys => (ys.len() <= 4096) → Nat {
                Nil => λ ok => 0,
                Cons(x, rest) => λ ok => {
                    let capped: (rest.len() <= 4096) = omega;
                    0
                }
            }
        }
    "#);
}

#[test]
fn an_arm_measure_finds_its_recursive_child_at_an_open_type() {
    ok(r#"
        theorem tail_bound_open<A>(xs: List<A>): (xs.len() <= 4096) → Nat {
            match xs as λ ys => (ys.len() <= 4096) → Nat {
                Nil => λ ok => 0,
                Cons(x, rest) => λ ok => {
                    let capped: (rest.len() <= 4096) = omega;
                    0
                }
            }
        }
    "#);
}

#[test]
fn an_unspellable_shadowed_fact_does_not_block_other_arithmetic() {
    ok(&format!(
        "{SHORT}\n\
         theorem skipped(chunks: List<List<Nat>>, carry: Nat, room: carry + 4096 < 10000): Short(chunks) → Nat {{\n\
             match chunks as λ cs => Short(cs) → Nat {{\n\
                 Nil => λ ok => 0,\n\
                 Cons(chunk, _) => λ ok => {{\n\
                     let capped = ok.left;\n\
                     let chunk: Nat = 5000;\n\
                     let here: (carry < 10000) = omega;\n\
                     0\n\
                 }}\n\
             }}\n\
         }}"
    ));
}

#[test]
fn an_arm_measure_recovers_both_recursive_children_in_declaration_order() {
    ok(r#"
        inductive Tree<A> { Leaf, Node(left: Tree<A>, value: A, right: Tree<A>) }
        fn nodes<A>(t: Tree<A>) → Nat {
            match t { Leaf => 0, Node(l, _, r) => Succ(nodes(l) + nodes(r)) }
        }
        theorem child_bounds<A>(t: Tree<A>): (nodes(t) <= 100) → Nat {
            match t as λ tree => (nodes(tree) <= 100) → Nat {
                Leaf => λ small => 0,
                Node(l, value, r) => λ small => {
                    let both: (nodes(l) + nodes(r) < 100) = omega;
                    0
                }
            }
        }
    "#);
}

#[test]
fn a_skipped_fact_rolls_back_atoms_interned_before_its_unspellable_operand() {
    let msg = elab_err(&format!(
        "{SHORT}\n\
         theorem partial(chunks: List<List<Nat>>, f: Nat → Nat): Short(chunks) → Nat {{\n\
             match chunks as λ cs => Short(cs) → Nat {{\n\
                 Nil => λ ok => 0,\n\
                 Cons(chunk, _) => λ ok => {{\n\
                     let stale: (f(123) + chunk.len() = f(123) + chunk.len()) = refl;\n\
                     let chunk: Nat = 5000;\n\
                     let impossible: False = omega;\n\
                     0\n\
                 }}\n\
             }}\n\
         }}"
    ));
    assert!(msg.contains("skipped unspellable facts") && msg.contains("stale"), "{msg}");
    assert!(msg.contains("atoms []"), "the declined fact leaked an atom: {msg}");
}

#[test]
fn constructor_fields_spell_under_a_lambda_without_losing_binder_depth() {
    ok(r#"
        theorem under_lambda(xs: List<Nat>, f: List<Nat> → Nat, g: (Nat → Nat) → Nat):
            (g(λ n => f(xs) + n) = 7) → Nat {
            match xs as λ ys => (g(λ n => f(ys) + n) = 7) → Nat {
                Nil => λ counted => 0,
                Cons(x, rest) => λ counted => {
                    let same: (g(λ n => f(Cons(x, rest)) + n) <= 7) = omega;
                    0
                }
            }
        }
    "#);
}
