//! Round 3 of `docs/host-elaboration-interface-design.md`: `split_all`
//! written in Heather (`lib/std/tactic/tactic.hthr`) on the host's `Cases`,
//! `Constructor` and `Close`, closing the goals the Rust combinator closes in
//! `goal_combinators.rs`, with `reflexivity()` as the leaf where that file's
//! leaf block is `refl`.
//!
//! A literal and a neutral scrutinee (a local, a field, a nested `match`), an
//! open element type (`sel<A>`), and a false statement as the negative
//! control. The requests themselves, a checking position and their refusals
//! are `tactic_splits.rs`'s; the two are separate processes, each well inside
//! the suite's CPU rail (evaluating the strategy between requests dominates).

use std::sync::OnceLock;

use heather_elab::{ElabError, Elaborator, SemanticImage};

use crate::support;

const MODULES: &[(&str, &str)] = &[
    ("logic", include_str!("../../../lib/std/core/logic.hthr")),
    ("bool", include_str!("../../../lib/std/core/bool.hthr")),
    ("nat", include_str!("../../../lib/std/num/nat.hthr")),
    ("option", include_str!("../../../lib/std/core/option.hthr")),
    ("pair", include_str!("../../../lib/std/core/pair.hthr")),
    ("list", include_str!("../../../lib/std/data/list.hthr")),
    ("char", include_str!("../../../lib/std/text/char.hthr")),
    ("string", include_str!("../../../lib/std/text/string.hthr")),
    ("tactic", include_str!("../../../lib/std/tactic/tactic.hthr")),
];

static BASE: OnceLock<SemanticImage> = OnceLock::new();

fn elaborator() -> Elaborator {
    BASE.get_or_init(|| support::semantic_test_base(MODULES).semantic_image()).elaborator()
}

const HEADER: &str = "import tactic;\nimport nat;\nimport bool;\nimport logic;\nimport list;\nimport string;\nimport char;\n";

fn check(src: &str) {
    let src = format!("{HEADER}{src}");
    elaborator().elab_source(&src).unwrap_or_else(|err| panic!("{}", err.render(&src)));
}

fn refused(src: &str) -> String {
    let src = format!("{HEADER}{src}");
    match elaborator().elab_source(&src) {
        Err(ElabError::Elab { msg, .. }) => msg,
        Err(other) => other.to_string(),
        Ok(()) => panic!("expected an error, but this elaborated:\n{src}"),
    }
}

/// A record of two flags, matched on through its fields and never split
/// itself: splitting a record adds no case.
const FLAGS: &str = "
record Flags { left: Bool, right: Bool }

fn either(p: Flags) → Bool { match p.left { True => True, False => p.right } }

fn sel<A>(c: Bool, x, y: A) → A { match c { True => x, False => y } }
";

#[test]
fn splits_every_boolean_and_checks_every_leaf() {
    check("theorem and_commutes(a, b: Bool): (a && b) = (b && a) { by split_all(reflexivity()) }");
}

#[test]
fn splits_an_ordinary_finite_inductive() {
    check(
        "inductive Turn { North, East, South }

         fn next(t: Turn) -> Turn {
             match t { North => East, East => South, South => North }
         }

         theorem three_turns(t: Turn): next(next(next(t))) = t { by split_all(reflexivity()) }",
    );
}

#[test]
fn no_finite_local_leaves_the_original_goal() {
    check("theorem reflexive(n: Nat): n = n { by split_all(reflexivity()) }");
}

#[test]
fn introduces_binders_and_splits_the_finite_ones() {
    check("theorem and_commutes(): (a: Bool) → (b: Bool) → (a && b) = (b && a) { by split_all(reflexivity()) }");
}

#[test]
fn reads_a_goal_a_definition_unfolds_to_a_binder() {
    check(
        "fn Commutes(f: Bool → Bool → Bool) → Type { (a: Bool) → (b: Bool) → f(a, b) = f(b, a) }

         theorem and_commutes(): Commutes(λ a b => a && b) { by split_all(reflexivity()) }",
    );
}

#[test]
fn proves_a_conjunction_one_side_at_a_time() {
    check(
        "theorem commute(a, b: Bool): ((a && b) = (b && a)) ∧ ((a || b) = (b || a)) {
             by split_all(reflexivity())
         }",
    );
}

/// `either(p)` and `p.left || p.right` each match on `p.left` behind a
/// definition: one split has to specialize both, or the second side is
/// split again with no link to the first.
#[test]
fn splits_a_field_both_sides_reach_through_definitions() {
    check(&format!(
        "{FLAGS}
         theorem either_is_or(p: Flags): either(p) = (p.left || p.right) {{ by split_all(reflexivity()) }}"
    ));
}

#[test]
fn splits_a_neutral_field_at_an_open_result_type() {
    check(&format!(
        "{FLAGS}
         theorem sel_same<A>(p: Flags, x: A): sel<A>(p.left, x, x) = x {{ by split_all(reflexivity()) }}"
    ));
}

/// The term being split occurs twice, the second time inside a constructor:
/// both have to be simplified alike after the first split.
#[test]
fn a_nested_scrutinee_splits_every_occurrence() {
    check(
        "inductive Step { Go(n: Nat), Stop(n: Nat) }

         fn payload(s: Step) → Nat { match s { Go(n) => n, Stop(n) => n } }

         theorem goes(a, b: Bool): (match (match a { True => True, False => b }) { True => Go(0), False => Go(1) }) =
             Go(payload(match (match a { True => True, False => b }) { True => Go(0), False => Go(1) })) {
             by split_all(reflexivity())
         }",
    );
}

/// The leaf that fails ends the run, and says which sides it compared.
#[test]
fn a_false_statement_is_refused_in_some_leaf() {
    let msg = refused(&format!(
        "{FLAGS}
         theorem wrong(p: Flags): either(p) = p.right {{ by split_all(reflexivity()) }}"
    ));
    assert!(msg.contains("the tactic failed: reflexivity: the two sides differ"), "{msg}");
    assert!(msg.contains("at `True`"), "{msg}");
}

/// An arm's context holds the match's own binder, which no source can name:
/// it is not a local to split.
#[test]
fn splits_inside_a_written_match_arm() {
    check(
        "theorem and_commutes(a, b: Bool): (a && b) = (b && a) {
             match a {
                 True => by split_all(reflexivity()),
                 False => by split_all(reflexivity()),
             }
         }",
    );
}
