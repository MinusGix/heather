//! End-to-end checks for `split_all; all_goals { ... }`.
//!
//! The combinators build an ordinary nested match. Each copied leaf block is
//! checked in its branch context and the completed declaration crosses the
//! ordinary kernel gate.

use heather_elab::Elaborator;

const LOGIC: &str = include_str!("../../../lib/std/logic.hthr");
const BOOL: &str = include_str!("../../../lib/std/bool.hthr");

fn elaborator() -> Elaborator {
    let mut elab = Elaborator::with_prelude().expect("prelude");
    elab.elab_module_source("logic", LOGIC).expect("logic");
    elab.elab_module_source("bool", BOOL).expect("bool");
    elab
}

fn check(source: &str) {
    elaborator().elab_module_source("probe", source)
        .unwrap_or_else(|error| panic!("{}", error.render(source)));
}

fn refused(source: &str) {
    assert!(elaborator().elab_module_source("probe", source).is_err(), "a false statement checked");
}

/// A record of two flags, matched on through its fields and never split
/// itself: splitting a record adds no case.
const FLAGS: &str = r#"
import bool;
import logic;

record Flags { left: Bool, right: Bool }

fn either(p: Flags) → Bool { match p.left { True => True, False => p.right } }

fn sel<A>(c: Bool, x, y: A) → A { match c { True => x, False => y } }
"#;

#[test]
fn splits_every_boolean_and_checks_every_leaf() {
    check(
        r#"
import bool;

theorem and_commutes(a, b: Bool): (a && b) = (b && a) {
    split_all;
    all_goals { refl }
}
"#,
    );
}

#[test]
fn splits_an_ordinary_finite_inductive() {
    check(
        r#"
inductive Turn { North, East, South }

fn next(t: Turn) -> Turn {
    match t { North => East, East => South, South => North }
}

theorem three_turns(t: Turn): next(next(next(t))) = t {
    split_all;
    all_goals { refl }
}
"#,
    );
}

#[test]
fn no_finite_local_leaves_the_original_goal() {
    check(
        r#"
theorem reflexive(n: Nat): n = n {
    split_all;
    all_goals {
        let same: (n = n) = refl;
        same
    }
}
"#,
    );
}

#[test]
fn introduces_binders_and_splits_the_finite_ones() {
    check(
        r#"
import bool;

theorem and_commutes(): (a: Bool) → (b: Bool) → (a && b) = (b && a) {
    split_all;
    all_goals { refl }
}
"#,
    );
}

#[test]
fn reads_a_goal_a_definition_unfolds_to_a_binder() {
    // After the binders the goal is the definition's body, spelled as its
    // code: the search reads the decoded equation.
    check(
        r#"
import bool;

fn Commutes(f: Bool → Bool → Bool) → Type { (a: Bool) → (b: Bool) → f(a, b) = f(b, a) }

theorem and_commutes(): Commutes(λ a b => a && b) {
    split_all;
    all_goals { refl }
}
"#,
    );
}

#[test]
fn proves_a_conjunction_one_side_at_a_time() {
    check(
        r#"
import bool;
import logic;

theorem commute(a, b: Bool): ((a && b) = (b && a)) ∧ ((a || b) = (b || a)) {
    split_all;
    all_goals { refl }
}
"#,
    );
}

#[test]
fn splits_a_field_both_sides_reach_through_definitions() {
    // `either(p)` and `p.left || p.right` each match on `p.left` behind a
    // definition: one split has to specialize both, or the second side is
    // split again with no link to the first.
    check(&format!(
        "{FLAGS}
theorem either_is_or(p: Flags): either(p) = (p.left || p.right) {{
    split_all;
    all_goals {{ refl }}
}}
"
    ));
}

#[test]
fn splits_a_neutral_field_at_an_open_result_type() {
    check(&format!(
        "{FLAGS}
theorem sel_same<A>(p: Flags, x: A): sel<A>(p.left, x, x) = x {{
    split_all;
    all_goals {{ refl }}
}}
"
    ));
}

#[test]
fn a_nested_scrutinee_splits_every_occurrence() {
    // The term being split occurs twice, the second time inside a
    // constructor: both have to be simplified alike after the first split.
    check(
        r#"
import bool;
import logic;

inductive Step { Go(n: Nat), Stop(n: Nat) }

fn payload(s: Step) → Nat { match s { Go(n) => n, Stop(n) => n } }

theorem goes(a, b: Bool): (match (match a { True => True, False => b }) { True => Go(0), False => Go(1) }) =
    Go(payload(match (match a { True => True, False => b }) { True => Go(0), False => Go(1) })) {
    split_all;
    all_goals { refl }
}
"#,
    );
}

#[test]
fn a_false_statement_is_refused_in_some_leaf() {
    refused(&format!(
        "{FLAGS}
theorem wrong(p: Flags): either(p) = p.right {{
    split_all;
    all_goals {{ refl }}
}}
"
    ));
}

#[test]
fn splits_inside_a_written_match_arm() {
    // An arm's context holds the match's own binder, which no source can
    // name: it is not a local to split.
    check(
        r#"
import bool;

theorem and_commutes(a, b: Bool): (a && b) = (b && a) {
    match a {
        True => { split_all; all_goals { refl } },
        False => { split_all; all_goals { refl } },
    }
}
"#,
    );
}
