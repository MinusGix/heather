//! End-to-end checks for `split_all; all_goals { ... }`.
//!
//! The combinators build an ordinary nested match. Each copied leaf block is
//! checked in its branch context and the completed declaration crosses the
//! ordinary kernel gate.

use heather_elab::Elaborator;

const LOGIC: &str = include_str!("../../../lib/std/logic.hthr");
const BOOL: &str = include_str!("../../../lib/std/bool.hthr");

fn check(source: &str) {
    let mut elab = Elaborator::with_prelude().expect("prelude");
    elab.elab_module_source("logic", LOGIC).expect("logic");
    elab.elab_module_source("bool", BOOL).expect("bool");
    elab.elab_module_source("probe", source)
        .unwrap_or_else(|error| panic!("{}", error.render(source)));
}

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
