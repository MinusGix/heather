//! Round 3 of `docs/host-elaboration-interface-design.md`: the split requests
//! `Cases`, `Constructor` and `Close` that `tactic_split_all.rs`'s `split_all`
//! is written on, used directly. A checking position (an annotated `let`), a
//! quoted scrutinee, and the refusals: a scrutinee no `match` splits, a
//! dependent field, a wrong number of proofs, a proof of another branch's
//! goal.

use std::sync::OnceLock;

use heather_elab::{ElabError, Elaborator, SemanticImage};

use crate::support;

const MODULES: &[(&str, &str)] = &[
    ("logic", include_str!("../../../lib/std/logic.hthr")),
    ("bool", include_str!("../../../lib/std/bool.hthr")),
    ("nat", include_str!("../../../lib/std/nat.hthr")),
    ("option", include_str!("../../../lib/std/option.hthr")),
    ("pair", include_str!("../../../lib/std/pair.hthr")),
    ("list", include_str!("../../../lib/std/list.hthr")),
    ("char", include_str!("../../../lib/std/char.hthr")),
    ("string", include_str!("../../../lib/std/string.hthr")),
    ("tactic", include_str!("../../../lib/std/tactic.hthr")),
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

/// A checking position: the goal is an annotation's.
#[test]
fn splits_at_an_annotated_let() {
    check(
        "theorem t(a, b: Bool): (a || b) = (b || a) {
             let p: ((a || b) = (b || a)) = by split_all(reflexivity());
             p
         }",
    );
}

/// `cases_on` splits on a quoted term of the goal's context; a scrutinee of
/// a type no `match` splits, or a goal that is not a function of it, is
/// refused or left as it is.
#[test]
fn cases_on_a_quoted_scrutinee() {
    check(
        "theorem not_not(b: Bool): b.not().not() = b { by cases_on(b, reflexivity()) }
         theorem unused(a, b: Bool): b = b { by cases_on(a, reflexivity()) }",
    );
    let msg = refused("theorem t(n: Nat): n = n { by cases_on(n, reflexivity()) }");
    assert!(msg.contains("the tactic failed: cases: its type `Nat` is not an inductive type"), "{msg}");
    let msg = refused("theorem t(l: List<Nat>): l = l { by cases_on(l, reflexivity()) }");
    assert!(msg.contains("has a recursive field or an index"), "{msg}");
}

/// `Constructor` splits a goal into its fields, and refuses a field whose
/// statement mentions an earlier field.
#[test]
fn constructor_splits_independent_fields() {
    let fields = "fn fields(t: tactic::Tac<tactic::Expr>) → tactic::Tac<tactic::Expr> {
             goal().bind(λ g => constructor(g.target).bind(λ c => match c {
                 Refused(why) => fail(why, []),
                 Accepted(s) => close_by(s, g.locals, t),
             }))
         }";
    check(&format!("{fields}\ntheorem both(a: Bool): (a = a) ∧ (1 + 1 = 2) {{ by fields(reflexivity()) }}"));
    let msg = refused(&format!(
        "{fields}\nrecord Zeroed {{ n: Nat, p: n = 0 }}\ntheorem z(): Zeroed {{ by fields(reflexivity()) }}"
    ));
    assert!(msg.contains("a branch's statement depends on another branch's proof"), "{msg}");
    let msg = refused(&format!("{fields}\ntheorem t(n: Nat): n = n {{ by fields(reflexivity()) }}"));
    assert!(msg.contains("is not a type with one constructor"), "{msg}");
}

/// `Close` checks what it is given: one proof per branch, each of its own
/// branch's goal.
#[test]
fn close_checks_its_proofs() {
    let msg = refused(
        "fn none() → tactic::Tac<tactic::Expr> {
             goal().bind(λ g => match g.locals {
                 Nil => fail(\"no local\", []),
                 Cons(l, _) => cases(Local(l.ref), g.target).bind(λ c => match c {
                     Refused(why) => fail(why, []),
                     Accepted(s) => close(s.id, []).bind(λ c2 => match c2 {
                         Refused(why) => fail(why, []),
                         Accepted(h) => Pure(Hd(h)),
                     }),
                 }),
             })
         }
         theorem t(b: Bool): b.not().not() = b { by none() }",
    );
    assert!(msg.contains("the split has 2 branches, and 0 proofs were given"), "{msg}");
    // Both branches given a proof of the first branch's goal, quoted from
    // the goal's context: the second is refused at its own goal.
    let msg = refused(
        "fn swapped(q: tactic::Expr) → tactic::Tac<tactic::Expr> {
             goal().bind(λ g => match g.locals {
                 Nil => fail(\"no local\", []),
                 Cons(_, rest) => match rest {
                     Nil => fail(\"one local\", []),
                     Cons(l, _) => cases(Local(l.ref), g.target).bind(λ c => match c {
                         Refused(why) => fail(why, []),
                         Accepted(s) => close(s.id, [q, q]).bind(λ c2 => match c2 {
                             Refused(why) => fail(why, []),
                             Accepted(h) => Pure(Hd(h)),
                         }),
                     }),
                 },
             })
         }
         theorem t(b: Bool, q: (True && True) = True): (b && True) = b { by swapped(q) }",
    );
    assert!(msg.contains("proof proves `and(True, True) = True`, not its goal `and(False, True) = False`"), "{msg}");
}


