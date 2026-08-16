//! `True` and `trivial` — the prelude proposition and its canonical
//! inhabitant (`issues/true-prop-trivial-hypotheses.md`, half 1).
//!
//! `True` is the kernel's `Unit^0` under a surface name, not a declaration:
//! `Unit`'s η is proof irrelevance (`crates/kernel/src/conv.rs`), so the
//! *judgmental* uniqueness of the inhabitant comes for free and the
//! `SProp`-vs-`Prop` question never has to be answered. Nothing here is a
//! generated term — the generated side of the round is the `datarepr`
//! defaulted `inv`, tested at `datarepr.rs` — so what is varied is the
//! positions: checking, inference, an **open** type parameter, a *printed*
//! statement, and a negative control beside each.

use heather_elab::{ElabError, Elaborator};

fn ok(src: &str) -> Elaborator {
    let mut e = Elaborator::with_prelude().expect("prelude");
    if let Err(err) = e.elab_source(src) {
        panic!("expected success, got: {}", err.render(src));
    }
    e
}

fn bad(src: &str) -> String {
    let mut e = Elaborator::with_prelude().expect("prelude");
    match e.elab_source(src) {
        Ok(()) => panic!("expected a rejection, but it elaborated"),
        Err(err) => err.render(src),
    }
}

/// The milestone: `True` is a type, `trivial` proves it in **checking**
/// position, and it also **infers** — unlike `refl` and `FZ`, because the
/// surface spells exactly one `True` and there is no level to recover.
#[test]
fn true_is_a_type_and_trivial_inhabits_it() {
    ok("
theorem t(): True { trivial }

// Inference position: no expected type reaches the `let`.
theorem u(): True { { let p = trivial; p } }

// A hypothesis, consumed and ignored — the shape a defaulted `inv` puts in
// every generated `refines` signature.
fn k(n: Nat, h: True) -> Nat { n }
theorem uses(n: Nat): k(n, trivial) = n { refl }
");
}

/// Proof irrelevance, which is the whole reason `True` is `Unit` and not a
/// one-constructor `inductive`: any two proofs are **convertible**, so `refl`
/// closes the equation between a variable and the canonical inhabitant, and
/// between two variables.
#[test]
fn any_two_proofs_of_true_are_convertible() {
    ok("
theorem canonical(p: True): p = trivial { refl }
theorem irrelevant(p: True, q: True): p = q { refl }
");
}

/// The open-type axis: `True` at a type parameter's side, inside a
/// polymorphic body where `A` is a variable and nothing about the
/// instantiation is known.
#[test]
fn true_holds_under_an_open_type_parameter() {
    ok("
fn keep<A>(a: A, h: True) -> A { a }
fn wrap<A>(a: A) -> A { keep<A>(a, trivial) }
theorem at_nat(n: Nat): wrap<Nat>(n) = n { refl }
");
}

/// `True` in **expression** position is the code `⌜Unit^0⌝`, so a
/// `Type`-valued function can return it — which is exactly what a `datarepr`'s
/// defaulted `inv` clause is.
#[test]
fn true_is_a_code_where_a_type_is_a_term() {
    ok("
fn always(n: Nat) -> Type { True }
theorem holds(n: Nat): always(n) { trivial }
");
}

/// The printing dress-up (the user want recorded on the issue): a type that
/// *is* `True` prints as `True`, not as the kernel's `Unit 0` spelling.
/// Checked at the goal listing, which is `display_type`'s customer.
#[test]
fn a_true_goal_prints_as_true() {
    let mut e = Elaborator::with_prelude().expect("prelude");
    let src = "
fn keep(n: Nat, h: True) -> Nat { n }
theorem g(n: Nat): keep(n, ?h) = n { refl }
";
    let Err(ElabError::UnsolvedGoals { goals, .. }) = e.elab_source(src) else {
        panic!("expected the hole to survive as a goal");
    };
    let row = goals.iter().find(|g| g.name == "h").expect("the `h` goal");
    assert_eq!(row.statement, "True", "{:?}", row.statement);
    assert!(!row.statement.contains("Unit"), "{:?}", row.statement);
}

/// …and the context entries are dressed the same way, since they go through
/// the same boundary.
#[test]
fn a_true_hypothesis_prints_as_true_in_the_context() {
    let mut e = Elaborator::with_prelude().expect("prelude");
    let src = "
theorem g(n: Nat, h: True): n = n { ?p }
";
    let Err(ElabError::UnsolvedGoals { goals, .. }) = e.elab_source(src) else {
        panic!("expected the hole to survive as a goal");
    };
    let row = &goals[0];
    let h = row.context.iter().find(|(n, _)| n == "h").expect("the `h` binder");
    assert_eq!(h.1, "True", "{:?}", row.context);
}

// -- negative controls -------------------------------------------------------

/// `refl` does not prove `True`: the two trivial propositions are different
/// types, and the flip of the defaulted `inv` really is a flip.
#[test]
fn refl_does_not_prove_true() {
    let msg = bad("theorem t(): True { refl }");
    assert!(msg.contains("`refl` needs an `=` expected type"), "{msg}");
}

/// …and `trivial` does not prove an equation. The diagnostic names `True` and
/// prints the expected type in the dressed spelling.
#[test]
fn trivial_does_not_prove_anything_else() {
    let msg = bad("theorem t(): Zero = Zero { trivial }");
    assert!(msg.contains("`trivial` proves `True`"), "{msg}");
    let msg = bad("fn f() -> Nat { trivial }");
    assert!(msg.contains("`trivial` proves `True`"), "{msg}");
}

/// A local binder named `trivial` wins, exactly as it does for `FZ` and
/// `refl`: the builtin is claimed only where nothing else answers.
#[test]
fn a_local_named_trivial_shadows_the_builtin() {
    ok("
fn f(trivial: Nat) -> Nat { trivial }
theorem g(): f(Succ(Zero)) = Succ(Zero) { refl }
");
}

/// A file that declares its own `True` keeps it — the surface name is claimed
/// only when no declaration answers.
#[test]
fn a_declared_true_shadows_the_builtin_type() {
    ok("
inductive True { yes, no }
fn flip(t: True) -> True { match t { yes => no, no => yes } }
theorem g(): flip(yes) = no { refl }
");
}

/// `Bool`'s `True` **constructor** is untouched: a constructor is not a type
/// name, so the two readings coexist in one file — the proposition in type
/// position, the constructor in expression position.
#[test]
fn bools_true_constructor_coexists_with_the_proposition() {
    ok("
inductive Bool { False, True }
fn not(b: Bool) -> Bool { match b { False => True, True => False } }
theorem not_false(): not(False) = True { refl }
theorem prop(): True { trivial }
fn both(b: Bool, h: True) -> Bool { not(b) }
theorem uses(): both(False, trivial) = True { refl }
");
}
