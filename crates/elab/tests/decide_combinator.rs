//! The `decide` goal combinator (issues/reflection-through-decide-instances.md,
//! docs/reflection-through-decide-instances-design.md §4): a closed decided
//! goal is proved by `logic::decide_yes(refl)`, with resolution picking the
//! `Decide` instance and the kernel running its decision. Every generated
//! term here is checked by the kernel, so the four axes of
//! docs/testing-generated-terms.md reduce to: a checking position (always),
//! composed and relation goals, an *open* goal as the refusal that must not
//! be misreported, and a false closed goal as the negative control.

use heather_elab::Elaborator;

const LOGIC: &str = include_str!("../../../lib/std/logic.hthr");
const BOOL: &str = include_str!("../../../lib/std/bool.hthr");
const NAT: &str = include_str!("../../../lib/std/nat.hthr");

fn with_std() -> Elaborator {
    let mut e = Elaborator::with_prelude().expect("prelude");
    e.elab_module_source("logic", LOGIC).expect("logic");
    e.elab_module_source("bool", BOOL).expect("bool");
    e.elab_module_source("nat", NAT).expect("nat");
    e
}

fn ok(src: &str) {
    with_std()
        .elab_module_source("probe", src)
        .unwrap_or_else(|err| panic!("{}", err.render(src)));
}

fn bad(src: &str) -> String {
    with_std()
        .elab_module_source("probe", src)
        .expect_err("source must be refused")
        .render(src)
}

#[test]
fn decide_discharges_closed_relations_equations_and_connectives() {
    ok(r#"
        import logic;
        import bool;
        import nat;

        theorem le(): nat::Nat::Le(2, 5) { decide }
        // A magnitude the derived decider peels in one run step, not 2^63 of them.
        theorem lt_at_magnitude(): nat::Nat::Lt(5, 9223372036854775808) { decide }
        theorem eq(): 7 = 7 { decide }
        theorem on_bool(): bool::Bool::Le(False, True) { decide }
        theorem composed(): nat::Nat::Le(2, 5) ∧ ¬nat::Nat::Le(5, 2) { decide }
        theorem either(): nat::Nat::Le(5, 2) ∨ nat::Nat::Even(4) { decide }
        // The proof is a term like any other: usable as an argument.
        theorem as_argument(): nat::Nat::Le(2, 5) ∧ nat::Nat::Le(3, 4) { And(decide, decide) }
        "#);
}

#[test]
fn decide_is_a_leaf_for_all_goals() {
    ok(r#"
        import logic;
        import bool;

        theorem every_bool(b: Bool): bool::Bool::Le(b, True) { split_all; all_goals { decide } }
        "#);
}

#[test]
fn a_false_closed_goal_is_refused_at_the_decide_and_names_the_instance() {
    let msg = bad(r#"
        import logic;
        import nat;

        theorem wrong(): nat::Nat::Le(5, 2) { decide }
        "#);
    assert!(msg.contains("NotConvertible"), "{msg}");
    assert!(msg.contains("`decide` resolved `Decide<"), "{msg}");
    assert!(msg.contains("nat::Nat::Le::Decide"), "{msg}");
    assert!(msg.contains("not `Inl`"), "{msg}");
    // The span is the `decide` (line 5, column 47 of the source above), not
    // the declaration head.
    assert!(msg.starts_with("5:47:"), "{msg}");
}

#[test]
fn a_passing_decide_is_not_blamed_for_another_refusal() {
    // The gate rejects the `refl`; the `decide` beside it decided its goal
    // and must not be named. Its record is consulted and found convertible.
    let msg = bad(r#"
        import logic;
        import nat;

        theorem mixed(): nat::Nat::Le(2, 5) ∧ (2 = 3) { And(decide, refl) }
        "#);
    assert!(msg.contains("NotConvertible"), "{msg}");
    assert!(!msg.contains("`decide` resolved"), "{msg}");
}

#[test]
fn an_open_goal_is_reported_as_undecided_not_false() {
    // `Decide<n = m>` at `Nat` resolves at open `n`, so the term elaborates and
    // the kernel is where it stops; the note says so without claiming falsity.
    let msg = bad(r#"
        import logic;
        import nat;

        theorem open_goal(n: Nat): n = n { decide }
        "#);
    assert!(msg.contains("`decide` resolved `Decide<"), "{msg}");
    assert!(msg.contains("not closed enough"), "{msg}");
}

#[test]
fn a_goal_with_no_instance_reports_the_search() {
    let msg = bad(r#"
        import logic;

        theorem no_instance(P: Type, p: P): P { decide }
        "#);
    assert!(msg.contains("no instance for") && msg.contains("Decide<"), "{msg}");
}

#[test]
fn decide_needs_the_logic_module() {
    let mut e = Elaborator::with_prelude().expect("prelude");
    let src = "theorem t(): 2 = 2 { decide }";
    let msg = e.elab_source(src).expect_err("no Decide class in scope").render(src);
    assert!(msg.contains("import logic;"), "{msg}");
}

#[test]
fn decide_gives_way_to_what_the_writer_bound() {
    ok(r#"
        import logic;
        import nat;

        // A hypothesis named `decide` is the hypothesis.
        theorem local_wins(decide: nat::Nat::Le(2, 5)): nat::Nat::Le(2, 5) { decide }
        // The library's `decide<P>()` keeps its meaning where it is applied.
        theorem bare_value(): Or<nat::Nat::Le(2, 5), ¬nat::Nat::Le(2, 5)> { decide<nat::Nat::Le(2, 5)>() }
        "#);
    // A user global of that name is not the combinator either.
    ok(r#"
        import logic;

        fn decide() -> Nat { 3 }
        theorem user_global(): decide() = 3 { refl }
        "#);
}
