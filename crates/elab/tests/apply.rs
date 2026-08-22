//! Goal-oriented application (`apply f; give a; b`).
//!
//! `apply` is deliberately an alternative surface layout for an ordinary
//! n-ary call. These tests pin both halves of that promise: it is useful in
//! programming code, and proof calls retain the elaborator's existing
//! expected-type and cross-argument implicit inference.

use heather_elab::{ElabError, Elaborator, GoalSource};

fn ok(src: &str) {
    let mut e = Elaborator::with_prelude().expect("prelude");
    if let Err(err) = e.elab_source(src) {
        panic!("expected success, got: {}", err.render(src));
    }
}

fn bad(src: &str) -> String {
    let mut e = Elaborator::with_prelude().expect("prelude");
    match e.elab_source(src) {
        Ok(()) => panic!("expected rejection, but it elaborated"),
        Err(err) => err.render(src),
    }
}

#[test]
fn unary_apply_wraps_an_ordinary_program_value() {
    ok("
fn wrap(n: Nat) -> Nat { apply Succ; n }
theorem computes(n: Nat): wrap(n) = Succ(n) { refl }
");
}

#[test]
fn the_final_body_can_chain_more_applications() {
    ok("
fn twice(n: Nat) -> Nat {
    apply Succ;
    apply Succ;
    n
}
theorem computes(n: Nat): twice(n) = Succ(Succ(n)) { refl }
");
}

#[test]
fn give_introduces_each_non_final_argument_body() {
    ok("
fn first(a: Nat, b: Nat) -> Nat { a }
fn via_apply(a: Nat, b: Nat) -> Nat {
    apply first;
    give { let x = a; x };
    { let y = b; y }
}
theorem computes(a: Nat, b: Nat): via_apply(a, b) = a { refl }
");
}

#[test]
fn proof_apply_uses_all_arguments_and_the_expected_result_for_implicits() {
    ok("
theorem chain(a: Nat, b: Nat, c: Nat, p: a = b, q: b = c): a = c {
    apply trans;
    give p;
    q
}
");
}

#[test]
fn an_implicit_can_be_fixed_on_the_apply_line() {
    ok("
theorem chain(a: Nat, b: Nat, c: Nat, p: a = b, q: b = c): a = c {
    apply trans(b := b);
    give p;
    q
}
");
}

#[test]
fn a_named_goal_on_the_apply_line_can_feed_dependent_argument_goals() {
    ok("
theorem chain(
    a: Nat,
    midpoint: Nat,
    c: Nat,
    p: a = midpoint,
    q: midpoint = c,
): a = c {
    apply trans(b := ?b);
    give ?left;
    ?right

    on ?b := midpoint;
    on ?left := p;
    on ?right := q;
}
");
}

#[test]
fn apply_promotes_an_uninferred_implicit_before_dependent_argument_goals() {
    ok("
theorem chain(
    a: Nat,
    midpoint: Nat,
    c: Nat,
    p: a = midpoint,
    q: midpoint = c,
): a = c {
    apply trans;
    give ?left;
    ?right

    on ?b := midpoint;
    on ?left := p;
    on ?right := q;
}
");
}

#[test]
fn apply_can_promote_several_dependent_implicits() {
    ok("
fn erase({A: Type<0>}, {x: A}, n: Nat) -> Nat { n }
fn choose(n: Nat) -> Nat {
    apply erase;
    n

    on ?A := Nat;
    on ?x := 0;
}
");
}

#[test]
fn separate_nested_apply_sites_each_receive_capacity() {
    ok("
fn erase({A: Type<0>}, n: Nat) -> Nat { n }
fn twice(n: Nat) -> Nat {
    apply erase;
    apply erase;
    n

    on ?A := Nat;
    on ?A.1 := Nat;
}
");
}

#[test]
fn ordinary_inference_wins_before_any_goal_is_promoted() {
    ok("
fn identity<A>(x: A) -> A { x }
fn choose(n: Nat) -> Nat {
    apply identity;
    n
}
");
}

#[test]
fn promotion_uses_a_local_callable_values_parameter_names() {
    ok("
fn invoke(f: {A: Type<0>} -> A -> Nat, n: Nat) -> Nat {
    apply f;
    ?arg

    on ?A := Nat;
    on ?arg := n;
}
");
}

#[test]
fn ordinary_calls_still_refuse_an_uninferable_implicit() {
    let msg = bad("
fn erase({A: Type<0>}, {x: A}, n: Nat) -> Nat { n }
fn choose(n: Nat) -> Nat { erase(n) }
");
    assert!(
        msg.contains("could not infer the implicit argument `x`"),
        "{msg}"
    );
}

#[test]
fn an_unfilled_promoted_goal_points_back_to_apply_and_names_its_parameter() {
    let src = "
fn erase({A: Type<0>}, n: Nat) -> Nat { n }
fn choose(n: Nat) -> Nat {
    apply erase;
    n
}
";
    let mut e = Elaborator::with_prelude().expect("prelude");
    let err = e
        .elab_source(src)
        .expect_err("the promoted goal is intentionally open");
    let ElabError::UnsolvedGoals { goals, .. } = &err else {
        panic!("expected an unsolved-goal report, got {err}")
    };
    let [goal] = goals.as_slice() else {
        panic!("expected one goal, got {goals:?}")
    };
    assert_eq!(
        goal.source,
        Some(GoalSource::ApplyImplicit {
            callee: "erase".into(),
            parameter: "A".into(),
            parameter_index: 0,
            apply_span: goal.span,
        })
    );
    let msg = err.render(src);
    assert!(msg.contains("?A"), "{msg}");
    assert!(msg.contains("the `A` parameter of `erase`"), "{msg}");
    assert!(
        msg.contains("4:5"),
        "the goal should point at `apply erase`: {msg}"
    );
}

#[test]
fn a_function_named_apply_is_still_callable() {
    ok("
fn apply(n: Nat) -> Nat { n }
theorem ordinary(n: Nat): apply(n) = n { refl }
");
}
