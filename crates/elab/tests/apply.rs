//! Goal-oriented application (`apply f; give a; b`).
//!
//! `apply` is deliberately an alternative surface layout for an ordinary
//! n-ary call. These tests pin both halves of that promise: it is useful in
//! programming code, and proof calls retain the elaborator's existing
//! expected-type and cross-argument implicit inference.

use heather_elab::Elaborator;

fn ok(src: &str) {
    let mut e = Elaborator::with_prelude().expect("prelude");
    if let Err(err) = e.elab_source(src) {
        panic!("expected success, got: {}", err.render(src));
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
fn a_function_named_apply_is_still_callable() {
    ok("
fn apply(n: Nat) -> Nat { n }
theorem ordinary(n: Nat): apply(n) = n { refl }
");
}
