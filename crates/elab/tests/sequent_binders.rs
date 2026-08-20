//! Acceptance for issues/sequent-binder-expression.md. A sequent binder is
//! parser sugar for an ordinary checking-position lambda; these tests pin the
//! one-expression and long-block surfaces and their inherited lambda behavior.

use heather_elab::Elaborator;

fn ok(src: &str) {
    let mut e = Elaborator::with_prelude().expect("prelude");
    e.elab_source(src).unwrap_or_else(|err| panic!("{}", err.render(src)));
}

fn bad(src: &str) -> String {
    let mut e = Elaborator::with_prelude().expect("prelude");
    e.elab_source(src).expect_err("source must be refused").render(src)
}

#[test]
fn unicode_and_ascii_sequents_introduce_one_or_several_binders() {
    ok(r#"
        fn unicode_id() -> Nat -> Nat { good ⊢ good }
        fn ascii_id() -> Nat -> Nat { good |- good }
        fn first() -> Nat -> Nat -> Nat { x y ⊢ x }
        fn second() -> Nat -> Nat -> Nat { x y ⊢ y }
    "#);
}

#[test]
fn annotations_are_checked_and_dependent_telescopes_see_earlier_binders() {
    ok(r#"
        fn annotated() -> Nat -> Nat { (n: Nat) ⊢ n }
        theorem all_refl(): (n: Nat) -> n = n { n ⊢ refl }
        theorem keep_proof(): (n: Nat) -> (p: n = n) -> n = n {
            n (p: n = n) ⊢ p
        }
    "#);

    let src = "fn bad() -> Nat -> Nat { (n: Nat -> Nat) ⊢ n }";
    let msg = bad(src);
    assert!(msg.contains("annotated") && msg.contains("not the one expected"), "{msg}");
}

#[test]
fn a_sequent_is_the_loosest_expression_and_needs_no_arm_block() {
    ok(r#"
        fn choose_id(n: Nat) -> Nat -> Nat {
            match n {
                Zero => good ⊢ good,
                Succ(k) => good ⊢ good,
            }
        }
    "#);
}

#[test]
fn a_block_header_scopes_over_the_remaining_statements() {
    ok(r#"
        fn long() -> Nat -> Nat {
            n ⊢
            let first = n;
            let second = first;
            second
        }

        fn outside_then_inside() -> Nat -> Nat {
            let zero = 0;
            n ⊢
            let chosen = n;
            chosen
        }

        fn split_inside(n: Nat) -> Nat -> Nat {
            x ⊢
            split n;
            on Zero := x;
            on Succ(k) := x;
        }
    "#);
}

#[test]
fn goal_discharges_after_a_sequent_keep_declaration_scope() {
    ok(r#"
        theorem with_goal(): Nat -> 0 = 0 {
            n ⊢
            let same = n;
            ?proof
            on ?proof := refl;
        }
    "#);
}

#[test]
fn sequent_and_lambda_spellings_are_definitionally_equal() {
    ok(r#"
        fn accept(f: Nat -> Nat) -> Nat -> Nat { f }
        theorem same(): accept(n ⊢ n) = accept(λ n => n) { refl }
    "#);
}

#[test]
fn a_non_function_goal_uses_the_existing_lambda_refusal() {
    let src = "fn bad() -> Nat { x ⊢ x }";
    let msg = bad(src);
    assert!(msg.contains("lambda") && msg.contains("function"), "{msg}");
}
