//! Acceptance for issues/argument-slot-sections.md. Argument slots are
//! checking-position shorthand for ordinary lambdas; ownership belongs to the
//! smallest function-typed checking position that can introduce them.

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
fn plain_slots_are_distinct_arguments_and_a_bare_slot_is_identity() {
    ok(r#"
        fn first(a: Nat, b: Nat) -> Nat { a }
        fn id() -> Nat -> Nat { · }
        fn section() -> Nat -> Nat -> Nat { first(·, ·) }

        theorem id_computes(): id()(7) = 7 { refl }
        theorem section_computes(): section()(3)(4) = 3 { refl }
    "#);
}

#[test]
fn indexed_slots_repeat_reorder_and_skip_arguments() {
    ok(r#"
        fn first(a: Nat, b: Nat) -> Nat { a }
        fn repeat() -> Nat -> Nat { first(·₀, ·₀) }
        fn third() -> Nat -> Nat -> Nat -> Nat { ·₂ }
        fn reorder() -> Nat -> Nat -> Nat -> Nat { first(·₂, ·₀) }

        theorem repeated(): repeat()(8) = 8 { refl }
        theorem skipped(): third()(1)(2)(3) = 3 { refl }
        theorem reordered(): reorder()(1)(2)(3) = 3 { refl }
    "#);
}

#[test]
fn indexed_slots_support_dependent_telescopes() {
    ok(r#"
        theorem keep_proof(): (n: Nat) -> (p: n = n) -> n = n { ·₁ }
    "#);
}

#[test]
fn the_smallest_function_typed_checking_position_owns_a_section() {
    ok(r#"
        fn eval(f: Nat -> Nat) -> Nat { f(0) }
        fn first(a: Nat, b: Nat) -> Nat { a }

        // The outer goal is not a function. The argument of `eval` is, so it
        // owns this slot and the entire expression computes to one.
        fn nested() -> Nat { eval(Succ(·)) }
        theorem nested_result(): nested() = 1 { refl }

        // These two slots belong to different sections. In particular, their
        // indexed and unindexed styles do not conflict at the outer boundary.
        fn two_sections() -> Nat -> Nat { first(·, eval(Succ(·₀))) }
        theorem two_sections_result(): two_sections()(9) = 9 { refl }
    "#);
}

#[test]
fn slots_do_not_cross_explicit_lambda_or_sequent_boundaries() {
    ok(r#"
        fn eval(f: Nat -> Nat) -> Nat { f(0) }
        fn under_lambda() -> Nat -> Nat { λ n => eval(Succ(·)) }
        fn under_sequent() -> Nat -> Nat { n ⊢ eval(Succ(·)) }

        theorem lambda_result(): under_lambda()(7) = 1 { refl }
        theorem sequent_result(): under_sequent()(7) = 1 { refl }
    "#);
}

#[test]
fn multi_digit_unicode_indices_are_one_slot() {
    let arrows = std::iter::repeat_n("Nat -> ", 11).collect::<String>();
    ok(&format!(
        "fn eleventh() -> {arrows}Nat {{ ·₁₀ }}\n\
         theorem result(): eleventh()(0)(1)(2)(3)(4)(5)(6)(7)(8)(9)(10) = 10 {{ refl }}"
    ));
}

#[test]
fn mixed_style_and_giant_indices_have_targeted_diagnostics() {
    let mixed = bad(
        "fn first(a: Nat, b: Nat) -> Nat { a }\n\
         fn bad() -> Nat -> Nat -> Nat { first(·, ·₁) }",
    );
    assert!(mixed.contains("indexed and unindexed") && mixed.contains("cannot mix"), "{mixed}");

    let giant = bad("fn bad() -> Nat -> Nat { ·₂₅₆ }");
    assert!(giant.contains("at most 256 arguments"), "{giant}");
}

#[test]
fn inference_and_non_function_positions_explain_the_missing_boundary() {
    let inference = bad("fn bad() -> Nat { let f = ·; 0 }");
    assert!(inference.contains("argument slot") && inference.contains("checking position"), "{inference}");

    let non_function = bad("fn bad() -> Nat { Succ(·) }");
    assert!(non_function.contains("argument slot") && non_function.contains("function type"), "{non_function}");
}
