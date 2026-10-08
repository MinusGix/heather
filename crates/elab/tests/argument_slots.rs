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

// -- projection sections (issues/field-projection-sections.md) --------------

#[test]
fn a_projection_section_reads_its_receiver_type_from_the_expected_function() {
    ok(r#"
        record S { a: Nat, b: Nat }
        inductive Flag { Up, Down }
        record Outer { inner: S, flag: Flag }

        fn get_a() -> S -> Nat { ·.a }
        fn get_b() -> S -> Nat { ·.b }
        theorem get_a_computes(): get_a()(S { a: 3, b: 4 }) = 3 { refl }
        theorem get_b_computes(): get_b()(S { a: 3, b: 4 }) = 4 { refl }

        // A chain projects from the same slot.
        fn deep() -> Outer -> Nat { ·.inner.b }
        theorem deep_computes(): deep()(Outer { inner: S { a: 1, b: 2 }, flag: Up }) = 2 { refl }

        // An argument position: the parameter's function type owns the slot,
        // whether the section is the whole argument or under an operator.
        fn apply(f: S -> Nat, s: S) -> Nat { f(s) }
        fn via_arg() -> Nat { apply(·.a, S { a: 5, b: 6 }) }
        fn via_call() -> Nat { apply(Succ(·.b), S { a: 5, b: 6 }) }
        theorem via_arg_computes(): via_arg() = 5 { refl }
        theorem via_call_computes(): via_call() = 7 { refl }
    "#);
}

#[test]
fn a_projection_section_has_an_open_receiver_type_in_a_generic_position() {
    ok(r#"
        record Cell<A> { value: A, count: Nat }
        inductive Flag { Up, Down }

        // The receiver's type mentions an open type variable, and the
        // section's codomain is that variable.
        fn apply_to<A, B>(f: Cell<A> -> B, c: Cell<A>) -> B { f(c) }
        fn value_of<A>(c: Cell<A>) -> A { apply_to(·.value, c) }
        fn count_of<A>(c: Cell<A>) -> Nat { apply_to(·.count, c) }

        theorem value_computes(): value_of(Cell { value: Down, count: 9 }) = Down { refl }
        theorem count_computes(): count_of(Cell { value: Up, count: 9 }) = 9 { refl }
        // A neutral receiver: the section is the projection, not a value
        // that happens to agree on literals.
        theorem value_is_projection<A>(c: Cell<A>): value_of(c) = c.value { refl }

        // At a domain that is a bare implicit, not a function type, slots
        // escape to the enclosing section, whose binder types solve it.
        fn pick<A>(a: A, b: A) -> A { a }
        fn first_of() -> Nat -> Nat -> Nat { pick(·, ·) }
        fn count_first() -> Cell<Flag> -> Cell<Flag> -> Nat { pick(·.count, ·.count) }
        theorem first_of_computes(): first_of()(1)(2) = 1 { refl }
        theorem count_first_computes(): count_first()(Cell { value: Up, count: 4 })(Cell { value: Down, count: 5 }) = 4 { refl }
    "#);
}

#[test]
fn projection_sections_beside_other_slots_are_independent_arguments() {
    ok(r#"
        record S { a: Nat, b: Nat }
        fn first(x: Nat, y: Nat) -> Nat { x }
        fn second(x: Nat, y: Nat) -> Nat { y }

        // Each slot is its own argument, in source order, and probing one
        // masks the others, projections included.
        fn left() -> S -> S -> Nat { first(·.a, ·.b) }
        fn right() -> S -> S -> Nat { second(·.a, ·.b) }
        fn mixed() -> S -> Nat -> Nat { second(·.a, ·) }
        theorem left_computes(): left()(S { a: 1, b: 2 })(S { a: 3, b: 4 }) = 1 { refl }
        theorem right_computes(): right()(S { a: 1, b: 2 })(S { a: 3, b: 4 }) = 4 { refl }
        theorem mixed_computes(): mixed()(S { a: 1, b: 2 })(8) = 8 { refl }

        // An indexed slot repeats one receiver.
        fn both() -> S -> Nat { first(·₀.b, ·₀.a) }
        theorem both_computes(): both()(S { a: 1, b: 2 }) = 2 { refl }
    "#);
}

#[test]
fn a_projection_section_is_refused_without_a_function_type_or_with_a_wrong_field() {
    let msg = bad(r#"
        record S { a: Nat, b: Nat }
        fn k() -> Nat { ·.a }
    "#);
    assert!(msg.contains("needs an enclosing checking position"), "{msg}");

    let msg = bad(r#"
        record S { a: Nat, b: Nat }
        fn k() -> S -> Nat { ·.c }
    "#);
    assert!(msg.contains("no field `c`"), "{msg}");

    // The binder type is the expected one, so a field of a different record
    // is refused rather than chosen by its name.
    let msg = bad(r#"
        record S { a: Nat, b: Nat }
        record T { c: Nat }
        fn k() -> S -> Nat { ·.c }
    "#);
    assert!(msg.contains("`S` has no field `c`"), "{msg}");

    // The field's type is checked against the expected codomain.
    let msg = bad(r#"
        inductive Flag { Up, Down }
        record S { a: Nat, flag: Flag }
        fn k() -> S -> Nat { ·.flag }
    "#);
    assert!(msg.contains("this has type `Flag`, but `Nat` is expected"), "{msg}");
}
