//! The surface vector type `[T; n]` and generic collection literals
//! (docs/language/container-fields.md §2), the surface half of container fields.

use heather_elab::{ElabError, Elaborator};

fn elab(src: &str) -> Elaborator {
    let mut e = Elaborator::with_prelude().expect("prelude");
    e.elab_source(src).unwrap_or_else(|err| panic!("{}", err.render(src)));
    e
}

fn elab_err(src: &str) -> String {
    let mut e = Elaborator::with_prelude().expect("prelude");
    match e.elab_source(src) {
        Err(ElabError::Elab { msg, .. }) => msg,
        Err(other) => format!("{other}"),
        Ok(()) => panic!("expected an error, but this elaborated:\n{src}"),
    }
}

// §8.1–2 — the type in every position, and literals at both ends.
#[test]
fn vector_types_and_literals() {
    elab(
        r#"
        fn empty() -> [Nat; 0] { [] }
        fn two() -> [Nat; 2] { [1, 2] }
        fn pass(xs: [Nat; 2]) -> [Nat; 2] { xs }
        theorem round(): pass([1, 2]) = [1, 2] { refl }
        "#,
    );
}

// The length is an ordinary expression, so a vector type may depend on a
// *variable* length — which is the whole point, since a container field's
// length is a field.
#[test]
fn the_length_may_be_a_variable() {
    elab(
        r#"
        fn id_vec(n: Nat, xs: [Nat; n]) -> [Nat; n] { xs }
        theorem t(): id_vec(2, [1, 2]) = [1, 2] { refl }
        "#,
    );
}

// A vector of a declared type, and a vector type nested in a function type —
// the two grammars have to compose.
#[test]
fn vectors_compose_with_the_other_type_formers() {
    elab(
        r#"
        inductive Bool { True, False }
        fn pick(f: [Nat; 2] -> Nat, xs: [Nat; 2]) -> Nat { f(xs) }
        fn head2(xs: [Bool; 2]) -> [Bool; 2] { xs }
        fn nested(xs: [[Nat; 2]; 1]) -> [[Nat; 2]; 1] { xs }
        "#,
    );
}

// The abbreviation's element type and length are both open. Conversion is
// exercised in both checking directions, before either can compute.
#[test]
fn vector_type_expressions_convert_at_neutral_lengths() {
    elab(r#"
        fn V<A>(n: Nat) -> Type { [A; n] }
        fn to_named<A>(n: Nat, xs: [A; n]) -> V<A>(n) { xs }
        fn from_named<A>(n: Nat, xs: V<A>(n)) -> [A; n] { xs }
        theorem shape<A>(n: Nat): V<A>(n) = [A; n] { refl }
        theorem round<A>(n: Nat, xs: [A; n]): from_named(n, to_named(n, xs)) = xs { refl }
    "#);
}

#[test]
fn vector_type_expressions_compose_and_check_literals() {
    elab(r#"
        fn V<A>(n: Nat) -> Type { [A; n] }
        fn nested<A>(n, m: Nat) -> Type { [[A; n]; m] }
        fn arrows<A>(n: Nat) -> Type { [A -> A; n] }
        fn higher() -> Type<1> { [Type; 0] }
        fn empty<A>() -> V<A>(0) { [] }
        fn one() -> V<Nat>(1) { [1] }
        fn two() -> V<Nat>(2) { [1, 2] }
        fn plain_two() -> [Nat; 2] { [1, 2] }
        fn nested_value() -> nested<Nat>(2, 1) { [[1, 2]] }
        fn functions<A>() -> arrows<A>(1) { [λ x => x] }
        theorem empty_shape<A>(): V<A>(0) = [A; 0] { refl }
        theorem closed_shape(): V<Nat>(2) = [Nat; 2] { refl }
        theorem two_values(): two() = plain_two() { refl }
    "#);
}

#[test]
fn vector_type_expressions_reject_wrong_types_lengths_and_levels() {
    let m = elab_err("fn V<A>(n: Nat) -> Type { [A; n] } fn bad(xs: [Nat; 1]) -> V<Nat>(2) { xs }");
    assert!(m.contains("[Nat; 1]") && m.contains("[Nat; 2]"), "{m}");
    for src in [
        "fn bad() -> Type { [0; 2] }",
        "fn bad() -> Type { [Nat; Type] }",
        "fn bad() -> Type { [Type; 0] }",
    ] {
        // These must reach semantic checking rather than fail to parse.
        heather_syntax::parse_file(src).expect("vector type expression parses");
        elab_err(src);
    }
}

#[test]
fn vector_literals_check_at_nested_and_computed_carriers() {
    elab(r#"
        fn V<A>(n: Nat) -> Type { [A; n] }
        fn Rows<A>(n, m: Nat) -> Type { [V<A>(n); m] }
        fn selected<A>(n: Nat) -> Type {
            match n { Zero => [A; 0], Succ(k) => [A; Succ(k)] }
        }
        fn empty<A>() -> selected<A>(0) { [] }
        fn row<A>(x: A) -> Rows<A>(2, 1) { [[x, x]] }
        fn selected_row<A>(x: A) -> selected<A>(1) { [x] }
        fn local_family<A>(x: A) -> [A; 1] {
            let family: Nat -> Type = λ (n: Nat) => [A; n];
            let xs: family(1) = [x]; xs
        }
        record Family<A> { carrier: Nat -> Type }
        fn projected_family<A>(x: A) -> [A; 1] {
            let family = Family<A>(λ (n: Nat) => [A; n]);
            let xs: family.carrier(1) = [x]; xs
        }
        theorem nested_value<A>(x: A): row(x) = [[x, x]] { refl }
        theorem selected_value<A>(x: A): selected_row(x) = [x] { refl }
        theorem local_value<A>(x: A): local_family(x) = [x] { refl }
        theorem projected_value<A>(x: A): projected_family(x) = [x] { refl }
    "#);
}

#[test]
fn vector_literals_at_computed_carriers_keep_intrinsic_refusals() {
    let m = elab_err("fn V<A>(n: Nat) -> Type { [A; n] } fn bad() -> V<Nat>(2) { [1] }");
    assert!(m.contains("1 element(s) but 2 are expected"), "{m}");
    let m = elab_err("fn V<A>(n: Nat) -> Type { [A; n] } fn bad<A>(n: Nat, x: A) -> V<A>(n) { [x] }");
    assert!(m.contains("literal length"), "{m}");
    // A type as an element used to reach the kernel as a bare `LevelMismatch`;
    // it is refused at the element (issues/prop-in-bool-position-reaches-kernel.md).
    let m = elab_err("fn V<A>(n: Nat) -> Type { [A; n] } fn bad() -> V<Nat>(1) { [Type] }");
    assert!(m.contains("this is a type (it has type `Type<1>`), but a value of `Nat` is expected here"), "{m}");
    let m = elab_err("fn Carrier() -> Type { Nat } fn bad() -> Carrier() { [1] }");
    assert!(m.contains("no instance for `CollectionLiteral<Nat>(1)`"), "{m}");
}

#[test]
fn rejections() {
    // wrong length
    let m = elab_err("fn f() -> [Nat; 2] { [1] }");
    assert!(m.contains("1 element(s) but 2 are expected"), "{m}");

    // no expected type
    let m = elab_err("fn f(n: Nat) -> Nat { let xs = [1, 2];\n n }");
    assert!(m.contains("needs an expected container type"), "{m}");

    // a literal at a variable length
    let m = elab_err("fn f(n: Nat) -> [Nat; n] { [1] }");
    assert!(m.contains("literal length"), "{m}");

    // not a supported container type at all
    let m = elab_err("fn f() -> Nat { [1] }");
    assert!(m.contains("no instance for `CollectionLiteral<Nat>(1)`"), "{m}");
}
