//! The surface vector type `[T; n]` and generic collection literals
//! (docs/container-fields.md §2), the surface half of container fields.

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
        fn empty<A>() -> V<A>(0) { let xs: [A; 0] = []; xs }
        fn one() -> V<Nat>(1) { let xs: [Nat; 1] = [1]; xs }
        fn two() -> V<Nat>(2) { let xs: [Nat; 2] = [1, 2]; xs }
        fn plain_two() -> [Nat; 2] { [1, 2] }
        fn nested_value() -> nested<Nat>(2, 1) { let xs: [[Nat; 2]; 1] = [[1, 2]]; xs }
        fn functions<A>() -> arrows<A>(1) { let xs: [A -> A; 1] = [λ x => x]; xs }
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
