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
    assert!(m.contains("expected `List<A>` or `[T; n]` type"), "{m}");
}
