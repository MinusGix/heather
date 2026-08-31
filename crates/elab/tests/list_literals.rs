//! `List[…]` construction syntax (`issues/list-literal-syntax.md`). Literals
//! are surface sugar for the ordinary `Nil`/`Cons` declaration and add no
//! kernel form.

use heather_elab::{ElabError, Elaborator};

const LIST: &str = "inductive List<A> { Nil, Cons(head: A, tail: List<A>) }\n";

fn elab(body: &str) -> Elaborator {
    let mut elaborator = Elaborator::with_prelude().expect("prelude");
    let source = format!("{LIST}{body}");
    elaborator
        .elab_source(&source)
        .unwrap_or_else(|error| panic!("{}", error.render(&source)));
    elaborator
}

fn elab_err(body: &str) -> (String, String) {
    let mut elaborator = Elaborator::with_prelude().expect("prelude");
    let source = format!("{LIST}{body}");
    let error = elaborator.elab_source(&source).expect_err("expected elaboration to fail");
    let message = match &error {
        ElabError::Elab { msg, .. } | ElabError::Parse(heather_syntax::ParseError { msg, .. }) => {
            msg.clone()
        }
        other => other.to_string(),
    };
    (message, error.render_snippet(&source, "test.hthr"))
}

#[test]
fn empty_nonempty_and_trailing_comma_literals_lower_to_list_constructors() {
    elab(
        r#"
        fn empty() -> List<Nat> { List[] }
        fn three() -> List<Nat> { List[1, 2, 3,] }

        theorem empty_lowers(): empty() = Nil { refl }
        theorem three_lowers(): three() = Cons(1, Cons(2, Cons(3, Nil))) { refl }
        "#,
    );
}

#[test]
fn a_nonempty_literal_infers_its_homogeneous_element_type() {
    elab(
        r#"
        fn inferred() -> List<Nat> {
            let xs = List[1, 2];
            xs
        }
        theorem inferred_lowers(): inferred() = Cons(1, Cons(2, Nil)) { refl }
        "#,
    );
}

#[test]
fn list_and_vector_brackets_remain_distinct() {
    elab(
        r#"
        fn list() -> List<Nat> { List[1, 2] }
        fn vector() -> [Nat; 2] { [1, 2] }
        fn spaced_index(List: [Nat; 1]) -> Nat { List [FZ] }
        theorem list_lowers(): list() = Cons(1, Cons(2, Nil)) { refl }
        "#,
    );
}

#[test]
fn empty_and_heterogeneous_literals_have_local_diagnostics() {
    let (message, _) = elab_err("fn f() -> Nat { let xs = List[]; 0 }");
    assert!(message.contains("cannot infer the element type of `List[]`"), "{message}");

    let (message, rendered) = elab_err(
        r#"
        inductive Bool { False, True }
        fn f() -> List<Nat> { List[1, True, 3] }
        "#,
    );
    assert!(message.contains("not the expected type"), "{message}");
    assert!(rendered.contains("List[1, True, 3]"), "{rendered}");
    assert!(rendered.lines().any(|line| line.contains("^^^^") && !line.contains("^^^^^^^^^^")), "the element, not the whole literal, should be highlighted: {rendered}");
}

#[test]
fn a_list_literal_refuses_non_list_expected_types_and_nonstandard_list_shapes() {
    let (message, _) = elab_err("fn f() -> Nat { List[1] }");
    assert!(message.contains("cannot construct") || message.contains("expected `List<A>`"), "{message}");

    let mut elaborator = Elaborator::with_prelude().expect("prelude");
    let source = "inductive List<A> { Empty, Push(A, List<A>) } fn f() -> List<Nat> { List[1] }";
    let error = elaborator.elab_source(source).expect_err("nonstandard List must be refused");
    assert!(error.to_string().contains("needs `List<A>` with `Nil` and `Cons"), "{error}");
}
