//! An equality may take its endpoint type from the right when the left
//! contains a checking-only form and cannot infer on its own. The emitted
//! identity type still keeps the endpoints in their written order.

use heather_elab::Elaborator;

use crate::support;

fn base() -> Elaborator {
    support::semantic_test_base(&[
        ("logic", include_str!("../../../lib/std/core/logic.hthr")),
        ("bool", include_str!("../../../lib/std/core/bool.hthr")),
        ("nat", include_str!("../../../lib/std/num/nat.hthr")),
        ("option", include_str!("../../../lib/std/core/option.hthr")),
        ("pair", include_str!("../../../lib/std/core/pair.hthr")),
        ("list", include_str!("../../../lib/std/data/list.hthr")),
        ("result", include_str!("../../../lib/std/core/result.hthr")),
    ])
}

fn ok(src: &str) {
    let src = format!("import result; import option; import list;\n{src}");
    base()
        .elab_module_source("client", &src)
        .unwrap_or_else(|err| panic!("{}", err.render(&src)));
}

fn bad(src: &str) -> String {
    let src = format!("import result; import option; import list;\n{src}");
    let err = base()
        .elab_module_source("client", &src)
        .expect_err("source must be rejected");
    err.render(&src)
}

#[test]
fn an_inferable_right_endpoint_types_a_deferred_left_call() {
    ok(r#"
        fn boxed<A,E>(r: Result<A,E>) -> Result<Option<List<A>>,E> {
            r.map(λ (a: A) => Some([a]))
        }
        theorem forward<A,E>(r: Result<A,E>):
            boxed(r) = r.map(λ (a: A) => Some([a])) { refl }
        theorem reverse<A,E>(r: Result<A,E>):
            r.map(λ (a: A) => Some([a])) = boxed(r) { refl }
    "#);
}

#[test]
fn a_collection_receiver_gets_the_generic_calls_type_from_the_right() {
    ok(r#"
        fn flatten<A>(self xss: List<List<A>>) -> List<A> {
            match xss { Nil => Nil, Cons(xs, rest) => xs }
        }
        theorem singleton<A>(xs: List<A>): ([xs]).flatten() = xs { refl }
    "#);
}

#[test]
fn incompatible_false_and_wholly_unanchored_equations_stay_rejected() {
    let incompatible = bad(r#"
        fn flatten<A>(self xss: List<List<A>>) -> List<A> {
            match xss { Nil => Nil, Cons(xs, rest) => xs }
        }
        theorem wrong<A>(xs: List<A>): ([xs]).flatten() = 0 { refl }
    "#);
    assert!(!incompatible.contains("internal:"), "{incompatible}");

    let false_equation = bad(r#"
        fn flatten<A>(self xss: List<List<A>>) -> List<A> {
            match xss { Nil => Nil, Cons(xs, rest) => xs }
        }
        theorem wrong(): ([[1]]).flatten() = Cons(2, Nil) { refl }
    "#);
    assert!(!false_equation.contains("internal:"), "{false_equation}");

    let unanchored = bad("theorem unknown(): ([1]) = ([1]) { refl }");
    assert!(
        unanchored.contains("collection literal needs an expected container type"),
        "{unanchored}"
    );
}
