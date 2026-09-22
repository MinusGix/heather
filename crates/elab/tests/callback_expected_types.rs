//! An annotated lambda domain does not make its body inferable. Callbacks
//! still need the enclosing application's expected result for constructors
//! and collection literals in checking-only positions.
use heather_elab::Elaborator;
mod support;

fn base() -> Elaborator {
    support::semantic_test_base(&[
        ("logic", include_str!("../../../lib/std/logic.hthr")),
        ("bool", include_str!("../../../lib/std/bool.hthr")),
        ("nat", include_str!("../../../lib/std/nat.hthr")),
        ("option", include_str!("../../../lib/std/option.hthr")),
        ("pair", include_str!("../../../lib/std/pair.hthr")),
        ("list", include_str!("../../../lib/std/list.hthr")),
        ("result", include_str!("../../../lib/std/result.hthr")),
    ])
}
fn ok(src: &str) {
    let src = format!("import result; import option; import list;\n{src}");
    base().elab_module_source("client", &src).unwrap_or_else(|err| panic!("{}", err.render(&src)));
}

#[test]
fn expected_result_reaches_annotated_callbacks() {
    ok(r#"
        fn qualified<A,E>(r: Result<A,E>) -> Result<Option<List<A>>,E> {
            r.map(λ (a: A) => Some([a]))
        }
        fn receiver<A,E>(r: Result<A,E>) -> Result<Option<List<A>>,E> {
            r.map(λ (a: A) => Some([a]))
        }
        theorem same<A,E>(r: Result<A,E>):
            qualified(r) = r.map(λ (a: A) => Some([a])) { refl }
        theorem dot_same<A,E>(r: Result<A,E>):
            qualified(r) = r.map(λ (a: A) => Some([a])) { refl }
        theorem success(): receiver<Nat,Nat>(Ok(2)) = Ok(Some([2])) { refl }
        theorem error(): receiver<Nat,Nat>(Err(7)) = Err(7) { refl }
        fn nested<A,E>(r: Result<A,E>) -> Result<Option<Option<List<A>>>,E> {
            r.map(λ (a: A) => Some(Some([a])))
        }
        theorem nesting(): nested<Nat,Nat>(Ok(2)) = Ok(Some(Some([2]))) { refl }
    "#);
}

#[test]
fn later_arguments_and_unannotated_callbacks_use_the_same_checking_path() {
    ok(r#"
        fn choose<A>(f: Nat → A, value: A) -> A { f(2) }
        fn singleton(n: Nat) -> List<Nat> { [n] }
        fn later() -> Nat {
            let xs = choose(λ (n: Nat) => [n], singleton(9));
            xs.len()
        }
        theorem later_value(): later() = 1 { refl }
        fn unannotated<A,E>(r: Result<A,E>) -> Result<Option<List<A>>,E> {
            r.map(λ a => Some([a]))
        }
        fn use_two<A>(f: Nat → Nat → A) -> A { f(2,3) }
        fn two_binders() -> List<Nat> { use_two(λ (a: Nat) (b: Nat) => [a,b]) }
        theorem two_values(): two_binders() = [2,3] { refl }
        theorem inferred_binder(): unannotated<Nat,Nat>(Ok(2)) = Ok(Some([2])) { refl }
    "#);
}

#[test]
fn callbacks_can_still_teach_their_result_type() {
    ok(r#"
        fn inferred<A,E>(r: Result<A,E>) -> Result<A,E> {
            let mapped = r.map(λ (a: A) => a);
            mapped
        }
        fn two<A,B>(f: A → B, x: A) -> B { f(x) }
        fn inference_position() -> Nat {
            let n = two(λ (x: Nat) => Succ(x), 2);
            n
        }
        theorem computed(): inference_position() = 3 { refl }
        theorem same<A,E>(r: Result<A,E>): inferred(r) = r.map(λ (a: A) => a) { refl }
        theorem standalone(): (λ (n: Nat) => n) = (λ (n: Nat) => n) { refl }
    "#);
}

#[test]
fn dependent_callbacks_keep_outer_and_local_binders_scoped() {
    ok(r#"
        fn use<A>(family: A → Type, f: (a: A) → family(a), x: A) -> family(x) { f(x) }
        theorem dependent<A>(x: A):
            use<A>(λ (a: A) => a = a, λ (a: A) => refl, x) = refl { refl }
        fn pair_with<A,E>(outer: A, r: Result<A,E>) -> Result<List<A>,E> {
            r.map(λ (inner: A) => [outer, inner])
        }
        theorem captured(): pair_with<Nat,Nat>(2,Ok(3)) = Ok([2,3]) { refl }
    "#);
}

#[test]
fn underconstrained_and_wrong_callbacks_are_refused() {
    for src in [
        "fn wrong(r: Result<Nat,Nat>) -> Nat { let x = r.map(λ (n: Nat) => [n]); 0 }",
        "fn wrong<A,E>(r: Result<A,E>) -> Result<Option<List<Nat>>,E> { r.map(λ (a: A) => Some([a])) }",
        "fn wrong(r: Result<Nat,Nat>) -> Result<Option<List<Nat>>,Nat> { r.map(λ (n: Option<Nat>) => Some([n])) }",
        "fn wrong(r: Result<Nat,Nat>) -> Result<[Nat;2],Nat> { r.map(λ (n: Nat) => [n]) }",
        "theorem wrong(): Result::map<Nat,Nat,Nat>(Ok(2), λ (n: Nat) => Succ(n)) = Ok(9) { refl }",
        "fn wrong(r: Result<Nat,Nat>) -> Result<Nat,Nat> { r.map(λ (n: Nat) => n(n)) }",
    ] {
        let src = format!("import result; import option; import list; {src}");
        let err = base().elab_module_source("client", &src).expect_err(&format!("must reject: {src}"));
        let message = err.render(&src);
        assert!(!message.contains("unbound") && !message.contains("ambiguous"), "{message}");
    }
}
