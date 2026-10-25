//! Receiver selection among ambiguous imported functions is independent of
//! callback inference. Every callback here has an inferable function type.
//!
//! std's `result` and `option` now own their `map`s as `Result::map` and
//! `Option::map`, which member dispatch reaches and never makes ambiguous, so
//! the two carriers here are fixtures that keep a free `self` `map` each.
use heather_elab::Elaborator;

const RESULT: &str = r#"
    inductive Result<A, E> { Ok(value: A), Err(error: E) }
    fn map<A, B, E>(self r: Result<A, E>, f: A → B) → Result<B, E> {
        match r { Ok(value) => Ok(f(value)), Err(error) => Err(error) }
    }
"#;

const OPTION: &str = r#"
    inductive Option<A> { None, Some(v: A) }
    fn map<A, B>(self o: Option<A>, f: A → B) → Option<B> {
        match o { None => None, Some(v) => Some(f(v)) }
    }
"#;

fn base() -> Elaborator {
    let mut e = Elaborator::with_prelude().expect("prelude");
    e.elab_module_source("result", RESULT).expect("result");
    e.elab_module_source("option", OPTION).expect("option");
    e
}

fn ok(e: &mut Elaborator, src: &str) {
    e.elab_module_source("client", src).unwrap_or_else(|err| panic!("{}", err.render(src)));
}

#[test]
fn imported_maps_follow_neutral_receivers_and_compute() {
    let mut e = base();
    ok(&mut e, r#"
        import result;
        import option;
        fn rmap<A,B,E>(r: Result<A,E>, f: A → B) -> Result<B,E> { r.map(f) }
        fn omap<A,B>(o: Option<A>, f: A → B) -> Option<B> { o.map(f) }
        fn vmap<A,B>(v: [A;2], f: A → B) -> [B;2] { v.map(f) }
        theorem same<A,B,E>(r: Result<A,E>, f: A → B): r.map(f) = result::map(r,f) { refl }
        theorem success(): rmap<Nat,Nat,Nat>(Ok(2),Succ) = Ok(3) { refl }
        theorem error(): rmap<Nat,Nat,Nat>(Err(2),Succ) = Err(2) { refl }
        theorem optional(): omap<Nat,Nat>(Some(2),Succ) = Some(3) { refl }
        theorem vector(): vmap<Nat,Nat>([2,3],Succ) = [3,4] { refl }
    "#);
}

fn refused(e: &mut Elaborator, src: &str) -> String {
    let err = e.elab_module_source("client", src).expect_err(&format!("must reject: {src}"));
    err.render(src)
}

#[test]
fn import_order_and_unrelated_carriers_do_not_choose_the_operation() {
    for imports in ["import result; import option; import unrelated;", "import unrelated; import option; import result;"] {
        let mut e = base();
        e.elab_module_source("unrelated", "fn map(n: Nat, f: Nat → Nat) -> Nat { f(n) }").expect("unrelated");
        ok(&mut e, &format!(r#"{imports}
            theorem result(): (Ok<Nat,Nat>(2)).map(Succ) = Ok(3) {{ refl }}
            theorem number(): (2).map(Succ) = 3 {{ refl }}
        "#));
    }
}

#[test]
fn same_carrier_and_unknown_generic_receivers_remain_ambiguous() {
    for extra in [
        "import result; fn map<A,B,E>(r: Result<A,E>, f: A → B) -> Result<B,E> { result::map(r,f) }",
        "fn map<A>(x: A, f: Nat → Nat) -> A { x }",
    ] {
        let mut e = base();
        e.elab_module_source("other", extra).expect("other");
        let msg = refused(&mut e, "import result; import option; import other; fn f(r: Result<Nat,Nat>) -> Result<Nat,Nat> { r.map(Succ) }");
        assert!(msg.contains("ambiguous") && msg.contains("result") && msg.contains("other"), "{msg}");
        assert!(!msg.contains("has to be a vector"), "{msg}");
    }
}

#[test]
fn local_bindings_selected_imports_and_fields_keep_their_precedence() {
    let mut e = base();
    ok(&mut e, r#"
        import result;
        import option;
        fn map(n: Nat, f: Nat → Nat) -> Nat { 9 }
        theorem local(): (2).map(Succ) = 9 { refl }
        fn alias(n: Nat) -> Nat {
            let map: Nat → (Nat → Nat) → Nat = λ x f => f(x);
            n.map(Succ)
        }
        theorem alias_value(): alias(2) = 3 { refl }
        record Mapper { map: Nat → Nat }
        theorem field(): Mapper(Succ).map(2) = 3 { refl }
        theorem qualified(): result::map<Nat,Nat,Nat>(Ok(2),Succ) = Ok(3) { refl }
    "#);
    let mut e = base();
    ok(&mut e, r#"
        import result::{map};
        import option;
        fn use_selected<A,B,E>(r: result::Result<A,E>, f: A → B) -> result::Result<B,E> { r.map(f) }
    "#);
}

#[test]
fn subject_position_and_declaring_type_identity_are_preserved() {
    let mut e = base();
    for name in ["a", "b"] {
        e.elab_module_source(name, "record Box { value: Nat } fn choose(n: Nat, self b: Box) -> Nat { b.value }").expect("box module");
    }
    ok(&mut e, r#"
        import a; import b;
        fn left(x: a::Box) -> Nat { x.choose(7) }
        fn right(x: b::Box) -> Nat { x.choose(7) }
        theorem left_value(): left(a::Box(2)) = 2 { refl }
        theorem right_value(): right(b::Box(3)) = 3 { refl }
    "#);
}

#[test]
fn failures_report_the_selected_operation_and_bare_calls_stay_ambiguous() {
    for (body, expected) in [
        ("fn wrong(r: Result<Nat,Nat>, f: Option<Nat> → Nat) -> Result<Nat,Nat> { r.map(f) }", "this has type `Option<Nat> -> Nat`, but `Nat -> Nat` is expected here"),
        ("fn wrong(n: Nat) -> Result<Nat,Nat> { (match n { Zero => Ok(0), Succ(k) => Ok(k) }).map(Succ) }", "infer"),
        ("fn wrong(v: [Nat;2]) -> [Nat;2] { map(v,Succ) }", "ambiguous"),
        ("theorem wrong(): (Ok<Nat,Nat>(2)).map(Succ) = Ok(9) { refl }", "NotConvertible"),
        ("fn wrong(v: [Nat;2]) -> [Nat;2] { v.map() }", "takes"),
        ("fn wrong(v: [Nat;2]) -> Nat { v.map(Succ) }", "Nat"),
        ("fn wrong(v: [Nat;2]) -> [Nat;2] { v.map(f := Succ) }", "positional"),
    ] {
        let mut e = base();
        let msg = refused(&mut e, &format!("import result; import option; {body}"));
        assert!(msg.contains(expected), "{msg}");
        assert!(!msg.contains("receiver has to be a vector"), "{msg}");
    }
}
