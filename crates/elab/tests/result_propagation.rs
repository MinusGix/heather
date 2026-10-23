use heather_elab::Elaborator;

fn base() -> Elaborator {
    let mut e = Elaborator::with_prelude().expect("prelude");
    e.elab_module_source("result", include_str!("../../../lib/std/core/result.hthr")).expect("result library");
    e
}
fn ok(src: &str) {
    base().elab_module_source("probe",src).unwrap_or_else(|e| panic!("{}",e.render(src)));
}
#[test]
fn propagates_and_agrees_with_an_explicit_match() {
    ok(r#"
        import result;
        fn step<A,E>(r: Result<A,E>) -> Result<A,E> { Ok(r?) }
        fn explicit<A,E>(r: Result<A,E>) -> Result<A,E> {
            match r { Ok(v) => Ok(v), Err(e) => Err(e) }
        }
        theorem same<A,E>(r: Result<A,E>): step(r) = explicit(r) { refl }
        theorem success(): step<Nat,Nat>(Ok(3)) = Ok(3) { refl }
        theorem failure(): step<Nat,Nat>(Err(7)) = Err(7) { refl }
        fn two(a: Result<Nat,Nat>, b: Result<Nat,Nat>) -> Result<Nat,Nat> {
            let x = a?;
            let y = b?;
            Ok(x)
        }
        theorem first(): two(Err(2),Err(3)) = Err(2) { refl }
        theorem second(): two(Ok(2),Err(3)) = Err(3) { refl }
    "#);
}
#[test]
fn nested_calls_blocks_branches_and_lambda_boundaries() {
    ok(r#"
        import result;
        fn nested(r: Result<Result<Nat,Nat>,Nat>) -> Result<Nat,Nat> { Ok(Succ(r??)) }
        theorem nested_ok(): nested(Ok(Ok(3))) = Ok(4) { refl }
        theorem inner_err(): nested(Ok(Err(5))) = Err(5) { refl }
        theorem outer_err(): nested(Err(6)) = Err(6) { refl }
        fn block(r: Result<Nat,Nat>) -> Result<Nat,Nat> {
            let x = { let y = r?; Succ(y) };
            Ok(Succ(x))
        }
        theorem block_ok(): block(Ok(3)) = Ok(5) { refl }
        theorem block_err(): block(Err(8)) = Err(8) { refl }
        fn branch(n: Nat, r: Result<Nat,Nat>) -> Result<Nat,Nat> {
            match n { Zero => Ok(0), Succ(k) => Ok(r?) }
        }
        theorem unselected(): branch(0,Err(9)) = Ok(0) { refl }
        fn lambda(r: Result<Nat,Nat>) -> Result<Result<Nat,Nat>,Nat> {
            let f: Nat → Result<Nat,Nat> = λ n => Ok(r?);
            Ok(f(0))
        }
        theorem lambda_error_stays_inside(): lambda(Err(4)) = Ok(Err(4)) { refl }
    "#);
}

#[test]
fn continuations_keep_their_outer_bindings() {
    ok(r#"
        import result;
        fn block_shadow(x: Nat, r: Result<Nat,Nat>) -> Result<Nat,Nat> {
            let y = { let x = 9; let z = r?; x };
            Ok(x)
        }
        theorem block_scope(): block_shadow(3,Ok(0)) = Ok(3) { refl }
        fn branch_shadow(x: Nat, n: Nat, r: Result<Nat,Nat>) -> Result<Nat,Nat> {
            let y = match n { Zero => r?, Succ(x) => r? };
            Ok(x)
        }
        theorem branch_scope(): branch_shadow(3,4,Ok(0)) = Ok(3) { refl }
        fn argument_shadow(x: Nat, r: Result<Nat,Nat>) -> Result<Nat,Nat> {
            Ok((λ (a: Nat) (b: Nat) => a)(x, { let x = 9; r? }))
        }
        theorem argument_scope(): argument_shadow(3,Ok(0)) = Ok(3) { refl }
    "#);
}

#[test]
fn wrong_carriers_errors_and_false_equations_are_refused() {
    for src in [
        "import result; fn f(r: Result<Nat,Nat>) -> Nat { r? }",
        "import result; fn f(r: Nat) -> Result<Nat,Nat> { Ok(r?) }",
        "import result; fn f(r: Result<Nat,Nat>) -> Result<Nat,Nat> { result::Ok(r?, wrong := 0) }",
        "import result; fn f(r: Result<Nat,Nat>) -> Result<Nat,Nat> { result::Ok(r?, value := 1) }",
        "import result; inductive E { Bad } fn f(r: Result<Nat,Nat>) -> Result<Nat,E> { Ok(r?) }",
        "import result; fn f(r: Result<Nat,Nat>) -> Result<Nat,Nat> { Ok(r?) } theorem bad(): f(Err(3)) = Ok(3) { refl }",
    ] {
        let err = base().elab_module_source("probe",src).expect_err("must reject");
        assert!(!err.render(src).contains("result-propagate"),"{}",err.render(src));
    }
}

#[test]
fn parser_client_checks_and_its_wrong_result_is_rejected() {
    let mut e = base();
    e.elab_module_source("logic",include_str!("../../../lib/std/core/logic.hthr")).expect("logic");
    e.elab_module_source("bool",include_str!("../../../lib/std/core/bool.hthr")).expect("bool");
    e.elab_module_source("pair",include_str!("../../../lib/std/core/pair.hthr")).expect("pair");
    e.elab_module_source("nat",include_str!("../../../lib/std/num/nat.hthr")).expect("nat");
    e.elab_module_source("option",include_str!("../../../lib/std/core/option.hthr")).expect("option");
    e.elab_module_source("list",include_str!("../../../lib/std/data/list.hthr")).expect("list");
    let src = include_str!("../../../docs/showcase/result_parser.hthr");
    e.elab_module_source("parser",src).unwrap_or_else(|e| panic!("{}",e.render(src)));
    let bad = "import parser; import result; theorem wrong(): parse_sum([Number(2), Plus, Number(3)]) = Ok(6) { refl }";
    e.elab_module_source("wrong",bad).expect_err("wrong parser result");
}

#[test]
fn postfix_composition_and_written_argument_order() {
    ok(r#"
        import result;
        record Cell { value: Nat }
        fn field(r: Result<Cell,Nat>) -> Result<Nat,Nat> { Ok(r?.value) }
        theorem field_ok(): field(Ok(Cell(7))) = Ok(7) { refl }
        fn index(r: Result<[Nat;2],Nat>) -> Result<Nat,Nat> { Ok(r?[0]) }
        theorem index_ok(): index(Ok([4,5])) = Ok(4) { refl }
        fn vector(a: Result<Nat,Nat>, b: Result<Nat,Nat>) -> Result<[Nat;2],Nat> { Ok([a?,b?]) }
        theorem vector_ok(): vector(Ok(2),Ok(3)) = Ok([2,3]) { refl }
        fn take(a: Nat, b: Nat) -> Nat { a }
        fn named(a: Result<Nat,Nat>, b: Result<Nat,Nat>) -> Result<Nat,Nat> {
            Ok(take(b := b?, a := a?))
        }
        theorem named_order(): named(Err(2),Err(3)) = Err(3) { refl }
        fn scopes(r: Result<Nat,Nat>, s: Result<Nat,Nat>) -> Result<Result<Nat,Nat>,Nat> {
            let f: Nat → Result<Nat,Nat> = λ n => Ok(r?);
            let y = s?;
            Ok(f(y))
        }
        theorem inner(): scopes(Err(2),Ok(3)) = Ok(Err(2)) { refl }
        theorem outer(): scopes(Err(2),Err(3)) = Err(3) { refl }
        theorem mapped(): (Ok<Nat,Nat>(3)).map(Succ) = Ok(4) { refl }
        theorem converted(): (Err<Nat,Nat>(3)).map_err(Succ) = Err(4) { refl }
        fn with_goal(r: Result<Nat,Nat>) -> Result<Nat,Nat> {
            let x = r?;
            let p: (x = x) = ?proof;
            Ok(x)
            on ?proof := refl;
        }
        theorem goal_ok(): with_goal(Ok(5)) = Ok(5) { refl }
    "#);
}
