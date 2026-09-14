use heather_syntax::{parse_file,ExprKind};

#[test]
fn prefix_goals_and_postfix_propagation_are_distinct() {
    let file = parse_file("theorem goal(): 0 = 0 { ?g on ?g := refl; }").unwrap();
    assert!(matches!(file.items[0].clone().into_decl().body.result.kind,ExprKind::Hole(Some(_))));
    parse_file("fn f(r: R) -> R { g(r??, ?proof) }").unwrap();
    parse_file("fn f(r: R) -> R { r?.field }").unwrap();
    parse_file("fn f(r: R) -> R { r?[0] }").unwrap();
    for src in [
        "fn f(r: R) -> R { r ? }",
        "fn f(r: R) -> R { r?name }",
        "fn f(r: R) -> R { let x: F(r?) = r; x }",
        "fn f(r: R) -> F(r?) { r }",
        "fn f(r: R) -> R { let f = fun (x: F(r?)) => x; r }",
        "fn f(r: R) -> R { r on _: F(r?) := r; }",
        "fn f(r: R) -> R { let x = match r as fun n => Nat { Ok(x) => x?, Err(e) => 0 }; Ok(x) }",
        "theorem f(r: R): R { r? }",
        "meta fn f(r: R) -> R { r? }",
        "fn f(r: R) -> R { code { r? } }",
    ] {
        assert!(parse_file(src).is_err(),"{src}");
    }
}

#[test]
fn lowering_is_deterministic_and_scopes_lambdas_separately() {
    let src = "fn f(r: R) -> R { let k = fun x => Ok(r?); let y = r?; Ok(k(y)) }";
    let a = parse_file(src).unwrap();
    let b = parse_file(src).unwrap();
    assert_eq!(format!("{a:?}"),format!("{b:?}"));
    assert!(!format!("{a:?}").contains("result-propagate"));
}
