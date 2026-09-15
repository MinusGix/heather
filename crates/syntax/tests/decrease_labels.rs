use heather_syntax::{parse_file, ExprKind, Item, OnTarget};

#[test]
fn postfix_labels_stay_on_their_own_nested_calls() {
    let file = parse_file("fn f(n: Nat) -> Nat decreases n { f(f(n) decreasing inner) decreasing outer on decreasing inner := p; on decreasing outer := q; }").unwrap();
    let Item::Decl(d) = &file.items[0] else { panic!("declaration") };
    let ExprKind::App { args, named, .. } = &d.body.result.kind else { panic!("outer call") };
    assert_eq!(named[0].name, "#decreasing:outer");
    assert!(matches!(&args[0].kind, ExprKind::App { named, .. } if named[0].name == "#decreasing:inner"));
    assert!(matches!(&d.body.ons[0].target, OnTarget::Name(n) if n == "#decreasing:inner"));
}

#[test]
fn malformed_or_unscoped_labels_are_rejected() {
    for (src, message) in [
        ("fn f(n: Nat) -> Nat decreases n { n decreasing tail }", "labels a recursive call"),
        ("fn f(n: Nat) -> Nat decreases n { f(n) decreasing a decreasing b }", "only one decrease label"),
        ("fn f(n: Nat) -> Nat { n on decreasing tail := p; }", "needs a declaration with `decreases`"),
    ] {
        let error = parse_file(src).unwrap_err();
        assert!(error.msg.contains(message), "{}", error.msg);
    }
    // The contextual word remains an ordinary name away from its postfix
    // and discharge positions.
    parse_file("fn decreasing(n: Nat) -> Nat { n }").unwrap();
}
