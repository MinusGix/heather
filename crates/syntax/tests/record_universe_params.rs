// A record's angle-bracket parameters declared at a universe
// (issues/record-universe-parameters.md): they become the record's leading
// value parameters, and they must come first.
use heather_syntax::{parse_file, Item};

#[test]
fn universe_parameters_lead_the_value_parameters() {
    let file = parse_file("record Hom<A: Type<1>, B: Type<1>>(map: A → B) { k: Nat }").unwrap();
    let Item::Inductive(r) = &file.items[0] else { panic!("record") };
    assert!(r.params.is_empty(), "no type parameters remain");
    let names: Vec<&str> = r.valparams.iter().map(|p| p.name.as_str()).collect();
    assert_eq!(names, ["A", "B", "map"]);
    // A plain type parameter may follow the universe ones.
    let file = parse_file("record Box1<A: Type<1>, X> { a: A, x: X }").unwrap();
    let Item::Inductive(r) = &file.items[0] else { panic!("record") };
    assert_eq!(r.params.len(), 1);
    assert_eq!(r.valparams.len(), 1);
}

#[test]
fn misplaced_or_non_universe_kinds_are_rejected() {
    for (src, message) in [
        ("record R<X, A: Type<1>> { a: A }", "lead its type parameters"),
        ("record R<M: Type → Type> { a: Nat }", "annotated only with a universe"),
    ] {
        let error = parse_file(src).unwrap_err();
        assert!(error.msg.contains(message), "{}", error.msg);
    }
}
