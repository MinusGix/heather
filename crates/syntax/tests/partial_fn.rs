//! Parse-level facts of `partial fn` (docs/partial-functions-design.md §9):
//! the word is contextual, `partial(E)` carries the events, and the
//! refusals a whole file's parse owns, which a Heather probe cannot state (a
//! parse error refuses the file). What a partial function means is probed in
//! Heather, `lib/_tests/std/itree/partial_fn_tests.hthr`.
use heather_syntax::parse_file;

#[test]
fn partial_marks_a_fn_with_or_without_events() {
    let file = parse_file("partial fn f(n: Nat) -> Nat { f(n) }").unwrap_or_else(|e| panic!("{}", e.msg));
    let d = file.items[0].clone().into_decl();
    assert!(d.partial.as_ref().is_some_and(|p| p.events.is_none()));
    let file = parse_file("partial(Events::ask()) fn f(n: Nat) -> Nat { f(n) }").unwrap_or_else(|e| panic!("{}", e.msg));
    let d = file.items[0].clone().into_decl();
    assert!(d.partial.as_ref().is_some_and(|p| p.events.is_some()));
    // Still a name elsewhere.
    parse_file("fn partial(n: Nat) -> Nat { n }").unwrap_or_else(|e| panic!("{}", e.msg));
    parse_file("fn f(partial: Nat) -> Nat { partial }").unwrap_or_else(|e| panic!("{}", e.msg));
}

#[test]
fn partial_refuses_what_has_no_run_and_a_measure() {
    for (src, says) in [
        ("partial theorem t(): True { trivial }", "`partial` marks a `fn`"),
        ("partial def x: Nat = 0;", "`partial` marks a `fn`"),
        ("partial fn f(n: Nat) -> Nat decreases n { f(n) }", "a `partial fn` has no measure"),
    ] {
        let error = parse_file(src).unwrap_err();
        assert!(error.msg.contains(says), "{src}: {}", error.msg);
    }
}
