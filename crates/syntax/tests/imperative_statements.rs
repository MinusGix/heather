//! Parse-level facts of local state in pure code
//! (docs/sequencing-surface-design.md §4, §5.1): the refusals a whole file's
//! parse owns, which a Heather probe cannot state (a parse error refuses the
//! file), and that the lowering leaves no marker behind. What the lowered
//! forms mean is probed in Heather,
//! `lib/_tests/std/core/imperative_statements_tests.hthr`.
use heather_syntax::parse_file;

#[test]
fn the_lowering_leaves_no_marker() {
    for src in [
        "fn f(n: Nat) -> Nat { let mut x = n; x := g(x); x }",
        "fn f(c: Bool) -> Nat { let mut x = 0; if c { x := 1 } x }",
        "fn f(c: Bool) -> Nat { let mut x = 0; if c { x := 1 } else if d { x := 2 } else { x := 3 } x }",
        "fn f(o: O) -> Nat { let mut x = 0; match o { A => { x := 1 }, B => {} } x }",
        "fn f(c: Bool) -> Nat { let mut x = 0; if c { let mut y = 1; if d { x := 2; y := 3 } x := y } x }",
    ] {
        let parsed = format!("{:?}", parse_file(src).unwrap_or_else(|e| panic!("{src}: {}", e.msg)));
        for marker in ["\\0mut", "\\0assign", "\\0stmt", "\\0unit"] {
            assert!(!parsed.contains(marker), "{src} keeps {marker}");
        }
    }
}

#[test]
fn an_assignment_reaches_only_a_mut_local_of_its_statement_scope() {
    for src in [
        // Never declared `mut`.
        "fn f() -> Nat { let x = 1; x := 2; x }",
        // Shadowed by a plain `let`.
        "fn f() -> Nat { let mut x = 1; let x = 2; x := 3; x }",
        // Through a λ.
        "fn f() -> Nat { let mut x = 1; let g = λ (u: Nat) => { x := u; x }; g(2) }",
        // Through a block in value position.
        "fn f() -> Nat { let mut x = 1; let y = { x := 2; x }; y }",
        // Inside a statement body, to a local of no enclosing scope.
        "fn f(c: Bool) -> Nat { let mut x = 1; if c { z := 2 } x }",
    ] {
        let error = parse_file(src).unwrap_err();
        assert!(error.msg.contains("is not mutable"), "{src}: {}", error.msg);
    }
}

#[test]
fn a_statement_body_has_no_value() {
    // A block that ends in an assignment where a value is needed.
    let error = parse_file("fn f() -> Nat { let mut x = 1; x := 2 }").unwrap_err();
    assert!(error.msg.contains("no value here"), "{}", error.msg);
    // An `if` without `else` is a statement only.
    let error = parse_file("fn f(c: Bool) -> Nat { let y = if c { 1 }; y }").unwrap_err();
    assert!(error.msg.contains("needs an `else"), "{}", error.msg);
}

#[test]
fn a_proof_if_of_empty_blocks_stays_a_proof() {
    // `{}` arms alone are the empty proof block, not statements.
    let parsed = format!("{:?}", parse_file("theorem t(c: Bool): P { if c {} else {} }").unwrap());
    assert!(parsed.contains("AutoRefl"));
    assert!(!parsed.contains("\\0stmt"));
}

#[test]
fn a_for_threads_the_locals_its_body_assigns() {
    let src = "fn f(xs: L) -> Nat { let mut n = 0; let mut m = 1; for x in xs { m := m + x; n := n + 1 } n }";
    let parsed = format!("{:?}", parse_file(src).unwrap_or_else(|e| panic!("{}", e.msg)));
    assert!(parsed.contains(heather_syntax::LOOP.escape_debug().to_string().as_str()), "{parsed}");
    assert!(parsed.contains(heather_syntax::PROJ.escape_debug().to_string().as_str()));
    assert!(!parsed.contains("\\0for\""));
}

#[test]
fn a_for_must_assign_and_be_a_statement() {
    let error = parse_file("fn f(xs: L) -> Nat { let mut n = 0; for x in xs { let y = x; } n }").unwrap_err();
    assert!(error.msg.contains("`;` to end") || error.msg.contains("expected"), "{}", error.msg);
    let error = parse_file("fn f(xs: L) -> Nat { let n = 0; for x in xs { n := n + x } n }").unwrap_err();
    assert!(error.msg.contains("is not mutable"), "{}", error.msg);
    let error = parse_file("fn f(xs: L) -> Nat { let mut n = 0; for x in xs { x } n }").unwrap_err();
    assert!(error.msg.contains("ends in a statement, not a value"), "{}", error.msg);
    let error = parse_file("fn f(xs: L) -> Nat { let mut n = 0; for x in xs {} n }").unwrap_err();
    assert!(error.msg.contains("assigns no `let mut` local"), "{}", error.msg);
}
