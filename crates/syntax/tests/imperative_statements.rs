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

#[test]
fn an_early_exit_is_refused_where_no_loop_lowers_it() {
    for (src, says) in [
        // No loop around it.
        ("fn f() -> Nat { let mut n = 0; break; n }", "is outside any loop"),
        ("fn f() -> Nat { let mut n = 0; continue; n }", "is outside any loop"),
        ("fn f(k: Nat) -> Nat { return k; }", "supported inside a `for` for now"),
        // Code after an exit never runs.
        ("fn f(xs: L) -> Nat { let mut n = 0; for x in xs { break; n := x } n }", "nothing after `break` runs"),
        // A returning loop nested in another loop or in a statement `if`:
        // its `Return` would have to cross the enclosing step.
        ("fn f(xs: L) -> Nat { let mut n = 0; for x in xs { for y in xs { if c { return 7 } n := y } } n }",
         "only as a statement of the function's own body"),
        ("fn f(xs: L) -> Nat { let mut n = 0; if c { for x in xs { if d { return 7 } n := x } } n }",
         "only as a statement of the function's own body"),
        // A loop that neither assigns a local nor returns computes nothing.
        ("fn f(xs: L) -> Nat { for x in xs { if c { break } } 0 }", "computes nothing"),
    ] {
        let error = parse_file(src).unwrap_err();
        assert!(error.msg.contains(says), "{src}: {}", error.msg);
    }
}

#[test]
fn an_early_exit_leaves_only_the_loop_markers() {
    // Exits become `ForStep` leaves the elaborator builds; no exit statement
    // or statement-form marker survives the parse.
    for src in [
        "fn f(xs: L) -> Nat { let mut n = 0; for x in xs { if c { break } n := x } n }",
        "fn f(xs: L) -> Nat { let mut n = 0; for x in xs { match x { A => { continue }, B => { n := 1 } } n := 2 } n }",
        "fn f(xs: L) -> Nat { for x in xs { if c { return x } } 0 }",
    ] {
        let parsed = format!("{:?}", parse_file(src).unwrap_or_else(|e| panic!("{src}: {}", e.msg)));
        for marker in ["\\0break", "\\0continue", "\\0return", "\\0stmt", "\\0assign"] {
            assert!(!parsed.contains(marker), "{src} keeps {marker}");
        }
    }
}

#[test]
fn a_while_names_its_measure_and_does_not_exit_yet() {
    for (src, says) in [
        // A `while` is a recursive function: its measure is required.
        ("fn f(n: Nat) -> Nat { let mut m = n; while 1 <= m { m := m - 1 } m }", "names what it decreases"),
        // Early exit threads `ForStep` through `f::run` (§5.3), not built yet.
        ("fn f(n: Nat) -> Nat { let mut m = n; while 1 <= m decreases m { if c { break } m := m - 1 } m }",
         "in a `while` are not built yet"),
        // Like a `for`, a `while` that assigns nothing computes nothing.
        ("fn f(n: Nat) -> Nat { while 1 <= n decreases n { } n }", "computes nothing"),
    ] {
        let error = parse_file(src).unwrap_err();
        assert!(error.msg.contains(says), "{src}: {}", error.msg);
    }
    // `while` stays a name where it is not a statement.
    parse_file("fn f(while: Nat) -> Nat { while }").unwrap_or_else(|e| panic!("{}", e.msg));
}
