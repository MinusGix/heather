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
        // With no measure, the loop is its carrier's (§18); one that assigns
        // nothing could only stop at once or never.
        ("fn f(n: Nat) -> P { while 1 <= n { } r(n) }", "its condition can never change"),
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

// A `while` with no measure (docs/sequencing-surface-design.md §18) is one
// `Iterate::then(init, step, rest)` call, written by the parser: no loop
// marker for the elaborator to lift, and the body's binds lowered inside
// the step, after the state is read.
#[test]
fn a_while_with_no_measure_is_one_iterate_call() {
    let src = "fn f(k: Nat, t: T) -> P { let mut i = 0; let mut a = 0; while i <= k { let x <- t; a := a + x; i := i + 1 } r(a) }";
    let parsed = format!("{:?}", parse_file(src).unwrap_or_else(|e| panic!("{}", e.msg)));
    assert!(parsed.contains("Iterate::then"), "{parsed}");
    assert!(parsed.contains("Bind::seq"), "the body's bind is lowered: {parsed}");
    assert!(parsed.contains("Step::Continue") && parsed.contains("Step::Break"), "{parsed}");
    assert!(parsed.contains("\"Mutated\""), "two locals nest in `Mutated`: {parsed}");
    for marker in ["\\0loop", "\\0bind", "\\0iterate", "\\0assign", "\\0for"] {
        assert!(!parsed.contains(marker), "keeps {marker}: {parsed}");
    }
}

#[test]
fn a_range_is_written_only_in_a_for_header() {
    let parsed = format!("{:?}", parse_file("fn f(n: Nat) -> Nat { let mut s = 0; for i in 0..n { s := s + i } s }").unwrap());
    assert!(parsed.contains("List::range\""), "{parsed}");
    let parsed = format!("{:?}", parse_file("fn f(a, b: Nat) -> Nat { let mut s = 0; for i in a..b { s := s + i } s }").unwrap());
    assert!(parsed.contains("List::range_from"), "{parsed}");
    let error = parse_file("fn f(n: Nat) -> Nat { let r = 0..n; 0 }").unwrap_err();
    assert!(error.msg.contains("a range only in a `for` header"), "{}", error.msg);
}

#[test]
fn a_mut_self_method_returns_its_receiver_beside_its_result() {
    // `fn C::tick(mut self c: C, …) → R` has result `Mutated<C, R>`, and its
    // body ends in `Mutated(c, value)` (docs/sequencing-surface-design.md §8.2).
    let parsed = format!("{:?}", parse_file("fn C::tick(mut self c: C, n: Nat) -> Nat { c := g(c, n); n }").unwrap());
    assert!(parsed.contains("\"Mutated\""), "{parsed}");
    // A `return` in a loop leaves with the receiver as it stands there:
    // the `Return` carries `Mutated(c, x)`, as the body's own end does.
    let parsed = format!("{:?}", parse_file("fn C::f(mut self c: C, xs: List<Nat>) -> Nat { for x in xs { c := g(c, x); return x; } 0 }").unwrap());
    assert_eq!(parsed.matches("\"Mutated\"").count(), 3, "{parsed}");
    // A plain `mut` parameter is a local copy: the result is unchanged.
    let parsed = format!("{:?}", parse_file("fn f(mut c: C) -> Nat { c := g(c); h(c) }").unwrap());
    assert!(!parsed.contains("\"Mutated\""), "{parsed}");
}

#[test]
fn a_mut_parameter_is_refused_where_nothing_is_updated() {
    for (src, says) in [
        ("theorem t(mut n: Nat): n = n { refl }", "only a `fn` takes `mut` parameters"),
        ("fn f({mut n: Nat}) -> Nat { n }", "an implicit parameter cannot be `mut`"),
    ] {
        let error = parse_file(src).unwrap_err();
        assert!(error.msg.contains(says), "{src}: {}", error.msg);
    }
}

#[test]
fn a_method_call_on_a_mutable_local_is_claimed_by_its_block() {
    // Claimed: the elaborator binds the receiver after the call.
    let parsed = format!("{:?}", parse_file("fn f(c: C) -> Nat { let mut c = c; let a = c.tick(1); c.tick(2); a }").unwrap());
    assert!(parsed.contains("\\0mutated") && !parsed.contains("\\0mutcall"), "{parsed}");
    // Not mutable: an ordinary call, unmarked.
    let parsed = format!("{:?}", parse_file("fn f(c: C) -> Nat { let a = c.tick(1); a }").unwrap());
    assert!(!parsed.contains("\\0mut"), "{parsed}");
}
