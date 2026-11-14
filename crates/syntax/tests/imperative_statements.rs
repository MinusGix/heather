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

#[test]
fn a_branch_that_ends_a_block_updates_the_blocks_locals() {
    // The arms of a tail `if`/`match` are the block's last statements, so
    // they assign its `let mut` locals (docs/sequencing-surface-design.md
    // §19.1), through an arm's own tail too.
    for src in [
        "fn f(c: Bool) -> Nat { let mut x = 1; if c { x := 2; x } else { x } }",
        "fn f(o: O) -> Nat { let mut x = 1; match o { A => { x := 2; x }, B => 0 } }",
        "fn f(c: Bool) -> Nat { let mut x = 1; if c { let y = 3; if d { x := y; x } else { y } } else { x } }",
        "fn f(c: Bool) -> Nat { let y = { let mut x = 1; if c { x := 2; x } else { x } }; y }",
    ] {
        let parsed = format!("{:?}", parse_file(src).unwrap_or_else(|e| panic!("{src}: {}", e.msg)));
        for marker in ["\\0mut", "\\0assign", "\\0stmt", "\\0unit"] {
            assert!(!parsed.contains(marker), "{src} keeps {marker}");
        }
    }
    for src in [
        // The branch does not end the block that declared the local.
        "fn f(c: Bool) -> Nat { let mut x = 1; let y = if c { x := 2; x } else { x }; y }",
        // The arm's pattern binds the name: it is the pattern's there.
        "fn f(o: O) -> Nat { let mut x = 1; match o { A(x) => { x := 2; x }, B => x } }",
        // So does the equation's name.
        "fn f(o: O) -> Nat { let mut h = 1; match h: o { A => { h := 2; 0 }, B => 0 } }",
        // Shadowed by a plain `let` in the arm.
        "fn f(c: Bool) -> Nat { let mut x = 1; if c { let x = 5; x := 2; x } else { x } }",
    ] {
        let error = parse_file(src).unwrap_err();
        assert!(error.msg.contains("is not mutable"), "{src}: {}", error.msg);
    }
}

#[test]
fn a_mut_self_body_that_ends_in_a_branch_returns_its_receiver_per_arm() {
    let count = |src: &str, what: &str| {
        format!("{:?}", parse_file(src).unwrap_or_else(|e| panic!("{src}: {}", e.msg))).matches(what).count()
    };
    // An arm assigns the receiver: each arm ends in its own `Mutated`
    // (§19.2), beside the one in the result type.
    assert_eq!(count("fn C::f(mut self c: C, b: Bool) -> Nat { if b { c := g(c); 1 } else { 0 } }", "\"Mutated\""), 3);
    // So does a call on it, as a statement or bound.
    assert_eq!(count("fn C::f(mut self c: C, b: Bool) -> Nat { if b { c.tick(1); 1 } else { 0 } }", "\"Mutated\""), 3);
    assert_eq!(count("fn C::f(mut self c: C, b: Bool) -> Nat { if b { let a = c.tick(1); a } else { 0 } }", "\"Mutated\""), 3);
    // And through an arm's own tail: three ends.
    assert_eq!(
        count("fn C::f(mut self c: C, b: Bool) -> Nat { if b { if d { c.tick(1); 1 } else { 2 } } else { 0 } }", "\"Mutated\""),
        4
    );
    // No arm touches the receiver: one `Mutated` round the branch, so the
    // receiver after the call does not wait on which arm runs.
    assert_eq!(count("fn C::f(mut self c: C, b: Bool) -> Nat { c.tick(1); if b { 1 } else { 0 } }", "\"Mutated\""), 2);
    // An arm that rebinds the receiver's name does not return that name.
    assert_eq!(count("fn C::f(mut self c: C, b: Bool) -> Nat { if b { let c = 5; c } else { 0 } }", "\"Mutated\""), 2);
    // A branch with a written motive is a value.
    assert_eq!(
        count("fn C::f(mut self c: C, n: Nat) -> Nat { match n as λ z => Nat { Zero => 0, Succ(k) => k } }", "\"Mutated\""),
        2
    );
}

#[test]
fn a_mut_self_methods_own_call_at_its_end_is_the_whole_result() {
    let parsed = |src: &str| format!("{:?}", parse_file(src).unwrap_or_else(|e| panic!("{src}: {}", e.msg)));
    // The method's own call on the receiver, where it ends an arm: the
    // record the body returns, with no `Mutated` round it.
    let own = parsed("fn C::f(mut self c: C, n: Nat) -> Nat { match n { Zero => 0, Succ(k) => { c.tick(k); c.f(k) } } }");
    assert_eq!(own.matches("\\0mutated_whole").count(), 1, "{own}");
    assert_eq!(own.matches("\"Mutated\"").count(), 2, "{own}");
    // An arm that is the bare call.
    let bare = parsed("fn C::f(mut self c: C, n: Nat) -> Nat { match n { Zero => 0, Succ(k) => c.f(k) } }");
    assert_eq!(bare.matches("\\0mutated_whole").count(), 1, "{bare}");
    // Another method's call there is bound as before, its two parts read.
    let other = parsed("fn C::f(mut self c: C, n: Nat) -> Nat { match n { Zero => 0, Succ(k) => { c.tick(k); c.g(k) } } }");
    assert!(!other.contains("\\0mutated_whole"), "{other}");
    // So is the method's name called on another local.
    let elsewhere = parsed("fn C::f(mut self c: C, n: Nat) -> Nat { let mut d = c; d.f(n) }");
    assert!(!elsewhere.contains("\\0mutated_whole"), "{elsewhere}");
}

#[test]
fn a_field_path_of_a_mutable_local_is_a_place() {
    let parsed = |src: &str| format!("{:?}", parse_file(src).unwrap_or_else(|e| panic!("{src}: {}", e.msg)));
    // `x.f := e` assigns `x` the record with the field replaced, and a path
    // of two fields nests the update.
    let one = parsed("fn f(p: P) -> P { let mut q = p; q.left := 1; q }");
    assert_eq!(one.matches("RecordUpdate").count(), 1, "{one}");
    let two = parsed("fn f(p: P) -> P { let mut q = p; q.inner.left := 1; q }");
    assert_eq!(two.matches("RecordUpdate").count(), 2, "{two}");
    // A method called on a field of a mutable local is a candidate its
    // block claims; on a field of anything else it is an ordinary call.
    let call = parsed("fn f(p: P) -> P { let mut q = p; q.left.tick(1); q }");
    assert_eq!(call.matches("\\0mutated").count(), 1, "{call}");
    let fixed = parsed("fn f(p: P) -> Nat { let n = p.left.tick(1); n }");
    assert!(!fixed.contains("\\0mut"), "{fixed}");
    // In a `mut self` body's tail arm, a bare call on a field of the
    // receiver is bound first, and the arm returns the receiver.
    let arm = parsed("fn P::f(mut self p: P, b: Bool) -> Nat { match b { True => p.left.tick(1), False => 0 } }");
    // (The declared result and one per arm.)
    assert_eq!(arm.matches("\"Mutated\"").count(), 3, "{arm}");
    assert_eq!(arm.matches("#tail").count(), 2, "{arm}");
    // The method's own name called on a field is not the body's own call.
    let field = parsed("fn P::f(mut self p: P, n: Nat) -> Nat { match n { Zero => 0, Succ(k) => p.left.f(k) } }");
    assert!(!field.contains("\\0mutated_whole"), "{field}");
    // A path through an index is a place: `q.items[i] := e` stores through
    // the field's own `put` (§21).
    let index = parsed("fn f(p: P, i: u64) -> Nat { let mut q = p; q.items[i] := 1; 0 }");
    assert!(index.contains("\"put\""), "{index}");
    assert!(index.contains("RecordUpdate"), "{index}");
    // What is no place: a path through a call, and a place whose local is
    // not mutable.
    for src in ["fn f(p: P) -> Nat { let mut q = p; q.left.get() := 1; 0 }", "fn f(p: P) -> Nat { let mut q = p; q.left.get()[0] := 1; 0 }"] {
        let error = parse_file(src).expect_err(src);
        assert!(error.msg.contains("only a place is assigned"), "{src}: {}", error.msg);
    }
    let error = parse_file("fn f(p: P) -> Nat { p.left := 1; 0 }").expect_err("an immutable local's field");
    assert!(error.msg.contains("is not mutable"), "{}", error.msg);
}
