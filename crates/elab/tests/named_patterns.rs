//! Named and renamed fields in record and constructor patterns
//! (`issues/named-patterns-by-field.md`).

use heather_elab::Elaborator;

fn ok(src: &str) {
    let mut e = Elaborator::with_prelude().expect("prelude");
    if let Err(err) = e.elab_source(src) {
        panic!("expected success, got: {}", err.render(src));
    }
}

fn bad(src: &str) -> String {
    let mut e = Elaborator::with_prelude().expect("prelude");
    match e.elab_source(src) {
        Ok(()) => panic!("expected a rejection, but it elaborated"),
        Err(err) => err.render(src),
    }
}

#[test]
fn a_dependent_record_opens_under_renamed_fields_in_declaration_order() {
    ok("
record Exists<A>(P: A -> Type) { witness: A, proof: P(witness) }

fn get_witness<A>(P: A -> Type, h: Exists<A>(P)) -> A {
    let { witness := x } = h;
    x
}

theorem get_proof<A>(P: A -> Type, h: Exists<A>(P)): P(get_witness(P, h)) {
    // Written backwards on purpose. `proof` depends on `witness`, so this
    // only works when the elaborator restores declaration order.
    let { proof := hx, witness := x } = h;
    hx
}
");
}

#[test]
fn record_shorthand_renaming_partial_patterns_and_wildcards_coexist() {
    ok("
record Pair { fst: Nat, snd: Nat }

fn old(p: Pair) -> Nat { let { fst } = p; fst }
fn renamed(p: Pair) -> Nat { let { fst := x } = p; x }
fn ignored(p: Pair) -> Nat { let { fst := _, snd := y } = p; y }

theorem shorthand_is_renaming(p: Pair): old(p) = renamed(p) { refl }
");
}

#[test]
fn constructor_fields_are_order_free_partial_and_nested() {
    ok("
inductive List { Nil, Cons(head: Nat, tail: List) }

fn first_or(xs: List, d: Nat) -> Nat {
    match xs {
        Nil => d,
        Cons(tail := _, head := h) => h,
    }
}

fn second_or(xs: List, d: Nat) -> Nat {
    match xs {
        Cons(tail := Cons(head := x), head := _) => x,
        _ => d,
    }
}

theorem first_computes(): first_or(Cons(3, Nil), 9) = 3 { refl }
theorem second_computes(): second_or(Cons(3, Cons(4, Nil)), 9) = 4 { refl }
theorem missing_inner_tail_is_ignored(): second_or(Cons(3, Cons(4, Cons(5, Nil))), 9) = 4 { refl }
theorem nested_failure_reaches_default(): second_or(Cons(3, Nil), 9) = 9 { refl }
");
}

#[test]
fn named_constructor_patterns_compose_with_if_let() {
    ok("
inductive Option { None, Some(value: Nat) }

fn unwrap(o: Option, d: Nat) -> Nat {
    if let Some(value := x) = o { x } else { d }
}

theorem yes(): unwrap(Some(7), 2) = 7 { refl }
theorem no(): unwrap(None, 2) = 2 { refl }
");
}

#[test]
fn unknown_and_duplicate_constructor_fields_are_targeted() {
    let unknown = bad("
inductive List { Nil, Cons(head: Nat, tail: List) }
fn f(xs: List) -> Nat {
    match xs { Nil => 0, Cons(nope := x) => x }
}
");
    assert!(unknown.contains("`Cons` has no field `nope`"), "{unknown}");

    let duplicate = bad("
inductive List { Nil, Cons(head: Nat, tail: List) }
fn f(xs: List) -> Nat {
    match xs { Nil => 0, Cons(head := x, head := y) => x }
}
");
    assert!(duplicate.contains("field `head` appears twice"), "{duplicate}");
}

#[test]
fn positional_only_and_mixed_constructor_patterns_are_refused_by_name() {
    let positional = bad("
inductive Box { Wrap(Nat) }
fn f(b: Box) -> Nat { match b { Wrap(value := x) => x } }
");
    assert!(positional.contains("positional-only pattern fields"), "{positional}");

    let mixed = bad("
inductive List { Nil, Cons(head: Nat, tail: List) }
fn f(xs: List) -> Nat {
    match xs { Nil => 0, Cons(x, tail := t) => x }
}
");
    assert!(mixed.contains("cannot mix positional binders"), "{mixed}");
}

#[test]
fn record_pattern_diagnostics_name_the_written_field_and_refutable_boundary() {
    let unknown = bad("
record Pair { fst: Nat, snd: Nat }
fn f(p: Pair) -> Nat { let { nope := x } = p; x }
");
    assert!(unknown.contains("`Pair` has no field `nope`"), "{unknown}");

    let duplicate = bad("
record Pair { fst: Nat, snd: Nat }
fn f(p: Pair) -> Nat { let { fst := x, fst := y } = p; x }
");
    assert!(duplicate.contains("field `fst` appears twice"), "{duplicate}");

    let refutable = bad("
inductive Option { None, Some(value: Nat) }
record Holder { item: Option }
fn f(h: Holder) -> Nat { let { item := Some(value := x) } = h; x }
");
    assert!(refutable.contains("record `let` field is irrefutable"), "{refutable}");
    assert!(refutable.contains("`match` or `if let`"), "{refutable}");
}
