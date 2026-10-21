//! `Pos<A>` binder sugar (`issues/pos-binder-sugar.md`,
//! `docs/positivity-evidence-design.md` §6 B and §11): a parameter, a
//! function result or a record field written `Pos<A>` is the carrier `A`
//! beside a fact `0 < x`, found by `:= infer`'s proposition search.
//!
//! The sugar is a desugaring, but what fills its facts is a generated term,
//! so the axes of `docs/testing-generated-terms.md` are varied: a literal and
//! a **neutral** operand (`5`, `Succ(k)`, a product of parameters), a second
//! carrier (`Int`, which no rule mentions), a **checking** position (a fact
//! used where a `let` states the goal), and a **negative control** beside
//! each position.

use std::sync::OnceLock;

use heather_elab::{Elaborator, SemanticImage};

use crate::support;

const MODULES: &[(&str, &str)] = &[
    ("logic", include_str!("../../../lib/std/logic.hthr")),
    ("bool", include_str!("../../../lib/std/bool.hthr")),
    ("nat", include_str!("../../../lib/std/nat.hthr")),
    ("option", include_str!("../../../lib/std/option.hthr")),
    ("pair", include_str!("../../../lib/std/pair.hthr")),
    ("list", include_str!("../../../lib/std/list.hthr")),
    ("algebra", include_str!("../../../lib/std/algebra.hthr")),
    ("int", include_str!("../../../lib/std/int.hthr")),
];

static BASE: OnceLock<SemanticImage> = OnceLock::new();

fn base() -> Elaborator {
    BASE.get_or_init(|| support::semantic_test_base(MODULES).semantic_image()).elaborator()
}

const HEAD: &str = "import logic; import nat; import algebra; import int;
theorem uses(n: Pos<Nat>): 0 < n { n_pos }
";

fn ok(src: &str) {
    let src = format!("{HEAD}{src}");
    if let Err(err) = base().elab_module_source("client", &src) {
        panic!("expected success, got: {}", err.render(&src));
    }
}

fn bad(src: &str) -> String {
    let src = format!("{HEAD}{src}");
    match base().elab_module_source("client", &src) {
        Ok(()) => panic!("expected a rejection, but it elaborated"),
        Err(err) => err.render(&src),
    }
}

// -- parameters -------------------------------------------------------------

#[test]
fn a_parameter_is_its_carrier_and_its_fact_is_searched() {
    // Computation (a literal, a neutral `Succ`), a local, and a rule over
    // two locals; the caller passes a plain `Nat` every time.
    ok("theorem lit(): 0 < 5 { uses(5) }
theorem succ(k: Nat): 0 < Succ(k) { uses(Succ(k)) }
theorem local(k: Nat, h: 0 < k): 0 < k { uses(k) }
theorem product(a, b: Nat, pa: 0 < a, pb: 0 < b): 0 < a * b { uses(a * b) }
");
}

#[test]
fn the_fact_is_a_local_of_the_body_and_flows_to_callees() {
    // `n_pos` is in scope by name, and the search finds it for a callee's
    // own `Pos<Nat>` parameter, under a rule and in a checking position.
    ok("theorem square(n: Pos<Nat>): 0 < n * n { uses(n * n) }
theorem stated(n: Pos<Nat>): 0 < n * 2 { let h: (0 < n * 2) = uses(n * 2); h }
fn halve(n: Pos<Nat>) -> Nat { n.div(2) }
fn caller(k: Pos<Nat>) -> Nat { halve(k) + halve(k * k) }
");
}

#[test]
fn a_parameter_without_evidence_is_refused_at_the_call() {
    let e = bad("theorem zero(): 0 < 0 { uses(0) }\n");
    assert!(e.contains("no instance for `Lt(0, 0)`"), "{e}");
    let e = bad("theorem open(k: Nat): 0 < k { uses(k) }\n");
    assert!(e.contains("no instance for `Lt(0, k)`"), "{e}");
}

#[test]
fn the_fact_is_named_by_hand_and_takes_no_positional_slot() {
    // `n_pos := …` overrides the search; `1 <= k` is convertible to `0 < k`.
    // A run of `Pos` names adds one fact after each, and the positional
    // arity is the values' alone: `two(x, y, 7)`. `@` passes every slot.
    ok("theorem named(k: Nat, h: 1 <= k): 0 < k { uses(k, n_pos := h) }
theorem two(a, b: Pos<Nat>, c: Nat): 0 < a * b { Nat::mul_pos() }
theorem call(x, y: Nat, px: 0 < x, py: 0 < y): 0 < x * y { two(x, y, 7) }
theorem by_hand(k: Nat, h: 0 < k): 0 < k { @uses(k, h) }
theorem order(x, y: Nat, px: 0 < x, py: 0 < y): 0 < x * y { @two(x, px, y, py, 7) }
");
}

#[test]
fn a_second_carrier_uses_its_own_designations() {
    // `Int` has `<` and a numeral, and no rule: locals and the named
    // override reach it, and a zero is refused.
    ok("theorem usesi(x: Pos<Int>): 0 < x { x_pos }
theorem local(x: Int, h: 0 < x): 0 < x { usesi(x) }
theorem named(x: Int, h: OfNat(1) <= x): 0 < x { usesi(x, x_pos := h) }
");
    let e = bad("theorem usesi(x: Pos<Int>): 0 < x { x_pos }
theorem open(x: Int): 0 < x { usesi(x) }
");
    assert!(e.contains("no instance"), "{e}");
}

#[test]
fn pos_is_not_a_type_outside_a_binder() {
    let e = bad("fn apply(f: Pos<Nat> -> Nat) -> Nat { f(1) }\n");
    assert!(e.contains("`Pos<A>` is binder sugar, not a type"), "{e}");
    let e = bad("fn dflt(n: Pos<Nat> := 3) -> Nat { n }\n");
    assert!(e.contains("a `Pos<A>` parameter takes no default"), "{e}");
}

// -- results ----------------------------------------------------------------

#[test]
fn a_result_declares_its_fact_as_an_evidence_rule() {
    // `sq::pos` exists by name and is found by the search: at a literal, at
    // a neutral argument whose own positivity is a local, and nested under
    // a rule. A body with `let`s is restated whole.
    ok("fn sq(n: Pos<Nat>) -> Pos<Nat> { n * n }
fn seven() -> Pos<Nat> { 7 }
fn grow(n: Nat) -> Pos<Nat> { let m = n + 1; m * 2 }
theorem named(k: Nat, h: 0 < k): 0 < sq(k) { sq::pos(n := k) }
theorem lit(): 0 < sq(3) { uses(sq(3)) }
theorem neutral(k: Nat, h: 0 < k): 0 < sq(k) { uses(sq(k)) }
theorem nested(i: Nat): 0 < grow(i) * seven() { uses(grow(i) * seven()) }
theorem stated(i: Nat): 0 < grow(i) { let h: (0 < grow(i)) = uses(grow(i)); h }
");
}

#[test]
fn a_result_fact_rests_on_the_arguments_evidence() {
    // `sq::pos`'s premise is `sq`'s own `n_pos`, which the call `sq(k)`
    // already needs: with no evidence for `k`, the call is what is refused.
    let e = bad("fn sq(n: Pos<Nat>) -> Pos<Nat> { n * n }
theorem open(k: Nat): 0 < sq(k) { uses(sq(k)) }
");
    assert!(e.contains("no instance for `Lt(0, k)`"), "{e}");
}

#[test]
fn a_recursive_result_is_proved_by_hand() {
    // `on ?pos := …` proves `0 < fact(n)` itself, so it can recurse on
    // `fact::pos`; the caller's search uses it all the same.
    ok("fn fact(n: Nat) -> Pos<Nat> {
    match n { Zero => 1, Succ(k) => Succ(k) * fact(k) }
    on ?pos := match n { Zero => trivial, Succ(k) => @Nat::mul_pos(Succ(k), fact(k), trivial, @fact::pos(k)) };
}
theorem used(i: Nat): 0 < fact(i) * 2 { uses(fact(i) * 2) }
");
}

#[test]
fn a_result_the_search_cannot_prove_is_refused_with_the_way_out() {
    let e = bad("fn ident(n: Nat) -> Pos<Nat> { n }\n");
    assert!(e.contains("`positivity` could not prove `Lt(0, n)`"), "{e}");
    assert!(e.contains("`on ?pos := …;`"), "{e}");
    // A recursion restated is a case split the search cannot read.
    let e = bad("fn up(n: Nat) -> Pos<Nat> { match n { Zero => 1, Succ(k) => up(k) + 1 } }\n");
    assert!(e.contains("`on ?pos := …;`"), "{e}");
    // A proof by hand is checked like any other proof, at the statement,
    // and the search does not run.
    let e = bad("fn ident(n: Nat) -> Pos<Nat> { n
    on ?pos := trivial;
}\n");
    assert!(!e.contains("`positivity` could not prove"), "{e}");
}

#[test]
fn a_result_is_a_functions_alone() {
    let e = bad("theorem t(n: Nat): Pos<Nat> { n }\n");
    assert!(e.contains("`Pos<A>` as a result is a function's"), "{e}");
}

#[test]
fn a_member_result_declares_the_members_fact() {
    // `fn Nat::spread` declares `Nat::spread::pos`, owned by the function: by
    // name, through the receiver and the qualified call, under a rule, in a
    // checking position, and over a `Pos` receiver whose fact is a premise.
    ok("fn Nat::spread(self n: Nat) -> Pos<Nat> { n + n + 1 }
fn Nat::sq(self n: Pos<Nat>) -> Pos<Nat> { n * n }
theorem named(k: Nat): 0 < k.spread() { Nat::spread::pos(n := k) }
theorem receiver(k: Nat): 0 < k.spread() { uses(k.spread()) }
theorem nested(k: Nat): 0 < Nat::spread(k) * 2 { uses(Nat::spread(k) * 2) }
theorem stated(k: Nat): 0 < k.spread() { let h: (0 < k.spread()) = uses(k.spread()); h }
theorem premise(k: Nat, h: 0 < k): 0 < k.sq() { uses(k.sq()) }
");
    let e = bad("fn Nat::sq(self n: Pos<Nat>) -> Pos<Nat> { n * n }
theorem open(k: Nat): 0 < k.sq() { uses(k.sq()) }
");
    assert!(e.contains("no instance for `Lt(0, k)`"), "{e}");
    // The restated body is searched as a plain function's is.
    let e = bad("fn Nat::ident(self n: Nat) -> Pos<Nat> { n }\n");
    assert!(e.contains("`positivity` could not prove `Lt(0, n)`"), "{e}");
}

#[test]
fn a_member_result_fact_reaches_an_importer() {
    let mut e = base();
    let a = format!("{HEAD}fn Nat::spread(self n: Nat) -> Pos<Nat> {{ n + n + 1 }}\n");
    if let Err(err) = e.elab_module_source("a", &a) {
        panic!("module a: {}", err.render(&a));
    }
    let b = "import nat; import a;
theorem uses(n: Pos<Nat>): 0 < n { n_pos }
theorem used(k: Nat): 0 < k.spread() * k.spread() { uses(k.spread() * k.spread()) }
theorem named(k: Nat): 0 < k.spread() { Nat::spread::pos(n := k) }
theorem qualified(k: Nat): 0 < k.spread() { a::Nat::spread::pos(n := k) }
";
    if let Err(err) = e.elab_module_source("b", b) {
        panic!("module b: {}", err.render(b));
    }
}

#[test]
fn a_result_fact_reaches_an_importer() {
    // The rule is an ordinary `evidence theorem`, so it travels as a module
    // event: the importer's search finds `sq::pos` with no name written.
    let mut e = base();
    let a = format!("{HEAD}fn sq(n: Pos<Nat>) -> Pos<Nat> {{ n * n }}\n");
    if let Err(err) = e.elab_module_source("a", &a) {
        panic!("module a: {}", err.render(&a));
    }
    let b = "import nat; import a;
theorem uses(n: Pos<Nat>): 0 < n { n_pos }
theorem used(k: Nat, h: 0 < k): 0 < sq(k) * sq(k) { uses(sq(k) * sq(k)) }
";
    if let Err(err) = e.elab_module_source("b", b) {
        panic!("module b: {}", err.render(b));
    }
}

// -- record fields ----------------------------------------------------------

const FRAC: &str = "record Frac { num: Nat, den: Pos<Nat> }\n";

#[test]
fn a_field_is_its_carrier_and_its_fact_is_searched_at_construction() {
    ok(&format!("{FRAC}fn lit() -> Frac {{ Frac(1, 2) }}
fn neutral(k: Nat) -> Frac {{ Frac(1, Succ(k)) }}
fn local(k: Nat, h: 0 < k) -> Frac {{ Frac(1, k) }}
fn product(f, g: Frac) -> Frac {{ Frac(f.num * g.num, f.den * g.den) }}
fn named(k: Nat, h: 1 <= k) -> Frac {{ Frac(1, k, den_pos := h) }}
fn written(k: Nat, h: 0 < k) -> Frac {{ Frac(1, k, h) }}
"));
}

#[test]
fn a_field_default_cites_a_rule_its_record_module_cannot_see() {
    // The `den_pos` default runs in `a`'s scope, which does not import `b`,
    // but `b`'s rule about its own `two` is `b`'s to use when `b` builds a
    // `Frac`.
    let mut e = base();
    let a = format!("{HEAD}{FRAC}");
    if let Err(err) = e.elab_module_source("a", &a) {
        panic!("module a: {}", err.render(&a));
    }
    let b = "import nat; import a;
fn two(k: Nat) -> Nat { k + k + 2 }
evidence theorem two_pos({k: Nat}): 0 < two(k) { Nat::add_pos_r(a := k + k, b := 2) }
fn half(k: Nat) -> Frac { Frac(1, two(k)) }
";
    if let Err(err) = e.elab_module_source("b", b) {
        panic!("module b: {}", err.render(b));
    }
}

#[test]
fn a_field_declares_a_rule_about_its_projection() {
    // `0 < f.den` is not a local, and `Frac::den_positive` is what reads it,
    // alone, under a rule and in a checking position.
    ok(&format!("{FRAC}theorem den(f: Frac): 0 < f.den {{ uses(f.den) }}
theorem product(f, g: Frac): 0 < f.den * g.den {{ uses(f.den * g.den) }}
theorem stated(f: Frac): 0 < f.den {{ let h: (0 < f.den) = Frac::den_positive(); h }}
"));
}

#[test]
fn a_field_without_evidence_is_refused_at_the_construction() {
    let e = bad(&format!("{FRAC}fn zero() -> Frac {{ Frac(1, 0) }}\n"));
    assert!(e.contains("no evidence for `Lt(0, 0)`"), "{e}");
    let e = bad(&format!("{FRAC}fn open(k: Nat) -> Frac {{ Frac(1, k) }}\n"));
    assert!(e.contains("no evidence for"), "{e}");
}

#[test]
fn a_field_on_a_type_parameterised_record_has_a_generic_rule() {
    // `Box::n_positive<A>` is found at a closed instance and at an **open**
    // one (`Box<A>` inside a generic function), in a checking position.
    ok("record Box<A> { a: A, n: Pos<Nat> }
fn mk<A>(x: A) -> Box<A> { Box(x, 4) }
fn local<A>(x: A, k: Nat, h: 0 < k) -> Box<A> { Box(x, k) }
theorem closed(b: Box<Nat>): 0 < b.n { uses(b.n) }
theorem open<A>(b: Box<A>): 0 < b.n * 2 { uses(b.n * 2) }
theorem stated<A>(b: Box<A>): 0 < b.n { let h: (0 < b.n) = Box::n_positive(); h }
");
    let e = bad("record Box<A> { a: A, n: Pos<Nat> }
fn zero<A>(x: A) -> Box<A> { Box(x, 0) }
");
    assert!(e.contains("no evidence for `Lt(0, 0)`"), "{e}");
}

#[test]
fn a_field_on_a_value_parameterised_record_has_a_rule_over_its_parameters() {
    // `{k}, {r: Window(k)}`: `k` is found by unifying the record's type, at a
    // literal, at a neutral `j + 1`, and under a rule.
    ok("record Window(k: Nat) { len: Pos<Nat>, fits: len <= k }
fn mk(j: Nat, h: 1 <= j + 1) -> Window(j + 1) { Window(1, h) }
theorem lit(w: Window(3)): 0 < w.len { uses(w.len) }
theorem neutral(j: Nat, w: Window(j + 1)): 0 < w.len * 2 { uses(w.len * 2) }
theorem stated(j: Nat, w: Window(j)): 0 < w.len { let h: (0 < w.len) = Window::len_positive(); h }
");
    // Both kinds of parameter at once, the type one open.
    ok("record Slot<A>(k: Nat) { a: A, len: Pos<Nat>, fits: len <= k }
theorem closed(s: Slot<Nat>(3)): 0 < s.len { uses(s.len) }
theorem open<A>(j: Nat, s: Slot<A>(j)): 0 < s.len * 2 { uses(s.len * 2) }
");
    let e = bad("record Window(k: Nat) { len: Pos<Nat>, fits: len <= k }
fn zero(j: Nat, h: 0 <= j) -> Window(j) { Window(0, h) }
");
    assert!(e.contains("no evidence for `Lt(0, 0)`"), "{e}");
}

#[test]
fn a_parameter_no_field_mentions_is_refused() {
    // `Tag(3)` and `Tag(5)` would be one type, with nothing to read `k` off.
    let e = bad("record Tag(k: Nat) { n: Pos<Nat> }\n");
    assert!(e.contains("`k` appears in none"), "{e}");
    let e = bad("record Tag<A> { n: Pos<Nat> }\n");
    assert!(e.contains("`A` appears in none"), "{e}");
    let e = bad("record Frac { den: Pos<Nat> := 1 }\n");
    assert!(e.contains("a `Pos<A>` field takes no default"), "{e}");
}

// -- constructor fields -----------------------------------------------------

const SHAPE: &str = "inductive Shape { Square(side: Pos<Nat>), Dot }\n";

#[test]
fn a_constructor_field_is_its_carrier_and_its_fact_is_searched() {
    // A literal, a neutral `Succ`, a local, a rule, the fact named and passed
    // positionally, and a construction nothing checks (`let s = …;`).
    ok(&format!("{SHAPE}fn lit() -> Shape {{ Square(2) }}
fn neutral(k: Nat) -> Shape {{ Square(Succ(k)) }}
fn local(k: Nat, h: 0 < k) -> Shape {{ Square(k) }}
fn product(a, b: Pos<Nat>) -> Shape {{ Square(a * b) }}
fn named(k: Nat, h: 1 <= k) -> Shape {{ Square(k, side_pos := h) }}
fn written(k: Nat, h: 0 < k) -> Shape {{ Square(k, h) }}
fn unchecked() -> Nat {{ let s = Square(3); match s {{ Square(n, _) => n, Dot => 0 }} }}
"));
}

#[test]
fn a_constructor_field_without_evidence_is_refused() {
    let e = bad(&format!("{SHAPE}fn zero() -> Shape {{ Square(0) }}\n"));
    assert!(e.contains("no evidence for `Lt(0, 0)`"), "{e}");
    let e = bad(&format!("{SHAPE}fn open(k: Nat) -> Shape {{ Square(k) }}\n"));
    assert!(e.contains("no evidence for"), "{e}");
}

#[test]
fn a_matched_constructor_binds_its_fact_for_the_search() {
    // The pattern binds every field; the fact, even as `_`, is a local the
    // search reads, so a callee's `Pos` parameter is satisfied. Without the
    // match there is no fact, and the call is refused.
    ok(&format!("{SHAPE}fn half(n: Pos<Nat>) -> Nat {{ n.div(2) }}
fn area(s: Shape) -> Nat {{ match s {{ Square(n, _) => half(n * n), Dot => 0 }} }}
"));
    let e = bad(&format!("{SHAPE}fn half(n: Pos<Nat>) -> Nat {{ n.div(2) }}
fn area(s: Shape, k: Nat) -> Nat {{ match s {{ Square(n, _) => half(k), Dot => 0 }} }}
"));
    assert!(e.contains("no instance for `Lt(0, k)`"), "{e}");
}

#[test]
fn a_constructor_field_works_in_a_recursive_and_a_parameterised_inductive() {
    // A recursive constructor (the `Wf` lowering), and a type parameter at a
    // closed and an open instance, in a checking position.
    ok("inductive Runs { End, Run(len: Pos<Nat>, rest: Runs) }
fn two() -> Runs { Run(2, Run(1, End)) }
fn total(r: Runs) -> Nat { match r { End => 0, Run(n, _, rest) => n + total(rest) } }
inductive Tagged<A> { Item(a: A, weight: Pos<Nat>), Blank }
fn closed() -> Tagged<Nat> { Item(7, 3) }
fn open<A>(x: A, k: Nat, h: 0 < k) -> Tagged<A> { Item(x, k * 2) }
fn every<A>(x: A, k: Nat, h: 0 < k) -> Nat { let t = Item(x, k, h); 0 }
");
    // With a type parameter and the fact left out, nothing fixes the
    // instance a default is filled at.
    let e = bad("inductive Tagged<A> { Item(a: A, weight: Pos<Nat>), Blank }
fn unchecked<A>(x: A) -> Nat { let t = Item(x, 3); 0 }
");
    assert!(e.contains("nothing here fixes `Tagged`'s parameters"), "{e}");
}

#[test]
fn a_constructor_field_is_refused_where_it_has_no_meaning() {
    let e = bad("inductive Q { Mk(Pos<Nat>) }\n");
    assert!(e.contains("a `Pos<A>` field needs a name"), "{e}");
    let e = bad("inductive Q { Mk(n: Pos<Nat> := 1) }\n");
    assert!(e.contains("a `Pos<A>` field takes no default"), "{e}");
    let e = bad("inductive I : (n: Nat) -> Type { Z(m: Pos<Nat>) : I(0) }\n");
    assert!(e.contains("indexed family `I`"), "{e}");
    // An ordinary default stays a record's.
    let e = bad("inductive Q { Mk(n: Nat := 1) }\n");
    assert!(e.contains("only a record's fields take a default"), "{e}");
}
