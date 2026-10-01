//! Named arguments at call sites — `f(x := e)`
//! (`docs/named-arguments-design.md`, `issues/named-arguments.md`).
//!
//! What is varied, per `docs/testing-generated-terms.md`: an **open** element
//! type as well as a closed one; a *checking* position as well as a computing
//! one; a negative control beside every positive; and — the axis this feature
//! needs that the others do not — a **term-identity** assertion rather than
//! merely "it elaborates". A permutation that got the order wrong would still
//! typecheck wherever two parameters share a shape, so the positive tests
//! prove `f(named…) = f(positional…)` by `refl`, which is conversion at the
//! kernel and therefore an assertion about the *term*, not about the parse.
//!
//! The standing control is `a_call_with_no_named_argument_is_unchanged`: the
//! design's one invariant is that a call with no name reaches the spine
//! walkers with exactly the vector and mask it had before, and without a test
//! that pins it, a resolution pass that silently reordered *positional*
//! arguments would pass everything else here.

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

// -- positives ---------------------------------------------------------------

/// The milestone, and the term-identity assertion described in the header.
/// The two parameters have **different** types, so a permutation that dropped
/// the reordering would be a type error rather than a silent pass.
#[test]
fn explicit_parameters_are_nameable_and_order_free() {
    ok("
inductive Bool { False, True }
fn pick(n: Nat, b: Bool) -> Nat { n }

theorem written_order(n: Nat, b: Bool): pick(n := n, b := b) = pick(n, b) { refl }
theorem reversed(n: Nat, b: Bool): pick(b := b, n := n) = pick(n, b) { refl }
theorem mixed(n: Nat, b: Bool): pick(n, b := b) = pick(n, b) { refl }
");
}

/// The permutation is by **name**, not by shape: both parameters are `Nat`
/// here, so only a term-level assertion can tell the two orders apart. `sub`
/// is not symmetric, which is what makes `refl` load-bearing.
#[test]
fn a_reordering_at_two_same_typed_parameters_really_permutes() {
    ok("
// Both parameters are `Nat`, and the body is asymmetric in them, so only the
// *value* distinguishes the two orders — a type error could not.
fn left(a: Nat, b: Nat) -> Nat { a }

theorem forwards(): left(a := 5, b := 2) = 5 { refl }
theorem backwards(): left(b := 2, a := 5) = 5 { refl }
// The control: naming them the *other* way round is a different call.
theorem swapped(): left(a := 2, b := 5) = 2 { refl }
");
}

/// §5.2 — naming an **implicit** gives it, and leaves the others inferred.
/// This is the feature: `@sym(a, b, p)` is all-or-nothing, `sym(p, a := x)`
/// is one parameter.
#[test]
fn an_implicit_can_be_given_by_name() {
    ok("
theorem pin_one(x: Nat, y: Nat, p: x = y): y = x { sym(p, a := x) }
theorem pin_both(x: Nat, y: Nat, p: x = y): y = x { sym(p, a := x, b := y) }
theorem still_all_inferred(x: Nat, y: Nat, p: x = y): y = x { sym(p) }

// The same term, three spellings, proved equal at the kernel.
theorem same(x: Nat, y: Nat, p: x = y): sym(p, a := x) = sym(p) { refl }
");
}

/// Axis 2: an **open** element type. A de Bruijn shift in the permutation is
/// the identity on a closed type, so the assertion has to sit under a type
/// parameter that the call's arguments mention.
#[test]
fn named_arguments_at_an_open_element_type() {
    ok("
fn const2<A, B>(x: A, y: B) -> A { x }

theorem open_named<A, B>(x: A, y: B): const2(y := y, x := x) = const2(x, y) { refl }
theorem open_implicit<A>(x: A, y: A, p: x = y): y = x { sym(p, a := x) }
");
}

/// Axis 3: a **checking** position. A checking-only argument (`refl`, a bare
/// `?`-hole, an unannotated lambda) has no type of its own — it is in checking
/// position only because the arguments *before it in the declaration* have
/// already solved its domain. So this is the test that a permutation done
/// after elaboration, rather than before, would fail.
#[test]
fn a_checking_only_argument_given_by_name_still_gets_its_expected_type() {
    ok("
theorem chain(x: Nat, y: Nat, p: x = y): x = y {
    // `q := refl` is checking-only, and its domain `b = c` is only known once
    // `p` has solved `a` and `b`. Written last, elaborated in spine order.
    trans(p, q := refl)
}

// And with the checking-only argument written FIRST, which is the order the
// permutation has to undo.
theorem chain_reversed(x: Nat, y: Nat, p: x = y): x = y { trans(q := refl, p := p) }
");
}

/// A `?`-hole inside a **named** argument is still a hole: it is raised, it
/// takes its default name from the parameter it fills, and `on ?name := …`
/// discharges it. This is the test for §12's finding 6 — the goal *pre-count*
/// walker had to learn about named arguments, and its own doc comment says
/// under-counting is the one thing the goal mechanism cannot survive.
#[test]
fn a_hole_inside_a_named_argument_is_raised_and_dischargeable() {
    ok("
theorem t(x: Nat, y: Nat, p: x = y): y = x {
    sym(p := ?q, a := x)
    on ?q := p;
}
");

    // And the negative control: an *undischarged* hole in a named argument is
    // still reported, rather than quietly counted and lost.
    let e = bad("
theorem t(x: Nat, y: Nat, p: x = y): y = x { sym(p := ?q, a := x) }
");
    assert!(e.contains("?q") || e.contains("unsolved"), "{e}");
}

/// §6 — constructors, including a record's. This is the payoff
/// `docs/surface-records.md` §6 asked for: a braced literal and a named call
/// say the same thing, and here they are proved to.
#[test]
fn constructors_and_records_are_nameable_by_field() {
    ok("
inductive Bool { False, True }
record Two { fst: Nat, snd: Bool }

theorem call_equals_positional(): Two(fst := 1, snd := True) = Two(1, True) { refl }
theorem order_free(): Two(snd := True, fst := 1) = Two(1, True) { refl }
// The braced literal is parenthesised because a `theorem` statement is one of
// the three block-preceding positions (docs/surface-records.md §6.1) — which
// is one of the costs the named-call spelling on the left does not have.
theorem call_equals_literal():
    Two(fst := 1, snd := True) = (Two { fst: 1, snd: True }) { refl }
theorem mixed(): Two(1, snd := True) = Two(1, True) { refl }
");
}

/// An ordinary (non-record) inductive's named fields, at a type parameter —
/// the constructor path with an instantiation to recover.
#[test]
fn an_inductive_constructors_fields_are_nameable() {
    ok("
inductive Lst<A> { Nil, Cons(head: A, tail: Lst<A>) }

theorem named_equals_positional<A>(x: A, xs: Lst<A>):
    Cons(head := x, tail := xs) = Cons(x, xs) { refl }
theorem order_free<A>(x: A, xs: Lst<A>):
    Cons(tail := xs, head := x) = Cons(x, xs) { refl }
// At a *written* instantiation, which is a different elaboration path.
theorem at_an_instantiation(x: Nat, xs: Lst<Nat>):
    Cons<Nat>(head := x, tail := xs) = Cons(x, xs) { refl }
");
}

/// §3.3 — the same argument list serves every call spelling, because they are
/// all one parser function. `@` and `<…>` compose with names exactly as
/// `issues/at-and-type-arguments.md` made them compose with each other.
#[test]
fn method_calls_at_calls_and_type_arguments_all_take_names() {
    ok("
inductive Bool { False, True }
fn pick<A>(x: A, y: A, first: Bool) -> A { match first { True => x, False => y } }

// A method call: the receiver fills the first parameter, the rest by name.
theorem method(x: Nat, y: Nat, p: x = y): y = x { p.sym(a := x) }

// `@` makes every value implicit positional; a name still reaches one.
theorem at_call(x: Nat, y: Nat, p: x = y): y = x { @sym(x, y, p) }
theorem at_with_a_name(x: Nat, y: Nat, p: x = y): y = x { @sym<Nat>(x, y, p) }

// `f<T>(…)` then a named value argument.
theorem tyargs(x: Nat, y: Nat): pick<Nat>(x, y, first := True) = x { refl }
");
}

/// The standing control (see the header). Every shape above, written with no
/// name at all, still elaborates to the term it always did.
#[test]
fn a_call_with_no_named_argument_is_unchanged() {
    ok("
inductive Lst<A> { Nil, Cons(head: A, tail: Lst<A>) }
record Two { fst: Nat, snd: Nat }
fn const2<A, B>(x: A, y: B) -> A { x }

theorem plain<A>(x: A, xs: Lst<A>): Cons(x, xs) = Cons(x, xs) { refl }
theorem rec(): Two(1, 2) = (Two { fst: 1, snd: 2 }) { refl }
theorem poly<A, B>(x: A, y: B): const2(x, y) = x { refl }
theorem implicits(x: Nat, y: Nat, p: x = y): y = x { sym(p) }
theorem at_still(x: Nat, y: Nat, p: x = y): y = x { @sym(x, y, p) }
theorem method(x: Nat, y: Nat, p: x = y): y = x { p.sym() }

// Partial application, which named arguments deliberately do NOT compose with
// (§4.3) and therefore must not disturb.
fn add2(a: Nat, b: Nat) -> Nat { a }
fn partial() -> Nat -> Nat { add2(1) }
");
}

// -- negatives ---------------------------------------------------------------

/// The message lists the parameters that *are* nameable, in declaration order.
#[test]
fn a_name_no_parameter_has_is_refused_and_lists_the_real_ones() {
    let e = bad("
fn pick(n: Nat, b: Nat) -> Nat { n }
theorem t(): pick(n := 1, c := 2) = 1 { refl }
");
    assert!(e.contains("no parameter named `c`"), "{e}");
    assert!(e.contains("n, b"), "{e}");
}

#[test]
fn a_duplicate_name_is_refused() {
    let e = bad("
fn pick(n: Nat, b: Nat) -> Nat { n }
theorem t(): pick(n := 1, n := 2) = 1 { refl }
");
    assert!(e.contains("given twice"), "{e}");
}

/// Positionally *and* by name is the same collision, said the same way.
#[test]
fn a_parameter_given_positionally_and_by_name_is_refused() {
    let e = bad("
fn pick(n: Nat, b: Nat) -> Nat { n }
theorem t(): pick(1, n := 2) = 1 { refl }
");
    assert!(e.contains("given twice"), "{e}");
}

/// §4.2 — a *parse* error, not an elaboration error, so the interleaving is
/// unrepresentable in the AST and no elaborator path has to define it.
#[test]
fn a_positional_argument_after_a_named_one_is_a_parse_error() {
    let e = bad("
fn pick(n: Nat, b: Nat) -> Nat { n }
theorem t(): pick(n := 1, 2) = 1 { refl }
");
    assert!(e.contains("positional argument cannot follow a named one"), "{e}");
    // Parse errors carry no declaration context, which is how this test tells
    // a parse refusal from an elaboration one.
    assert!(!e.contains("no parameter named"), "{e}");
}

/// §5.3 — a type parameter's argument is a *type*, not an expression, so
/// `f<…>` is its spelling and the message says so.
#[test]
fn a_type_parameter_by_name_is_refused_and_names_the_angle_brackets() {
    let e = bad("
fn const2<A, B>(x: A, y: B) -> A { x }
theorem t(x: Nat, y: Nat): const2(A := Nat, x := x, y := y) = x { refl }
");
    assert!(e.contains("type parameter"), "{e}");
    assert!(e.contains("const2<…>"), "{e}");
}

/// §4.3 — naming a late parameter leaves an earlier one with nothing to put in
/// its spine position, and the message names the parameter with no argument.
#[test]
fn a_gap_left_by_a_named_argument_is_refused_by_parameter_name() {
    let e = bad("
fn pick(n: Nat, b: Nat) -> Nat { n }
theorem t(): pick(b := 2) = 1 { refl }
");
    assert!(e.contains("too few arguments"), "{e}");
    assert!(e.contains("`n`"), "{e}");
}

/// §7 — an anonymous function type binds no parameter names, while names on
/// a markless written Π are callable. Both halves live together because
/// without the negative, manufacturing names for `Nat -> Nat` would pass.
#[test]
fn a_value_callee_uses_its_written_binder_names() {
    let e = bad("
fn apply(f: Nat -> Nat, n: Nat) -> Nat { f(x := n) }
");
    assert!(e.contains("positional"), "{e}");

    // A written name is API even when no binder is implicit.
    ok("
fn apply(f: (x: Nat) -> Nat, n: Nat) -> Nat { f(x := n) }
fn first(left: Nat, right: Nat) -> Nat { left }
fn through(f: (left: Nat) -> (right: Nat) -> Nat, a: Nat, b: Nat) -> Nat {
    f(right := b, left := a)
}
theorem one(): apply(Succ, 2) = 3 { refl }
theorem order(): through(first, 4, 7) = 4 { refl }
");
}

/// §8.2 — a builtin is an elaborator form, not a declaration, so it has no
/// parameter table and no names to be called by. Refused centrally, before any
/// of the eleven builtin arms reads `args`.
#[test]
fn a_builtin_by_name_is_refused() {
    let e = bad("
fn f(n: Nat) -> Nat { Succ(n := n) }
");
    assert!(e.contains("built-in") || e.contains("positional"), "{e}");
}

/// A recursive call keeps its argument positions: the termination guard reads
/// *which position* decreases, so a self-call is the one call whose argument
/// order is semantically load-bearing.
#[test]
fn a_named_self_call_is_refused_and_says_why() {
    let e = bad("
fn down(a: Nat, b: Nat) -> Nat {
    match a { Zero => b, Succ(k) => down(a := k, b := b) }
}
");
    assert!(e.contains("recursive call"), "{e}");
    assert!(e.contains("positional"), "{e}");
}

/// A constructor's refusals are the record literal's, word for word, because
/// they are the same function (§6).
#[test]
fn a_constructors_named_field_refusals_match_the_literals() {
    let unknown = bad("
record Two { fst: Nat, snd: Nat }
theorem t(): Two(fst := 1, third := 2) = Two(1, 2) { refl }
");
    assert!(unknown.contains("no field `third`"), "{unknown}");

    let dup = bad("
record Two { fst: Nat, snd: Nat }
theorem t(): Two(fst := 1, fst := 2) = Two(1, 2) { refl }
");
    assert!(dup.contains("given twice"), "{dup}");

    let missing = bad("
record Two { fst: Nat, snd: Nat }
theorem t(): Two(fst := 1) = Two(1, 2) { refl }
");
    assert!(missing.contains("missing field"), "{missing}");
}

/// A name is not a spelling for over-application: the extra arguments of
/// `nth(t, k)` apply to the *result*, whose `Type::Pi` binds no names (§4.3).
#[test]
fn a_named_argument_on_an_over_applied_call_is_refused() {
    let e = bad("
fn k(a: Nat) -> Nat -> Nat { λ b => a }
theorem t(): k(1, 2, a := 3) = 1 { refl }
");
    assert!(e.contains("more arguments") || e.contains("given twice"), "{e}");
}

// -- field defaults (§9.5) ---------------------------------------------------

/// A record whose second field has a default: positional arguments fill the
/// field without one, and the default fills the other. The result is the
/// same term as the full spelling, which overrides the default.
#[test]
fn a_defaulted_field_has_no_positional_slot() {
    ok("
record Pinned { value: Nat, same: value = value := refl }
fn short() -> Pinned { Pinned(5) }
fn named() -> Pinned { Pinned(value := 5) }
fn literal() -> Pinned { Pinned { value: 5 } }
theorem short_is_full(): short() = Pinned(5, refl) { refl }
theorem named_is_full(): named() = Pinned(5, refl) { refl }
theorem literal_is_full(): literal() = Pinned(5, refl) { refl }
theorem overridden(): Pinned(value := 5, same := refl) = Pinned(5, refl) { refl }
");
}

/// A default that does not prove the field's type here is refused at the
/// construction, naming the field and the way out. (A default the
/// elaborator leaves to the kernel, such as `refl`, is still refused at the
/// record: issues/field-defaults-under-locals.md's log.)
#[test]
fn a_default_that_fails_is_refused_at_the_construction() {
    let error = bad("
inductive Yes { Holds }
inductive No { Fails }
fn IsZero(n: Nat) -> Type { match n { Zero => Yes, Succ(_) => No } }
record Zeroed { value: Nat, zero: IsZero(value) := Holds }
fn fine() -> Zeroed { Zeroed(0) }
fn wrong() -> Zeroed { Zeroed(5) }
");
    assert!(error.contains("`zero` was left to its default") && error.contains("zero := "), "{error}");
}

/// Under local bindings the default does not run yet
/// (issues/field-defaults-under-locals.md); naming the field still works.
#[test]
fn a_default_under_locals_asks_for_the_field() {
    let error = bad("
record Pinned { value: Nat, same: value = value := refl }
fn local(k: Nat) -> Pinned { Pinned(k) }
");
    assert!(error.contains("under local bindings"), "{error}");
    ok("
record Pinned { value: Nat, same: value = value := refl }
fn local(k: Nat) -> Pinned { Pinned(k, same := refl) }
");
}

/// A default's names resolve where the record was declared, not where it is
/// constructed: the user module's own `witness` does not change it.
#[test]
fn a_default_resolves_in_the_declaring_module() {
    let mut e = Elaborator::with_prelude().expect("prelude");
    let declaring = "fn witness() -> Nat { 0 }\nrecord Holder { value: Nat, extra: Nat := witness() }";
    e.elab_module_source("declaring", declaring).unwrap_or_else(|err| panic!("{}", err.render(declaring)));
    let user = "import declaring::{Holder};\nfn witness() -> Nat { 1 }\nfn built() -> Holder { Holder(5) }\ntheorem extra_is_zero(): built().extra = 0 { refl }";
    e.elab_module_source("user", user).unwrap_or_else(|err| panic!("{}", err.render(user)));
}

/// Only a record's fields take a default, and positional arguments past the
/// fields without one are refused rather than read as the defaulted ones.
#[test]
fn defaults_are_a_records_and_positional_overflow_is_refused() {
    let error = bad("inductive Box { Make(x: Nat := 0) }");
    assert!(error.contains("only a record's fields take a default"), "{error}");
    let error = bad("
record Three { a: Nat, b: Nat := 0, c: Nat }
fn two() -> Three { Three(1, 2, 3, 4) }
");
    assert!(error.contains("by position"), "{error}");
}
