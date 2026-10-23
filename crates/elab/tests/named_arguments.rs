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

/// Under local bindings the default runs too: its goal is open in the
/// construction's locals, so it is checked under them
/// (issues/field-defaults-under-locals.md). A neutral field value and a
/// literal one build the same term as the full spelling.
#[test]
fn a_field_default_runs_under_locals() {
    ok("
record Pinned { value: Nat, same: value = value := refl }
fn local(k: Nat) -> Pinned { Pinned(k) }
fn named(k: Nat) -> Pinned { Pinned(value := k) }
fn in_let(k: Nat) -> Pinned { let p: Pinned = Pinned(Succ(k)); p }
theorem local_is_full(k: Nat): local(k) = Pinned(k, refl) { refl }
theorem named_is_full(k: Nat): named(k) = Pinned(k, refl) { refl }
theorem in_let_is_full(k: Nat): in_let(k) = Pinned(Succ(k), refl) { refl }
fn given(k: Nat) -> Pinned { Pinned(k, same := refl) }
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

// -- parameter defaults (§9.6) -----------------------------------------------

const SECOND: &str = "
fn seven() -> Nat { 7 }
fn second(a: Nat, b: Nat := seven()) -> Nat { b }
";

/// A defaulted parameter has no positional slot (§9.2): `second(1)` is
/// `second(1, b := seven())`, proved by `refl` against both the full
/// spelling and the value, and the value is the *default's* (7) rather than
/// the positional argument's, so a slot mix-up cannot pass. A named argument
/// overrides it, and `@` passes it positionally.
#[test]
fn a_defaulted_parameter_has_no_positional_slot() {
    ok(&format!("{SECOND}
theorem short(): second(1) = 7 {{ refl }}
theorem is_full(): second(1) = second(1, b := seven()) {{ refl }}
theorem overridden(): second(1, b := 2) = 2 {{ refl }}
theorem reordered(): second(b := 2, a := 1) = 2 {{ refl }}
theorem at_call(): @second(1, 3) = 3 {{ refl }}
theorem neutral(k: Nat): second(k) = 7 {{ refl }}
"));
}

/// The default is checked at the parameter's domain *as the call
/// instantiates it*: `same: x = x` becomes `True = True`, `a = a` at an open
/// `A`, and `Succ(k) = Succ(k)` at a neutral argument. In checking position
/// too, where the call's own type is the expected one.
#[test]
fn a_default_is_checked_at_the_instantiated_domain() {
    ok("
inductive Bool { False, True }
fn first<A>(x: A, y: A, same: x = x := refl) -> A { x }
theorem closed(): first(True, False) = True { refl }
theorem open<A>(a: A, b: A): first(a, b) = a { refl }
theorem neutral(k: Nat): first(Succ(k), k) = Succ(k) { refl }
fn checked(k: Nat) -> Nat { first(k, Zero) }
");
}

/// A method call fills the receiver and leaves the default to fill itself.
#[test]
fn a_method_call_leaves_the_default_to_fill_itself() {
    ok("
fn seven() -> Nat { 7 }
inductive Holder { Hold(n: Nat) }
fn Holder::get(self h: Holder, extra: Nat := seven()) -> Nat { extra }
theorem by_default(): Hold(1).get() = 7 { refl }
theorem by_name(): Hold(1).get(extra := 2) = 2 { refl }
");
}

/// §9.4: a default's names resolve where the declaration was written. A
/// caller's local `seven` would make the dynamically scoped reading of
/// `seven()` an application of a `Nat` — and a caller's local `trivial`
/// would be a `Nat` where a proof of `True` is due.
#[test]
fn a_callers_locals_cannot_capture_a_defaults_names() {
    ok(&format!("{SECOND}
fn shadowing(seven: Nat) -> Nat {{ second(seven) }}
theorem still_seven(): shadowing(1) = 7 {{ refl }}
fn trivially(n: Nat, h: True := trivial) -> Nat {{ n }}
fn caller(trivial: Nat) -> Nat {{ trivially(trivial) }}
"));
}

/// The same rule across modules: the user module's own `witness` does not
/// change the declaring module's default.
#[test]
fn a_parameter_default_resolves_in_the_declaring_module() {
    let mut e = Elaborator::with_prelude().expect("prelude");
    let declaring = "fn witness() -> Nat { 0 }\nfn extra(n: Nat, w: Nat := witness()) -> Nat { w }";
    e.elab_module_source("declaring", declaring).unwrap_or_else(|err| panic!("{}", err.render(declaring)));
    let user = "import declaring::{extra};\nfn witness() -> Nat { 1 }\ntheorem zero(): extra(5) = 0 { refl }";
    e.elab_module_source("user", user).unwrap_or_else(|err| panic!("{}", err.render(user)));
}

/// A default that does not give the parameter's type at this call is
/// refused at the call, naming the parameter and the way out; the positive
/// call beside it is the control.
#[test]
fn a_parameter_default_that_fails_is_refused_at_the_call() {
    let error = bad("
inductive Yes { Holds }
inductive No { Fails }
fn IsZero(n: Nat) -> Type { match n { Zero => Yes, Succ(_) => No } }
fn zeroed(n: Nat, zero: IsZero(n) := Holds) -> Nat { n }
fn fine() -> Nat { zeroed(0) }
fn wrong() -> Nat { zeroed(5) }
");
    assert!(error.contains("`zeroed`'s `zero` was left to its default") && error.contains("zero := "), "{error}");
    assert!(error.starts_with("7:"), "the refusal points at the call in `wrong`: {error}");
}

/// Positional arguments past the parameters that take one are refused
/// rather than read as the defaulted one.
#[test]
fn a_positional_argument_cannot_fill_a_default() {
    let error = bad(&format!("{SECOND}\ntheorem two(): second(1, 2) = 2 {{ refl }}"));
    assert!(error.contains("by position") && error.contains("b := "), "{error}");
}

/// The declaration-side refusals: a default on an implicit or on `self`
/// (two filling disciplines on one slot, or a slot the receiver always
/// fills), and a default that mentions its own parameter, a later one, or a
/// type parameter. The telescope is ordered, so only the parameters before a
/// default have arguments when it runs (§9.4); a type parameter has no alias
/// to bind it (issues/parameter-defaults-mention-type-parameters.md).
#[test]
fn declaration_side_refusals() {
    let error = bad("fn f({b: Nat := 0}) -> Nat { b }");
    assert!(error.contains("already filled by unification"), "{error}");
    let error = bad("inductive Holder { Hold(n: Nat) }\nfn Holder::get(self h: Holder := Hold(0)) -> Nat { 0 }");
    assert!(error.contains("`self` cannot have a default"), "{error}");
    let error = bad("fn f(k: Nat := n, n: Nat) -> Nat { k }");
    assert!(error.contains("mentions the later parameter `n`"), "{error}");
    let error = bad("fn f(k: Nat := Succ(k)) -> Nat { k }");
    assert!(error.contains("mentions its own parameter"), "{error}");
    let error = bad("inductive List<A> { Nil, Cons(h: A, t: List<A>) }\nfn f<A>(x: A, xs: List<A> := Nil<A>) -> A { x }");
    assert!(error.contains("mentions the type parameter `A`"), "{error}");
    // A binder of the default's own that shadows a later parameter's name is
    // not a mention of it.
    ok("fn apply(f: Nat -> Nat, x: Nat) -> Nat { f(x) }
fn g(m: Nat, k: Nat := apply(λ (n: Nat) => n, m), n: Nat) -> Nat { k }
theorem shadowed(): g(1, 2) = 1 { refl }");
    // `:= infer` is still the solver, not a default naming `infer`.
    ok("fn f(n: Nat, h: True := infer) -> Nat { n }\nfn g() -> Nat { f(1) }");
}

// -- defaults that mention earlier parameters (§9.6) -------------------------
//
// issues/parameter-defaults-mention-parameters.md. At the call, each earlier
// parameter a default mentions is bound to the call's argument for it, so
// `k: Nat := n` reads the argument the call gave `n`. The axes: a literal and
// a neutral argument, an open element type, a checking position, an
// implicit learned from another argument and one learned only from the
// expected type, a chain of defaults, and negative controls.

const ECHO: &str = "
fn echo(n: Nat, k: Nat := n) -> Nat { k }
";

/// `echo(3)` is `echo(3, k := 3)`, by `refl` against the full spelling and
/// the value; a neutral argument and a checking position too. A named
/// argument still overrides.
#[test]
fn a_default_reads_an_earlier_argument() {
    ok(&format!("{ECHO}
theorem literal(): echo(3) = 3 {{ refl }}
theorem is_full(): echo(3) = echo(3, k := 3) {{ refl }}
theorem neutral(m: Nat): echo(Succ(m)) = Succ(m) {{ refl }}
theorem overridden(): echo(3, k := 5) = 5 {{ refl }}
fn checked(m: Nat) -> Nat {{ echo(m) }}
theorem checked_is(m: Nat): checked(m) = m {{ refl }}
"));
}

/// The default's `n` is the parameter, never the caller's own `n`: here the
/// caller's `n` is a different argument, and `echo(m)` is still `m`.
#[test]
fn a_callers_local_of_the_same_name_is_not_the_parameter() {
    ok(&format!("{ECHO}
fn other(n: Nat, m: Nat) -> Nat {{ echo(m) }}
theorem is_m(): other(1, 2) = 2 {{ refl }}
"));
    // The negative control: if the default were the caller's `n`, this
    // would be 1.
    let error = bad(&format!("{ECHO}
fn other(n: Nat, m: Nat) -> Nat {{ echo(m) }}
theorem is_n(): other(1, 2) = 1 {{ refl }}
"));
    assert!(error.contains("is_n"), "{error}");
}

/// At an open type the default is the argument at that type.
#[test]
fn a_default_at_an_open_type() {
    ok("
inductive Bool { False, True }
fn dup<A>(x: A, y: A := x) -> A { y }
theorem closed(): dup(True) = True { refl }
theorem open<A>(a: A): dup(a) = a { refl }
theorem overridden(): dup(True, y := False) = False { refl }
");
}

/// A default may mention an earlier defaulted parameter, which is filled
/// first; overriding the earlier one changes what the later one reads.
#[test]
fn a_chain_of_defaults() {
    ok("
fn chain(a: Nat, b: Nat := Succ(a), c: Nat := Succ(b)) -> Nat { c }
theorem both(): chain(0) = 2 { refl }
theorem first_given(): chain(0, b := 5) = 6 { refl }
theorem last_given(): chain(0, c := 9) = 9 { refl }
");
}

/// The mentioned parameter is an implicit, learned from another argument;
/// and one learned only from the expected type, so the default waits for it.
/// There the later `h := refl` default proves `k = n`, so `k` is `n`'s
/// argument or the call does not elaborate.
#[test]
fn a_default_mentions_an_implicit() {
    ok("
record Sized(n: Nat) { x: Nat, p: x = n }
fn size_of({n: Nat}, s: Sized(n), k: Nat := n) -> Nat { k }
theorem closed(s: Sized(4)): size_of(s) = 4 { refl }
theorem open(m: Nat, s: Sized(m)): size_of(s) = m { refl }
fn pinned({n: Nat}, k: Nat := n, h: k = n := refl) -> n = n { refl }
theorem learned_late(): 3 = 3 { pinned() }
");
}

/// A default whose *type* also depends on the earlier argument: the domain
/// and the default are instantiated by the same argument.
#[test]
fn a_dependent_default() {
    ok("
fn self_eq(n: Nat, h: n = n := refl, m: Nat := n) -> Nat { m }
theorem t(k: Nat): self_eq(k) = k { refl }
");
}

/// A method call: the receiver is an earlier argument like any other.
#[test]
fn a_default_reads_the_receiver() {
    ok("
inductive Holder { Hold(n: Nat) }
fn Holder::count(self h: Holder) -> Nat { match h { Hold(n) => n } }
fn Holder::get(self h: Holder, extra: Nat := h.count()) -> Nat { extra }
theorem by_default(): Hold(4).get() = 4 { refl }
theorem by_name(): Hold(4).get(extra := 2) = 2 { refl }
");
}

/// A default that does not give the parameter's type at this call is still
/// refused at the call, naming the parameter: here `zero`'s goal is
/// `IsZero(m)`, and `m` is the earlier default's copy of `n`.
#[test]
fn a_mentioning_default_that_fails_is_refused_at_the_call() {
    let error = bad("
inductive Yes { Holds }
inductive No { Fails }
fn IsZero(n: Nat) -> Type { match n { Zero => Yes, Succ(_) => No } }
fn zeroed(n: Nat, m: Nat := n, zero: IsZero(m) := Holds) -> Nat { n }
fn fine() -> Nat { zeroed(0) }
fn wrong() -> Nat { zeroed(5) }
");
    assert!(error.contains("`zeroed`'s `zero` was left to its default") && error.contains("zero := "), "{error}");
    assert!(error.starts_with("7:"), "the refusal points at the call in `wrong`: {error}");
    // An argument of the wrong type for what the default does with it is
    // refused too, though at the default rather than the call: the mismatch
    // is the gate's verdict, which is
    // issues/default-kernel-failure-reported-at-declaration.md's case.
    let error = bad("
inductive Bool { False, True }
fn pick<A>(x: A, k: Nat := x) -> Nat { k }
fn fine() -> Nat { pick(3) }
fn wrong() -> Nat { pick(True) }
");
    assert!(error.contains("this has type `Bool`, but `Nat` is expected here"), "{error}");
}

/// Across modules: the default's parameter names bind in the user module's
/// call, and its other names still resolve where it was declared.
#[test]
fn a_mentioning_default_across_modules() {
    let mut e = Elaborator::with_prelude().expect("prelude");
    let declaring = "fn bump(n: Nat) -> Nat { Succ(n) }\nfn next(n: Nat, k: Nat := bump(n)) -> Nat { k }";
    e.elab_module_source("declaring", declaring).unwrap_or_else(|err| panic!("{}", err.render(declaring)));
    let user = "import declaring::{next};\nfn bump(n: Nat) -> Nat { n }\ntheorem one(n: Nat): next(n) = Succ(n) { refl }";
    e.elab_module_source("user", user).unwrap_or_else(|err| panic!("{}", err.render(user)));
}

// -- defaults checked where they are written (§9.7) --------------------------
//
// issues/parameter-default-unchecked-at-declaration.md. A value default is
// checked in the declaration's telescope, by the kernel, whether or not any
// call leaves it out; a discharge (a tactic, `refl`) runs only at a call. The
// axes: no call at all, a theorem as well as a `fn`, a default mentioning an
// earlier parameter, an open type, a fit only some calls make, and a
// positive control beside each refusal.

const CHECKED: &str = "
record P { a: Nat, h: a = 3 }
";

/// The issue's case: `P(2, refl)`'s `refl` is the kernel's to judge, and no
/// call uses the default, so before §9.7 nothing judged it. Refused at the
/// default, in the declaration; the control is the same default made right.
#[test]
fn a_default_no_call_uses_is_still_checked() {
    let error = bad(&format!("{CHECKED}fn g(x: Nat := P(2, refl).a) -> Nat {{ x }}\n"));
    assert!(error.starts_with("3:") && error.contains("rejected `g`"), "{error}");
    let error = bad(&format!("{CHECKED}theorem t(x: Nat := P(2, refl).a): x = x {{ refl }}\n"));
    assert!(error.starts_with("3:") && error.contains("rejected `t`"), "{error}");
    ok(&format!("{CHECKED}fn g(x: Nat := P(3, refl).a) -> Nat {{ x }}\ntheorem used(): g() = 3 {{ refl }}\n"));
}

/// Mentioning an earlier parameter: the default is checked with `n` a
/// binder, so it is right for every argument or refused. `add(n, True)` is
/// wrong whatever `n` is.
#[test]
fn a_mentioning_default_is_checked_at_the_parameter() {
    let error = bad("
inductive Bool { False, True }
fn add(a: Nat, b: Nat) -> Nat { a }
fn f(n: Nat, k: Nat := add(n, True)) -> Nat { k }
");
    assert!(error.contains("`k`'s default does not check where it is written"), "{error}");
    let error = bad("fn f(n: Nat, k: Nat := missing(n)) -> Nat { k }");
    assert!(error.contains("`k`'s default does not check where it is written") && error.contains("missing"), "{error}");
    ok("
fn add(a: Nat, b: Nat) -> Nat { a }
fn f(n: Nat, k: Nat := add(n, n)) -> Nat { k }
");
}

/// A default whose fit to the parameter no call can change is refused: here
/// both `Bool` and the numeral's `Nat` are the same at every call.
#[test]
fn a_default_that_fits_no_call_is_refused() {
    let error = bad("inductive Bool { False, True }\nfn f(n: Nat, b: Bool := 5) -> Nat { n }");
    assert!(error.contains("`b`'s default does not check where it is written"), "{error}");
    ok("inductive Bool { False, True }\nfn f(n: Nat, b: Bool := True) -> Nat { n }");
}

/// A default whose fit depends on the call stays legal, and the call is
/// still what refuses a misfit (the two `…_refused_at_the_call` tests above
/// pin that): `Holds` is a `Yes`, which `IsZero(n)` is exactly when `n` is
/// zero, and `x` is a `Nat` exactly when `A` is. Its own subterms are still
/// checked here: `Holds2(refl)` proves `2 = 3` at no call.
#[test]
fn a_default_whose_fit_depends_on_the_call() {
    ok("
inductive Yes { Holds }
inductive No { Fails }
fn IsZero(n: Nat) -> Type { match n { Zero => Yes, Succ(_) => No } }
fn zeroed(n: Nat, zero: IsZero(n) := Holds) -> Nat { n }
fn pick<A>(x: A, k: Nat := x) -> Nat { k }
");
    let error = bad("
inductive Yes { Holds(p: 2 = 3) }
inductive No { Fails }
fn IsZero(n: Nat) -> Type { match n { Zero => Yes, Succ(_) => No } }
fn zeroed(n: Nat, zero: IsZero(n) := Holds(refl)) -> Nat { n }
");
    assert!(error.starts_with("5:") && error.contains("rejected `zeroed`"), "{error}");
}

/// A discharge has no meaning apart from a call's goal and hypotheses, so a
/// declaration with no call accepts it: here a `refl` only some calls'
/// endpoints make true, and the call still checks it. `omega` over facts
/// only a caller has is `positivity_tactic.rs`'s `DEFAULTS`.
#[test]
fn a_discharge_waits_for_a_call() {
    ok("
fn zero_only(n: Nat, h: n = Zero := refl) -> Nat { n }
fn at_zero() -> Nat { zero_only(Zero) }
");
    let error = bad("
fn zero_only(n: Nat, h: n = Zero := refl) -> Nat { n }
fn at_one() -> Nat { zero_only(Succ(Zero)) }
");
    assert!(error.contains("rejected"), "{error}");
}

/// At an open type a default is checked with the type parameter abstract: a
/// lambda at `A → A` checks, and is the identity at each call.
#[test]
fn a_default_at_an_open_type_is_checked_abstractly() {
    ok("
inductive Bool { False, True }
fn twice<A>(x: A, f: A -> A := λ y => y) -> A { f(f(x)) }
theorem closed(): twice(True) = True { refl }
theorem overridden(): twice(True, f := λ b => False) = False { refl }
");
}
