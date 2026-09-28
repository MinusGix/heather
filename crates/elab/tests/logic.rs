//! `lib/std/logic.hthr` and the connective syntax
//! (`issues/std-logic-module.md`, `docs/logic-connectives-design.md`).
//!
//! Two things are under test and they fail differently, so they are kept
//! apart below: the **module** (§1–2), which is ordinary declarations and
//! needed no language change at all, and the **notation** (§3–7), which is a
//! lexer window, three parser rungs and a precedence table.
//!
//! Nothing here is a generated term, so the four axes of
//! `docs/testing-generated-terms.md` do not all apply. The axis that does, and
//! that every precedence test below uses, is the **negative control in the
//! form of a shape assertion**: a precedence claim is checked by handing the
//! sugar a hypothesis written in the *desugared* spelling and letting
//! conversion agree or refuse. `p <= q ∧ q <= r ∧ p <= r` typechecking says
//! nothing on its own — it is only evidence once the term it is fed is
//! `And<nat::Nat::Le(p,q), And<nat::Nat::Le(q,r), nat::Nat::Le(p,r)>>` and the left-nested rival is refused
//! beside it.

use crate::support;
use heather_elab::{ElabError, Elaborator};

const BOOL: &str = include_str!("../../../lib/std/bool.hthr");
const NAT: &str = include_str!("../../../lib/std/nat.hthr");
const LOGIC: &str = include_str!("../../../lib/std/logic.hthr");

fn run(extra: &str) -> Result<Elaborator, String> {
    let mut e = support::library(&[("logic", LOGIC), ("bool", BOOL), ("nat", NAT)]);
    if !extra.is_empty() {
        let src = format!("import bool;\nimport nat;\nimport logic;\n{extra}");
        if let Err(err) = e.elab_module_source("probe", &src) {
            return Err(match err {
                ElabError::Elab { msg, .. } => msg,
                other => format!("{other}"),
            });
        }
    }
    Ok(e)
}

fn ok(extra: &str) -> Elaborator {
    run(extra).unwrap_or_else(|e| panic!("expected this to check, got: {e}"))
}

fn bad(extra: &str) -> String {
    match run(extra) {
        Err(e) => e,
        Ok(_) => panic!("expected a refusal, but it checked"),
    }
}

// ---------------------------------------------------------------------------
// 1. The module.

#[test]
fn the_logic_module_checks() {
    ok("");
}

/// Every connective is usable, in the call spelling, with no notation
/// involved — the module is a library file first and a notation target
/// second. If this passes and §3 onward fails, the grammar is at fault; if
/// this fails, the declarations are.
#[test]
fn the_connectives_work_without_notation() {
    ok("
theorem a(P: Type, Q: Type, h: And<P, Q>): And<Q, P> { and_swap(h) }
theorem b(P: Type, Q: Type, h: Or<P, Q>): Or<Q, P> { or_swap(h) }
theorem c(P: Type, p: P): Not(Not(P)) { not_not_intro(P, p) }
theorem d(P: Type, h: False): P { false_elim(h) }
theorem e(P: Type): Iff<P, P> { iff_refl() }
");
}

#[test]
fn let_bound_propositions_are_type_values() {
    ok("
fn EqAt<A>(x: A) -> Type { x = x }
theorem conjunction<A>(x: A, h: And<EqAt(x), x = x>, n: Nat):
    EqAt(x) ∧ x = x {
    let result = EqAt(x) ∧ x = x;
    let named = And<EqAt(x), x = x>;
    let annotated: Type = EqAt(x) ∧ x = x;
    let p: result = h;
    let q: named = p;
    let r: annotated = q;
    match n as λ z => result { Zero => r, Succ(k) => r }
}
theorem disjunction(P: Type, Q: Type, h: Or<P, Q>): P ∨ Q {
    let result = P ∨ Q;
    let p: result = h;
    p
}
theorem equivalence(P: Type, Q: Type, h: Iff<P, Q>): P ↔ Q {
    let result = P ↔ Q;
    let p: result = h;
    p
}
theorem constructor(P: Type, Q: Type, p: P, q: Q): P ∧ Q {
    let proof = And<P, Q>(p, q);
    proof
}
inductive Opt<A> { None, Some(A) }
fn nullary<A>() -> Opt<A> { let x = None<A>; x }
record Empty<A> {}
fn empty<A>() -> Empty<A> { let x = Empty<A>; x }
fn empty_type<A>() -> Type { let t: Type = Empty<A>; t }
record Higher<A> { carrier: Type, value: A }
fn higher_type<A>() -> Type<1> { let t = Higher<A>; t }
fn id<A>(x: A) -> A { x }
fn function_value() -> Nat { let f = id<Nat>; f(3) }
");
    let msg = bad("fn shadowed(And: Nat) -> Type { let t = And<Nat, Nat>; t }");
    assert!(msg.contains("takes no type arguments"), "{msg}");
    let msg = bad("fn wrong(P: Type) -> Type { let result = And<P>; result }");
    assert!(msg.contains("type argument"), "{msg}");
    let msg = bad("theorem wrong(P: Type, Q: Type, p: P): P ∧ Q {
        let result = P ∧ Q; let h: result = p; h
    }");
    assert!(msg.contains("this has type `P`") && msg.contains("`And<P, Q>` is expected"), "{msg}");
}

/// **`logic::False` the type and `bool::False` the constructor coexist**, in
/// one declaration, with neither shadowing the other and neither qualified
/// (`issues/false-collides-with-bools-constructor.md`, fixed 2026-08-16).
///
/// Two rules make it work and both are *shrinks*, never choices — the
/// dropped reading could not have checked where it was dropped:
///
/// - **type position** never considers a constructor a candidate
///   (`names::resolve_kinds`), which covers the annotation `h: False`;
/// - **an expected type that is an inductive** never considers a *type name*
///   one (`only_ctors_visible`), which covers `and(False, True)`.
///
/// The second needed the expected type whnf'd first, which is why the
/// argument case is here beside the result case: they are the same question
/// asked in two spellings, and before the fix only one of them fired.
#[test]
fn the_two_falses_coexist() {
    ok("
theorem both(h: False): Bool::and(False, True) = False { match h {} }

// type position, each spelling
theorem ann(P: Type, h: False): P { match h {} }
fn Neg(P: Type) -> Type { P -> False }
theorem arg_ty(P: Type, h: Neg(False)): Neg(False) { h }
theorem targ(P: Type, h: Or<P, False>): Or<P, False> { h }

// expression position, each spelling — the constructor, checked and inferred
theorem chk(): Bool { False }
fn idb(x: Bool) -> Bool { x }
theorem in_arg(): Bool { idb(False) }
theorem in_eq(): idb(False) = False { refl }
theorem nested(b: Bool): Bool { Bool::and(False, Bool::or(b, False)) }
");
}

/// The control: the shrink is licensed by *impossibility*, so where both
/// readings really could check, the ambiguity must still be reported. A `fn`
/// of the same name returning the expected type is exactly that case — it
/// lives in no constructor namespace and may well have the type — so the
/// expected-type route stands down and the name is ambiguous as before.
#[test]
fn a_global_of_the_same_name_still_stands_the_route_down() {
    let mut e = Elaborator::with_prelude().expect("prelude");
    e.elab_module_source("logic", LOGIC).expect("logic");
    e.elab_module_source("bool", BOOL).expect("bool");
    e.elab_module_source("shadow", "import bool;\nfn False() -> Bool { True }")
        .expect("shadow");
    let err = e
        .elab_module_source("probe", "import bool;\nimport shadow;\ntheorem t(): Bool { False }")
        .expect_err("expected the name collision to survive");
    let msg = match err {
        ElabError::Elab { msg, .. } => msg,
        other => format!("{other}"),
    };
    assert!(msg.contains("ambiguous"), "got: {msg}");
}

/// Falsity eliminates through a zero-arm `match` and needs no special form.
/// The negative control is the same `match` at a NON-empty type, which must
/// still be told it is missing arms — without it, deleting the arm check
/// entirely would pass the positive.
#[test]
fn false_eliminates_by_a_zero_arm_match() {
    ok("theorem t(P: Type, h: False): P { match h {} }");
    let err = bad("theorem t(b: Bool): Nat { match b {} }");
    assert!(err.contains("missing an arm"), "got: {err}");
}

// ---------------------------------------------------------------------------
// 2. The existential.

#[test]
fn exists_states_and_introduces() {
    ok("
fn Even(n: Nat) -> Type { Exists<Nat>(λ (k: Nat) => k.add(k) = n) }
theorem four(): Even(4) { Exists(2, refl) }
theorem out(n: Nat, h: Even(n)): h.witness.add(h.witness) = n { h.proof }
");
}

/// The type argument is **inferred from the predicate's own binder**
/// (`issues/exists-type-arg-not-inferred.md`, fixed 2026-08-16): the value
/// argument is inferred and its type matched against the declared `A -> Type`,
/// so `A` falls out of the domains.
///
/// Both spellings are pinned, and pinned to *agree* — `same` passes the
/// inferred form where the explicit one is expected, so the two are one type
/// and not merely two that each check.
#[test]
fn exists_infers_its_type_argument_from_the_predicate() {
    ok("
fn Even(n: Nat) -> Type { Exists(λ (k: Nat) => k.add(k) = n) }
theorem four(): Even(4) { Exists(2, refl) }
theorem same(n: Nat, h: Exists<Nat>(λ (k: Nat) => k.add(k) = n)): Even(n) { h }
theorem sugar(n: Nat, h: ∃ k: Nat, k.add(k) = n): Even(n) { h }

// Not hardcoded to `Nat`: an **open** predicate at another carrier, where
// the domain is a parameter rather than a written type.
fn AtBool(P: Bool -> Type) -> Type { Exists(P) }
");
}

/// What is still refused, and why it is not the same question: an argument
/// whose type determines nothing. The matcher is first-order and reads the
/// declared side as a skeleton, so a parameter that appears nowhere in it
/// cannot be recovered — and says so by name rather than by arity.
#[test]
fn an_undetermined_type_argument_is_still_refused() {
    let err = bad(
        "record Phantom<A>(k: Nat) { v: Nat }
         fn P(n: Nat) -> Type { Phantom(n) }",
    );
    assert!(err.contains("cannot infer the type argument `A`"), "got: {err}");
    // …and writing it is the way out the message names.
    ok("record Phantom<A>(k: Nat) { v: Nat }
        fn P(n: Nat) -> Type { Phantom<Nat>(n) }");
}

/// A *partial* type-argument list is still an arity error: filling some and
/// inferring the rest is a different feature, and this round does not open it.
#[test]
fn a_partial_type_argument_list_is_still_an_arity_error() {
    let err = bad(
        "record Two<A, B>(k: A) { v: B }
         fn P(n: Nat) -> Type { Two<Nat>(n) }",
    );
    assert!(err.contains("takes 2 type argument(s), found 1"), "got: {err}");
}

// ---------------------------------------------------------------------------
// 3. The notation, connective by connective.

#[test]
fn the_unicode_connectives_parse_and_mean_their_declarations() {
    ok("
theorem con(P: Type, Q: Type, h: And<P, Q>): P ∧ Q { h }
theorem dis(P: Type, Q: Type, h: Or<P, Q>): P ∨ Q { h }
theorem neg(P: Type, h: Not(P)): ¬P { h }
theorem bi(P: Type, Q: Type, h: Iff<P, Q>): P ↔ Q { h }
theorem all(h: (n: Nat) -> nat::Nat::Le(n, n)): ∀ n: Nat, n <= n { h }
theorem ex(h: Exists<Nat>(λ (k: Nat) => k.add(k) = 4)): ∃ k: Nat, k.add(k) = 4 { h }
");
}

/// `<->` is the one ASCII survivor and lexes to the same token, so the two
/// spellings are not merely equivalent — they are indistinguishable
/// downstream.
#[test]
fn the_ascii_iff_is_the_same_token() {
    ok("theorem t(P: Type, Q: Type, h: P <-> Q): P ↔ Q { h }");
    ok("theorem t(P: Type, Q: Type, h: P ↔ Q): P <-> Q { h }");
}

/// …and no other ASCII digraph was admitted: Unicode is the spelling.
#[test]
fn no_ascii_digraph_for_the_other_connectives() {
    for src in [
        r"theorem t(P: Type, Q: Type, h: And<P, Q>): P /\ Q { h }",
        r"theorem t(P: Type, Q: Type, h: Or<P, Q>): P \/ Q { h }",
        "theorem t(P: Type, h: Not(P)): ~P { h }",
    ] {
        let err = bad(src);
        assert!(
            err.contains("unexpected character") || err.contains("parse error"),
            "expected `{src}` not to lex, got: {err}"
        );
    }
}

// ---------------------------------------------------------------------------
// 4. Precedence, each claim pinned by the desugared shape.

/// The connectives are LOOSER than the comparison rung — the opposite of
/// where `&&`/`||` sit. `n <= m ∧ m <= k` is a conjunction of comparisons.
#[test]
fn connectives_are_looser_than_comparison() {
    ok("
theorem t(a: Nat, b: Nat, c: Nat, h: And<nat::Nat::Le(a, b), nat::Nat::Le(b, c)>): a <= b ∧ b <= c { h }
");
}

/// `∧` binds tighter than `∨`, and both are right-associative — the fixity
/// `++` chose and for the same reason: `And(p, And(q, r))` is the nesting the
/// record builds and projects.
#[test]
fn wedge_binds_tighter_than_vee_and_both_associate_right() {
    ok("
theorem assoc(p: Nat, q: Nat, r: Nat, h: And<nat::Nat::Le(p, q), And<nat::Nat::Le(q, r), nat::Nat::Le(p, r)>>):
    p <= q ∧ q <= r ∧ p <= r { h }
theorem prec(p: Nat, q: Nat, r: Nat, h: Or<And<nat::Nat::Le(p, q), nat::Nat::Le(q, r)>, nat::Nat::Le(r, p)>):
    p <= q ∧ q <= r ∨ r <= p { h }
");
    // The left-nested rival, refused. Without this the associativity claim is
    // untested: a left-associative parse would pass `assoc` too if `And` were
    // symmetric, and nothing above says it is not.
    let err = bad(
        "theorem t(p: Nat, q: Nat, r: Nat, h: And<And<nat::Nat::Le(p, q), nat::Nat::Le(q, r)>, nat::Nat::Le(p, r)>):
            p <= q ∧ q <= r ∧ p <= r { h }",
    );
    assert!(
        err.contains(
            "this has type `And<And<Le(p, q), Le(q, r)>, Le(p, r)>`, but \
             `And<Le(p, q), And<Le(q, r), Le(p, r)>>` is expected here"
        ),
        "got: {err}"
    );
}

/// `¬` binds tighter than `∧` and looser than the comparison rung, so
/// `¬ a = b` is `¬(a = b)` — the reading anyone writing it wants.
#[test]
fn neg_binds_tighter_than_wedge_and_looser_than_equality() {
    ok("
theorem eqn(h: Not(1 = 0)): ¬ 1 = 0 { h }
theorem conj(P: Type, np: Not(P), q: nat::Nat::Le(0, 1)): And<Not(P), nat::Nat::Le(0, 1)> { And(np, q) }
theorem conj_sugar(P: Type, np: ¬P, q: 0 <= 1): ¬P ∧ 0 <= 1 { And(np, q) }
theorem dbl(P: Type, h: Not(Not(P))): ¬¬P { h }
");
}

/// `≠` is only parser sugar, so both spellings use the same expected-carrier
/// path even when the equality endpoints have an open polymorphic carrier.
#[test]
fn inequality_and_negated_equality_share_open_endpoint_resolution() {
    ok("
theorem long_to_short<A>(x, y: A, h: ¬(x = y)): x ≠ y { h }
theorem short_to_long<A>(x, y: A, h: x ≠ y): ¬(x = y) { h }
");
}

/// `↔` is looser than `->`, which the arrow's right-associativity would
/// otherwise beat: `P -> Q ↔ Q -> P` relates two implications.
#[test]
fn iff_is_looser_than_the_arrow() {
    ok("
theorem t(P: Type, Q: Type, h: Iff<P -> Q, Q -> P>): P -> Q ↔ Q -> P { h }
theorem u(P: Type, Q: Type, h: Iff<(n: Nat) -> P, Q>): ((n: Nat) -> P) ↔ Q { h }
");
    // The rival reading, refused: `P -> (Q ↔ (Q -> P))`.
    let err = bad(
        "theorem t(P: Type, Q: Type, h: P -> Iff<Q, Q -> P>): P -> Q ↔ Q -> P { h }",
    );
    // The rival reading is refused with both readings spelled
    // (issues/check-fallback-discards-expected-type.md).
    assert!(err.contains("this has type `P -> Iff<…>`"), "got: {err}");
}

/// A type-argument-applied type as a connective's left operand. `ty_atom`
/// returns early on `D<A>` and would leave the `∧` dangling, so the rewind
/// that sends it back to the expression grammar is what this pins.
#[test]
fn an_applied_type_can_be_a_connective_operand() {
    ok("
theorem t(P: Type, Q: Type, h: And<Or<P, Q>, P>): Or<P, Q> ∧ P { h }
theorem u(P: Type, Q: Type, h: Iff<Or<P, Q>, And<P, Q>>): Or<P, Q> ↔ And<P, Q> { h }
");
}

/// A **parenthesised** connective inside a function type's codomain. `↔` is
/// suppressed while a codomain is read (that is what makes it looser than
/// `->`), and until `issues/iff-in-type-valued-body.md` that suppression
/// reached all the way down: `(a: A) -> (P(a) ↔ Q(a))` was
/// "expected `)`, found Iff". The restriction is a rule about the codomain's
/// own spine, so every bracket lifts it, exactly as `no_eq`'s does.
///
/// Two negative controls below. Both operands mention the binder, so the
/// grouping is load-bearing rather than cosmetic: without the parentheses the
/// `↔` is the looser rung, the binder's scope ends at the arrow's codomain,
/// and the right-hand `a` is unbound — which the issue asked be left exactly
/// as it is. And parenthesising must not have turned the group into that
/// looser reading either.
#[test]
fn a_parenthesised_connective_is_readable_inside_a_codomain() {
    // Type-valued body and type annotation, against the named-constructor
    // spelling in each direction: conversion has to see one type.
    ok("
fn SameOn<A>(P, Q: A -> Type) -> Type { (a: A) -> (P(a) ↔ Q(a)) }
fn SameOnNamed<A>(P, Q: A -> Type) -> Type { (a: A) -> Iff<P(a), Q(a)> }
theorem body_to_named<A>(P, Q: A -> Type, h: SameOn(P, Q)): SameOnNamed(P, Q) { h }
theorem named_to_body<A>(P, Q: A -> Type, h: SameOnNamed(P, Q)): SameOn(P, Q) { h }
theorem in_an_annotation<A>(P, Q: A -> Type, h: (a: A) -> (P(a) ↔ Q(a))):
    (a: A) -> Iff<P(a), Q(a)> { h }
");
    // One hypothesis, both readings, and the parentheses are what choose:
    // bracketed, the `↔` is the codomain and the type is a `Pi`, so the
    // `Iff`-at-the-root hypothesis is refused; bare, it is the loose rung and
    // the same hypothesis is exactly right. The second half is the precedence
    // this fix had to leave alone.
    let err = bad("theorem t(P: Type, Q: Type, R: Type, h: Iff<P -> Q, R>): P -> (Q ↔ R) { h }");
    assert!(err.contains("Iff"), "got: {err}");
    ok("theorem t(P: Type, Q: Type, R: Type, h: Iff<P -> Q, R>): P -> Q ↔ R { h }");
    // The spelling the parentheses exist to distinguish, unmoved: dropping
    // them puts the right-hand operand outside the binder.
    let err = bad("fn SameOn<A>(P, Q: A -> Type) -> Type { (a: A) -> P(a) ↔ Q(a) }");
    assert!(err.contains("unbound name `a`"), "got: {err}");
}

/// A **binder-headed** function type as the `↔`'s left operand. `↔` is looser
/// than `->`, so `(a: A) -> P(a) ↔ R` is `((a: A) -> P(a)) ↔ R` — the reading
/// `P -> Q ↔ R` already got. `Parser::ty`'s binder-group path builds its Π and
/// returns it, so until `issues/binder-headed-arrow-as-connective-operand.md`
/// it sat below the loosest rung and the spelling was
/// ``expected `{`, found Iff``.
///
/// Checked against the named-constructor hypothesis, not against itself, so
/// the test says which grouping it got.
#[test]
fn a_binder_headed_function_type_can_be_the_iff_operand() {
    ok("
theorem bare<A>(P: A -> Type, R: Type, h: Iff<(a: A) -> P(a), R>):
    (a: A) -> P(a) ↔ R { h }
theorem bracketed<A>(P: A -> Type, R: Type, h: Iff<(a: A) -> P(a), R>):
    ((a: A) -> P(a)) ↔ R { h }
");
    // …and in a Type-valued *body*, which is expression position and reaches
    // the rung by a different route (the Π arrives as a `TyLit`, the plain
    // arrow's as a `TyApp`). All three spellings have to be one type.
    ok("
fn Bare<A>(P: A -> Type, R: Type) -> Type { (a: A) -> P(a) ↔ R }
fn Bracketed<A>(P: A -> Type, R: Type) -> Type { ((a: A) -> P(a)) ↔ R }
theorem to<A>(P: A -> Type, R: Type, h: Bare(P, R)): Bracketed(P, R) { h }
theorem back<A>(P: A -> Type, R: Type, h: Bracketed(P, R)): Bare(P, R) { h }
theorem named<A>(P: A -> Type, R: Type, h: Iff<(a: A) -> P(a), R>): Bare(P, R) { h }
");
    // The binder's scope does not move: the Π is complete before the `↔`
    // applies, so the right operand is still outside the binder. This is the
    // reading [[iff-in-type-valued-body]] asked be left alone — what changed
    // is that it is a reading rather than a parse error.
    let err = bad("fn SameOn<A>(P, Q: A -> Type) -> Type { (a: A) -> P(a) ↔ Q(a) }");
    assert!(err.contains("unbound name `a`"), "got: {err}");
    // Still one non-associative rung.
    let err = bad("theorem t<A>(P: A -> Type, R: Type, S: Type, h: R):
                       (a: A) -> P(a) ↔ R ↔ S { h }");
    assert!(err.contains("does not chain"), "got: {err}");
    // A codomain still declines, so a binder-headed *codomain* leaves the `↔`
    // to the outer arrow: this is `(P -> (a: A) -> Q(a)) ↔ R`.
    ok("theorem t<A>(P: Type, Q: A -> Type, R: Type, h: Iff<P -> (a: A) -> Q(a), R>):
            P -> (a: A) -> Q(a) ↔ R { h }");
}

/// The grammar boundary, not `SameMembers`: `∧` and `∨` were never suppressed
/// in a codomain and still are not, and the brackets the `↔` fix had to reach
/// are all of them — a parenthesised group whose own top level is an arrow, a
/// type-argument list, and a call's arguments.
#[test]
fn every_bracket_inside_a_codomain_admits_a_connective() {
    ok("
theorem conj<A>(P, Q: A -> Type, h: (a: A) -> And<P(a), Q(a)>):
    (a: A) -> (P(a) ∧ Q(a)) { h }
theorem disj<A>(P, Q: A -> Type, h: (a: A) -> Or<P(a), Q(a)>):
    (a: A) -> (P(a) ∨ Q(a)) { h }
theorem arrow_inside(P: Type, Q: Type, R: Type, S: Type, h: P -> Iff<Q -> R, S>):
    P -> (Q -> R ↔ S) { h }
theorem tyargs(P: Type, Q: Type, R: Type, h: P -> Or<Iff<Q, R>, P>):
    P -> Or<Q ↔ R, P> { h }
theorem call_args(P: Type, Q: Type, R: Type, h: P -> ¬(Iff<Q, R>)):
    P -> ¬(Q ↔ R) { h }
");
}

// ---------------------------------------------------------------------------
// 4b. Expected-type-directed connective introductions and patterns.

#[test]
fn concise_conjunction_introduction_nests_to_three_fields() {
    ok("
theorem pair<P, Q>(p: P, q: Q): P ∧ Q { ⟨p, q⟩ }
theorem triple<P, Q, R>(p: P, q: Q, r: R): P ∧ Q ∧ R { ⟨p, ⟨q, r⟩⟩ }
theorem consume<P, Q, R>(h: P ∧ Q ∧ R): Q {
    match h { ⟨_, ⟨q, _⟩⟩ => q }
}
");
}

#[test]
fn concise_binary_sum_introduction_and_elimination() {
    ok("
theorem left<P, Q>(p: P): P ∨ Q { ⟨p |⟩ }
theorem right<P, Q>(q: Q): P ∨ Q { ⟨| q⟩ }
theorem choose<P, Q>(h: P ∨ Q, p0: P): P {
    match h { ⟨p |⟩ => p, ⟨| _⟩ => p0 }
}
");
}

#[test]
fn anonymous_constructor_notation_generalizes_by_shape() {
    ok("
record Wrap<A> { value: A }
inductive Choice<A> { No, Yes(value: A) }
theorem wrap<A>(a: A): Wrap<A> { ⟨a⟩ }
theorem yes<A>(a: A): Choice<A> { ⟨| a⟩ }
theorem unwrap<A>(w: Wrap<A>): A { match w { ⟨a⟩ => a } }
theorem witness(): ∃ n: Nat, n = 2 { ⟨2, refl⟩ }
");
}

#[test]
fn anonymous_constructor_notation_is_checking_only_and_shape_checked() {
    let e = bad("fn inferred<P>(p: P) -> P { let x = ⟨p⟩; p }");
    assert!(e.contains("checking-only"), "{e}");

    let e = bad("theorem wrong<P, Q>(p: P): P ∧ Q { ⟨p |⟩ }");
    assert!(e.contains("with 2 constructor(s)"), "{e}");
}

// ---------------------------------------------------------------------------
// 5. The quantifiers.

/// `∀` is a synonym: it desugars to the arrow form the surface already had,
/// so the two are the same type and not merely equivalent ones.
#[test]
fn forall_is_the_arrow_form() {
    ok("
theorem one(h: (n: Nat) -> nat::Nat::Le(n, n)): ∀ n: Nat, n <= n { h }
theorem many(h: (n: Nat) -> (m: Nat) -> nat::Nat::Le(n, n.add(m))): ∀ n, m: Nat, n <= n.add(m) { h }
theorem body_runs_right(h: (n: Nat) -> And<nat::Nat::Le(n, n), nat::Nat::Le(0, n)>):
    ∀ n: Nat, n <= n ∧ 0 <= n { h }
");
}

/// `∃` supplies the type argument from its own binder — which is the whole
/// reason the sugar earns its keep, given §2's rough edge.
#[test]
fn exists_supplies_its_type_argument_from_the_binder() {
    ok("
fn Even(n: Nat) -> Type { ∃ k: Nat, k.add(k) = n }
theorem four(): Even(4) { Exists(2, refl) }
theorem nested(): ∃ a: Nat, ∃ b: Nat, a.add(b) = 3 { Exists(1, Exists(2, refl)) }
theorem many(h: Exists<Nat>(λ (a: Nat) => Exists<Nat>(λ (b: Nat) => a.add(b) = 3))):
    ∃ a, b: Nat, a.add(b) = 3 { h }
");
}

// ---------------------------------------------------------------------------
// 6. What the grammar refuses, and whether it says why.

#[test]
fn iff_does_not_chain() {
    let err = bad("theorem t(P: Type, Q: Type, R: Type, h: P): P ↔ Q ↔ R { h }");
    assert!(err.contains("does not chain"), "got: {err}");
}

#[test]
fn a_quantifier_binder_needs_its_annotation() {
    let err = bad("theorem t(): ∀ n, n <= n { trivial }");
    assert!(err.contains("has no type"), "got: {err}");
    // A second binder group written flat gets its own message, naming the
    // nesting that replaces it — the parse otherwise ends at `m` and the
    // error surfaces a span away, as whatever the declaration expected next.
    let err = bad("theorem t(): ∀ n: Nat, m: Nat, n <= n { trivial }");
    assert!(err.contains("one binder group per quantifier"), "got: {err}");
}

// ---------------------------------------------------------------------------
// 7. Controls on the rungs the connectives sit between.

/// `&&`/`||` remain arithmetic, tighter than comparison, and are now owned by
/// `bool` itself. Thus `x && True = x` is `(x && True) = x`, and the named and
/// designated spellings convert without importing `algebra`.
#[test]
fn the_boolean_doubles_keep_their_precedence_and_resolve_from_bool() {
    ok("theorem t(x: Bool): x.and(True) = x { x.and_true_r() }");
    ok("theorem u(x: Bool, h: x.and(True) = x): x && True = x { h }");
}

/// Comparisons still do not chain, and the message is still theirs rather
/// than the new `↔` one.
#[test]
fn comparisons_still_do_not_chain() {
    let err = bad("theorem t(a: Nat, b: Nat, c: Nat): a <= b <= c { trivial }");
    assert!(err.contains("comparisons do not chain"), "got: {err}");
}
