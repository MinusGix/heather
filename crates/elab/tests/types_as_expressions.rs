//! Types are expressions: a function type in expression position, and so a
//! type-valued `fn` as an ordinary `fn` (`docs/types-as-expressions.md`).
//! Tracking issue: `issues/type-definitions.md` (route 2).
//!
//! Nothing here touches the kernel. A named abbreviation elaborates to `El` of
//! a call to a δ-transparent global, and `El ⌜T⌝ ⇝ T` plus δ are both kernel
//! reductions that predate this round — so the round's whole surface is the
//! grammar plus the elaborator's structural readers, and every term below is
//! re-checked by the real kernel.
//!
//! Per `docs/testing-generated-terms.md` the suite varies: a **checking**
//! position and not only computation (§3, §4), a **neutral** argument as well
//! as a literal one (§2), an **open** element type — an abbreviation applied
//! at a variable, used before it can possibly be known (§2, §5) — and negative
//! controls (§6), including the level mismatch the universe round's
//! non-cumutativity makes possible.
//!
//! §5 is the regression the round was written by: `tag_value` read the tag
//! component of a *decoded* type as a `Unit` and emitted `⟨⟩` where a pair was
//! needed, so every declaration whose nominal tag was not 0 built a
//! kernel-rejected constructor. It is invisible to a one-declaration test.

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

// -- 1: the grammar -------------------------------------------------------

// The one form the round adds: `->` after an expression. Before it, this was
// `parse error: expected `}`, found Arrow`
// (`docs/surface-existential-investigation.md`).
#[test]
fn an_arrow_is_an_expression() {
    ok("fn Q() -> Type { Nat -> Nat }");
}

// A *dependent* binder group in expression position. `:` is not in the
// expression grammar, so the three-token lookahead cannot collide.
#[test]
fn a_binder_group_is_an_expression() {
    ok("fn D() -> Type { (n: Nat) -> n = n }");
    ok("fn D2() -> Type { (n: Nat) -> (m: Nat) -> n = m -> m = n }");
}

// `=` binds tighter than `->`, in expression position exactly as in type
// position — there is one parse, so the two cannot disagree.
#[test]
fn equality_binds_tighter_than_the_arrow() {
    // If `->` bound tighter, this would be `0 = (Nat -> Nat)`, which is
    // ill-typed rather than merely differently grouped.
    ok("fn E(n: Nat) -> Type { n = n -> n = n }");
}

// Grouping still works, and a parenthesised function type is a domain.
#[test]
fn a_parenthesised_function_type_is_a_domain() {
    ok("fn G() -> Type { (Nat -> Nat) -> Nat }");
}

// The expression grammar is otherwise untouched: every position that used to
// take an expression still does, and `=` is still suppressed where it is
// punctuation.
#[test]
fn the_expression_grammar_is_unchanged() {
    ok("fn f(n: Nat) -> Nat { Succ(n) }");
    ok("theorem t(a: Nat, b: Nat, p: a = b): b = a { sym(p) }");
    ok("fn g(n: Nat) -> Nat { match n { Zero => 0, Succ(k) => k } }");
}

// -- 2: a type-valued `fn` is used in type position ------------------------

// The abbreviation applied at a **neutral** argument (a variable), in a
// **checking** position (`refl` has no inferable type), at an **open** body
// (`n = n` mentions the abbreviation's own parameter). All three axes at once,
// which is what makes this the round's core positive test.
#[test]
fn an_abbreviation_is_used_at_a_neutral_argument() {
    ok("fn P(n: Nat) -> Type { n = n }
        theorem use_p(n: Nat): P(n) { refl }");
}

// The same abbreviation at a **literal** argument, where everything reduces.
// Paired with the neutral one deliberately (axis 1).
#[test]
fn an_abbreviation_is_used_at_a_literal_argument() {
    ok("fn P(n: Nat) -> Type { n = n }
        theorem use_p(): P(3) { refl }");
}

// A function-typed abbreviation, applied — so the elaborator has to see a `Π`
// through `El` and δ, not merely accept the type.
#[test]
fn an_abbreviation_of_a_function_type_is_applied() {
    ok("fn Q() -> Type { Nat -> Nat }
        theorem use_q(f: Q()): Nat { f(2) }");
}

// A *dependent* abbreviation inhabited by a λ: checking a lambda against a
// name, which needs the name unfolded to find the domain.
#[test]
fn a_lambda_checks_against_an_abbreviation() {
    ok("fn D(n: Nat) -> Type { (m: Nat) -> m = m }
        theorem use_d(n: Nat): D(n) { λ m => refl }");
}

// A nullary abbreviation — the degenerate arity, which must not be special.
#[test]
fn a_nullary_abbreviation_works() {
    ok("fn C() -> Type { Nat }
        theorem use_c(x: C()): Nat { x }");
}

// -- 3: abbreviations compose ---------------------------------------------

// One abbreviation in another's body: conversion unfolds two δ steps.
#[test]
fn an_abbreviation_may_mention_another() {
    ok("fn Inner(n: Nat) -> Type { n = n }
        fn Outer(n: Nat) -> Type { (m: Nat) -> Inner(m) }
        theorem use_outer(n: Nat): Outer(n) { λ m => refl }");
}

// An abbreviation as a *hypothesis*, applied to reach the conclusion: the name
// appears in both directions, which is `refines_trans`'s shape.
#[test]
fn an_abbreviation_is_a_hypothesis_and_a_conclusion() {
    ok("fn Imp(a: Nat, b: Nat) -> Type { a = b -> b = a }
        theorem chain(a: Nat, b: Nat, h: Imp(a, b), p: a = b): b = a { h(p) }");
}

// -- 4: a declared type through an abbreviation ---------------------------

// A record's *value parameters* supplied through the name, and the record
// built in checking position against it. Construction reads every annotation
// off the expected type, and through a name that type arrives as **code** —
// so this is where a structural reader that does not decode goes wrong.
#[test]
fn a_record_is_built_against_an_abbreviated_type() {
    ok("record Halts(p: Nat) { n: Nat, h: n = p }
        fn Same(a: Nat, b: Nat) -> Type { Halts(a) -> Halts(b) }
        theorem id_halts(p: Nat): Same(p, p) { λ c => Halts(c.n, c.h) }");
}

// -- 5: the tag regression -------------------------------------------------

// The same shape at a **non-zero nominal tag**. `tag_value` walks the tag
// component of the expected type; through an abbreviation that component is
// `El` of a `Σ` code, and reading it as a `Unit` emits `⟨⟩` where a pair is
// needed. Tag 0's tag type *is* `Unit`, so the declaration order is the whole
// test: a single-declaration file cannot see this.
#[test]
fn a_record_at_a_nonzero_tag_is_built_against_an_abbreviated_type() {
    ok("record First() { z: Nat }
        record Halts(p: Nat) { n: Nat, h: n = p }
        fn Same(a: Nat, b: Nat) -> Type { Halts(a) -> Halts(b) }
        theorem id_halts(p: Nat): Same(p, p) { λ c => Halts(c.n, c.h) }");
}

// Tag 2 as well, so the test is about the tag's *shape* (a two-bit spine)
// rather than about the number 1.
#[test]
fn a_record_at_tag_two_is_built_against_an_abbreviated_type() {
    ok("record First() { z: Nat }
        record Second() { z: Nat }
        record Halts(p: Nat) { n: Nat, h: n = p }
        fn Same(a: Nat, b: Nat) -> Type { Halts(a) -> Halts(b) }
        theorem id_halts(p: Nat): Same(p, p) { λ c => Halts(c.n, c.h) }");
}

// A **tier-1** (recursive) inductive as a value parameter, so the abbreviated
// type's code contains a `Wf`. This is `Converges`'s shape in
// `lib/certgen/ir_v1.hthr`, minus the interpreter.
#[test]
fn a_recursive_value_parameter_survives_the_abbreviation() {
    ok("inductive Val { VNil, VCons(a: Nat, b: Val) }
        record Conv(p: Nat, env: Val) { n: Nat, h: n = p }
        fn Ref(a: Nat, b: Nat) -> Type { (env: Val) -> Conv(a, env) -> Conv(b, env) }
        theorem refl_ref(p: Nat): Ref(p, p) { λ env c => Conv(c.n, c.h) }
        theorem rebuild(p: Nat): Ref(p, p) { λ env c => Conv(c.n, c.h) }");
}

// -- 6: negative controls --------------------------------------------------

// Wrong arity at the use site. The abbreviation is an ordinary `fn`, so a
// partial application is an ordinary *value* — of type `Nat -> Type<0>`, which
// is not a universe — and the diagnostic is the type-position one rather than
// an arity one. Pinned as it is, not as one might wish it: the message is
// correct and unhelpful, and improving it is
// `issues/cli-check-diagnostics.md`'s, not this round's
// (`docs/types-as-expressions.md` §5).
#[test]
fn a_wrong_arity_use_is_rejected() {
    let msg = bad("fn P(n: Nat, m: Nat) -> Type { n = m }
                   theorem t(n: Nat): P(n) { refl }");
    assert!(msg.contains("this is not a type"), "{msg}");
}

// Over-application is the ordinary argument-count diagnostic, since it is an
// ordinary call that has too many arguments.
#[test]
fn an_over_applied_abbreviation_is_rejected() {
    let msg = bad("fn P(n: Nat) -> Type { n = n }
                   theorem t(n: Nat): P(n, n) { refl }");
    assert!(!msg.is_empty(), "{msg}");
}

// A **level** mismatch, which is the negative control the universe round's
// non-cumulativity makes possible: the body is a `Type<0>`, which lives at
// level 1, and the declared result type is `Type<0>`.
#[test]
fn a_level_mismatch_in_an_abbreviation_is_rejected() {
    let msg = bad("fn Bad() -> Type { Type }");
    assert!(msg.contains("non-cumulative"), "{msg}");
    ok("fn Good() -> Type<1> { Type }");
}

// A `fn` whose result type is *not* a universe cannot have a type as its body:
// the bridge is an opportunity, not a claim (`docs/surface-universe.md` §12.3).
#[test]
fn a_type_body_at_a_non_universe_result_is_rejected() {
    let msg = bad("fn Bad() -> Nat { Nat -> Nat }");
    assert!(!msg.is_empty(), "{msg}");
}

// The abbreviation is not *transparently* something else: a wrong inhabitant
// is still rejected through the name. Axis 4 — a positive test alone cannot
// tell an abbreviation from anything it happens to unfold to.
#[test]
fn a_wrong_inhabitant_is_rejected_through_the_name() {
    let msg = bad("fn P(n: Nat) -> Type { n = Succ(n) }
                   theorem t(n: Nat): P(n) { refl }");
    assert!(!msg.is_empty(), "{msg}");
}

// A use in *term* position, where a term is expected: `P(n)` is a code, so it
// is a `Ty 0` and not a `Nat`.
#[test]
fn an_abbreviation_is_not_a_term_of_its_own_type() {
    let msg = bad("fn P(n: Nat) -> Type { n = n }
                   theorem t(n: Nat): Nat { P(n) }");
    assert!(!msg.is_empty(), "{msg}");
}

// -- 7: the acceptance customer, in miniature ------------------------------

// `Refines` as `lib/certgen/ir_v1.hthr` now spells it: a four-parameter type-valued
// `fn` whose body is a chain of implications between record formations, used
// as hypothesis, conclusion, and the thing a λ is checked against — all at
// **neutral** arguments.
#[test]
fn the_refines_shape_is_nameable() {
    ok("inductive Val { VNil, VCons(a: Nat, b: Val) }
        inductive Ir { INil, ICons(a: Nat, b: Ir) }
        record Converges(p: Nat, env: Val, ir: Ir, vs: Val) { n: Nat, h: n = p }
        fn Refines(p1: Nat, i1: Ir, p2: Nat, i2: Ir) -> Type {
            (env: Val) -> (vs: Val)
            -> Converges(p1, env, i1, vs) -> Converges(p2, env, i2, vs)
        }
        theorem refines_refl(p: Nat, i: Ir): Refines(p, i, p, i)
        { λ env vs c => c }
        theorem refines_trans(p1: Nat, i1: Ir, p2: Nat, i2: Ir, p3: Nat, i3: Ir,
                              r1: Refines(p1, i1, p2, i2),
                              r2: Refines(p2, i2, p3, i3))
            : Refines(p1, i1, p3, i3)
        { λ env vs c => r2(env, vs, r1(env, vs, c)) }");
}
