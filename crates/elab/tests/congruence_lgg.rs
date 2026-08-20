//! Congruence with an *implicit* function, inferred from the expected type by
//! anti-unification (issues/congruence-by-anti-unification.md, interim round).
//!
//! The rule is checking-position-only and structurally triggered: an
//! implicit-inserting call whose result type is `?f(s) = ?f(t)` with `s`, `t`
//! meta-free, against an expected `Id`. Nothing is keyed to the name `cong` —
//! the prelude's declaration is an ordinary theorem, and any declaration of
//! that shape gets the same treatment.
//!
//! The axes of docs/testing-generated-terms.md, each with its own test:
//! literal *and* neutral endpoints, an **open** element type (a type
//! parameter, and a goal at a function type), checking position against
//! inference position, and negative controls for each way the rule declines.
//! Acceptance is what is asserted throughout: `elab_source` kernel-checks
//! every declaration, so a wrongly solved `?f` would be a rejection here
//! rather than a silent pass.

use heather_elab::{ElabError, Elaborator};

fn ok(src: &str) {
    let mut e = Elaborator::with_prelude().expect("prelude");
    if let Err(err) = e.elab_source(src) {
        panic!("must elaborate and kernel-check, got: {err:?}");
    }
}

fn fails(src: &str) -> String {
    let mut e = Elaborator::with_prelude().expect("prelude");
    match e.elab_source(src) {
        Ok(()) => panic!("must not elaborate"),
        Err(ElabError::Elab { msg, .. }) => msg,
        Err(other) => panic!("expected an elaboration error, got: {other:?}"),
    }
}

// -- the rule fires ---------------------------------------------------------

#[test]
fn literal_endpoints() {
    // `LGG(Succ 0, Succ 1) = Succ(□)`, `□ ↦ (0, 1)` — the issue's own example.
    ok("theorem t(p: 0 = 1): Succ(0) = Succ(1) { cong(p) }");
}

#[test]
fn neutral_endpoints() {
    // The same with *variable* endpoints: nothing here reduces, so a rule
    // that only worked on closed numerals would be caught by this and by
    // nothing above it.
    ok("theorem t(a: Nat, b: Nat, p: a = b): Succ(a) = Succ(b) { cong(p) }");
}

#[test]
fn open_element_type() {
    // The endpoints live at a *type parameter*, so neither the element type
    // nor the goal is closed: `A` comes from the proof, `B` only from the
    // expected type, and `f` only from anti-unifying it.
    ok(r#"
    theorem t<A>(g: A -> A, a: A, b: A, p: a = b): g(a) = g(b) { cong(p) }
    "#);
}

#[test]
fn open_element_type_at_a_different_codomain() {
    // `A -> B` with the two distinct, which is what makes `B` a real
    // inference obligation rather than a copy of `A`.
    ok(r#"
    theorem t<A, B>(g: A -> B, a: A, b: A, p: a = b): g(a) = g(b) { cong(p) }
    "#);
}

#[test]
fn open_element_type_mentions_an_ambient_variable() {
    // Axis 2 of docs/testing-generated-terms.md, the one closed types hide: a
    // shift error in the abstraction's *domain* is the identity at `Nat` and
    // visible at `Fin(m)`, whose code mentions the ambient `m`. The domain is
    // read off `?f`'s declared parameter type and lands under a fresh binder,
    // so this is exactly the position a shift can be wrong in.
    ok(r#"
    theorem t(m: Nat, g: Fin(m) -> Nat, xs: Fin(m), ys: Fin(m), p: xs = ys):
        g(xs) = g(ys)
    {
        cong(p)
    }
    "#);
}

#[test]
fn multiple_occurrences() {
    // §6: LGG abstracts *every* differing position, so `add(a,a) = add(b,b)`
    // yields `λz. add(z, z)` — a correct congruence, and a different theorem
    // from congruence in one argument.
    ok(r#"
    fn add(m: Nat, n: Nat) -> Nat { match m { Zero => n, Succ(k, ih) => Succ(ih) } }
    theorem t(a: Nat, b: Nat, p: a = b): add(a, a) = add(b, b) { cong(p) }
    "#);
}

#[test]
fn hole_under_a_binder() {
    // The differing position sits under a λ, so the witness is `a`/`b`
    // weakened by one and the abstraction variable lands at index 1
    // (decision 3). The goal is an equation between *functions*, which also
    // makes `B` a function type.
    ok(r#"
    fn add(m: Nat, n: Nat) -> Nat { match m { Zero => n, Succ(k, ih) => Succ(ih) } }
    theorem t(a: Nat, b: Nat, p: a = b):
        (λ (x: Nat) => add(x, a)) = (λ (x: Nat) => add(x, b))
    {
        cong(p)
    }
    "#);
}

#[test]
fn zero_holes_is_the_constant_congruence() {
    // `X ≡ Y` — no position differs, so `λz. Succ(0)` is the answer and the
    // proof is discarded (decision 5). Uninteresting and correct; the point
    // is that it is not an *error*.
    ok("theorem t(p: 0 = 1): Succ(0) = Succ(0) { cong(p) }");
}

#[test]
fn nested_under_a_constructor_spine() {
    // Two constructor layers deep: the walk has to descend through both and
    // find the hole at the bottom.
    ok("theorem t(a: Nat, b: Nat, p: a = b): Succ(Succ(a)) = Succ(Succ(b)) { cong(p) }");
}

#[test]
fn the_explicit_spelling_still_works() {
    // `@cong(f, a, b, p)` gives every implicit positionally — the rule is an
    // addition, not a replacement, and this is the spelling inference
    // position still needs.
    ok(r#"
    theorem t(a: Nat, b: Nat, p: a = b): Succ(a) = Succ(b) {
        @cong(λ (x: Nat) => Succ(x), a, b, p)
    }
    "#);
}

// -- negative controls ------------------------------------------------------

#[test]
fn inference_position_still_fails() {
    // The whole rule is checking-only: an unannotated `let` has no expected
    // type to anti-unify against, so the pre-existing message stands.
    let msg = fails(
        r#"
    theorem t(a: Nat, b: Nat, p: a = b): Succ(a) = Succ(b) {
        { let q = cong(p); q }
    }
    "#,
    );
    assert!(
        msg.contains("could not infer the implicit argument `f`"),
        "expected the pre-existing message, got: {msg}"
    );
}

#[test]
fn witness_mismatch_is_loud() {
    // `Succ(0) = Succ(1)` from `p : 0 = 2`: the differing position's witness
    // is `(0, 1)`, which is not the proof's `(0, 2)`. Once the trigger has
    // fired the failure is *this* message — not "could not infer", and not a
    // kernel error about a term nobody wrote.
    let msg = fails("theorem t(p: 0 = 2): Succ(0) = Succ(1) { cong(p) }");
    assert!(msg.contains("cannot generalize"), "expected the LGG message, got: {msg}");
    assert!(
        msg.contains("congruence-by-anti-unification"),
        "the message should cite the rule, got: {msg}"
    );
}

#[test]
fn a_captured_witness_is_refused() {
    // Under the λ the differing position is the *bound* variable on the left
    // and `b` on the right. No shift of `a` is the bound variable, so the
    // rule refuses rather than capturing (decision 3).
    let msg = fails(
        r#"
    theorem t(a: Nat, b: Nat, p: a = b):
        (λ (x: Nat) => x) = (λ (x: Nat) => b)
    {
        cong(p)
    }
    "#,
    );
    assert!(msg.contains("cannot generalize"), "expected the LGG message, got: {msg}");
}

#[test]
fn sides_differ_beyond_the_witness() {
    // Two differing positions, only one of them witnessed by the proof.
    let msg = fails(
        r#"
    fn add(m: Nat, n: Nat) -> Nat { match m { Zero => n, Succ(k, ih) => Succ(ih) } }
    theorem t(a: Nat, b: Nat, p: a = b): add(a, 0) = add(b, 1) { cong(p) }
    "#,
    );
    assert!(msg.contains("cannot generalize"), "expected the LGG message, got: {msg}");
}

#[test]
fn expected_not_an_id_leaves_the_old_error() {
    // The trigger needs an `Id` on *both* sides. At a `Nat` goal the rule
    // does not fire at all and the pre-existing diagnostic is preserved.
    let msg = fails(
        r#"
    fn t(a: Nat, b: Nat, p: a = b) -> Nat { cong(p) }
    "#,
    );
    assert!(
        msg.contains("could not infer the implicit argument `f`"),
        "expected the pre-existing message, got: {msg}"
    );
}

#[test]
fn the_lgg_trigger_precedes_the_general_harvest() {
    // Since the expected-type harvest became general
    // (docs/unifier-completeness-design.md §5.2), a shape matching both the
    // flex-`Id` trigger and a would-be first-order reading must still take
    // the LGG: `λz. add(z, 0)` is the congruence, where peeling would have
    // guessed `add(a)` and died at the kernel.
    ok(r#"
    fn add(m: Nat, n: Nat) -> Nat { match m { Zero => n, Succ(k, ih) => Succ(ih) } }
    theorem t(a: Nat, b: Nat, p: a = b): add(a, 0) = add(b, 0) { cong(p) }
    "#);
}

#[test]
fn other_implicits_are_untouched() {
    // A call with a *different* unsolved implicit in checking position gets
    // no help from the rule: the trigger is `?f(s) = ?f(t)` and nothing else
    // resembles it. (`sym`'s endpoints come from its proof, so this is really
    // a check that the hook cannot fire spuriously and mis-solve.)
    ok("theorem t(a: Nat, b: Nat, p: a = b): b = a { sym(p) }");
}

// -- inside a `trans` chain -------------------------------------------------
//
// docs/congruence-in-inference-position-design.md. A call whose callee has a
// **result-only implicit** — one no explicit parameter's domain mentions — is
// checking-only, so `trans`'s argument is elaborated after its sibling and at
// the domain the sibling determined. Two thirds of the library's congruence
// sites are this shape and none of them elaborated before.

#[test]
fn first_argument_of_a_trans_chain() {
    // `cong(p)`'s goal is `Succ(a) = ?b`: the expected type of the `trans`
    // pins the *outer* endpoints and never the middle one, so this works only
    // because `q` runs first and its type is what says `?b := Succ(b)`.
    ok(r#"
    theorem t(a: Nat, b: Nat, c: Nat, p: a = b, q: Succ(b) = c): Succ(a) = c {
        trans(cong(p), q)
    }
    "#);
}

#[test]
fn second_argument_of_a_trans_chain() {
    // The mirror image, and it is *not* the same test: here the middle
    // endpoint comes from the first argument and the far endpoint from the
    // expected type, so it exercises the expected-type harvest running before
    // the deferred retry rather than the sibling's inferred type.
    ok(r#"
    theorem t(a: Nat, b: Nat, c: Nat, p: c = Succ(a), q: a = b): c = Succ(b) {
        trans(p, cong(q))
    }
    "#);
}

#[test]
fn trans_chain_at_an_open_element_type() {
    // Axis 2 of docs/testing-generated-terms.md at the new position: the
    // deferral has to carry an element type that is a *parameter*, and a
    // codomain `B` that only the expected type mentions.
    ok(r#"
    theorem t<A, B>(g: A -> B, a: A, b: A, c: B, p: a = b, q: g(b) = c): g(a) = c {
        trans(cong(p), q)
    }
    "#);
}

#[test]
fn a_goal_that_only_reduction_spells_through_the_context() {
    // The second attempt (design §3): `g2(a)` names no congruence context in
    // its syntax, and one whnf apiece turns both sides into `Succ(Succ(□))`.
    // The syntactic attempt runs first and fails here, so this is the *only*
    // test that reaches the reduced one.
    ok(r#"
    fn g2(n: Nat) -> Nat { Succ(Succ(n)) }
    theorem t(a: Nat, b: Nat, p: a = b): g2(a) = Succ(Succ(b)) { cong(p) }
    "#);
}

#[test]
fn a_chain_the_deferral_cannot_reach_keeps_the_old_message() {
    // The strict-additivity claim (design §2). The *inner* `trans` is itself
    // in inference position, so its middle endpoint is determined by nothing
    // and its `cong(q)` can never become ready. The obligation falls back to
    // inference — the path this call took before the rule existed — and the
    // reader gets the message they got before, not a report about deferral.
    let msg = fails(
        r#"
    theorem t(a: Nat, b: Nat, c: Nat, d: Nat,
              p: a = b, q: b = c, r: Succ(c) = d): Succ(a) = d {
        trans(cong(p), trans(cong(q), r))
    }
    "#,
    );
    assert!(
        msg.contains("could not infer the implicit argument `f`"),
        "expected the pre-existing message, got: {msg}"
    );
}

#[test]
fn a_witness_mismatch_inside_a_chain_is_still_loud() {
    // The negative control for the deferral: reaching checking position must
    // not make the rule *lenient*. `Succ(Succ(a)) = ?b` against `p : a = b`
    // has a differing position whose witness is not the proof's, and that is
    // reported rather than swallowed back into "could not infer".
    let msg = fails(
        r#"
    theorem t(a: Nat, b: Nat, c: Nat, p: a = b, q: Succ(b) = c):
        Succ(Succ(a)) = c
    {
        trans(cong(p), q)
    }
    "#,
    );
    assert!(msg.contains("cannot generalize"), "expected the LGG message, got: {msg}");
}

// -- the diagnostic (issues/lgg-diagnostic-dumps-kernel-terms.md) -----------

/// Every kernel term the message used to print, at the goal where that was a
/// wall: a **lowered inductive**. Four `{:?}`d terms there are four
/// multi-thousand-character `inl[0,0](Σ[0,0](Unit 0). …)` dumps, and the one
/// fact the reader wants — where the walk stopped — was not recoverable from
/// any of them.
///
/// The assertions are the halves of the fix plus one bound: the position, the
/// goal spelled as surface, the endpoints spelled as surface, and *no kernel
/// encoding at all*. A `Nat` goal would have hidden every one of them
/// (`docs/testing-generated-terms.md`: three of five past defects here were
/// invisible at a closed simple type), which is why the carrier is a tree.
#[test]
fn the_mismatch_at_a_lowered_inductive_is_readable() {
    let msg = fails(
        r#"
    inductive Tree { Leaf, Node(l: Tree, r: Tree) }
    theorem t(a: Tree, b: Tree, p: a = b):
        Node(a, Leaf) = Node(b, Node(Leaf, Leaf))
    {
        cong(p)
    }
    "#,
    );
    assert!(msg.contains("cannot generalize"), "{msg}");
    // Where the walk stopped: it agreed down a path and differed under it.
    assert!(msg.contains("agree down through"), "{msg}");
    // The endpoints, by name rather than by encoding.
    assert!(msg.contains("the proof's endpoints are `a` and `b`"), "{msg}");
    assert!(
        msg.contains("The goal is `Node(a, Leaf) = Node(b, Node(Leaf, Leaf))`"),
        "{msg}"
    );
    // And no kernel encoding: these are the fragments the dump was made of.
    for wall in ["inl[", "inr[", "Σ[", "«", "El["] {
        assert!(!msg.contains(wall), "the message still prints kernel syntax ({wall}): {msg}");
    }
    // The bound that says it is a sentence and not a dump. The walls ran to
    // several thousand characters; a readable diagnostic is two lines.
    assert!(msg.len() < 600, "the message is {} chars: {msg}", msg.len());
}

/// The goal clause at a flat lowered inductive remains covered separately.
#[test]
fn the_diagnostic_states_the_goal_where_it_spells() {
    let msg = fails(
        r#"
    inductive Col { Red, Green }
    fn same(c: Col) -> Col { c }
    theorem t(a: Col, b: Col, p: a = b): same(a) = Red { cong(p) }
    "#,
    );
    assert!(msg.contains("cannot generalize"), "{msg}");
    assert!(msg.contains("The goal is `same(a) = Red`"), "{msg}");
    assert!(msg.contains("the proof's endpoints are `a` and `b`"), "{msg}");
    assert!(msg.len() < 600, "the message is {} chars: {msg}", msg.len());
}

/// The same claim where the walk stops **under a binder** — the case whose two
/// sides cannot be spelled at all: a subterm mentioning the λ's own variable
/// has no reading in the reader's context, and inventing one would name their
/// variables wrongly. The position and the goal are still named, which is the
/// point: the message degrades by a clause, not into a dump.
#[test]
fn a_mismatch_under_a_binder_still_names_the_position() {
    let msg = fails(
        r#"
    theorem t(a: Nat, b: Nat, p: a = b):
        (λ (x: Nat) => x) = (λ (x: Nat) => b)
    {
        cong(p)
    }
    "#,
    );
    assert!(msg.contains("cannot generalize"), "{msg}");
    assert!(msg.contains("λ"), "the path should reach the λ: {msg}");
    assert!(msg.len() < 600, "the message is {} chars: {msg}", msg.len());
}
