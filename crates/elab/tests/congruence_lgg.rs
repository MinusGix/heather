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
fn other_implicits_are_untouched() {
    // A call with a *different* unsolved implicit in checking position gets
    // no help from the rule: the trigger is `?f(s) = ?f(t)` and nothing else
    // resembles it. (`sym`'s endpoints come from its proof, so this is really
    // a check that the hook cannot fire spuriously and mis-solve.)
    ok("theorem t(a: Nat, b: Nat, p: a = b): b = a { sym(p) }");
}
