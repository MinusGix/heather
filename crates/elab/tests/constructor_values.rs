//! Acceptance for constructors as function values, against the checklist of
//! `docs/constructor-function-values.md` §4. Tracking issue:
//! `issues/constructors-as-function-values.md`.
//!
//! Two independent halves: `Succ` becomes a name (§2.1), and a declared
//! constructor η-expands against an expected `Π` (§2). Every positive test is
//! elaborated and then re-checked by the real kernel, so a wrong η-expansion —
//! arguments in the wrong holes, a domain quietly mismatched — shows up as a
//! rejection rather than as a passing test.

use heather_elab::{ElabError, Elaborator};

fn elab(src: &str) -> Elaborator {
    let mut e = Elaborator::with_prelude().expect("prelude");
    e.elab_source(src).unwrap_or_else(|err| panic!("{}", err.render(src)));
    e
}

fn elab_err(src: &str) -> String {
    let mut e = Elaborator::with_prelude().expect("prelude");
    match e.elab_source(src) {
        Err(ElabError::Elab { msg, .. }) => msg,
        Err(other) => format!("{other}"),
        Ok(()) => panic!("expected an error, but this elaborated:\n{src}"),
    }
}

// §4.1–2 — the builtin. `Succ` passed as an argument, written at an annotated
// type, and η-convertible with its own lambda.
#[test]
fn succ_is_a_function_value() {
    elab(
        r#"
        fn twice(f: Nat -> Nat, n: Nat) -> Nat { f(f(n)) }

        theorem passed(): twice(Succ, 0) = 2 { refl }
        theorem open(n: Nat): twice(Succ, n) = Succ(Succ(n)) { refl }

        // bare, at a written function type
        fn s() -> Nat -> Nat { Succ }
        theorem applied(): s()(3) = 4 { refl }

        // η against the builtin (the `eta_*` family of function_types.rs, at
        // the one head that was not a name until now)
        theorem eta(): (λ (x: Nat) => Succ(x)) = Succ { refl }
        "#,
    );
}

// §4.3 — **the payoff.** `.cong(Succ)`, the spelling
// `issues/surface-operators.md` deferred and `surface-function-types` only
// half-delivered. Note the position: `cong` has implicit endpoints, so the
// argument is *inferred*, not checked — this works because `Succ`'s type is a
// constant (§2.1), and would not for a declared constructor.
#[test]
fn cong_at_succ_by_name() {
    elab(
        r#"
        theorem cong(f: Nat -> Nat, {a: Nat}, {b: Nat}, p: a = b): f(a) = f(b)
        { j(p, (y, q) -> f(a) = f(y), refl) }

        theorem method(n: Nat, m: Nat, p: n = m): Succ(n) = Succ(m)
        { p.cong(Succ) }

        theorem call(n: Nat, m: Nat, p: n = m): Succ(n) = Succ(m)
        { cong(Succ, p) }
        "#,
    );
}

// §4.4 — a declared tier-0 constructor, η-expanded against the parameter's
// domain.
#[test]
fn a_declared_constructor_is_a_function_value() {
    elab(
        r#"
        inductive Box { Wrap(Nat) }

        fn ap(f: Nat -> Box, n: Nat) -> Box { f(n) }
        fn unbox(b: Box) -> Nat { match b { Wrap(x) => x } }

        theorem t(): unbox(ap(Wrap, 1)) = 1 { refl }

        // bare, at a written function type, and η-convertible with the lambda
        fn w() -> Nat -> Box { Wrap }
        theorem applied(n: Nat): w()(n) = Wrap(n) { refl }
        theorem eta(): (λ (x: Nat) => Wrap(x)) = Wrap { refl }
        "#,
    );
}

// §4.5 — partial application: the same feature, with the argument list
// starting non-empty. `Cons(1)` is tier 1, so this also covers a `sup_f`
// payload built under a λ.
#[test]
fn a_constructor_partially_applies() {
    elab(
        r#"
        inductive List { Nil, Cons(Nat, List) }

        fn ap(f: List -> List, xs: List) -> List { f(xs) }

        theorem t(): Cons(1)(Nil) = Cons(1, Nil) { refl }
        theorem through(xs: List): ap(Cons(1), xs) = Cons(1, xs) { refl }

        // the curried spelling in checking position, and re-applied twice
        fn one() -> List -> List { Cons(1) }
        theorem curried(xs: List): one()(xs) = Cons(1, xs) { refl }
        theorem nested(): Cons(1)(Cons(2)(Nil)) = Cons(1, Cons(2, Nil)) { refl }
        "#,
    );
}

// §4.6 — a parameterized declaration. The type arguments come off the
// expected type (they are monomorphized, never inferred:
// `docs/inductive-tier0-lowering.md` §2), so the *same* constructor is a
// function value at two instantiations in one file.
#[test]
fn a_parameterized_constructor_takes_its_arguments_from_the_expected_type() {
    elab(
        r#"
        inductive Bool { True, False }
        inductive Option<A> { None, Some(A) }

        fn or_else(d: Nat, o: Option<Nat>) -> Nat {
            match o { None => d, Some(x) => x }
        }
        fn is_set(o: Option<Bool>) -> Bool {
            match o { None => False, Some(b) => b }
        }

        fn apn(f: Nat -> Option<Nat>, n: Nat) -> Option<Nat> { f(n) }
        fn apb(f: Bool -> Option<Bool>, b: Bool) -> Option<Bool> { f(b) }

        theorem at_nat(): or_else(0, apn(Some, 5)) = 5 { refl }
        theorem at_bool(): is_set(apb(Some, True)) = True { refl }
        "#,
    );
}

// §4.7 — tier 1, a plain child: the synthetic argument is checked against
// `⟦D⟧` by `build_children`, the same path an open child already takes.
#[test]
fn a_tier1_child_field_eta_expands() {
    elab(
        r#"
        inductive Tree { Leaf, Node(Tree, Tree) }

        fn ap(f: Tree -> Tree, t: Tree) -> Tree { f(t) }

        theorem t(x: Tree): ap(Node(Leaf), x) = Node(Leaf, x) { refl }
        theorem both(x: Tree): Node(x)(x) = Node(x, x) { refl }

        fn add(a: Nat, b: Nat) -> Nat {
            match b { Zero => a, Succ(k) => Succ(add(a, k)) }
        }
        fn size(t: Tree) -> Nat {
            match t { Leaf => 1, Node(l, r) => Succ(add(size(l), size(r))) }
        }
        theorem computes(): size(ap(Node(Leaf), Leaf)) = 3 { refl }
        "#,
    );
}

// §4.8–9 — tier 1, a container field: the missing argument is a *vector*
// variable, whose length is still projected out of the label just built. And
// the dependent case, where the length itself is a peeled binder — the
// codomain is used under it, which is the whole reason peeling pushes into the
// context rather than counting arrows.
#[test]
fn a_container_field_eta_expands_dependently() {
    elab(
        r#"
        inductive Rose { Node(label: Nat, len: Nat, kids: [Rose; len]) }

        fn ap(f: [Rose; 1] -> Rose, ks: [Rose; 1]) -> Rose { f(ks) }

        theorem one(k: Rose): ap(Node(0, 1), [k]) = Node(0, 1, [k]) { refl }

        // the length is a binder of the expected type, and the field after it
        // depends on it
        fn mk() -> (n: Nat) -> [Rose; n] -> Rose { Node(7) }
        theorem dep(k: Rose): mk()(1)([k]) = Node(7, 1, [k]) { refl }
        theorem dep0(): mk()(0)([]) = Node(7, 0, []) { refl }
        "#,
    );
}

// §4.10 — the rejections.
#[test]
fn rejections() {
    // Not enough arrows to absorb the missing fields: counted against what the
    // expected type provides, not against what the user wrote.
    let msg = elab_err(
        r#"
        inductive List { Nil, Cons(Nat, List) }
        fn f() -> Nat -> List { Cons }
        "#,
    );
    assert!(msg.contains("`Cons` needs 2 more argument(s)"), "{msg}");
    assert!(msg.contains("provides only 1"), "{msg}");

    // A non-function expected type is the pre-existing arity error, unchanged.
    let msg = elab_err(
        r#"
        inductive Box { Wrap(Nat) }
        fn f() -> Box { Wrap }
        "#,
    );
    assert!(msg.contains("`Wrap` takes 1 argument(s), found 0"), "{msg}");

    // …and a constructor of the wrong declaration still says so.
    let msg = elab_err(
        r#"
        inductive Box { Wrap(Nat) }
        inductive Crate { Pack(Nat) }
        fn f() -> Nat -> Box { Pack }
        "#,
    );
    assert!(msg.contains("`Pack` is a constructor of `Crate`"), "{msg}");

    // Inference position stays rejected, and points at the annotation (§3).
    let msg = elab_err(
        r#"
        inductive Box { Wrap(Nat) }
        fn f(n: Nat) -> Box { let g = Wrap; g(n) }
        "#,
    );
    assert!(msg.contains("`Wrap` takes 1 argument(s), found 0"), "{msg}");
}

// **The negative control**, and the reason §2.2 argues rather than asserts: a
// peeled domain that disagrees with the field it fills must be a *rejection*.
// If the η arm read the field types off the peeled domains instead of off the
// encoding, this would elaborate — a `Box` built from a `Bool`, i.e. the
// hazard class `docs/inductive-tier0-lowering.md` opens by naming.
#[test]
fn a_domain_that_disagrees_with_its_field_is_rejected() {
    let msg = elab_err(
        r#"
        inductive Bool { True, False }
        inductive Box { Wrap(Nat) }

        fn ap(f: Bool -> Box, b: Bool) -> Box { f(b) }
        fn bad(b: Bool) -> Box { ap(Wrap, b) }
        "#,
    );
    assert!(msg.contains("NotConvertible") || msg.contains("kernel"), "{msg}");
}
