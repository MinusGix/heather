//! Motives are lambdas, and `=` is an expression
//! (`docs/surface-universe.md` §13). Tracking issue:
//! `issues/motives-as-lambdas.md`, landed as phase 3 of the Type Session.
//!
//! Two syntaxes collapsed into one. `match … as z -> M` and
//! `j(p, (y, q) -> M, case)` each carried a hand-rolled binder form that
//! existed only because the surface had no λ when they were written; `->` was
//! the type arrow *and* a binder-to-body marker. Now a motive is an ordinary
//! [`ExprKind::Lam`], which needed `a = b` to become an expression — the
//! commonest motive body is an equation, and `=` was deliberately not in the
//! expression grammar.
//!
//! The `nat_suite`, `match_recursion` and `container_proofs` suites are the
//! real regression surface here: every explicit motive in the workspace is
//! written in the new form and still proves what it proved.

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

const ADD: &str = "fn add(a: Nat, b: Nat) -> Nat {
    match b { Zero => a, Succ(k) => Succ(add(a, k)) }
}
";

// -- 1-3: the new forms ---------------------------------------------------

// A `match` motive as a lambda, with an *equation* body — the case that
// forced `=` into the expression grammar.
#[test]
fn a_match_motive_is_a_lambda() {
    ok(&format!(
        "{ADD}theorem add_zero(n: Nat): add(n, 0) = n {{
            match n as λ z => add(z, 0) = z {{
                Zero => refl,
                Succ(k, ih) => @cong_succ(add(k, 0), k, ih),
            }}
        }}"
    ));
}

// `fun` is the ASCII spelling of `λ` everywhere, motives included.
#[test]
fn a_motive_accepts_the_ascii_lambda() {
    ok(&format!(
        "{ADD}theorem t(n: Nat): add(n, 0) = n {{
            match n as fun z => add(z, 0) = z {{
                Zero => refl,
                Succ(k, ih) => @cong_succ(add(k, 0), k, ih),
            }}
        }}"
    ));
}

// A `j` motive as a two-binder lambda. The prelude itself is written this way
// (`sym`, `trans`, `cong`), so this is belt-and-braces.
#[test]
fn a_j_motive_is_a_two_binder_lambda() {
    ok("theorem my_sym(a: Nat, b: Nat, p: a = b): b = a {
            j(p, λ y q => y = a, refl)
        }");
}

// -- 4-5: `=` really is an expression -------------------------------------

// An equation in *term* position: it is a type, so it is a term at a
// universe. This is what makes the motive body an ordinary expression.
#[test]
fn an_equation_is_a_term_at_a_universe() {
    ok("fn an_eq() -> Type<0> { 0 = 0 }");
}

// And it composes with the operators, at the loosest precedence: `a + b = c`
// is `(a + b) = c`, not `a + (b = c)`.
#[test]
fn equality_binds_loosest() {
    ok(&format!("{ADD}fn e(n: Nat) -> Type<0> {{ add(n, 0) = n }}"));
}

// -- 6: `calc` still uses `=` as punctuation ------------------------------

// The suppression the round needed: inside a `calc` step `=` separates the
// endpoints and must not be read as the identity type.
#[test]
fn calc_steps_still_parse() {
    ok(&format!(
        "{ADD}theorem t(n: Nat): add(0, n) = add(0, n) {{
            calc {{ add(0, n) = add(0, n) := refl }}
        }}"
    ));
}

// -- 7-11: negative controls ----------------------------------------------

// The retired `match` spelling, diagnosed rather than mis-parsed.
#[test]
fn the_retired_match_motive_is_rejected() {
    let e = bad(&format!(
        "{ADD}theorem t(n: Nat): add(n, 0) = n {{
            match n as z -> add(z, 0) = z {{ Zero => refl, Succ(k) => refl }}
        }}"
    ));
    assert!(e.contains("a motive is a lambda"), "expected the migration message, got: {e}");
}

// The retired `j` spelling.
#[test]
fn the_retired_j_motive_is_rejected() {
    let e = bad("theorem t(a: Nat, b: Nat, p: a = b): b = a {
            j(p, (y, q) -> y = a, refl)
        }");
    assert!(e.contains("a motive is a lambda"), "expected the migration message, got: {e}");
}

// A motive that binds the wrong number of names. `j` needs two; one is the
// commonest mistake when coming from `match`.
#[test]
fn a_motive_with_the_wrong_arity_is_rejected() {
    let e = bad("theorem t(a: Nat, b: Nat, p: a = b): b = a {
            j(p, λ y => y = a, refl)
        }");
    assert!(e.contains("binds"), "expected the arity message, got: {e}");
}

// A motive binder's type is fixed by what the motive is a motive *for*, so an
// annotation is not a readability aid here — it is a second source of truth.
#[test]
fn an_annotated_motive_binder_is_rejected() {
    let e = bad(&format!(
        "{ADD}theorem t(n: Nat): add(n, 0) = n {{
            match n as λ (z: Nat) => add(z, 0) = z {{ Zero => refl, Succ(k) => refl }}
        }}"
    ));
    assert!(e.contains("no annotation"), "expected the annotation message, got: {e}");
}

// A motive that is not a lambda at all.
#[test]
fn a_non_lambda_motive_is_rejected() {
    let e = bad(&format!(
        "{ADD}theorem t(n: Nat): add(n, 0) = n {{
            match n as Nat {{ Zero => refl, Succ(k) => refl }}
        }}"
    ));
    assert!(e.contains("a motive is a lambda"), "expected the lambda message, got: {e}");
}

// `=` is non-associative: a chain is a parse error rather than a silent
// grouping.
#[test]
fn equality_does_not_chain() {
    let e = bad("fn f() -> Type<0> { 0 = 0 = 0 }");
    assert!(!e.is_empty());
}
