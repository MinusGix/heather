//! A structurally recursive `fn` means what its source means
//! (issues/recursive-arm-reads-outer-scrutinee.md).
//!
//! The recursion is compiled at the `match`: a self-call is the eliminator's
//! hypothesis, i.e. *the `match` at the smaller value*, and everything outside
//! the `match` is evaluated once, by the top call. Each shape below used to
//! elaborate and compute a different value from its source, pinned by `refl`
//! (`sum(2) = 4` for a source that means 3); it is now refused by name. The
//! accepted cases are the spellings the messages point at, and the
//! near-misses that were never wrong: a parameter passed along unchanged, a
//! varying accumulator, a `match` with no self-call, a theorem. That
//! `decreases` recursion already computes the source's value is recorded in
//! the issue's log; it needs `import nat`, which this harness does not load.

use heather_elab::{ElabError, Elaborator};

const ADD: &str =
    "fn add(a: Nat, b: Nat) -> Nat { match b { Zero => a, Succ(k) => Succ(add(a, k)) } }\n";

fn ok(src: &str) {
    let mut e = Elaborator::with_prelude().expect("prelude");
    if let Err(err) = e.elab_source(src) {
        panic!("expected success, got: {}", err.render(src));
    }
}

fn bad(src: &str) -> String {
    let mut e = Elaborator::with_prelude().expect("prelude");
    match e.elab_source(src) {
        Ok(()) => panic!("expected a rejection, but it elaborated:\n{src}"),
        Err(ElabError::Elab { msg, .. }) => msg,
        Err(ElabError::Parse(p)) => p.msg,
        Err(other) => format!("{other}"),
    }
}

fn refused(src: &str, needle: &str) {
    let m = bad(&format!("{ADD}{src}"));
    assert!(m.contains(needle), "wrong refusal for\n{src}\n---\n{m}");
    assert!(m.contains("recursive-arm-reads-outer-scrutinee"), "{m}");
}

// -- M1: the parameter, read inside its own recursive `match` ----------------

#[test]
fn the_parameter_in_its_own_arm_is_refused() {
    refused(
        "fn sum(n: Nat) -> Nat { match n { Zero => 0, Succ(k) => add(sum(k), n) } }",
        "`n` inside its own recursive `match`",
    );
    // The base arm too: it runs at the bottom level, where `n` is not zero.
    refused(
        "fn f(n: Nat) -> Nat { match n { Zero => n, Succ(k) => f(k) } }",
        "`n` inside its own recursive `match`",
    );
    // Two levels down, through the course-of-values chain.
    refused(
        "fn h(n: Nat) -> Nat {
             match n { Zero => 0, Succ(k) => match k { Zero => 1, Succ(j) => add(h(j), n) } }
         }",
        "`n` inside its own recursive `match`",
    );
    // Under a λ in the arm: still the top call's `n`.
    refused(
        "fn g(n: Nat) -> Nat { match n { Zero => 0, Succ(k) => (\u{3bb} (x: Nat) => add(x, n))(g(k)) } }",
        "`n` inside its own recursive `match`",
    );
}

#[test]
fn a_binding_of_the_parameter_above_the_match_is_refused() {
    refused(
        "fn g(n: Nat) -> Nat { let m = n; match n { Zero => 0, Succ(k) => add(g(k), m) } }",
        "`m` is bound from `n` above its recursive `match`",
    );
    refused(
        "fn g(n: Nat) -> Nat { have m = n; match n { Zero => 0, Succ(k) => add(g(k), m) } }",
        "`m` is a `have` bound above the recursive `match`",
    );
}

#[test]
fn a_declared_inductive_is_held_to_the_same_rule() {
    let list = "inductive L { N, C(h: Nat, t: L) }
                fn size(xs: L) -> Nat { match xs { N => 0, C(h, t) => Succ(size(t)) } }\n";
    refused(
        &format!("{list}fn w(xs: L) -> Nat {{ match xs {{ N => 0, C(h, t) => add(w(t), size(xs)) }} }}"),
        "`xs` inside its own recursive `match`",
    );
    refused(
        &format!("{list}fn v(xs: L) -> Nat {{ Succ(match xs {{ N => 0, C(h, t) => v(t) }}) }}"),
        "is not the result of `v`",
    );
}

// -- M2: the recursive `match` is not the body's result ----------------------

#[test]
fn a_recursive_match_off_the_tail_is_refused() {
    refused(
        "fn f(n: Nat) -> Nat { add(1, match n { Zero => 0, Succ(k) => f(k) }) }",
        "is not the result of `f`",
    );
    refused(
        "fn e(n: Nat) -> Nat { add(match n { Zero => 0, Succ(k) => e(k) }, n) }",
        "is not the result of `e`",
    );
    // A bound value is never the result.
    refused(
        "fn e(n: Nat) -> Nat { let r = match n { Zero => 0, Succ(k) => e(k) }; add(r, 1) }",
        "is not the result of `e`",
    );
}

#[test]
fn a_recursive_match_under_a_branch_on_its_parameter_is_refused() {
    refused(
        "inductive B { T, F }
         fn is_zero(n: Nat) -> B { match n { Zero => T, Succ(k) => F } }
         fn f(n: Nat) -> Nat { match is_zero(n) { T => 7, F => match n { Zero => 0, Succ(k) => f(k) } } }",
        "sits under a branch that depends on `n`",
    );
}

// -- What stays accepted, and computes what it says --------------------------

#[test]
fn the_spellings_the_messages_suggest_compute_the_source_value() {
    ok(&format!(
        "{ADD}
         fn sum(n: Nat) -> Nat {{ match n {{ Zero => 0, Succ(k) => add(sum(k), Succ(k)) }} }}
         theorem sum_2(): sum(2) = 3 {{ refl }}
         fn f(n: Nat) -> Nat {{ match n {{ Zero => 1, Succ(k) => add(1, f(k)) }} }}
         theorem f_2(): f(2) = 3 {{ refl }}
         fn g(n: Nat) -> Nat {{ match n {{ Zero => 0, Succ(k) => {{ have m = Succ(k); add(g(k), m) }} }} }}
         theorem g_2(): g(2) = 3 {{ refl }}"
    ));
}

#[test]
fn unchanged_and_varying_parameters_are_not_the_recursion() {
    ok(&format!(
        "{ADD}
         inductive B {{ T, F }}
         fn pick(n: Nat, b: B) -> Nat {{
             match n {{ Zero => 0, Succ(k) => match b {{ T => Succ(pick(k, b)), F => pick(k, b) }} }}
         }}
         theorem pick_t(): pick(2, T) = 2 {{ refl }}
         fn count(n: Nat, acc: Nat) -> Nat {{ match n {{ Zero => acc, Succ(k) => count(k, add(acc, 1)) }} }}
         theorem count_2(): count(2, 5) = 7 {{ refl }}"
    ));
}

#[test]
fn non_recursive_matches_and_theorems_are_untouched() {
    // No self-call: the `match` runs once, so `n` in its arms is this call's.
    // A theorem's body is not observable past its statement, so naming `n`
    // in its own recursive arm changes which proof, not what is proved.
    ok(&format!(
        "{ADD}
         fn once(n: Nat) -> Nat {{ add(1, match n {{ Zero => n, Succ(k) => n }}) }}
         theorem walk(n: Nat): True {{
             match n {{ Zero => trivial, Succ(k) => {{ let r = walk(k); let q: (n = n) = refl; trivial }} }}
         }}"
    ));
}
