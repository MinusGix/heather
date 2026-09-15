//! Acceptance for issues/match-recursion.md: the unified `match`, where a
//! structurally guarded **self-call** is the induction hypothesis. `add` is
//! an ordinary recursive function and `add_zero` is an ordinary recursive
//! *theorem* — literally the same language, no `induction`/`rec` keyword, no
//! `Succ(k, ih)` binder.
//!
//! The lowering builds `elim_Nat`, so the guardedness analysis is untrusted:
//! everything here still passes the kernel's `check_type` + `check_term`, and
//! the analysis can only reject.

use heather_elab::{ElabError, Elaborator};

// The stage-1/stage-2 suite, rewritten with self-calls throughout.
const NAT_SUITE_REC: &str = r#"
fn add(m: Nat, n: Nat) -> Nat {
    match m {
        Zero => n,
        Succ(k) => Succ(add(k, n)),
    }
}

theorem add_zero(n: Nat): add(n, 0) = n {
    match n {
        Zero => refl,
        Succ(k) => cong_succ(add_zero(k)),
    }
}

theorem add_succ(m: Nat, n: Nat): add(m, Succ(n)) = Succ(add(m, n)) {
    match m {
        Zero => refl,
        Succ(k) => cong_succ(add_succ(k, n)),
    }
}

theorem add_comm(m: Nat, n: Nat): add(m, n) = add(n, m) {
    match m {
        Zero => sym(add_zero(n)),
        Succ(k) => trans(cong_succ(add_comm(k, n)), sym(add_succ(n, k))),
    }
}

theorem add_assoc(a: Nat, b: Nat, c: Nat): add(add(a, b), c) = add(a, add(b, c)) {
    match a {
        Zero => refl,
        Succ(k) => cong_succ(add_assoc(k, b, c)),
    }
}
"#;

#[test]
fn nat_suite_recursive_style() {
    let mut e = Elaborator::with_prelude().expect("prelude");
    e.elab_source(NAT_SUITE_REC)
        .expect("recursive-style Nat suite must elaborate and kernel-check");
    // prelude's 5 (4 theorems and `CollectionLiteral#tycode_fn`,
    // docs/per-instantiation-type-codes-design.md §2) + `3·nfields + 1 = 7`
    // for that declaration's projections (its spine is dependent;
    // docs/telescoped-record-projections-design.md §3) + the suite's `fn add`
    // and 4 theorems, all landed as Ψ-globals (a `fn` is a *defined* one
    // since issues/simulate-conversion-cost.md).
    assert_eq!(e.psi().bindings.len(), 17);
}

#[test]
fn recursive_add_still_computes() {
    // The self-call really did lower to `elim_Nat`: concrete arithmetic
    // reduces, so `refl` alone proves 2 + 2 = 4.
    let mut e = Elaborator::with_prelude().expect("prelude");
    e.elab_source(NAT_SUITE_REC).expect("suite");
    e.elab_source("theorem two_plus_two(): add(2, 2) = 4 { refl }")
        .expect("2 + 2 = 4 by refl");
}

#[test]
fn both_spellings_agree() {
    // The explicit-ih arm remains the low-level fallback, and the two
    // spellings coexist in one file.
    let mut e = Elaborator::with_prelude().expect("prelude");
    e.elab_source(
        r#"
        fn add(m: Nat, n: Nat) -> Nat {
            match m { Zero => n, Succ(k, ih) => Succ(ih) }
        }
        fn add2(m: Nat, n: Nat) -> Nat {
            match m { Zero => n, Succ(k) => Succ(add2(k, n)) }
        }
        theorem same(m: Nat, n: Nat): add(m, n) = add2(m, n) {
            match m { Zero => refl, Succ(k) => cong_succ(same(k, n)) }
        }
        "#,
    )
    .expect("both spellings elaborate, and agree pointwise");
}

// -- the guardedness analysis rejects ---------------------------------------

/// Source checked on top of the `Nat` suite above, so a test may use `add`.
fn elab_ok(src: &str) {
    let mut e = Elaborator::with_prelude().expect("prelude");
    e.elab_source(&format!("{NAT_SUITE_REC}\n{src}"))
        .unwrap_or_else(|err| panic!("expected this to check, got: {err:?}"));
}

/// Any refusal, elaborator or kernel — for a control that asserts *which*
/// refusal it is rather than that there is one.
fn any_err(src: &str) -> String {
    let mut e = Elaborator::with_prelude().expect("prelude");
    match e.elab_source(&format!("{NAT_SUITE_REC}\n{src}")) {
        Err(other) => format!("{other:?}"),
        Ok(()) => panic!("expected this to be refused"),
    }
}

fn elab_err(src: &str) -> String {
    let mut e = Elaborator::with_prelude().expect("prelude");
    match e.elab_source(src) {
        Err(ElabError::Elab { msg, .. }) => msg,
        other => panic!("expected a surface elaboration error, got {other:?}"),
    }
}

#[test]
fn unguarded_self_call_rejected() {
    // No enclosing match: nothing to descend on.
    let msg = elab_err("fn loop(n: Nat) -> Nat { loop(n) }");
    assert!(msg.contains("not structurally guarded"), "{msg}");
}

#[test]
fn non_descending_self_call_rejected() {
    // Passing the scrutinee itself back is the classic non-terminating loop.
    let msg = elab_err(
        "fn loop(m: Nat, n: Nat) -> Nat { match m { Zero => n, Succ(k) => loop(m, n) } }",
    );
    assert!(msg.contains("must descend"), "{msg}");
}

#[test]
fn varying_argument_generalized() {
    // The MVP's documented limitation, lifted (issues/ih-generalization.md,
    // docs/ih-generalization-design.md): a non-decreasing argument that
    // changes is generalized into the motive. The refusal survives only where
    // there is no goal to generalize from — tests/ih_generalization.rs holds
    // that control and the rest of the acceptance.
    elab_ok(
        "fn loop(m: Nat, n: Nat) -> Nat { match m { Zero => n, Succ(k) => loop(k, Succ(n)) } }\n\
         theorem loop_is_add(m: Nat, n: Nat): loop(m, n) = add(n, m) {\n\
             match m { Zero => sym(add_zero(n)), Succ(k) => trans(loop_is_add(k, Succ(n)), sym(add_succ(n, k))) }\n\
         }",
    );
}

#[test]
fn shadowing_cannot_fake_a_guard() {
    // The analysis compares binders, not names: an inner `k` that is not the
    // predecessor does not count as descending.
    let msg = elab_err(
        r#"
        fn loop(m: Nat) -> Nat {
            match m {
                Zero => 0,
                Succ(k) => match m as λ z => Nat { Zero => 0, Succ(k, ih) => loop(k) },
            }
        }
        "#,
    );
    assert!(msg.contains("must descend"), "{msg}");
}

const HALF: &str = "
        fn half(n: Nat) -> Nat {
            match n {
                Zero => 0,
                Succ(k) => match k { Zero => 0, Succ(l) => Succ(half(l)) },
            }
        }";

/// A self-call at the predecessor's predecessor, written the way anyone writes
/// it (issues/recursion-at-deeper-subterms.md). The arm that contains it is a
/// recursor step whose ih is the value at `k`, so the term it lowers to is a
/// projection out of a recursion carrying its last two values.
#[test]
fn a_deeper_subterm_descends() {
    elab_ok(HALF);
}

/// The property the whole transformation is for: it is still ONE `elim_Nat`,
/// so a closed argument still computes. Half of `issues/nat-parity-and-half.md`'s
/// acceptance is this line.
#[test]
fn a_course_of_values_recursion_still_reduces() {
    elab_ok(&format!(
        "{HALF}
        theorem seven(): half(7) = 3 {{ refl }}
        theorem eight(): half(8) = 4 {{ refl }}
        theorem zero(): half(0) = 0 {{ refl }}
        theorem one(): half(1) = 0 {{ refl }}"
    ));
    // The control: it computes the *right* values, not merely something.
    let msg = any_err(&format!("{HALF}\ntheorem t(): half(7) = 4 {{ refl }}"));
    assert!(!msg.contains("must descend"), "should be a conversion failure, got: {msg}");
}

/// `fib`, the other classic — two calls at two different depths in one arm,
/// which is what says the window slides rather than the deepest call alone
/// being served.
#[test]
fn two_depths_in_one_arm() {
    elab_ok(
        "
        fn fib(n: Nat) -> Nat {
            match n {
                Zero => 0,
                Succ(k) => match k { Zero => 1, Succ(l) => add(fib(k), fib(l)) },
            }
        }
        theorem f7(): fib(7) = 13 { refl }
        theorem f1(): fib(1) = 1 { refl }",
    );
}

/// A `Type`-valued two-step recursion: the same lowering with the motive at a
/// universe, which is what `Even`/`Odd` need. Reduces, so `P(4)` is `trivial`.
#[test]
fn a_deeper_recursion_at_a_type_motive() {
    elab_ok(
        "
        fn P(n: Nat) -> Type {
            match n {
                Zero => 0 = 0,
                Succ(k) => match k { Zero => 0 = 1, Succ(l) => P(l) },
            }
        }
        theorem four(): P(4) { refl }",
    );
}

/// A **dependent** motive, which is every two-step *proof* and the case the
/// non-dependent ones cannot stand in for: the carried value one below `k` has
/// type `M[pred k]`, and `pred k` is stuck at a variable. It becomes usable
/// only because the window is convoyed through the nested `match`, where the
/// arm knows its scrutinee is `Succ(l)` and `pred (Succ l)` reduces
/// (docs/course-of-values-recursion-design.md §5). Nothing here is written by
/// the author of the proof — the arms below are the ordinary ones.
#[test]
fn a_deeper_recursion_at_a_dependent_motive() {
    elab_ok(
        "
        fn E(n: Nat) -> Type {
            match n { Zero => True, Succ(k) => match k { Zero => 0 = 1, Succ(l) => E(l) } }
        }
        fn O(n: Nat) -> Type {
            match n { Zero => 0 = 1, Succ(k) => match k { Zero => True, Succ(l) => O(l) } }
        }
        theorem not_both(n: Nat): E(n) -> O(n) -> 0 = 1 {
            match n {
                Zero => λ (e: E(0)) (o: O(0)) => o,
                Succ(k) => match k {
                    Zero => λ (e: E(1)) (o: O(1)) => e,
                    Succ(l) => λ (e: E(l)) (o: O(l)) => not_both(l)(e)(o),
                },
            }
        }
        theorem four(): E(4) { trivial }
        theorem five(): O(5) { trivial }",
    );
}

/// Depth **three**, where the two things depth two cannot show up: a
/// component whose type carries a two-deep `pred` chain, and a nested convoy —
/// the innermost `match` passing on a window that was itself passed in to the
/// one above it. `trib` reads all three of its past values in one arm, so the
/// window has to arrive intact at the bottom.
#[test]
fn three_deep_and_the_nested_convoy() {
    elab_ok(
        "
        fn trib(n: Nat) -> Nat {
            match n {
                Zero => 0,
                Succ(k) => match k {
                    Zero => 1,
                    Succ(l) => match l {
                        Zero => 1,
                        Succ(m) => add(add(trib(k), trib(l)), trib(m)),
                    },
                },
            }
        }
        theorem t3(): trib(3) = 2 { refl }
        theorem t4(): trib(4) = 4 { refl }
        theorem t7(): trib(7) = 24 { refl }
        theorem t2(): trib(2) = 1 { refl }
        theorem t0(): trib(0) = 0 { refl }",
    );
}

/// The same depth with a **dependent** motive, which is where the convoy is
/// load-bearing (§5 of the design doc) — and at depth three the innermost arm
/// needs `pred (pred (Succ (Succ l)))` to reduce, not merely `pred (Succ l)`.
#[test]
fn three_deep_at_a_dependent_motive() {
    elab_ok(
        "
        fn D(n: Nat) -> Type {
            match n {
                Zero => True,
                Succ(k) => match k {
                    Zero => 0 = 1,
                    Succ(l) => match l { Zero => 0 = 1, Succ(m) => D(m) },
                },
            }
        }
        fn R(n: Nat) -> Type {
            match n {
                Zero => 0 = 1,
                Succ(k) => match k {
                    Zero => True,
                    Succ(l) => match l { Zero => 0 = 1, Succ(m) => R(m) },
                },
            }
        }
        theorem not_both(n: Nat): D(n) -> R(n) -> 0 = 1 {
            match n {
                Zero => λ (d: D(0)) (r: R(0)) => r,
                Succ(k) => match k {
                    Zero => λ (d: D(1)) (r: R(1)) => d,
                    Succ(l) => match l {
                        Zero => λ (d: D(2)) (r: R(2)) => d,
                        Succ(m) => λ (d: D(m)) (r: R(m)) => not_both(m)(d)(r),
                    },
                },
            }
        }
        theorem six(): D(6) { trivial }
        theorem seven(): R(7) { trivial }",
    );
}

/// Depth **four**, dependent — a third nesting, so the window is lifted twice.
/// Depth three is what caught the anchor bug (a window re-indexed at the
/// scrutinee instead of lifted above it slides every component by one), and
/// the fix generalized over the nesting count rather than special-casing the
/// second level; this is what says so.
#[test]
fn four_deep_at_a_dependent_motive() {
    elab_ok(
        "
        fn A(n: Nat) -> Nat {
            match n {
                Zero => 0,
                Succ(k) => match k {
                    Zero => 0,
                    Succ(l) => match l {
                        Zero => 0,
                        Succ(m) => match m { Zero => 0, Succ(p) => Succ(A(p)) },
                    },
                },
            }
        }
        fn B(n: Nat) -> Nat {
            match n {
                Zero => 0,
                Succ(k) => match k {
                    Zero => 0,
                    Succ(l) => match l {
                        Zero => 0,
                        Succ(m) => match m { Zero => 0, Succ(p) => add(1, B(p)) },
                    },
                },
            }
        }
        theorem agree(n: Nat): A(n) = B(n) {
            match n {
                Zero => refl,
                Succ(k) => match k {
                    Zero => refl,
                    Succ(l) => match l {
                        Zero => refl,
                        Succ(m) => match m { Zero => refl, Succ(p) => cong_succ(agree(p)) },
                    },
                },
            }
        }
        theorem nine(): A(9) = 2 { refl }
        theorem same(): B(9) = 2 { refl }",
    );
}

/// The chain is followed by *binder*, not by name: a nested `match` on
/// something else does not extend it, and a call at its pattern variable is
/// refused — with the mechanism, not just the rule
/// (issues/recursion-at-deeper-subterms.md).
#[test]
fn a_nested_match_on_another_variable_does_not_extend_the_chain() {
    let msg = elab_err(
        "
        fn f(n: Nat, m: Nat) -> Nat {
            match n {
                Zero => 0,
                Succ(k) => match m { Zero => 0, Succ(l) => f(l, m) },
            }
        }",
    );
    assert!(msg.contains("must descend"), "{msg}");
    assert!(msg.contains("genuinely smaller"), "the rule without the mechanism: {msg}");
    assert!(msg.contains("recursion-at-deeper-subterms"), "{msg}");
}

#[test]
fn arity_is_checked() {
    let msg = elab_err(
        "fn loop(m: Nat, n: Nat) -> Nat { match m { Zero => n, Succ(k) => loop(k) } }",
    );
    assert!(msg.contains("must pass all 2 argument"), "{msg}");
}

#[test]
fn self_name_is_not_a_value() {
    let msg = elab_err("fn loop(n: Nat) -> Nat { match n { Zero => 0, Succ(k) => loop } }");
    assert!(msg.contains("saturated recursive call"), "{msg}");
}

