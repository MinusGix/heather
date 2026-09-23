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
        Succ(k) => Nat::cong_succ(add_zero(k)),
    }
}

theorem add_succ(m: Nat, n: Nat): add(m, Succ(n)) = Succ(add(m, n)) {
    match m {
        Zero => refl,
        Succ(k) => Nat::cong_succ(add_succ(k, n)),
    }
}

theorem add_comm(m: Nat, n: Nat): add(m, n) = add(n, m) {
    match m {
        Zero => sym(add_zero(n)),
        Succ(k) => trans(Nat::cong_succ(add_comm(k, n)), sym(add_succ(n, k))),
    }
}

theorem add_assoc(a: Nat, b: Nat, c: Nat): add(add(a, b), c) = add(a, add(b, c)) {
    match a {
        Zero => refl,
        Succ(k) => Nat::cong_succ(add_assoc(k, b, c)),
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
            match m { Zero => refl, Succ(k) => Nat::cong_succ(same(k, n)) }
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

/// Receiver syntax denotes the same guarded call as the direct spelling, so
/// it must size and convoy the same two-value course-of-values window.
#[test]
fn a_receiver_spelled_deeper_subterm_descends() {
    elab_ok(
        "
        fn Nat::half_m(self n: Nat) -> Nat {
            match n {
                Zero => 0,
                Succ(k) => match k { Zero => 0, Succ(l) => Succ(l.half_m()) },
            }
        }
        theorem Nat::half_m_refl(self n: Nat): n.half_m() = n.half_m() {
            match n {
                Zero => refl,
                Succ(k) => match k {
                    Zero => refl,
                    Succ(l) => Nat::cong_succ(l.half_m_refl()),
                },
            }
        }
        theorem eight_m(): (8).half_m() = 4 { refl }",
    );
}

/// While a member is being checked it is not a committed global yet. Its own
/// `self` marker, rather than the global metadata fallback, therefore decides
/// where receiver syntax inserts the recursive argument.
#[test]
fn a_recursive_receiver_uses_a_nonfirst_self_slot() {
    elab_ok(
        "
        fn Nat::count_from(prefix: Nat, self n: Nat) -> Nat {
            match n { Zero => prefix, Succ(k) => k.count_from(Succ(prefix)) }
        }
        theorem counted(): (3).count_from(4) = 7 { refl }",
    );
}

/// Receiver spelling is visible to the IH-generalization sizing pass too: the
/// accumulator varies while the receiver supplies the decreasing argument.
#[test]
fn a_receiver_spelled_self_call_generalizes_varying_parameters() {
    elab_ok(
        "
        fn Nat::add_acc(self n: Nat, acc: Nat) -> Nat {
            match n { Zero => acc, Succ(k) => k.add_acc(Succ(acc)) }
        }
        theorem accumulated(): (3).add_acc(4) = 7 { refl }",
    );
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
                        Succ(m) => match m { Zero => refl, Succ(p) => Nat::cong_succ(agree(p)) },
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


// -- the window on chain-shaped `Wf` inductives ------------------------------
//
// `docs/list-course-of-values-design.md`: the same transformation with `pred`
// replaced by the recursive-field projection. Every test below mirrors one of
// the `Nat` tests above, and the dependent ones are dependent for the reason
// §5 of the `Nat` design gives — a non-dependent motive makes every anchoring
// agree, so it hides the bug it is there to catch.

/// `List` and the arithmetic these tests need, declared here rather than
/// imported: an elaborator test builds its own world.
const LIST: &str = "
inductive List { Nil, Cons(head: Nat, tail: List) }
fn plus(a: Nat, b: Nat) -> Nat { match b { Zero => a, Succ(k) => Succ(plus(a, k)) } }
";

fn list_ok(src: &str) {
    let mut e = Elaborator::with_prelude().expect("prelude");
    e.elab_source(&format!("{LIST}\n{src}"))
        .unwrap_or_else(|err| panic!("expected this to check, got: {err:?}"));
}

fn list_err(src: &str) -> String {
    let mut e = Elaborator::with_prelude().expect("prelude");
    match e.elab_source(&format!("{LIST}\n{src}")) {
        Err(ElabError::Elab { msg, .. }) => msg,
        other => panic!("expected a surface elaboration error, got {other:?}"),
    }
}

const ALTERNATE: &str = "
fn alternate(xs: List) -> Nat {
    match xs {
        Nil => 0,
        Cons(h, t) => match t { Nil => h, Cons(h2, t2) => plus(h, alternate(t2)) },
    }
}";

/// The customer's shape at depth two: a self-call on the *grandchild*, which
/// the one-step guard refuses and the window admits.
#[test]
fn a_deeper_list_subterm_descends() {
    list_ok(ALTERNATE);
}

/// Still ONE `elim_Wf`, so a closed list computes — the property the whole
/// transformation exists to keep. With the wrong-value control beside it, so
/// that "it computes" means "it computes the right thing".
#[test]
fn a_list_course_of_values_recursion_still_reduces() {
    list_ok(&format!(
        "{ALTERNATE}
        theorem a0(): alternate(Nil) = 0 {{ refl }}
        theorem a1(): alternate(Cons(5, Nil)) = 5 {{ refl }}
        theorem a2(): alternate(Cons(5, Cons(9, Nil))) = 5 {{ refl }}
        theorem a3(): alternate(Cons(5, Cons(9, Cons(7, Nil)))) = 12 {{ refl }}"
    ));
    let mut e = Elaborator::with_prelude().expect("prelude");
    let msg = match e.elab_source(&format!(
        "{LIST}\n{ALTERNATE}\ntheorem bad(): alternate(Cons(5, Cons(9, Cons(7, Nil)))) = 13 {{ refl }}"
    )) {
        Err(other) => format!("{other:?}"),
        Ok(()) => panic!("expected the wrong value to be refused"),
    };
    assert!(!msg.contains("must descend"), "should be a conversion failure, got: {msg}");
}

/// …and it unfolds at an **open** tail, which is what a proof about the
/// recursion needs and what a closed-argument test cannot see.
#[test]
fn the_list_window_unfolds_at_an_open_tail() {
    list_ok(&format!(
        "{ALTERNATE}
        theorem step(h: Nat, h2: Nat, r: List):
            alternate(Cons(h, Cons(h2, r))) = plus(h, alternate(r)) {{ refl }}"
    ));
}

/// Two calls at two different depths in one arm: the window slides rather
/// than the deepest call alone being served.
#[test]
fn two_list_depths_in_one_arm() {
    list_ok(
        "
        fn fibl(xs: List) -> Nat {
            match xs {
                Nil => 0,
                Cons(h, t) => match t { Nil => 1, Cons(h2, t2) => plus(fibl(t), fibl(t2)) },
            }
        }
        theorem f7(): fibl(Cons(1, Cons(1, Cons(1, Cons(1, Cons(1, Cons(1, Cons(1, Nil)))))))) = 13 { refl }",
    );
}

/// A **dependent** motive at depth two. The carried value one below the arm's
/// child has type `M[tail_D t]`, and `tail_D t` is stuck at an alias; it
/// becomes usable only because the window is convoyed through the nested
/// `match`, where the arm knows its scrutinee is `Cons(h2, t2)`.
#[test]
fn a_deeper_list_recursion_at_a_dependent_motive() {
    list_ok(&format!(
        "theorem plus_zero(a: Nat): plus(0, a) = a {{
            match a {{ Zero => refl, Succ(k) => Nat::cong_succ(plus_zero(k)) }}
        }}
        theorem plus_succ(a: Nat, b: Nat): plus(Succ(a), b) = Succ(plus(a, b)) {{
            match b {{ Zero => refl, Succ(k) => Nat::cong_succ(plus_succ(a, k)) }}
        }}
        theorem plus_comm(a: Nat, b: Nat): plus(a, b) = plus(b, a) {{
            match b {{
                Zero => sym(plus_zero(a)),
                Succ(k) => trans(Nat::cong_succ(plus_comm(a, k)), sym(plus_succ(k, a))),
            }}
        }}
        theorem cong_plus(h: Nat, a: Nat, b: Nat, p: a = b): plus(h, a) = plus(h, b) {{
            j(p, \u{3bb} y _ => plus(h, a) = plus(h, y), refl)
        }}
        {ALTERNATE}
        fn altB(xs: List) -> Nat {{
            match xs {{
                Nil => 0,
                Cons(h, t) => match t {{ Nil => plus(h, 0), Cons(h2, t2) => plus(altB(t2), h) }},
            }}
        }}
        theorem agree(xs: List): alternate(xs) = altB(xs) {{
            match xs {{
                Nil => refl,
                Cons(h, t) => match t {{
                    Nil => refl,
                    Cons(h2, t2) => trans(cong_plus(h, alternate(t2), altB(t2), agree(t2)),
                        plus_comm(h, altB(t2))),
                }},
            }}
        }}"
    ));
}

/// Depth **three**, dependent: a second nesting, so both anchors compose once
/// — the window's, which stays at the chain's head, and the goal's, which sits
/// one constructor above it.
#[test]
fn three_deep_on_a_list_at_a_dependent_motive() {
    list_ok(
        "
        fn A(xs: List) -> Nat {
            match xs {
                Nil => 0,
                Cons(h, t) => match t {
                    Nil => 0,
                    Cons(h2, t2) => match t2 { Nil => 0, Cons(h3, t3) => Succ(A(t3)) },
                },
            }
        }
        fn B(xs: List) -> Nat {
            match xs {
                Nil => 0,
                Cons(h, t) => match t {
                    Nil => 0,
                    Cons(h2, t2) => match t2 { Nil => 0, Cons(h3, t3) => plus(B(t3), 1) },
                },
            }
        }
        theorem agree3(xs: List): A(xs) = B(xs) {
            match xs {
                Nil => refl,
                Cons(h, t) => match t {
                    Nil => refl,
                    Cons(h2, t2) => match t2 {
                        Nil => refl,
                        Cons(h3, t3) => Nat::cong_succ(agree3(t3)),
                    },
                },
            }
        }
        theorem a7(): A(Cons(1, Cons(1, Cons(1, Cons(1, Cons(1, Cons(1, Cons(1, Nil)))))))) = 2 { refl }",
    );
}

/// Depth **four**, dependent — a third nesting, so the anchors compose twice.
/// Depth three is where a window re-indexed at the scrutinee instead of at the
/// chain's head would first slide; this says the fix generalized over the
/// nesting count rather than special-casing one level.
#[test]
fn four_deep_on_a_list_at_a_dependent_motive() {
    list_ok(
        "
        fn A4(xs: List) -> Nat {
            match xs {
                Nil => 0,
                Cons(h, t) => match t {
                    Nil => 0,
                    Cons(h2, t2) => match t2 {
                        Nil => 0,
                        Cons(h3, t3) => match t3 { Nil => 0, Cons(h4, t4) => Succ(A4(t4)) },
                    },
                },
            }
        }
        fn B4(xs: List) -> Nat {
            match xs {
                Nil => 0,
                Cons(h, t) => match t {
                    Nil => 0,
                    Cons(h2, t2) => match t2 {
                        Nil => 0,
                        Cons(h3, t3) => match t3 { Nil => 0, Cons(h4, t4) => plus(B4(t4), 1) },
                    },
                },
            }
        }
        theorem agree4(xs: List): A4(xs) = B4(xs) {
            match xs {
                Nil => refl,
                Cons(h, t) => match t {
                    Nil => refl,
                    Cons(h2, t2) => match t2 {
                        Nil => refl,
                        Cons(h3, t3) => match t3 {
                            Nil => refl,
                            Cons(h4, t4) => Nat::cong_succ(agree4(t4)),
                        },
                    },
                },
            }
        }",
    );
}

/// A user chain-shaped declaration with **two** base constructors and two
/// recursive ones: `tail_D` branches on the tag, the base arms each emit their
/// own value `d` times, and the window still computes.
#[test]
fn a_user_chain_shaped_declaration_with_two_base_constructors() {
    list_ok(
        "
        inductive Run { Stop, Halt, Step(p: Nat, next: Run), Skip(next: Run) }
        fn sum2(r: Run) -> Nat {
            match r {
                Stop => 0,
                Halt => 1,
                Step(p, n) => match n {
                    Stop => p,
                    Halt => p,
                    Step(q, m) => plus(p, sum2(m)),
                    Skip(m) => sum2(m),
                },
                Skip(n) => match n {
                    Stop => 0,
                    Halt => 0,
                    Step(q, m) => sum2(m),
                    Skip(m) => sum2(m),
                },
            }
        }
        theorem s0(): sum2(Stop) = 0 { refl }
        theorem s1(): sum2(Step(3, Step(4, Step(5, Stop)))) = 8 { refl }
        theorem s2(): sum2(Skip(Step(4, Halt))) = 1 { refl }",
    );
}

/// A nested `match` on **another variable** does not extend the chain, and a
/// call at its pattern variable is refused. The chain is followed by *term*
/// here rather than by binder position — a `Wf` arm binder is an alias — which
/// is the same property the positional comparison gives for `Nat`.
#[test]
fn a_nested_list_match_on_another_variable_does_not_extend_the_chain() {
    let msg = list_err(
        "
        fn f(xs: List, ys: List) -> Nat {
            match xs {
                Nil => 0,
                Cons(h, t) => match ys { Nil => 0, Cons(a, b) => f(b, ys) },
            }
        }",
    );
    assert!(msg.contains("must descend"), "{msg}");
}

/// A **tree** keeps today's refusal, with the message extended to say that the
/// window exists for chain-shaped declarations and why a branching constructor
/// is not one (§1).
#[test]
fn a_tree_is_not_chain_shaped_and_says_so() {
    let msg = list_err(
        "
        inductive Tree { Leaf, Node(l: Tree, r: Tree) }
        fn deep(t: Tree) -> Nat {
            match t {
                Leaf => 0,
                Node(l, r) => match l { Leaf => 0, Node(a, b) => Succ(deep(a)) },
            }
        }",
    );
    assert!(msg.contains("must descend"), "{msg}");
    assert!(msg.contains("chain-shaped"), "the rule without the mechanism: {msg}");
    assert!(msg.contains("list-course-of-values-design"), "{msg}");
}

/// The depth scan reads **names**, so a shadowed binder can under-size the
/// window — and under-sizing is a refusal, never a wrong term (§5). This is
/// the `Wf` twin of `shadowing_cannot_fake_a_guard`.
#[test]
fn a_shadowed_chain_binder_under_sizes_and_is_refused() {
    let msg = list_err(
        "
        fn g(xs: List) -> Nat {
            match xs {
                Nil => 0,
                Cons(h, t) => match t {
                    Nil => 0,
                    Cons(h2, t) => match t { Nil => 0, Cons(h3, t3) => g(t3) },
                },
            }
        }",
    );
    assert!(msg.contains("must descend"), "{msg}");
}
