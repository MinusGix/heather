//! Goal-hole acceptance (issues/goal-holes.md): `?name` holes as real
//! metavariables that survive to the end of the block, discharged by `on`.
//!
//! The load-bearing property, and the reason a hole is a Ψ-global rather than
//! a source-level rewrite, is *contextual capture*: a goal raised inside a
//! `match` arm records that arm's context, so its `on` — written at block end,
//! where those binders are lexically long gone — still elaborates with them in
//! scope. The kernel is unaffected either way: it only ever sees the
//! discharged term.

use heather_elab::{ElabError, Elaborator};

/// `add` + the theorems the discharge tests lean on, all stage-2 forms.
const PREAMBLE: &str = r#"
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
"#;

fn check(src: &str) -> Result<Elaborator, ElabError> {
    let mut e = Elaborator::with_prelude().expect("prelude");
    e.elab_source(PREAMBLE).expect("preamble");
    e.elab_source(src)?;
    Ok(e)
}

fn accept(src: &str) -> Elaborator {
    match check(src) {
        Ok(e) => e,
        Err(other) => panic!("expected acceptance, got {other:?}"),
    }
}

fn reject(src: &str) -> ElabError {
    match check(src) {
        Ok(_) => panic!("expected a rejection, got acceptance"),
        Err(e) => e,
    }
}

fn elab_err(src: &str) -> String {
    match reject(src) {
        ElabError::Elab { msg, .. } => msg,
        other => panic!("expected a surface elaboration error, got {other:?}"),
    }
}

#[test]
fn a_body_hole_is_discharged_by_name() {
    let e = accept(
        r#"
        theorem body_hole(n: Nat): add(n, 0) = n {
            ?p
            on ?p := add_zero(n);
        }
        "#,
    );
    // 4 prelude + 3 preamble (`add` included: a `fn` is a *defined* Ψ-global
    // since issues/simulate-conversion-cost.md) + this one; goals never leak
    // into the real Ψ.
    assert_eq!(e.psi().bindings.len(), 8);
}

#[test]
fn a_goal_captures_its_match_arm() {
    // The money test. `?step` is raised under `Succ(k)`, so its context has
    // `k` — and the discharge, written after the `match` where `k` is lexically
    // out of scope, still elaborates against exactly that context. The self-
    // call `add_zero_hole(k)` is the arm's induction hypothesis
    // (issues/match-recursion.md), reached from inside the discharge.
    accept(
        r#"
        theorem add_zero_hole(n: Nat): add(n, 0) = n {
            match n {
                Zero => refl,
                Succ(k) => ?step,
            }
            on ?step := cong_succ(add_zero_hole(k));
        }
        "#,
    );
}

#[test]
fn a_hole_can_be_an_ordinary_argument() {
    // Checking position through `apply_explicit`: `Succ(?x)` and `@f(…, ?p)`.
    accept(
        r#"
        fn two() -> Nat {
            Succ(?x)
            on ?x := 1;
        }

        theorem explicit_arg(a: Nat, b: Nat, p: a = b): b = a {
            @sym(a, b, ?q)
            on ?q := p;
        }
        "#,
    );
}

#[test]
fn a_hole_survives_calcs_cloned_spine() {
    // `calc` desugars in the parser by *cloning* endpoints into nested
    // `@trans` calls, so one syntactic hole is elaborated more than once. It
    // must stay one goal — the pre-count is an upper bound, not the count.
    accept(
        r#"
        theorem calc_hole(m: Nat, n: Nat): add(Succ(m), n) = Succ(add(m, n)) {
            calc {
                add(Succ(m), n)
                    = Succ(add(m, n)) := refl,
                    = Succ(add(m, n)) := ?last,
            }
            on ?last := refl;
        }
        "#,
    );
}

#[test]
fn let_binds_a_hole_through_its_annotation() {
    // The hole-programming pattern of docs/sketches/surface-v3.md §2: bind a
    // goal to a name, use it as an ordinary value. The annotation is what puts
    // the right-hand side in checking position.
    accept(
        r#"
        theorem let_hole(n: Nat): n = add(n, 0) {
            let strong: (add(n, 0) = n) = ?g;
            sym(strong)
            on ?g := add_zero(n);
        }
        "#,
    );
}

#[test]
fn let_binds_an_ordinary_value() {
    accept(
        r#"
        fn double(n: Nat) -> Nat {
            let m = add(n, n);
            m
        }
        "#,
    );
}

#[test]
fn a_let_shadows_and_is_shadowed_by_position() {
    // An alias is not a kernel binder, so shadowing is decided by where it was
    // bound: it shadows the parameter of the same name, and a later `match`
    // binder shadows it in turn.
    accept(
        r#"
        fn shadowing(n: Nat) -> Nat {
            let n = add(n, n);
            match n {
                Zero => n,
                Succ(n) => n,
            }
        }
        "#,
    );
}

#[test]
fn goals_coexist_with_implicit_argument_metas() {
    // The composition test: a goal is live at the innermost Ψ index while the
    // `Succ` arm runs implicit-argument insertion (which opens a scratch world
    // of its own), and the discharge itself uses implicit insertion inside the
    // goal world before being strengthened out of it.
    accept(
        r#"
        theorem mixed(m: Nat, n: Nat): add(m, n) = add(n, m) {
            match m {
                Zero => ?base,
                Succ(k) => trans(cong_succ(mixed(k, n)), sym(add_succ(n, k))),
            }
            on ?base := sym(add_zero(n));
        }
        "#,
    );
}

#[test]
fn the_kernel_still_gates_a_discharged_goal() {
    // `refl` checks against the *shape* of the goal (an `Id`), so this
    // elaborates — and the kernel rejects it, because `add(n, 0)` and `n` are
    // not convertible for an open `n`. Goals do not weaken the gate.
    let r = reject(
        r#"
        theorem bogus(n: Nat): add(n, 0) = n {
            ?p
            on ?p := refl;
        }
        "#,
    );
    assert!(matches!(r, ElabError::Kernel { .. }), "expected a kernel rejection, got {r:?}");
}

#[test]
fn an_undischarged_goal_is_listed() {
    let r = reject(
        r#"
        theorem unfilled(n: Nat): add(n, 0) = n {
            match n {
                Zero => refl,
                Succ(k) => ?step,
            }
        }
        "#,
    );
    let ElabError::UnsolvedGoals { decl, goals } = r else {
        panic!("expected an unsolved-goal listing");
    };
    assert_eq!(decl, "unfilled");
    assert_eq!(goals.len(), 1);
    assert_eq!(goals[0].name, "step");
    // The listing carries the statement and the context the discharge may use
    // — including the arm's `k`, which is the non-obvious part.
    // Rendered with the kernel's budget-bounded `Debug` (kernel/src/fmt.rs),
    // so an equality goal reads as `Id[l](A; lhs; rhs)`.
    assert!(goals[0].statement.starts_with("Id["), "statement: {}", goals[0].statement);
    let ctx: Vec<&str> = goals[0].context.iter().map(|(n, _)| n.as_str()).collect();
    assert!(ctx.contains(&"n") && ctx.contains(&"k"), "context: {ctx:?}");
    // The elaborator's own hidden ih binder is unspellable, so it is not
    // offered as something to use.
    assert!(!ctx.iter().any(|n| n.starts_with('#')), "context: {ctx:?}");
}

#[test]
fn every_undischarged_goal_is_listed_at_once() {
    let r = reject(
        r#"
        theorem two_unfilled(a: Nat, b: Nat, p: a = b): b = a {
            @trans(b, a, a, @sym(a, b, ?first), ?second)
        }
        "#,
    );
    let ElabError::UnsolvedGoals { goals, .. } = r else {
        panic!("expected an unsolved-goal listing");
    };
    let names: Vec<&str> = goals.iter().map(|g| g.name.as_str()).collect();
    assert_eq!(names, ["first", "second"]);
}

#[test]
fn an_anonymous_argument_hole_is_named_after_the_parameter() {
    // "Proof-parameter names are API" (docs/sketches/surface-v2.md §2): the
    // default name comes from the callee's parameter, collisions get ordinals,
    // and the listing says which call site each came from.
    let r = reject(
        r#"
        theorem named_by_callee(a: Nat, b: Nat, p: a = b): b = b {
            @trans(b, a, b, @sym(a, b, ?), @sym(b, a, ?))
            on ?p.1 := @sym(a, b, p);
        }
        "#,
    );
    let ElabError::UnsolvedGoals { goals, .. } = r else {
        panic!("expected an unsolved-goal listing");
    };
    // `sym`'s and `trans`'s proof parameters are both `p`; the second is
    // deduplicated. The first was discharged by name, proving the assigned
    // name is usable, not just printable.
    let names: Vec<&str> = goals.iter().map(|g| g.name.as_str()).collect();
    assert_eq!(names, ["p"]);
    assert_eq!(goals[0].origin.as_deref(), Some("the `p` parameter of `sym`"));
}

#[test]
fn the_listing_reads() {
    let src = r#"
theorem unfilled(n: Nat): add(n, 0) = n {
    match n {
        Zero => refl,
        Succ(k) => ?step,
    }
}
"#;
    let rendered = reject(src).render(src);
    assert!(rendered.contains("unsolved goals in `unfilled`"), "{rendered}");
    assert!(rendered.contains("?step :"), "{rendered}");
    // Source position, the captured context, and how to act on it.
    assert!(rendered.contains("(5:20)"), "{rendered}");
    assert!(rendered.contains("k : Nat"), "{rendered}");
    assert!(rendered.contains("on ?name := proof;"), "{rendered}");
}

#[test]
fn anonymous_holes_get_checker_assigned_names() {
    let r = reject(
        r#"
        theorem anon(n: Nat): add(n, 0) = n {
            ?
        }
        "#,
    );
    let ElabError::UnsolvedGoals { goals, .. } = r else {
        panic!("expected an unsolved-goal listing");
    };
    assert_eq!(goals[0].name, "g1");
}

#[test]
fn one_statement_discharge_fills_every_matching_goal() {
    // docs/sketches/surface-v2.md §2: the common pattern is one proof feeding
    // several sites, so `on _: P := e` discharges *all* goals stating `P` —
    // name-free and order-free.
    accept(
        r#"
        theorem by_statement(a: Nat, b: Nat, p: a = b): b = b {
            @trans(b, a, b, @sym(a, b, ?first), ?second)
            on _: a = b := p;
        }
        "#,
    );
}

#[test]
fn a_statement_discharge_leaves_other_goals_alone() {
    let r = reject(
        r#"
        theorem partial(a: Nat, b: Nat, p: a = b): b = a {
            @trans(b, a, a, @sym(a, b, ?matching), ?other)
            on _: a = b := p;
        }
        "#,
    );
    let ElabError::UnsolvedGoals { goals, .. } = r else {
        panic!("expected an unsolved-goal listing");
    };
    let names: Vec<&str> = goals.iter().map(|g| g.name.as_str()).collect();
    assert_eq!(names, ["other"], "only the non-matching goal stays open");
}

#[test]
fn a_statement_discharge_matches_up_to_conversion() {
    // Matching is kernel convertibility, not syntax: `add(0, a)` reduces to
    // `a`, so this statement matches a goal stated as `a = b`.
    accept(
        r#"
        theorem up_to_conv(a: Nat, b: Nat, p: a = b): b = a {
            @sym(a, b, ?g)
            on _: add(0, a) = b := p;
        }
        "#,
    );
}

// -- negatives --------------------------------------------------------------

#[test]
fn a_hole_needs_an_expected_type() {
    let msg = elab_err(
        r#"
        theorem infer_hole(n: Nat): n = n {
            match ? {
                Zero => refl,
                Succ(k) => refl,
            }
        }
        "#,
    );
    assert!(msg.contains("no expected type"), "{msg}");
}

#[test]
fn discharging_an_unknown_goal_lists_the_real_ones() {
    let msg = elab_err(
        r#"
        theorem unknown_on(n: Nat): add(n, 0) = n {
            ?p
            on ?nope := add_zero(n);
        }
        "#,
    );
    assert!(msg.contains("?nope"), "{msg}");
    assert!(msg.contains("?p"), "should list the goals that exist: {msg}");
}

#[test]
fn a_goal_cannot_be_discharged_twice() {
    let msg = elab_err(
        r#"
        theorem twice(n: Nat): add(n, 0) = n {
            ?p
            on ?p := add_zero(n);
            on ?p := add_zero(n);
        }
        "#,
    );
    assert!(msg.contains("twice"), "{msg}");
}

#[test]
fn a_named_hole_is_one_goal_per_block() {
    let msg = elab_err(
        r#"
        theorem duplicate(a: Nat, b: Nat, p: a = b): b = a {
            @trans(b, a, a, @sym(a, b, ?g), ?g)
            on ?g := p;
        }
        "#,
    );
    assert!(msg.contains("already used"), "{msg}");
}

#[test]
fn a_statement_discharge_matching_nothing_is_an_error() {
    // Silence would read as "handled". It is not.
    let msg = elab_err(
        r#"
        theorem no_match(a: Nat, b: Nat, p: a = b): b = a {
            @sym(a, b, ?g)
            on _: b = a := p;
            on ?g := p;
        }
        "#,
    );
    assert!(msg.contains("no outstanding goal"), "{msg}");
}

#[test]
fn a_hole_may_not_appear_in_a_discharge() {
    // Goal payloads are not telescoped among each other, so a discharge that
    // itself deferred would never be substituted. Refused, not silently wrong.
    let msg = elab_err(
        r#"
        theorem nested(n: Nat): add(n, 0) = n {
            ?p
            on ?p := ?q;
        }
        "#,
    );
    assert!(msg.contains("right-hand side"), "{msg}");
}
