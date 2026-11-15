//! Acceptance for surface function types and lambdas, against the checklist
//! of `docs/language/surface-function-types.md` §9. Tracking issue:
//! `issues/surface-function-types.md`.
//!
//! Nothing here touches the kernel: `Type::Pi`, `Term::Lam` and `Term::App`
//! have been there since v0. What is new is that the *surface* can say them,
//! so every positive test below is elaborated and then re-checked by the real
//! kernel, and a wrong elaboration shows up as a rejection.

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

// §9.1 — the type parses, elaborates, and is usable as a parameter type.
// Right-associativity is observed by applying the result twice.
#[test]
fn arrow_types_parse_and_associate_right() {
    elab(
        r#"
        fn ap(f: Nat -> Nat, n: Nat) -> Nat { f(n) }

        // `Nat -> Nat -> Nat` is `Nat -> (Nat -> Nat)`: applying it to one
        // argument leaves a function, which `ap` can then take.
        fn const2(a: Nat) -> Nat -> Nat { λ (b: Nat) => a }

        theorem right_assoc(): ap(const2(7), 3) = 7 { refl }
        "#,
    );
}

// §9.2 — `=` binds tighter than `->`.
#[test]
fn equality_binds_tighter_than_the_arrow() {
    elab(
        r#"
        theorem t(n: Nat): n = n -> n = n { λ (p: n = n) => p }
        "#,
    );
}

// §9.2 (regression) — the parenthesis rule. A type may open with `(` because
// it groups a *type*, or because it opens the expression that is an
// equality's left endpoint. `add_assoc`'s statement is the second kind and
// was broken by the first draft of the rule.
#[test]
fn a_leading_paren_can_open_an_expression_not_a_type() {
    elab(
        r#"
        fn add(a: Nat, b: Nat) -> Nat {
            match b { Zero => a, Succ(k) => Succ(add(a, k)) }
        }

        theorem assoc_shaped(a: Nat, b: Nat, c: Nat): (a + b) + c = (a + b) + c
        { refl }

        // …and the first kind still groups.
        fn apply_fn(f: (Nat -> Nat) -> Nat, g: Nat -> Nat) -> Nat { f(g) }
        "#,
    );
}

// §9.3 — `D<A> -> B`: the applied-inductive case used to return before any
// arrow check, which is why the parse needed restructuring rather than an
// added branch.
#[test]
fn an_applied_inductive_can_be_a_domain() {
    elab(
        r#"
        inductive Box<A> { Wrap(A) }

        fn unwrap_with(f: Box<Nat> -> Nat, b: Box<Nat>) -> Nat { f(b) }

        fn get(b: Box<Nat>) -> Nat { match b { Wrap(x) => x } }

        theorem t(): unwrap_with(λ (b: Box<Nat>) => get(b), Wrap(4)) = 4 { refl }
        "#,
    );
}

// §9.4 — both spellings, same term.
#[test]
fn lambda_and_fun_are_the_same_binder() {
    elab(
        r#"
        fn a() -> Nat -> Nat { λ (x: Nat) => Succ(x) }
        fn b() -> Nat -> Nat { fun (x: Nat) => Succ(x) }
        theorem same(n: Nat): a()(n) = b()(n) { refl }
        "#,
    );
}

// §9.5 — checking mode supplies the domain, so the binder needs no
// annotation; inference mode requires one.
#[test]
fn checking_supplies_the_domain() {
    elab(
        r#"
        fn inc() -> Nat -> Nat { λ x => Succ(x) }
        theorem t(): inc()(1) = 2 { refl }

        // annotated, so it also infers
        fn inc2() -> Nat -> Nat { λ (x: Nat) => Succ(x) }
        theorem t2(): inc2()(1) = 2 { refl }
        "#,
    );
}

// §9.6 — juxtaposed binders are sugar for nesting.
#[test]
fn multi_binder_lambdas_equal_their_nested_form() {
    elab(
        r#"
        fn add(a: Nat, b: Nat) -> Nat {
            match b { Zero => a, Succ(k) => Succ(add(a, k)) }
        }

        fn flat() -> Nat -> Nat -> Nat { λ (x: Nat) (y: Nat) => add(x, y) }
        fn nested() -> Nat -> Nat -> Nat { λ (x: Nat) => λ (y: Nat) => add(x, y) }
        theorem same(a: Nat, b: Nat): flat()(a)(b) = nested()(a)(b) { refl }
        "#,
    );
}

// §9.7 — β fires.
#[test]
fn beta_fires_on_an_applied_lambda() {
    elab(
        r#"
        theorem t(): (λ (x: Nat) => Succ(x))(3) = 4 { refl }
        theorem open_beta(n: Nat): (λ (x: Nat) => Succ(x))(n) = Succ(n) { refl }
        "#,
    );
}

// §9.8 — **η at `Π` is definitional** (`crates/kernel/src/conv.rs:535`
// compares at a `Π` by applying both sides to a fresh variable, at every
// layer). Users will expect this; it is cheap to protect and would be an
// unpleasant surprise to lose.
#[test]
fn eta_at_pi_is_definitional() {
    elab(
        r#"
        fn inc(n: Nat) -> Nat { Succ(n) }

        // η against a global.
        theorem eta_global(): (λ (x: Nat) => inc(x)) = inc { refl }

        // η against a *neutral* — `f` is a bound variable, so nothing about
        // it reduces, and only the η rule can close this.
        theorem eta_neutral(f: Nat -> Nat): (λ (x: Nat) => f(x)) = f { refl }

        // …and one level up.
        theorem eta_twice(f: Nat -> Nat -> Nat):
            (λ (x: Nat) (y: Nat) => f(x)(y)) = f { refl }
        "#,
    );
}

// §9.9 — a function-typed parameter, taken and applied.
#[test]
fn a_function_typed_parameter() {
    elab(
        r#"
        fn twice(f: Nat -> Nat, n: Nat) -> Nat { f(f(n)) }
        theorem t(): twice(λ x => Succ(x), 0) = 2 { refl }
        theorem open(f: Nat -> Nat, n: Nat): twice(f, n) = f(f(n)) { refl }
        "#,
    );
}

// §9.10 — **the payoff.** `cong` over an *arbitrary* function, which
// `issues/surface-operators.md` deferred for want of function values. The
// motive is genuinely dependent in `f`.
#[test]
fn cong_over_an_arbitrary_function() {
    elab(
        r#"
        theorem cong(f: Nat -> Nat, {a: Nat}, {b: Nat}, p: a = b): f(a) = f(b)
        { j(p, λ y q => f(a) = f(y), refl) }

        fn add(a: Nat, b: Nat) -> Nat {
            match b { Zero => a, Succ(k) => Succ(add(a, k)) }
        }

        fn double(n: Nat) -> Nat { add(n, n) }

        theorem use_it(n: Nat, m: Nat, p: n = m): double(n) = double(m)
        { cong(λ (x: Nat) => double(x), p) }

        // the same lemma at a different function, which is the point of
        // taking `f` as an argument at all
        theorem use_it_again(n: Nat, m: Nat, p: n = m): Succ(n) = Succ(m)
        { cong(λ (x: Nat) => Succ(x), p) }
        "#,
    );
}

// §9.11 — partial application of a *named* callee with no implicits was
// already supported by `apply_explicit`; it now has a type to be written at.
#[test]
fn partial_application_yields_a_function_value() {
    elab(
        r#"
        fn add(a: Nat, b: Nat) -> Nat {
            match b { Zero => a, Succ(k) => Succ(add(a, k)) }
        }

        fn add3(a: Nat, b: Nat, c: Nat) -> Nat { add(a, add(b, c)) }

        fn plus1() -> Nat -> Nat -> Nat { add3(1) }

        theorem t(): plus1()(2)(3) = 6 { refl }
        theorem agrees(b: Nat, c: Nat): add3(1)(b)(c) = add3(1, b, c) { refl }
        "#,
    );
}

// §9.12 — the head of an application is an expression, not a name.
#[test]
fn the_head_of_an_application_can_be_any_expression() {
    elab(
        r#"
        theorem t(): (λ (f: Nat -> Nat) => f(0))(λ (x: Nat) => Succ(x)) = 1 { refl }

        fn add(a: Nat, b: Nat) -> Nat {
            match b { Zero => a, Succ(k) => Succ(add(a, k)) }
        }

        fn pick(n: Nat) -> Nat -> Nat { λ (x: Nat) => add(n, x) }
        theorem chained(): pick(2)(3) = 5 { refl }
        "#,
    );
}

// §9.13 — the interactions the scheme said to observe rather than assume
// (§6). Each is "true by construction"; so was the `Vec^l` level drop.
mod interactions {
    use super::*;

    // §6.1 — a self-call inside a lambda body. The `Nat` guard compares a de
    // Bruijn *level* and the `Wf` guard shifts by `names.len() - depth`, both
    // of which are stable under the extra binder a lambda pushes.
    #[test]
    fn a_self_call_under_a_lambda_still_descends() {
        elab(
            r#"
            inductive Tree { Leaf, Node(Tree, Tree) }

            fn add(a: Nat, b: Nat) -> Nat {
                match b { Zero => a, Succ(k) => Succ(add(a, k)) }
            }

            fn ap(f: Nat -> Nat, n: Nat) -> Nat { f(n) }

            fn size(t: Tree) -> Nat {
                match t {
                    Leaf => 1,
                    // the recursive calls happen *under* a lambda binder
                    Node(l, r) => ap(λ (k: Nat) => add(k, size(r)), size(l)),
                }
            }

            theorem s0(): size(Leaf) = 1 { refl }
            // `ap(λ k => add(k, size(r)), size(l))` at `l = r = Leaf` is
            // `add(1, 1)`, so the count is "sum of the children", not a node
            // count — what matters here is that the self-calls *under the
            // lambda* elaborate to the ih at all.
            theorem s2(): size(Node(Leaf, Leaf)) = 2 { refl }
            theorem s3(): size(Node(Node(Leaf, Leaf), Leaf)) = 3 { refl }
            "#,
        );
    }

    // …and on `Nat`, whose guard is the positional one.
    #[test]
    fn a_nat_self_call_under_a_lambda_still_descends() {
        elab(
            r#"
            fn ap(f: Nat -> Nat, n: Nat) -> Nat { f(n) }

            fn dbl(n: Nat) -> Nat {
                match n {
                    Zero => 0,
                    Succ(k) => ap(λ (x: Nat) => Succ(Succ(x)), dbl(k)),
                }
            }

            theorem d0(): dbl(0) = 0 { refl }
            theorem d3(): dbl(3) = 6 { refl }
            "#,
        );
    }

    // §6.2 — an alias (a `let`, and a `Wf` arm binder) referenced from under
    // a lambda binder. Aliases carry a `depth` and are shifted on use.
    #[test]
    fn an_alias_is_shifted_correctly_under_a_lambda() {
        elab(
            r#"
            inductive Tree { Leaf, Node(Tree, Tree) }

            fn add(a: Nat, b: Nat) -> Nat {
                match b { Zero => a, Succ(k) => Succ(add(a, k)) }
            }

            fn ap(f: Nat -> Nat, n: Nat) -> Nat { f(n) }
            fn one(t: Tree) -> Nat { 1 }

            fn f(n: Nat) -> Nat {
                let k = Succ(n);
                ap(λ (x: Nat) => add(k, x), k)
            }
            theorem t(): f(1) = 4 { refl }

            // the arm binder `l` is an alias too (tier-1 §5.1), used under λ
            fn g(t: Tree) -> Nat {
                match t {
                    Leaf => 0,
                    Node(l, r) => ap(λ (x: Nat) => add(one(l), x), one(r)),
                }
            }
            theorem u(): g(Node(Leaf, Leaf)) = 2 { refl }
            "#,
        );
    }

    // §6.3 — a hole raised *under* a lambda binder. The scheme predicted this
    // would need a rejection: `new_goal` builds `?m^{id_Γ}` over the current
    // Γ, which now includes the λ-binder, while the `on` discharge sits
    // outside the lambda. It turns out to work, because an `on` RHS is
    // elaborated *in the goal world* (issues/goal-holes.md) — so the binder is
    // legitimately in scope there and means the binder.
    //
    // Kept as a test rather than a note, because "the name resolves to the
    // wrong variable but the term still typechecks" is the exact hazard class
    // of [[tyvar-scoping-in-lowered-fields]]: the negative control is what
    // distinguishes `y` meaning the binder from `y` meaning a neighbouring
    // index.
    #[test]
    fn a_hole_under_a_lambda_binder_sees_the_binder() {
        elab(
            r#"
            fn ap(f: Nat -> Nat, n: Nat) -> Nat { f(n) }

            fn g(n: Nat) -> Nat {
                ap(λ (y: Nat) => ?h, n)
                on ?h := Succ(y);
            }

            theorem check(): g(1) = 2 { refl }
            "#,
        );
    }

    // …the negative control. If `y` above were silently resolving to `n`, or
    // to any other index, `g(1)` would not be `2` and this would be the
    // passing one instead.
    #[test]
    fn the_binder_a_hole_sees_is_not_a_neighbouring_index() {
        let msg = elab_err(
            r#"
            fn ap(f: Nat -> Nat, n: Nat) -> Nat { f(n) }

            fn g(n: Nat) -> Nat {
                ap(λ (y: Nat) => ?h, n)
                on ?h := Succ(y);
            }

            theorem check(): g(1) = 3 { refl }
            "#,
        );
        assert!(msg.contains("NotConvertible"), "{msg}");
    }

    // §6.5 — a partially applied function value, applied again.
    #[test]
    fn a_partial_application_can_be_applied_again() {
        elab(
            r#"
            fn add(a: Nat, b: Nat) -> Nat {
                match b { Zero => a, Succ(k) => Succ(add(a, k)) }
            }

            fn add3(a: Nat, b: Nat, c: Nat) -> Nat { add(a, add(b, c)) }
            fn step(a: Nat) -> Nat -> Nat -> Nat { add3(a) }
            theorem t(a: Nat, b: Nat, c: Nat): step(a)(b)(c) = add3(a, b, c) { refl }
            "#,
        );
    }
}

// §9.14 — the rejections, with their messages.
mod rejections {
    use super::*;

    #[test]
    fn an_unannotated_binder_needs_a_checking_position() {
        // `let` with no annotation infers, so the binder has nothing to take
        // its domain from.
        let msg = elab_err(
            r#"
            fn f(n: Nat) -> Nat {
                let g = λ x => Succ(x);
                n
            }
            "#,
        );
        assert!(msg.contains("needs a type annotation"), "{msg}");
        assert!(msg.contains("checking position"), "{msg}");
    }

    #[test]
    fn a_lambda_needs_a_function_type() {
        let msg = elab_err("fn f() -> Nat { λ (x: Nat) => x }");
        assert!(msg.contains("lambda needs a function type"), "{msg}");
    }

    #[test]
    fn a_lambda_expected_type_value_is_decoded_for_the_diagnostic() {
        let msg = elab_err(
            r#"
            fn N(v: Nat) -> Type { Nat }
            fn bad(v: Nat) -> N(v) { λ x => x }
            "#,
        );
        assert!(msg.contains("found `Nat`"), "{msg}");
        assert!(!msg.contains("El["), "{msg}");
    }

    #[test]
    fn a_wrong_binder_annotation_is_diagnosed() {
        let msg = elab_err(
            r#"
            inductive Bool { True, False }
            fn f() -> Nat -> Nat { λ (x: Bool) => 0 }
            "#,
        );
        assert!(msg.contains("not the one expected here"), "{msg}");
    }

    // Successor of `implicit_binders_are_diagnosed_not_parsed` (retired
    // 2026-08-06): both spellings are parses now
    // (docs/language/implicit-binders-design.md §8) — a `{n: Nat}` parameter type
    // elaborates, and an implicit lambda binder is accepted where the
    // expected skeleton says implicit. What stays refused is the mark in a
    // *result* position, whose skeleton has no consumer (§3.4), and an
    // implicit lambda binder against a skeleton-less expected type (§6.2).
    #[test]
    fn implicit_binders_parse_where_a_skeleton_consumes_them() {
        elab("fn f(g: {n: Nat} -> Nat) -> Nat { 0 }");
        elab(
            r#"
            fn use1(f: {n: Nat} -> Nat) -> Nat { 0 }
            fn go() -> Nat { use1(λ {n: Nat} => n) }
            "#,
        );

        let res = elab_err("fn mk() -> {n: Nat} -> Nat { λ {n: Nat} => n }");
        assert!(res.contains("this position cannot use one"), "{res}");
        assert!(res.contains("implicit-binders-in-function-types"), "{res}");

        let lam = elab_err("fn f() -> Nat -> Nat { λ {x: Nat} => x }");
        assert!(lam.contains("carries no implicitness"), "{lam}");
    }

    // What makes a function field infinitary is a *self-occurrence* inside
    // it, not the arrow (corrected 2026-07-27, docs/language/surface-records.md §11 —
    // the original check keyed on the shape of the field type and so rejected
    // `Nat -> Nat` too, which is an ordinary payload). Since 2026-10-20 the
    // strictly positive shape is the infinitary tier, lowered on `W`
    // (docs/inductives/inductive-tier2-w-lowering.md; its own acceptance is
    // inductive_tier2.rs), so `Acc`-style `Intro(h: Nat -> Acc)` declares.
    #[test]
    fn a_recursive_function_field_is_the_infinitary_tier() {
        elab("inductive Acc { Intro(h: Nat -> Acc) }");

        // …in the domain it is the *negative* occurrence, and stays a
        // rejection, by name.
        let neg = elab_err("inductive Bad { Mk(h: Bad -> Nat) }");
        assert!(neg.contains("function type"), "{neg}");
        assert!(neg.contains("not strictly positive"), "{neg}");
    }

    // The other side of the same correction: a function field that does not
    // mention the declaration is a payload, and always was one.
    #[test]
    fn a_non_recursive_function_field_is_a_payload() {
        elab(
            r#"
            inductive Endo { Mk(f: Nat -> Nat) }
            fn run(e: Endo, n: Nat) -> Nat { match e { Mk(f) => f(n) } }
            theorem runs(): run(Mk(λ (x: Nat) => x), 3) = 3 { refl }
            "#,
        );
    }

    // `@` suppresses implicit insertion, which is name-directed — so it is
    // the *grammar* that refuses a non-name head, one layer earlier than the
    // scheme placed it (§10). The elaborator keeps the same check, but
    // nothing at the surface can reach it.
    #[test]
    fn at_on_a_non_name_head_is_rejected_by_the_grammar() {
        let msg = elab_err("fn f() -> Nat { @(λ (x: Nat) => x)(0) }");
        assert!(msg.contains("call head after `@`"), "{msg}");
    }

    #[test]
    fn too_many_arguments_names_the_head() {
        let msg = elab_err("fn f(g: Nat -> Nat) -> Nat { g(1, 2) }");
        assert!(msg.contains("too many arguments"), "{msg}");
    }
}

// Multi-binder groups (issues/multi-binder-function-types.md). The parser
// desugars `(x: A, y: B) -> C` to the curried chain, so what is left to check
// here is that the elaborator sees exactly the chain — every test below writes
// the sugar and *uses* the value as the curried function it is.
mod multi_binder_groups {
    use super::*;

    #[test]
    fn a_higher_order_parameter_takes_two_binders_in_one_group() {
        elab(
            r#"
            fn ap2(f: (x: Nat, y: Nat) -> Nat, a: Nat, b: Nat) -> Nat { f(a)(b) }
            fn k(a: Nat) -> Nat -> Nat { λ (b: Nat) => a }

            theorem t(): ap2(k, 3, 7) = 3 { refl }
            "#,
        );
    }

    // The shared annotation, and the mix — plus the negative control that the
    // sugar is only sugar: the hand-curried callee is accepted at the sugared
    // type, because they are the same type.
    #[test]
    fn a_run_of_names_shares_one_annotation() {
        elab(
            r#"
            fn ap3(f: (x, y, z: Nat) -> Nat, a: Nat) -> Nat { f(a)(a)(a) }
            fn mixed(f: (x, y: Nat, p: 0 = 0) -> Nat) -> Nat { f(1)(2)(refl) }

            fn first(a: Nat) -> Nat -> Nat -> Nat {
                λ (b: Nat) => λ (c: Nat) => a
            }
            theorem t(): ap3(first, 5) = 5 { refl }
            "#,
        );
    }

    // A telescope: the second binder's type mentions the first binder, which
    // is the whole reason the group is not just a tuple of annotations.
    #[test]
    fn a_later_binders_type_mentions_an_earlier_binder() {
        elab(
            r#"
            fn use_eq(f: (n: Nat, p: n = n) -> Nat) -> Nat { f(2)(refl) }
            fn ignore(n: Nat) -> n = n -> Nat { λ (p: n = n) => n }

            theorem t(): use_eq(ignore) = 2 { refl }
            "#,
        );
    }

    // A parameter list takes the same run.
    #[test]
    fn a_parameter_run_elaborates_to_separate_parameters() {
        elab(
            r#"
            fn add(a, b: Nat) -> Nat {
                match b { Zero => a, Succ(k) => Succ(add(a, k)) }
            }
            theorem t(): add(2, 3) = 5 { refl }

            // …and the receiver mark still prefixes one name, beside a run.
            record Box { n: Nat }
            fn Box::shift(self b: Box, k, j: Nat) -> Nat { add(b.n, add(k, j)) }
            fn one() -> Box { Box { n: 1 } }
            theorem s(): one().shift(2, 3) = 6 { refl }
            "#,
        );
    }

    // Class fields are types, so they inherit the sugar; this is the case the
    // cleanup rider in the issue is about.
    #[test]
    fn a_class_field_takes_a_multi_binder_law() {
        elab(
            r#"
            class Semi<A> {
                op: (a, b: A) -> A,
                assoc: (a, b, c: A) -> op(op(a, b), c) = op(a, op(b, c))
            }

            fn add(a, b: Nat) -> Nat {
                match b { Zero => a, Succ(k) => Succ(add(a, k)) }
            }
            "#,
        );
    }

    // The negative control from the parser, seen through the real front end:
    // names with no annotation are not binders.
    #[test]
    fn an_unannotated_group_is_not_a_binder_list() {
        let msg = elab_err("fn f(g: (x, y) -> Nat) -> Nat { 0 }");
        assert!(msg.contains("has no type"), "{msg}");
    }
}
