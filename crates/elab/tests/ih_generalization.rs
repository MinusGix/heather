//! Acceptance for issues/ih-generalization.md
//! (docs/tactics/ih-generalization-design.md): a structurally recursive `match` whose
//! self-calls *vary* a non-decreasing parameter gets a motive that quantifies
//! that parameter, computed by the elaborator. Before this round every such
//! definition was curried by hand (`fn sub(m: Nat) -> Nat -> Nat`) and every
//! such proof wrote its motive out.
//!
//! The lowering builds the same recursor the manual route did, so the
//! analysis is untrusted: everything here passes the kernel, and the negative
//! controls at the end are the ones that show a wrong varied argument is
//! refused rather than accepted.
//!
//! What the positives vary (docs/testing-generated-terms.md): a literal *and*
//! a neutral scrutinee, an **open** element type (`take<A>`, `foldl<A, B>`),
//! checking position throughout, and a dependent motive (every theorem).

use heather_elab::{ElabError, Elaborator};

/// A second-argument recursion for `add`, so an accumulator proof has a
/// definitional side to lean on.
const PLUS: &str = r#"
fn plus(m: Nat, n: Nat) -> Nat {
    match n {
        Zero => m,
        Succ(k) => Succ(plus(m, k)),
    }
}

theorem plus_succ_left(m: Nat, n: Nat): plus(Succ(m), n) = Succ(plus(m, n)) {
    match n {
        Zero => refl,
        Succ(k) => Nat::cong_succ(plus_succ_left(m, k)),
    }
}
"#;

fn ok(src: &str) -> Elaborator {
    let mut e = Elaborator::with_prelude().expect("prelude");
    e.elab_source(&format!("{PLUS}\n{src}"))
        .unwrap_or_else(|err| panic!("expected this to check, got: {err:?}"));
    e
}

fn elab_err(src: &str) -> String {
    let mut e = Elaborator::with_prelude().expect("prelude");
    match e.elab_source(&format!("{PLUS}\n{src}")) {
        Err(ElabError::Elab { msg, .. }) => msg,
        other => panic!("expected a surface elaboration error, got {other:?}"),
    }
}

fn any_err(src: &str) -> String {
    let mut e = Elaborator::with_prelude().expect("prelude");
    match e.elab_source(&format!("{PLUS}\n{src}")) {
        Err(other) => format!("{other:?}"),
        Ok(()) => panic!("expected this to be refused"),
    }
}

// -- programs on Nat ----------------------------------------------------------

/// Truncated subtraction, **uncurried**: both arguments descend together, and
/// the inner `match n` sits on the generalized parameter. `lib/std/num/nat.hthr`'s
/// `sub` is the curried spelling this replaces.
const SUB: &str = r#"
fn sub(m: Nat, n: Nat) -> Nat {
    match m {
        Zero => 0,
        Succ(m2) => match n { Zero => Succ(m2), Succ(n2) => sub(m2, n2) },
    }
}
"#;

#[test]
fn uncurried_sub_computes_at_a_literal() {
    // One `elim_Nat`, so closed arguments still compute: `refl` alone.
    ok(&format!(
        "{SUB}\ntheorem five_minus_two(): sub(5, 2) = 3 {{ refl }}\n\
         theorem two_minus_five(): sub(2, 5) = 0 {{ refl }}"
    ));
}

#[test]
fn uncurried_sub_proves_at_a_neutral_scrutinee() {
    ok(&format!(
        "{SUB}\n\
         theorem sub_zero(m: Nat): sub(m, 0) = m {{ match m {{ Zero => refl, Succ(k) => refl }} }}\n\
         theorem sub_self(n: Nat): sub(n, n) = 0 {{ match n {{ Zero => refl, Succ(k) => sub_self(k) }} }}"
    ));
}

/// An accumulator: the varying argument is the *result* being built, and the
/// theorem about it is exactly the IH-generalizing proof the issue names —
/// the ih is wanted at `Succ(acc)`, not at `acc`.
const ADD_ACC: &str = r#"
fn add_acc(n: Nat, acc: Nat) -> Nat {
    match n {
        Zero => acc,
        Succ(k) => add_acc(k, Succ(acc)),
    }
}

theorem add_acc_spec(n: Nat, acc: Nat): add_acc(n, acc) = plus(acc, n) {
    match n {
        Zero => refl,
        Succ(k) => trans(add_acc_spec(k, Succ(acc)), plus_succ_left(acc, k)),
    }
}
"#;

#[test]
fn accumulator_program_and_its_generalized_proof() {
    ok(&format!(
        "{ADD_ACC}\ntheorem three_two(): add_acc(3, 2) = 5 {{ refl }}"
    ));
}

#[test]
fn a_generalized_proof_is_still_refused_when_wrong() {
    // The ih at `Succ(acc)` says `add_acc(k, Succ(acc)) = plus(Succ(acc), k)`;
    // the goal here wants `= acc`. Generalization hands the arm a *stronger*
    // hypothesis, not a free pass — the kernel still has to agree.
    let msg = any_err(&format!(
        "{ADD_ACC}\n\
         theorem wrong(n: Nat, acc: Nat): add_acc(n, acc) = acc {{\n\
             match n {{ Zero => refl, Succ(k) => wrong(k, Succ(acc)) }}\n\
         }}"
    ));
    assert!(!msg.is_empty());
}

// -- a Type-valued predicate ---------------------------------------------------

/// The recommended propositional order, uncurried — the spelling
/// [[nat-order-kit]] wanted and could not write (issue log, 2026-08-16).
/// `False` is declared locally so the fixture rests on the prelude alone.
const LE: &str = r#"
inductive False {}

fn Le(n: Nat, m: Nat) -> Type {
    match n {
        Zero => True,
        Succ(k) => match m { Zero => False, Succ(l) => Le(k, l) },
    }
}

theorem le_refl(n: Nat): Le(n, n) {
    match n { Zero => trivial, Succ(k) => le_refl(k) }
}
"#;

#[test]
fn uncurried_predicate_computes_and_is_provable() {
    ok(&format!(
        "{LE}\n\
         theorem two_le_three(): Le(2, 3) {{ trivial }}\n\
         theorem not_three_le_two(h: Le(3, 2)): False {{ h }}"
    ));
}

#[test]
fn hypotheses_after_the_generalized_parameters_stay_reducible() {
    // Transitivity: `m` and `l` are generalized, the hypotheses stay in
    // checking position behind the arrows (as `lib/std/num/nat.hthr`'s `le_trans`
    // keeps them), and the self-call is over-applied to them
    // (issues/call-site-overapplication.md).
    ok(&format!(
        "{LE}\n\
         theorem le_trans(n: Nat, m: Nat, l: Nat): Le(n, m) -> Le(m, l) -> Le(n, l) {{\n\
             match n {{\n\
                 Zero => λ h1 h2 => trivial,\n\
                 Succ(k) => match m {{\n\
                     Zero => λ bad h2 => match bad {{}},\n\
                     Succ(m2) => match l {{\n\
                         Zero => λ a bad => match bad {{}},\n\
                         Succ(l2) => λ a c => le_trans(k, m2, l2, a, c),\n\
                     }},\n\
                 }},\n\
             }}\n\
         }}"
    ));
}

#[test]
fn a_dependent_hypothesis_is_generalized_with_its_parameter() {
    // `h : acc = b` mentions both varied parameters, so it is generalized with
    // them (the dependency closure) and the self-call passes it *changed*: the
    // ih is `Π(acc' b' : Nat)(h' : acc' = b'). …` and the call instantiates
    // all three. Every previous customer varied only indices; this one varies
    // a proof.
    ok(&format!(
        "{ADD_ACC}\n\
         theorem acc_eq(n: Nat, acc: Nat, b: Nat, h: acc = b): add_acc(n, acc) = add_acc(n, b) {{\n\
             match n {{\n\
                 Zero => h,\n\
                 Succ(k) => acc_eq(k, Succ(acc), Succ(b), Nat::cong_succ(h)),\n\
             }}\n\
         }}"
    ));
    // A hypothesis that has to *reduce* at the inner `match` is kept behind
    // the arrow, exactly as the library keeps it — the context is not refined
    // by a `match`, and generalization does not change that.
    ok(&format!(
        "{LE}\n\
         theorem le_succ_r(n: Nat, m: Nat): Le(n, m) -> Le(n, Succ(m)) {{\n\
             match n {{\n\
                 Zero => λ h => trivial,\n\
                 Succ(k) => match m {{\n\
                     Zero => λ bad => match bad {{}},\n\
                     Succ(m2) => λ good => le_succ_r(k, m2, good),\n\
                 }},\n\
             }}\n\
         }}"
    ));
}

// -- a Wf inductive at an open element type -----------------------------------

const LIST: &str = r#"
inductive List<A> { Nil, Cons(A, List<A>) }

fn len<A>(xs: List<A>) -> Nat {
    match xs { Nil => 0, Cons(h, t) => Succ(len(t)) }
}

fn take<A>(xs: List<A>, n: Nat) -> List<A> {
    match xs {
        Nil => Nil,
        Cons(h, t) => match n { Zero => Nil, Succ(k) => Cons(h, take(t, k)) },
    }
}

fn foldl<A, B>(xs: List<A>, f: B -> A -> B, z: B) -> B {
    match xs {
        Nil => z,
        Cons(h, t) => foldl(t, f, f(z, h)),
    }
}
"#;

#[test]
fn wf_recursion_generalizes_at_an_open_element_type() {
    ok(&format!(
        "{LIST}\n\
         theorem take_two(): take(Cons(1, Cons(2, Cons(3, Nil))), 2) = Cons(1, Cons(2, Nil)) {{ refl }}\n\
         theorem take_nil<A>(n: Nat): take<A>(Nil<A>, n) = Nil<A> {{ refl }}\n\
         theorem take_zero<A>(xs: List<A>): take(xs, 0) = Nil {{\n\
             match xs {{ Nil => refl, Cons(h, t) => refl }}\n\
         }}\n\
         theorem fold_plus(): foldl(Cons(1, Cons(2, Nil)), λ (b: Nat) (a: Nat) => plus(b, a), 3) = 6 {{ refl }}"
    ));
}

#[test]
fn a_fold_law_generalizes_the_seed_at_a_wf_guard() {
    // The seed varies at every step, so the law is proved with the ih at
    // `Succ(z)`: the higher-order customer from the L1 wave (issue log,
    // 2026-08-17), stated uncurried.
    ok(&format!(
        "{LIST}\n\
         theorem fold_count<A>(xs: List<A>, z: Nat): foldl(xs, λ (b: Nat) (a: A) => Succ(b), z) = plus(z, len(xs)) {{\n\
             match xs {{\n\
                 Nil => refl,\n\
                 Cons(h, t) => trans(fold_count(t, Succ(z)), plus_succ_left(z, len(t))),\n\
             }}\n\
         }}"
    ));
}

// -- composition with the rest of the recursion machinery ---------------------

#[test]
fn composes_with_a_course_of_values_window() {
    // Depth-2 descent (`l` under `match k`) *and* a varying parameter: the
    // window's components are Π types, and a self-call projects then applies.
    ok(r#"
        fn skip2(n: Nat, acc: Nat) -> Nat {
            match n {
                Zero => acc,
                Succ(k) => match k {
                    Zero => acc,
                    Succ(l) => skip2(l, Succ(acc)),
                },
            }
        }
        theorem skip2_five(): skip2(5, 0) = 2 { refl }
        theorem skip2_spec(n: Nat, acc: Nat): plus(acc, n) = plus(acc, n) { refl }
    "#);
}

#[test]
fn an_implicit_parameter_varies_under_at() {
    ok(r#"
        fn f(n: Nat, {m: Nat}) -> Nat {
            match n { Zero => m, Succ(k) => @f(k, Succ(m)) }
        }
        theorem f_two(): @f(2, 1) = 3 { refl }
    "#);
}

#[test]
fn unchanged_arguments_still_emit_the_plain_recursor() {
    // No self-call varies anything, so nothing is generalized and the term is
    // the one the Nat suite always produced — visible here only as "still
    // checks", which is the point: the empty case is a no-op.
    let e = ok("theorem plus_zero_left(n: Nat): plus(0, n) = n { match n { Zero => refl, Succ(k) => Nat::cong_succ(plus_zero_left(k)) } }");
    assert!(e.psi().bindings.len() > 4);
}

// -- negative controls --------------------------------------------------------

#[test]
fn a_written_motive_is_the_manual_route() {
    // A `match` with a *written* motive is the manual route, and a written
    // motive that does not quantify `m` has no ih at `Succ(m)`. The plain
    // lowering refuses the varying call; recursion at the top generalizes
    // `m` around the whole body (docs/language/recursion/recursion-at-the-top-design.md §5),
    // and the written `match` takes its arm inside it.
    ok(r#"
        fn g(n: Nat, m: Nat) -> Nat {
            match n as λ z => Nat { Zero => m, Succ(k) => g(k, Succ(m)) }
        }
        theorem g_2(): g(2, 0) = 2 { refl }
        theorem g_step(k: Nat, m: Nat): g(Succ(k), m) = g(k, Succ(m)) { refl }
        "#);
}

#[test]
fn a_shadowing_name_does_not_fake_an_unchanged_argument() {
    // The scan reads `m` and plans nothing; the by-binder check then sees a
    // lambda-bound `m`, not the parameter, and refuses the plain lowering.
    // Neither half trusts the name. At the top, `m` is generalized, so the
    // call means what it says: `s(Succ(k), m) = s(k, 0)`.
    ok(r#"
        fn s(n: Nat, m: Nat) -> Nat {
            match n { Zero => m, Succ(k) => (λ (m: Nat) => s(k, m))(0) }
        }
        theorem s_1(): s(1, 5) = 0 { refl }
        theorem s_step(k: Nat, m: Nat): s(Succ(k), m) = s(k, 0) { refl }
        "#);
}

#[test]
fn a_varied_argument_at_the_wrong_type_is_refused_where_written() {
    let msg = any_err(
        r#"
        fn h(n: Nat, m: Nat) -> Nat {
            match n { Zero => m, Succ(k) => h(k, refl) }
        }
        "#,
    );
    assert!(!msg.is_empty());
}

#[test]
fn an_implicit_parameter_varied_without_at_is_named() {
    let msg = elab_err(
        r#"
        fn f(n: Nat, {m: Nat}) -> Nat {
            match n { Zero => m, Succ(k) => plus(@f(k, Succ(m)), f(k)) }
        }
        "#,
    );
    assert!(msg.contains("pass it explicitly"), "{msg}");
}

// -- self-calls under `j` and a record update ---------------------------------
// (issues/ih-generalization-misses-call-under-j.md: the scan's walk skipped
// these forms, so the varying call met the by-binder refusal)

#[test]
fn a_varying_call_as_the_case_of_j_generalizes() {
    // The congruence shape (`ITree::same_sym`): rewrite the other side with
    // `j`, then recurse with `b` and the equation both varied. A neutral
    // scrutinee, a dependent goal, and the call in `j`'s case — which is
    // checked at the motive's instance, not inferred.
    ok(&format!(
        "{LE}\n\
         theorem le_of_eq(a: Nat, b: Nat, e: a = b): Le(a, b) {{\n\
             match a {{\n\
                 Zero => trivial,\n\
                 Succ(k) => j(e, λ y q => Le(Succ(k), y), le_of_eq(k, k, refl)),\n\
             }}\n\
         }}\n\
         theorem three_le_three(): Le(3, 3) {{ le_of_eq(3, 3, refl) }}"
    ));
}

#[test]
fn a_varying_call_under_j_computes_at_a_literal() {
    // A program, so the recursor has to reduce: each step's `j` is at `refl`
    // and contracts to its case, which is the ih at the varied arguments.
    ok(r#"
        fn walk(n: Nat, m: Nat, e: n = m) -> Nat {
            match n { Zero => m, Succ(k) => j(e, λ y q => Nat, Succ(walk(k, k, refl))) }
        }
        theorem walk_three(): walk(3, 3, refl) = 3 { refl }
    "#);
}

#[test]
fn a_varying_call_in_a_record_update_generalizes() {
    ok(r#"
        record P { x: Nat, y: Nat }
        fn spread(n: Nat, m: Nat) -> P {
            match n {
                Zero => P { x: m, y: m },
                Succ(k) => spread(k, Succ(m)) with { y = 0 },
            }
        }
        theorem spread_two(): spread(2, 1) = P(3, 0) { refl }
    "#);
}

#[test]
fn a_wrong_varied_argument_under_j_is_still_refused() {
    // Negative control: the scan now plans the generalization, and the ih's
    // Π domain is what refuses `e` (a proof of `Succ(k) = b`) where `k = k`
    // is due — the call is not waved through because it was found.
    let msg = any_err(&format!(
        "{LE}\n\
         theorem bad(a: Nat, b: Nat, e: a = b): Le(a, b) {{\n\
             match a {{\n\
                 Zero => trivial,\n\
                 Succ(k) => j(e, λ y q => Le(Succ(k), y), bad(k, k, e)),\n\
             }}\n\
         }}"
    ));
    assert!(!msg.contains("unchanged"), "{msg}");
}
