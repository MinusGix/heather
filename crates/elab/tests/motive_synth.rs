//! Stage-2 motive synthesis (issues/elab-stage2-metas.md): the `match` arms
//! of the Nat suite drop their explicit `as λ z => M` motives. The elaborator
//! recovers the dependent motive by abstracting the (variable) scrutinee out
//! of the checking-position expected type; the kernel still gates every
//! declaration, so a wrong synthesized motive would be a rejection, not a
//! silent pass.

use heather_elab::Elaborator;

// The arithmetic lemmas, all `match`es motive-less. Lemma endpoints are still
// supplied explicitly (via `@`) so this file isolates motive synthesis from
// implicit-argument inference (which `implicit_args.rs` covers).
const NAT_SUITE_NO_MOTIVE: &str = r#"
fn add(m: Nat, n: Nat) -> Nat {
    match m {
        Zero => n,
        Succ(k, ih) => Succ(ih),
    }
}

theorem add_zero(n: Nat): add(n, 0) = n {
    match n {
        Zero => refl,
        Succ(k, ih) => @cong_succ(add(k, 0), k, ih),
    }
}

theorem add_succ(m: Nat, n: Nat): add(m, Succ(n)) = Succ(add(m, n)) {
    match m {
        Zero => refl,
        Succ(k, ih) => @cong_succ(add(k, Succ(n)), Succ(add(k, n)), ih),
    }
}

theorem add_comm(m: Nat, n: Nat): add(m, n) = add(n, m) {
    match m {
        Zero => @sym(add(n, 0), n, add_zero(n)),
        Succ(k, ih) => @trans(
            Succ(add(k, n)),
            Succ(add(n, k)),
            add(n, Succ(k)),
            @cong_succ(add(k, n), add(n, k), ih),
            @sym(add(n, Succ(k)), Succ(add(n, k)), add_succ(n, k))
        ),
    }
}

theorem add_assoc(a: Nat, b: Nat, c: Nat): add(add(a, b), c) = add(a, add(b, c)) {
    match a {
        Zero => refl,
        Succ(k, ih) => @cong_succ(add(add(k, b), c), add(k, add(b, c)), ih),
    }
}
"#;

#[test]
fn nat_suite_motives_synthesized() {
    let mut e = Elaborator::with_prelude().expect("prelude");
    e.elab_source(NAT_SUITE_NO_MOTIVE)
        .expect("motive-less Nat suite must elaborate and kernel-check");
}

#[test]
fn non_dependent_motive_still_works() {
    // A match whose expected type does not mention the scrutinee: the
    // synthesized motive is non-dependent and the kernel accepts it.
    let mut e = Elaborator::with_prelude().expect("prelude");
    e.elab_source(
        "theorem const_zero(n: Nat): 0 = 0 { match n { Zero => refl, Succ(k, ih) => ih } }",
    )
    .expect("non-dependent motive");
}

// ---------------------------------------------------------------------------
// Inference position (issues/match-arg-of-polymorphic-callee-needs-motive.md,
// 2026-08-17). Everything above is *checking* position, where the motive comes
// from abstracting the scrutinee out of the expected type. An argument of a
// polymorphic callee whose type argument is still unsolved has no expected
// type at all, so a `match` there was refused outright: it now takes its
// motive from an arm that binds nothing, and every other arm is checked
// against that — the reading is widened, never the meaning.

const LIST: &str = "inductive Bool2 { False2, True2 }\n\
                    inductive List<A> { Nil, Cons(head: A, tail: List<A>) }\n\
                    fn len<A>(xs: List<A>) -> Nat { match xs { Nil => 0, Cons(h, t) => Succ(len(t)) } }\n";

fn ok(src: &str) {
    let mut e = Elaborator::with_prelude().expect("prelude");
    if let Err(err) = e.elab_source(src) {
        panic!("expected success, got: {}", err.render(src));
    }
}

fn bad(src: &str) -> String {
    let mut e = Elaborator::with_prelude().expect("prelude");
    match e.elab_source(src) {
        Ok(()) => panic!("expected a refusal, but it checked:\n{src}"),
        Err(err) => err.render(src),
    }
}

#[test]
fn a_match_under_a_polymorphic_callee_needs_no_motive() {
    ok(&format!(
        "{LIST}
         fn probe<A>(b: Bool2, xs: List<A>) -> Nat {{
             len(match b {{ False2 => Nil, True2 => xs }})
         }}"
    ));
}

// The naming arm is the first that binds nothing — the *other* arms may bind,
// and are checked against the type it named rather than joined with it.
#[test]
fn only_one_arm_has_to_bind_nothing() {
    ok(&format!(
        "{LIST}
         fn probe<A>(ys: List<A>, xs: List<A>) -> Nat {{
             len(match ys {{ Nil => xs, Cons(h, t) => t }})
         }}"
    ));
}

// Negative control: every arm binds, so no arm can name the type without a
// branch context, and the message is the one that asks for the motive.
#[test]
fn every_arm_binding_still_asks_for_a_motive() {
    let e = bad(&format!(
        "{LIST}
         inductive Two<A> {{ L(v: A), R(v: A) }}
         fn probe<A>(t: Two<List<A>>) -> Nat {{
             len(match t {{ L(v) => v, R(v) => v }})
         }}"
    ));
    assert!(e.contains("needs a motive"), "{e}");
}

// Negative control: checking position is untouched — a motive-less `match`
// there still goes through the stage-2 synthesis above, dependent motive and
// all, which this file's first test is the acceptance for.
#[test]
fn the_dependent_synthesis_is_not_disturbed() {
    ok("fn add2(m: Nat, n: Nat) -> Nat { match m { Zero => n, Succ(k, ih) => Succ(ih) } }
        theorem t(n: Nat): add2(n, 0) = n {
            match n { Zero => refl, Succ(k, ih) => @cong_succ(add2(k, 0), k, ih) }
        }");
}
