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
        Succ(k, ih) => @Nat::cong_succ(add(k, 0), k, ih),
    }
}

theorem add_succ(m: Nat, n: Nat): add(m, Succ(n)) = Succ(add(m, n)) {
    match m {
        Zero => refl,
        Succ(k, ih) => @Nat::cong_succ(add(k, Succ(n)), Succ(add(k, n)), ih),
    }
}

theorem add_comm(m: Nat, n: Nat): add(m, n) = add(n, m) {
    match m {
        Zero => @sym(add(n, 0), n, add_zero(n)),
        Succ(k, ih) => @trans(
            Succ(add(k, n)),
            Succ(add(n, k)),
            add(n, Succ(k)),
            @Nat::cong_succ(add(k, n), add(n, k), ih),
            @sym(add(n, Succ(k)), Succ(add(n, k)), add_succ(n, k))
        ),
    }
}

theorem add_assoc(a: Nat, b: Nat, c: Nat): add(add(a, b), c) = add(a, add(b, c)) {
    match a {
        Zero => refl,
        Succ(k, ih) => @Nat::cong_succ(add(add(k, b), c), add(k, add(b, c)), ih),
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
            match n { Zero => refl, Succ(k, ih) => @Nat::cong_succ(add2(k, 0), k, ih) }
        }");
}

// ---------------------------------------------------------------------------
// Abstracting the scrutinee TERM, and reducing the goal to find it
// (docs/goal-motive-synthesis-design.md; issues/goal-motive-by-scrutinee-
// abstraction.md and issues/nested-match-on-field-binder-motive.md, both
// 2026-08-17).
//
// Two failure conditions, one fix: motive synthesis used to abstract only a
// `Term::Var`, and only where the goal already spelled it. A constructor field
// binder is a *projection* out of the arm's value, and a goal that mentions
// `filter(Cons(h, t), p)` mentions `p(h)` only after it reduces. Neither is a
// variable occurring in the goal as written, and both are recoverable.
//
// The axes (docs/testing-generated-terms.md): every theorem below is a
// *checking* position; the scrutinee is neutral in one test of each pair and a
// literal constructor in the other; `Pack<A>` and `filt` carry an OPEN element
// type; and the last three tests are the negative controls — arms that
// genuinely disagree, a sibling field that must not be abstracted, and a split
// on a decision the goal is not blocked on.

// A constructor field binder: `n` is `fst(snd v)`, never a variable, and the
// arm's goal is stated at `v`, so the abstraction has to rebuild `v` around
// `z`. This is the issue's four-line repro verbatim.
const BOX: &str = "inductive Box { Wrap(n: Nat) }
    fn ddb(b: Box) -> Box {
        match b { Wrap(n) => match n { Zero => Wrap(0), Succ(k) => Wrap(Succ(k)) } }
    }
";

#[test]
fn a_nested_match_on_a_field_binder_needs_no_motive() {
    ok(&format!(
        "{BOX}
         theorem ddb_id(b: Box): ddb(b) = b {{
             match b {{ Wrap(n) => match n {{ Zero => refl, Succ(k) => refl }} }}
         }}"
    ));
}

// The same at a *literal* scrutinee, where everything reduces: axis 1's other
// end, and not redundant — a wrong motive is substituted away here and
// survives above.
#[test]
fn the_field_binder_split_also_checks_at_a_literal() {
    ok(&format!(
        "{BOX}
         theorem ddb_two(): ddb(Wrap(2)) = Wrap(2) {{
             match Wrap(2) {{ Wrap(n) => match n {{ Zero => refl, Succ(k) => refl }} }}
         }}"
    ));
}

// One level deeper: the `Succ` payload of the field, a genuine `Nat` binder
// inside a goal that only the outer abstraction put there.
#[test]
fn the_field_binder_split_nests_at_succ_depth() {
    ok("inductive Box { Wrap(n: Nat) }
        fn ddb2(b: Box) -> Box {
            match b {
                Wrap(n) => match n {
                    Zero => Wrap(0),
                    Succ(k) => match k { Zero => Wrap(1), Succ(j) => Wrap(Succ(Succ(j))) },
                },
            }
        }
        theorem ddb2_id(b: Box): ddb2(b) = b {
            match b {
                Wrap(n) => match n {
                    Zero => refl,
                    Succ(k) => match k { Zero => refl, Succ(j) => refl },
                },
            }
        }");
}

// Axis 2 on the field-binder path: an OPEN element type, and the split field
// is the *second* one, so the projection path is longer and the rebuilt value
// has to put the first field back by projection.
#[test]
fn a_field_binder_split_at_an_open_element_type() {
    ok("inductive Pack<A> { Mk(a: A, n: Nat) }
        fn norm<A>(p: Pack<A>) -> Pack<A> {
            match p { Mk(a, n) => match n { Zero => Mk(a, 0), Succ(k) => Mk(a, Succ(k)) } }
        }
        theorem norm_id<A>(p: Pack<A>): norm(p) = p {
            match p { Mk(a, n) => match n { Zero => refl, Succ(k) => refl } }
        }");
}

// The goal is one unfolding away: `filt(C(h, t), p)` mentions `p(h)` only
// after `filt` reduces, and the split is on `p(h)`. The `std/list` shape with
// the library's dependencies cut away — open element type, neutral scrutinee,
// checking position.
const FILT: &str = "inductive B { F, T }
    inductive L<A> { N, C(head: A, tail: L<A>) }
    fn app<A>(xs, ys: L<A>) -> L<A> {
        match xs { N => ys, C(h, t) => C(h, app(t, ys)) }
    }
    fn filt<A>(xs: L<A>, p: A -> B) -> L<A> {
        match xs { N => N, C(h, t) => match p(h) { T => C(h, filt(t, p)), F => filt(t, p) } }
    }
    theorem cong_c<A>(h: A, {a, b: L<A>}, e: a = b): C(h, a) = C(h, b) {
        j(e, λ y q => C(h, a) = C(h, y), refl)
    }
";

#[test]
fn a_split_on_a_decided_predicate_needs_no_motive() {
    ok(&format!(
        "{FILT}
         theorem filt_app<A>(xs, ys: L<A>, p: A -> B):
             filt(app(xs, ys), p) = app(filt(xs, p), filt(ys, p))
         {{
             match xs {{
                 N => {{}},
                 C(h, t) => match p(h) {{
                     T => cong_c(h, filt_app(t, ys, p)),
                     F => filt_app(t, ys, p),
                 }},
             }}
         }}"
    ));
}

// Negative control (axis 4), and the first issue's acceptance clause: a
// `match` whose arms genuinely disagree is still refused. The `T` arm is given
// the `F` arm's proof, which is about a different list.
#[test]
fn arms_that_genuinely_disagree_are_still_refused() {
    let e = bad(&format!(
        "{FILT}
         theorem filt_app_bad<A>(xs, ys: L<A>, p: A -> B):
             filt(app(xs, ys), p) = app(filt(xs, p), filt(ys, p))
         {{
             match xs {{
                 N => {{}},
                 C(h, t) => match p(h) {{
                     T => filt_app_bad(t, ys, p),
                     F => filt_app_bad(t, ys, p),
                 }},
             }}
         }}"
    ));
    assert!(e.contains("NotConvertible"), "{e}");
}

// Negative control on the reduction rung: the split is on a *different*
// decision than the one the goal is blocked on, so nothing converts, nothing
// is abstracted, and the declaration is refused instead of being accepted at a
// motive that guessed.
#[test]
fn a_split_on_another_decision_is_refused() {
    let e = bad(&format!(
        "{FILT}
         theorem filt_q<A>(xs, ys: L<A>, p: A -> B, q: A -> B):
             filt(app(xs, ys), p) = app(filt(xs, p), filt(ys, p))
         {{
             match xs {{
                 N => {{}},
                 C(h, t) => match q(h) {{
                     T => cong_c(h, filt_q(t, ys, p, q)),
                     F => filt_q(t, ys, p, q),
                 }},
             }}
         }}"
    ));
    // A kernel conversion refusal; since arm binders spell it is reported
    // with both sides at the site.
    assert!(e.contains("this has type `filt(app(t, ys), p) = app(filt(t, p), filt(ys, p))`"), "{e}");
}

// Mutation control: the goal mentions a second field of the same value, at the
// same type, which is NOT the scrutinee and must not be abstracted. An
// abstraction that generalized the whole value — or the wrong slot — would
// replace `m`'s occurrences too, and `Mk(z, …)` is not what the arms prove.
#[test]
fn a_sibling_field_is_not_abstracted() {
    ok("inductive Two { Mk(m: Nat, n: Nat) }
        fn bump(t: Two) -> Two {
            match t { Mk(m, n) => match n { Zero => Mk(m, 0), Succ(k) => Mk(m, Succ(k)) } }
        }
        theorem bump_id(t: Two): bump(t) = t {
            match t { Mk(m, n) => match n { Zero => refl, Succ(k) => refl } }
        }");
}

// …and the same shape at a false statement, so the control above is not
// vacuous: with the two fields swapped the theorem is wrong, and abstracting
// both would be one way to make it look right.
#[test]
fn a_sibling_field_swap_is_refused() {
    let e = bad("inductive Two { Mk(m: Nat, n: Nat) }
        fn swap(t: Two) -> Two {
            match t { Mk(m, n) => match n { Zero => Mk(m, 0), Succ(k) => Mk(Succ(k), m) } }
        }
        theorem swap_id(t: Two): swap(t) = t {
            match t { Mk(m, n) => match n { Zero => refl, Succ(k) => refl } }
        }");
    assert!(e.contains("NotConvertible"), "{e}");
}

// An absurd match's scrutinee sits at an Empty type, where conversion (Empty
// η) accepts any two terms. The goal `Le(Succ(k), Succ(Zero))` has stuck
// `Nat` subterms, and none of them is the scrutinee: a candidate stands only
// once its own type converts to the scrutinee's, so none is abstracted.
#[test]
fn an_absurd_match_abstracts_no_candidate_of_another_type() {
    ok("inductive False {}
        fn Le(n: Nat, m: Nat) -> Type {
            match n {
                Zero => True,
                Succ(k) => match m { Zero => False, Succ(l) => Le(k, l) },
            }
        }
        theorem le_succ_r(n: Nat, m: Nat): Le(n, m) -> Le(n, Succ(m)) {
            match n {
                Zero => λ h => trivial,
                Succ(k) => match m {
                    Zero => λ bad => match bad {},
                    Succ(m2) => λ good => le_succ_r(k, m2, good),
                },
            }
        }");
}
