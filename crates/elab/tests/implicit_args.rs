//! Stage-2 acceptance (issues/elab-stage2-metas.md): the Nat suite with
//! *both* stage-2 ergonomics on — motive-less `match` (synthesized motives)
//! and implicit lemma endpoints (`sym(add_zero(n))`, not
//! `sym(add(n,0), n, add_zero(n))`). The endpoints `a`, `b`, (`c`) of the
//! prelude lemmas are `{}`-implicit; the elaborator recovers them by unifying
//! the proof argument's type against the parameter domain, discharges the
//! metavariables with one global substitution, and hands a fully explicit
//! core term to the kernel — which gates it exactly as before.

use heather_elab::{ElabError, Elaborator};

// The benchmark from the issue: no `as`, no endpoint arguments anywhere.
const NAT_SUITE_IMPLICIT: &str = r#"
fn add(m: Nat, n: Nat) -> Nat {
    match m {
        Zero => n,
        Succ(k, ih) => Succ(ih),
    }
}

theorem add_zero(n: Nat): add(n, 0) = n {
    match n {
        Zero => refl,
        Succ(k, ih) => Nat::cong_succ(ih),
    }
}

theorem add_succ(m: Nat, n: Nat): add(m, Succ(n)) = Succ(add(m, n)) {
    match m {
        Zero => refl,
        Succ(k, ih) => Nat::cong_succ(ih),
    }
}

theorem add_comm(m: Nat, n: Nat): add(m, n) = add(n, m) {
    match m {
        Zero => sym(add_zero(n)),
        Succ(k, ih) => trans(Nat::cong_succ(ih), sym(add_succ(n, k))),
    }
}

theorem add_assoc(a: Nat, b: Nat, c: Nat): add(add(a, b), c) = add(a, add(b, c)) {
    match a {
        Zero => refl,
        Succ(k, ih) => Nat::cong_succ(ih),
    }
}
"#;

#[test]
fn nat_suite_annotation_free() {
    let mut e = Elaborator::with_prelude().expect("prelude");
    e.elab_source(NAT_SUITE_IMPLICIT)
        .expect("annotation-free Nat suite must elaborate and kernel-check");
    // prelude's 5 (4 theorems and `CollectionLiteral#tycode_fn`,
    // docs/per-instantiation-type-codes-design.md §2) + `3·nfields + 1 = 7`
    // for that declaration's projections (its spine is dependent;
    // docs/telescoped-record-projections-design.md §3) + the suite's `fn add`
    // and 4 theorems, all landed as Ψ-globals (a `fn` is a *defined* one
    // since issues/simulate-conversion-cost.md).
    // +6: the prelude's binding-statement classes and calls.
    // +3: the prelude's `Mutated` record (a `mut self` method's result,
    // docs/effects-capabilities-design.md §2).
    assert_eq!(e.psi().bindings.len(), 26);
}

#[test]
fn implicit_endpoints_are_solved() {
    // A single implicit-endpoint call, in isolation: `sym` with only its
    // proof argument; the endpoints come from `add_zero(n) : add(n,0) = n`.
    let mut e = Elaborator::with_prelude().expect("prelude");
    e.elab_source(
        r#"
        fn add(m: Nat, n: Nat) -> Nat { match m { Zero => n, Succ(k, ih) => Succ(ih) } }
        theorem add_zero(n: Nat): add(n, 0) = n {
            match n { Zero => refl, Succ(k, ih) => Nat::cong_succ(ih) }
        }
        theorem flip(n: Nat): n = add(n, 0) { sym(add_zero(n)) }
        "#,
    )
    .expect("sym's endpoints must be inferred from its proof argument");
}

#[test]
fn explicit_override_still_available() {
    // `@sym(a, b, p)` supplies the implicit endpoints positionally — the
    // stage-1 fallback the sketches promise.
    let mut e = Elaborator::with_prelude().expect("prelude");
    e.elab_source("theorem manual(a: Nat, b: Nat, p: a = b): b = a { @sym(a, b, p) }")
        .expect("explicit `@` override must accept positional endpoints");
}

#[test]
fn wrong_implicit_proof_is_kernel_rejected() {
    // If the (inferred) endpoints make a false statement, the *kernel* — not
    // the unifier — must reject: `sym` of `add_zero(n)` proves
    // `n = add(n,0)`, which is not `add(n,0) = add(n,0)`.
    let mut e = Elaborator::with_prelude().expect("prelude");
    let r = e.elab_source(
        r#"
        fn add(m: Nat, n: Nat) -> Nat { match m { Zero => n, Succ(k, ih) => Succ(ih) } }
        theorem add_zero(n: Nat): add(n, 0) = n {
            match n { Zero => refl, Succ(k, ih) => Nat::cong_succ(ih) }
        }
        theorem bogus(n: Nat): add(n, 0) = add(n, 0) { sym(add_zero(n)) }
        "#,
    );
    // The expected type settles `sym`'s endpoints before its argument is
    // elaborated (issues/surface-gaps-from-sha256-proof.md item 2), so the
    // argument is checked, and the message names its own statement against
    // the one `sym` needs of it.
    let Err(ElabError::Elab { msg, .. }) = r else { panic!("expected a rejection, got {r:?}") };
    assert!(
        msg.contains("this has type `add(n, 0) = n`, but `add(n, 0) = add(n, 0)` is expected here"),
        "{msg}"
    );
}

#[test]
fn too_few_explicit_args_is_an_elab_error() {
    // `trans` needs two proof arguments; giving one is an arity error caught
    // before the kernel.
    let mut e = Elaborator::with_prelude().expect("prelude");
    let r = e.elab_source(
        "theorem oops(a: Nat, b: Nat, p: a = b): a = b { trans(p) }",
    );
    assert!(matches!(r, Err(ElabError::Elab { .. })), "expected an elab arity error, got {r:?}");
}

// ---------------------------------------------------------------------------
// The expected-type harvest and its guards
// (docs/unifier-completeness-design.md §5).

#[test]
fn refl_as_an_argument_is_deferred_and_retried() {
    // `refl` is checking-only; its parameter's domain (`a = b`) still
    // mentions the endpoint metas when the argument is reached, so it is
    // deferred, the expected type solves the endpoints, and the retried
    // `refl` gets a meta-free `Id`.
    let mut e = Elaborator::with_prelude().expect("prelude");
    e.elab_source("theorem t(n: Nat): n = n { sym(refl) }")
        .expect("`refl` must defer until the endpoints are harvested");
}

#[test]
fn a_vector_literal_argument_is_deferred_and_retried() {
    // Same for a vector literal, with the retry unblocked by a *later*
    // argument's inference rather than by the expected type.
    let mut e = Elaborator::with_prelude().expect("prelude");
    e.elab_source(
        "fn pick<A>(xs: [A; 2], x: A) -> A { x }
         fn go() -> Nat { pick([1, 2], 5) }",
    )
    .expect("the literal must defer until `x` solves `A`");
}

#[test]
fn a_flex_headed_result_is_not_peeled_by_the_harvest() {
    // The flex-head guard (design §5.4), pinned directly: `ap`'s result type
    // is `?f(a) = a`, and both the argument's type and the expected type
    // offer `add(n, n) = n`. First-order peeling would "solve"
    // `?f := add(n)` — here even acceptably, which is exactly why the guard
    // must be what refuses: flex-headed applications are outside the Miller
    // fragment, only the LGG rule (whose both-sides trigger does not fire on
    // this one-sided shape) is trusted for them, and the outcome is the
    // caller's message rather than a solution nobody stated.
    let mut e = Elaborator::with_prelude().expect("prelude");
    let r = e.elab_source(
        "fn add(m: Nat, n: Nat) -> Nat { match m { Zero => n, Succ(k, ih) => Succ(ih) } }
         theorem ap<A>({f: A -> A}, a: A, p: f(a) = a): f(a) = a { p }
         theorem use(n: Nat, q: add(n, n) = n): add(n, n) = n { ap(n, q) }",
    );
    match r {
        Err(ElabError::Elab { msg, .. }) => {
            assert!(msg.contains("could not infer the implicit argument `f`"), "{msg}");
        }
        other => panic!("expected the could-not-infer message, got {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// Inference through an indexed family's type
// (issues/type-arg-inference-through-index.md). A declared-index family's
// type is `El` of an index recursion choosing among quoted codes, with the
// payload type a variable *inside* the code literals — so until the walker
// could descend `elimN` and the code constructors, `t: W3<A>(n)` could not
// teach it `A` even though a plain `r: Res<A>` could.

const W3I: &str = r#"
inductive W3i<A> : (n: Nat) -> Type {
    WNil                            : W3i<A>(0),
    WOne(x: A)                      : W3i<A>(0),
    WTwo                            : W3i<A>(0),
    WCons(n: Nat, x: A, t: W3i<A>(n)) : W3i<A>(Succ(n)),
}
"#;

#[test]
fn a_declared_index_familys_argument_solves_the_type_parameter() {
    // The reproducer from the issue: no `<A>` at either call site.
    let mut e = Elaborator::with_prelude().expect("prelude");
    e.elab_source(&format!(
        "{W3I}
         fn idw<A>(n: Nat, t: W3i<A>(n)) -> W3i<A>(n) {{ t }}
         theorem idw_id<A>(n: Nat, t: W3i<A>(n)): idw(n, t) = t {{ refl }}"
    ))
    .expect("`t`'s type mentions `A`; the call must infer it");
}

#[test]
fn a_forded_familys_argument_solves_the_type_parameter() {
    // The other family class: a computed-index (forded) declaration over a
    // non-recursive skeleton, whose Σ-ford the structural walk reaches
    // directly.
    let mut e = Elaborator::with_prelude().expect("prelude");
    e.elab_source(
        r#"
        inductive Fq<A> : (n: Nat) -> Type {
            FqZ              : Fq<A>(0),
            FqA(n: Nat, x: A) : Fq<A>(n),
        }
        fn idq<A>(n: Nat, t: Fq<A>(n)) -> Fq<A>(n) { t }
        theorem idq_id<A>(n: Nat, t: Fq<A>(n)): idq(n, t) = t { refl }
        "#,
    )
    .expect("a forded family's type argument must infer the same way");
}

#[test]
fn a_structural_look_alike_still_fails_at_the_kernel() {
    // Negative control. A family's lowered type is *structural* — there is
    // no name in it for the walker to compare — so against a look-alike
    // family the walker may well learn `A`. That is fine exactly as long as
    // the kernel still judges the call — a wrong pairing must fail
    // *somewhere*, and the walker's license ("only learns, kernel decides")
    // is what this pins. If these families ever become genuinely
    // convertible, this call becomes well-typed and the learned solution
    // correct — then the test should flip to a positive, not the walker to
    // a refusal.
    let mut e = Elaborator::with_prelude().expect("prelude");
    let r = e.elab_source(
        r#"
        inductive P2<A> : (n: Nat) -> Type {
            PNil            : P2<A>(0),
            PCons(x: A)     : P2<A>(0),
        }
        inductive Q2<A> : (n: Nat) -> Type {
            QNil            : Q2<A>(0),
            QCons(x: A)     : Q2<A>(0),
        }
        fn fp<A>(n: Nat, t: P2<A>(n)) -> Nat { 0 }
        fn fq(n: Nat, t: Q2<Nat>(n)) -> Nat { fp(n, t) }
        "#,
    );
    assert!(r.is_err(), "a mismatched family argument must not typecheck, got {r:?}");
}

#[test]
fn a_numeral_index_solves_a_successor_pattern() {
    // `Succ(?n) ≟ 3` learns `?n := 2`: a numeral is `Succ^k(Zero)`. Literal
    // and neutral indices, an open element type, a checking position (the
    // call is an argument), and computation through the solved index.
    let mut e = Elaborator::with_prelude().expect("prelude");
    e.elab_source(
        r#"
        fn first<A>({n: Nat}, v: [A; Succ(n)]) -> A { v[0] }
        fn rest_len<A>({n: Nat}, v: [A; Succ(n)]) -> Nat { n }
        fn at_literal<A>(v: [A; 3]) -> A { first(v) }
        fn at_neutral<A>(k: Nat, v: [A; Succ(k)]) -> A { first(v) }
        fn checked(v: [Nat; 3]) -> Nat { Succ(rest_len(v)) }
        theorem computes(): checked([7, 8, 9]) = 3 { refl }
        theorem first_computes(): at_literal<Nat>([7, 8, 9]) = 7 { refl }
        "#,
    )
    .unwrap_or_else(|err| panic!("{err:?}"));
    // Negative control: `Succ(?n) ≟ 0` has no solution.
    let mut e = Elaborator::with_prelude().expect("prelude");
    let r = e.elab_source(
        r#"
        fn first<A>({n: Nat}, v: [A; Succ(n)]) -> A { v[0] }
        fn empty<A>(v: [A; 0]) -> A { first(v) }
        "#,
    );
    assert!(r.is_err(), "a zero-length vector has no first element, got {r:?}");
}

// `add` recursing on its second argument, as `Nat::add` does in lib/std:
// `m + Succ(k)` reduces to `Succ(m + k)`, `Succ(k) + m` is stuck on `m`.
const ADD: &str = r#"
fn add(m: Nat, n: Nat) -> Nat {
    match n { Zero => m, Succ(k, ih) => Succ(ih) }
}
"#;

#[test]
fn a_successor_pattern_meets_a_sum_that_computes_to_one() {
    // `Succ(?n) ≟ add(m, Succ(k))` has nothing to align until the subject
    // takes its δι step (issues/unify-succ-under-addition.md). A bare vector
    // and a record's field under its lowering's Σ binder, a neutral and a
    // literal summand, an open element type, and computation through the
    // solved length.
    let mut e = Elaborator::with_prelude().expect("prelude");
    e.elab_source(&format!(
        r#"{ADD}
        fn first<A>({{n: Nat}}, v: [A; Succ(n)]) -> A {{ v[0] }}
        fn rest_len<A>({{n: Nat}}, v: [A; Succ(n)]) -> Nat {{ n }}
        fn at_sum<A>(m: Nat, k: Nat, v: [A; add(m, Succ(k))]) -> A {{ first(v) }}
        fn at_plus_one<A>(k: Nat, v: [A; add(k, 1)]) -> A {{ first(v) }}
        record W(n: Nat) {{ bits: [Nat; n] }}
        fn W::head({{n: Nat}}, self w: W(Succ(n))) -> Nat {{ w.bits[0] }}
        fn wrapped(k: Nat, w: W(add(k, 1))) -> Nat {{ w.head() }}
        theorem length_computes(v: [Nat; add(2, 1)]): rest_len(v) = 2 {{ refl }}
        "#
    ))
    .unwrap_or_else(|err| panic!("{err:?}"));
    // Negative control: `add(Succ(k), m)` is stuck on `m`, so there is no
    // successor to learn from and the implicit stays unsolved.
    let mut e = Elaborator::with_prelude().expect("prelude");
    let r = e.elab_source(&format!(
        r#"{ADD}
        fn first<A>({{n: Nat}}, v: [A; Succ(n)]) -> A {{ v[0] }}
        fn stuck<A>(m: Nat, k: Nat, v: [A; add(Succ(k), m)]) -> A {{ first(v) }}
        "#
    ));
    assert!(r.is_err(), "a sum stuck on its second summand exposes no successor, got {r:?}");
}

#[test]
fn a_collection_literal_counts_its_length_into_a_vector_domain() {
    // A literal is checking-only, but its length is counted, not inferred
    // (issues/vector-literal-length-pins-implicit.md): at `[Nat; ?n]` it
    // teaches `?n` before the deferral decision. A statement that pins
    // nothing else, a literal beside an argument that pins a second length,
    // and computation.
    let mut e = Elaborator::with_prelude().expect("prelude");
    e.elab_source(&format!(
        r#"{ADD}
        fn vlen({{n: Nat}}, v: [Nat; n]) -> Nat {{ n }}
        fn cat({{m: Nat}}, {{k: Nat}}, lo: [Nat; m], hi: [Nat; k]) -> Nat {{ add(k, m) }}
        fn statement(y: Nat) -> Type {{ vlen([y, 2, 3]) = vlen([1, 2, 3]) }}
        fn wide(lo: [Nat; 2]) -> Nat {{ cat(lo, [9]) }}
        theorem counts(): vlen([4, 5, 6]) = 3 {{ refl }}
        theorem sums(lo: [Nat; 2]): wide(lo) = 3 {{ refl }}
        "#
    ))
    .unwrap_or_else(|err| panic!("{err:?}"));
    // Negative control: an open element type is not solved by the count, so
    // a literal at `[?A; ?n]` with nothing else to pin `?A` stays refused.
    let mut e = Elaborator::with_prelude().expect("prelude");
    let r = e.elab_source(
        r#"
        fn plen<A>({n: Nat}, v: [A; n]) -> Nat { n }
        fn open() -> Type { plen([1, 2]) = plen([3, 4]) }
        "#,
    );
    assert!(r.is_err(), "the count alone does not solve an open element type, got {r:?}");
}

#[test]
fn a_nested_call_that_does_not_infer_waits_for_its_domain() {
    // `and(inc(mk()), y)`: `mk()`'s width is fixed only once `y` has pinned
    // `and`'s, so the argument is re-planned as deferred instead of failing
    // in inference (issues/nested-uninferable-argument-under-checking.md).
    // Pinned by a later argument, by the expected type through two levels,
    // and as a method chain.
    let mut e = Elaborator::with_prelude().expect("prelude");
    e.elab_source(
        r#"
        record W(n: Nat) { x: Nat, p: x = n }
        fn W::mk({n: Nat}) -> W(n) { W(x := n, p := refl) }
        fn W::inc({n: Nat}, self w: W(n)) -> W(n) { w }
        fn W::and({n: Nat}, self a: W(n), b: W(n)) -> W(n) { a }
        fn W::get({n: Nat}, self w: W(n)) -> Nat { w.x }
        fn by_later(n: Nat, y: W(n)) -> W(n) { W::and(W::inc(W::mk()), y) }
        fn by_expected(n: Nat) -> W(n) { W::inc(W::inc(W::mk())) }
        fn chained(n: Nat, y: W(n)) -> W(n) { W::mk().inc().and(y) }
        theorem computes(y: W(3)): W::get(W::and(W::inc(W::mk()), y)) = 3 { refl }
        "#,
    )
    .unwrap_or_else(|err| panic!("{err:?}"));
    // Negative control: nothing pins the width, and the deferred argument's
    // fallback reports the inner call's own error, as before.
    let mut e = Elaborator::with_prelude().expect("prelude");
    let r = e.elab_source(
        r#"
        record W(n: Nat) { x: Nat, p: x = n }
        fn W::mk({n: Nat}) -> W(n) { W(x := n, p := refl) }
        fn W::inc({n: Nat}, self w: W(n)) -> W(n) { w }
        fn W::get({n: Nat}, self w: W(n)) -> Nat { w.x }
        fn open() -> Nat { W::get(W::inc(W::mk())) }
        "#,
    );
    match r {
        Err(ElabError::Elab { msg, .. }) => assert!(
            msg.contains("`n` of `W::mk`"),
            "the unpinned width is reported at the call that owns it, got: {msg}"
        ),
        other => panic!("an unpinned width must be refused, got {other:?}"),
    }
}

#[test]
fn a_bare_nullary_constructor_waits_for_its_domain() {
    // The same re-plan for an argument with no arguments of its own: `Nil`
    // and `None` cannot say their `A`, and a later argument or the expected
    // type can (issues/nullary-ctor-argument-not-deferred.md). `Nat` and an
    // open element type; a checking position (a declared result) and an
    // inference one (an equation's side); a receiver; and the order that
    // always worked, as the reference.
    let mut e = Elaborator::with_prelude().expect("prelude");
    e.elab_source(
        r#"
        inductive Option<A> { None, Some(v: A) }
        inductive List<A> { Nil, Cons(head: A, tail: List<A>) }
        fn List::first_then<A>(self xs: List<A>, d: A) -> A { match xs { Nil => d, Cons(h, _) => h } }
        fn then_first<A>(d: A, xs: List<A>) -> A { match xs { Nil => d, Cons(h, _) => h } }
        fn Option::or<A>(self o: Option<A>, d: A) -> A { match o { None => d, Some(v) => v } }

        fn checked() -> Nat { List::first_then(Nil, 3) }
        fn open_checked<A>(a: A) -> A { List::first_then(Nil, a) }
        fn by_result<A>() -> Option<A> { None }
        theorem later(): List::first_then(Nil, 3) = 3 { refl }
        theorem earlier(): then_first(3, Nil) = 3 { refl }
        theorem receiver(n: Nat): Nil.first_then(n) = n { refl }
        theorem open_later<A>(a: A): Option::or(None, a) = a { refl }
        theorem option_later(): Option::or(None, 7) = 7 { refl }
        "#,
    )
    .unwrap_or_else(|err| panic!("{err:?}"));
    // Negative control: nothing ever pins `A`. Still refused, with the
    // constructor's own error first and the implicit that stayed open after.
    let mut e = Elaborator::with_prelude().expect("prelude");
    let r = e.elab_source(
        r#"
        inductive List<A> { Nil, Cons(head: A, tail: List<A>) }
        fn List::len<A>(self xs: List<A>) -> Nat { match xs { Nil => 0, Cons(_, t) => 1 } }
        fn open() -> Nat { List::len(Nil) }
        "#,
    );
    match r {
        Err(ElabError::Elab { msg, .. }) => {
            assert!(msg.contains("cannot infer the type argument `A` of `List`"), "{msg}");
            assert!(msg.contains("still mentions the implicit `A`"), "{msg}");
        }
        other => panic!("an unpinned element type must be refused, got {other:?}"),
    }
}

#[test]
fn a_congruence_lemma_solves_from_the_constructor_values_of_its_goal() {
    // `Cons(?l, ?lt) = Cons(?r, ?rt)` against a goal: the implicits sit
    // inside constructor values — a `supf` whose label is an injection into
    // a pair tower — so the unifier walks those, in either spelling
    // (issues/unify-through-constructor-values.md). A recursive inductive
    // (`Cons` and `Nil`, both injections), a record's pair tower, a goal
    // stated syntactically, and one whose side is behind a definition that
    // has to unfold before it shows a constructor.
    let mut e = Elaborator::with_prelude().expect("prelude");
    e.elab_source(
        r#"
        inductive L { N, C(h: Nat, t: L) }
        theorem cc({l, r: Nat}, {lt, rt: L}, h: l = r, t: lt = rt): C(l, lt) = C(r, rt) {
            j(t, λ z _ => C(l, lt) = C(r, z), j(h, λ z _ => C(l, lt) = C(z, lt), refl))
        }
        fn two() -> L { C(1, C(2, N)) }
        theorem syntactic(): C(1, C(2, N)) = C(1, C(2, N)) { cc(refl, cc(refl, refl)) }
        theorem behind_a_definition(): C(1, C(2, N)) = two() { cc(refl, cc(refl, refl)) }
        record P { a: Nat, b: Nat }
        theorem pc({a1, a2, b1, b2: Nat}, p: a1 = a2, q: b1 = b2): P(a1, b1) = P(a2, b2) {
            j(q, λ z _ => P(a1, b1) = P(a2, z), j(p, λ z _ => P(a1, b1) = P(z, b1), refl))
        }
        fn one_two() -> P { P(1, 2) }
        theorem record_value(): P(1, 2) = one_two() { pc(refl, refl) }
        "#,
    )
    .unwrap_or_else(|err| panic!("{err:?}"));
    // Negative control: a goal whose sides are different constructors has
    // no congruence to learn from, and the lemma is refused.
    let mut e = Elaborator::with_prelude().expect("prelude");
    let r = e.elab_source(
        r#"
        inductive L { N, C(h: Nat, t: L) }
        theorem cc({l, r: Nat}, {lt, rt: L}, h: l = r, t: lt = rt): C(l, lt) = C(r, rt) {
            j(t, λ z _ => C(l, lt) = C(r, z), j(h, λ z _ => C(l, lt) = C(z, lt), refl))
        }
        theorem mismatched(): C(1, N) = N { cc(refl, refl) }
        "#,
    );
    assert!(r.is_err(), "a Cons against a Nil is no congruence, got {r:?}");
}

// A known input determines the bare argument's instance; its result then
// determines the enclosing call's still-unknown output. The let binding has
// no expected type, so result-type harvesting cannot hide the cycle.
#[test]
fn polymorphic_argument_teaches_an_unsolved_callee() {
    let mut e = Elaborator::with_prelude().expect("prelude");
    e.elab_source(r#"
        record Pair<A, B> { fst: A, snd: B }
        fn swap<A, B>(p: Pair<A, B>) -> Pair<B, A> { Pair(p.snd, p.fst) }
        fn apply<A, B>(x: A, f: A -> B) -> B { f(x) }
        fn first<A, B>(f: A -> B, x: A) -> B { f(x) }
        fn open<A, B>(p: Pair<A, B>) -> Pair<B, A> {
            let q = apply(p, swap);
            q
        }
        fn reordered<A, B>(p: Pair<A, B>) -> Pair<B, A> {
            let q = first(swap, p);
            q
        }
        fn concrete() -> Nat {
            let q = apply(Pair(2, 3), swap);
            q.fst
        }
        fn width({n: Nat}, xs: [Nat; n]) -> Nat { n }
        fn vector(xs: [Nat; 2]) -> Nat {
            let n = apply(xs, width);
            n
        }
        theorem computes(): concrete() = 3 { refl }
        theorem value_implicit(): vector([1, 2]) = 2 { refl }
    "#).expect("partial parameter types must instantiate bare polymorphic arguments");
}

#[test]
fn polymorphic_value_argument_teaches_an_unsolved_callee() {
    let mut e = Elaborator::with_prelude().expect("prelude");
    e.elab_source(r#"
        fn apply<A, B>(x: A, f: A -> B) -> B { f(x) }
        fn local<A>(x: A, f: {T: Type<0>} -> T -> T) -> A {
            let y = apply(x, f);
            y
        }
        fn identity<T>(x: T) -> T { x }
        fn alias<A>(x: A) -> A {
            let f: {T: Type<0>} -> T -> T = identity;
            let y = apply(x, f);
            y
        }
    "#).expect("local and alias implicit skeletons must use the same inference route");
}

#[test]
fn an_undetermined_polymorphic_argument_implicit_is_still_named() {
    let mut e = Elaborator::with_prelude().expect("prelude");
    let result = e.elab_source(r#"
        fn mystery<A, B>(x: A) -> A { x }
        fn apply<A, B>(x: A, f: A -> B) -> B { f(x) }
        fn bad(n: Nat) -> Nat { apply(n, mystery) }
    "#);
    let Err(ElabError::Elab { msg, .. }) = result else { panic!("expected an implicit diagnostic"); };
    assert!(msg.contains("type argument `B` of `mystery`"), "{msg}");
}

#[test]
fn a_polymorphic_argument_must_not_capture_a_callback_binder() {
    let mut e = Elaborator::with_prelude().expect("prelude");
    let result = e.elab_source(r#"
        fn identity<A>(x: A) -> A { x }
        fn apply<A, B>(f: (n: Nat) -> [A; n], x: B) -> B { x }
        fn bad() -> Nat { let y = apply(identity, 0); y }
    "#);
    assert!(matches!(&result, Err(ElabError::Elab { .. } | ElabError::Kernel { .. })),
        "an implicit cannot be solved to a type depending on the callback binder: {result:?}");
}
