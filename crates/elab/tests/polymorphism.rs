//! Type parameters on `fn`/`theorem` (docs/surface-polymorphism.md §9).

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

// -- 1-5: grammar and declaration -----------------------------------------

#[test]
fn identity_is_polymorphic() {
    ok("fn id<A>(x: A) -> A { x }
        fn use_it(n: Nat) -> Nat { id(n) }");
}

#[test]
fn map_over_a_declared_list() {
    // The issue's headline: `fn map<A, B>` was not writable at all.
    ok("inductive List<A> { Nil, Cons(A, List<A>) }
        fn map<A, B>(f: A -> B, xs: List<A>) -> List<B> {
            match xs {
                Nil => Nil,
                Cons(x, tl) => Cons(f(x), map(f, tl)),
            }
        }");
}

#[test]
fn duplicate_type_parameter_is_rejected() {
    let e = bad("fn f<A, A>(x: A) -> A { x }");
    assert!(e.contains("duplicate type parameter"), "{e}");
}

#[test]
fn a_type_parameter_takes_no_arguments() {
    let e = bad("fn f<A>(x: A<Nat>) -> A { x }");
    assert!(e.contains("takes no arguments"), "{e}");
}

#[test]
fn a_type_parameter_may_not_shadow_a_parameter() {
    let e = bad("fn f<A>(A: Nat) -> Nat { A }");
    assert!(e.contains("both a type parameter"), "{e}");
}

// -- 6-11: inference -------------------------------------------------------

#[test]
fn type_arguments_come_from_the_arguments() {
    ok("inductive Bool { True, False }
        inductive List<A> { Nil, Cons(A, List<A>) }
        fn map<A, B>(f: A -> B, xs: List<A>) -> List<B> {
            match xs {
                Nil => Nil,
                Cons(x, tl) => Cons(f(x), map(f, tl)),
            }
        }
        fn is_zero(n: Nat) -> Bool { match n { Zero => True, Succ(k) => False } }
        fn go(xs: List<Nat>) -> List<Bool> { map(is_zero, xs) }");
}

#[test]
fn a_type_argument_is_solved_from_under_a_binder() {
    // Axis 2 / §4: `B` occurs only in `f`'s *codomain*, which is one binder
    // deep, so the solution has to be strengthened before it is recorded.
    ok("inductive Bool { True, False }
        fn apply<A, B>(f: A -> B, x: A) -> B { f(x) }
        fn is_zero(n: Nat) -> Bool { match n { Zero => True, Succ(k) => False } }
        fn go(n: Nat) -> Bool { apply(is_zero, n) }");
}

#[test]
fn a_nullary_calls_type_argument_comes_from_the_expected_type() {
    // Retired-and-replaced (docs/unifier-completeness-design.md §5.1): this
    // was the "cannot infer the type argument" pin — before the general
    // harvest, a call with no argument mentioning `A` was refused even in
    // checking position, where `List<Nat>` says everything. Now the expected
    // type is consulted; the refusal moved to genuine inference position
    // (next test).
    ok("inductive List<A> { Nil, Cons(A, List<A>) }
        fn nil<A>() -> List<A> { Nil }
        fn go() -> List<Nat> { nil() }");
}

#[test]
fn an_uninferable_type_argument_is_diagnosed() {
    // Inference position: an unannotated `let` has no expected type, so the
    // pre-existing message still stands — and is now literally true only
    // after the expected type has been consulted, which is the point.
    let e = bad("inductive List<A> { Nil, Cons(A, List<A>) }
                 fn nil<A>() -> List<A> { Nil }
                 fn go() -> Nat { let xs = nil(); 0 }");
    assert!(e.contains("cannot infer the type argument"), "{e}");
    assert!(e.contains("nil<"), "the message should name the escape hatch: {e}");
}

#[test]
fn explicit_type_arguments_work() {
    ok("inductive List<A> { Nil, Cons(A, List<A>) }
        fn nil<A>() -> List<A> { Nil }
        fn go() -> List<Nat> { nil<Nat>() }");
}

#[test]
fn at_leaves_type_parameters_inferred() {
    // `@` makes the *value* implicits positional and says nothing about type
    // parameters, so a callee that gains one does not break its `@`-callers
    // (issues/at-and-type-arguments.md).
    ok("fn id<A>(x: A) -> A { x }
        fn go(n: Nat) -> Nat { @id(n) }");
}

#[test]
fn at_and_type_arguments_compose() {
    ok("theorem sym_at<A>({a: A}, {b: A}, p: a = b): b = a {
            j(p, λ y q => y = a, refl)
        }
        theorem inferred(n: Nat, m: Nat, p: n = m): m = n { sym_at(p) }
        theorem endpoints(n: Nat, m: Nat, p: n = m): m = n { @sym_at(n, m, p) }
        theorem both(n: Nat, m: Nat, p: n = m): m = n { @sym_at<Nat>(n, m, p) }
        theorem carrier(n: Nat, m: Nat, p: n = m): m = n { sym_at<Nat>(p) }");
}

#[test]
fn a_type_argument_solved_twice_is_not_silently_kept() {
    // Negative control: `f : Nat -> Bool` fixes `A := Nat`, but the list is a
    // `List<Bool>`. Nothing may quietly keep the first solution.
    let e = bad("inductive Bool { True, False }
                 inductive List<A> { Nil, Cons(A, List<A>) }
                 fn map<A, B>(f: A -> B, xs: List<A>) -> List<B> {
                     match xs {
                         Nil => Nil,
                         Cons(x, tl) => Cons(f(x), map(f, tl)),
                     }
                 }
                 fn is_zero(n: Nat) -> Bool { match n { Zero => True, Succ(k) => False } }
                 fn go(xs: List<Bool>) -> List<Bool> { map(is_zero, xs) }");
    assert!(!e.is_empty(), "{e}");
}

// -- 12-17: interactions ---------------------------------------------------

#[test]
fn a_polymorphic_theorem_is_a_global() {
    ok("theorem sym_at<A>({a: A}, {b: A}, p: a = b): b = a {
            j(p, λ y q => y = a, refl)
        }
        theorem use_at_nat(n: Nat, m: Nat, p: n = m): m = n { sym_at(p) }");
}

#[test]
fn a_polymorphic_theorem_serves_two_types() {
    ok("inductive Bool { True, False }
        theorem sym_at<A>({a: A}, {b: A}, p: a = b): b = a {
            j(p, λ y q => y = a, refl)
        }
        theorem at_nat(n: Nat, m: Nat, p: n = m): m = n { sym_at(p) }
        theorem at_bool(a: Bool, b: Bool, p: a = b): b = a { sym_at(p) }");
}

#[test]
fn a_hole_in_a_type_argument_is_counted() {
    ok("fn id<A>(x: A) -> A { x }
        theorem t(n: Nat): n = n { id<n = ?p>(refl) on ?p := n; }");
}

#[test]
fn a_polymorphic_fn_at_two_instantiations_in_one_declaration() {
    ok("inductive Bool { True, False }
        inductive Pair<A, B> { Both(A, B) }
        fn id<A>(x: A) -> A { x }
        fn go(n: Nat, b: Bool) -> Pair<Nat, Bool> { Both(id(n), id(b)) }");
}

#[test]
fn a_container_field_at_an_open_element_type() {
    // Axis 2 for the container machinery: `[A; n]` with `A` a type parameter.
    ok("inductive Rose<A> { Node(A, n: Nat, [Rose<A>; n]) }
        fn count<A>(t: Rose<A>) -> Nat {
            match t { Node(a, n, kids) => n }
        }");
}

#[test]
fn matching_at_an_open_type_dispatches() {
    ok("inductive Opt<A> { None, Some(A) }
        fn or_else<A>(o: Opt<A>, d: A) -> A {
            match o { None => d, Some(x) => x }
        }");
}

// -- 18-19: negative controls ---------------------------------------------

#[test]
fn a_wrong_explicit_type_argument_is_rejected() {
    let e = bad("inductive Bool { True, False }
                 fn id<A>(x: A) -> A { x }
                 fn go(n: Nat) -> Nat { id<Bool>(n) }");
    assert!(!e.is_empty(), "{e}");
}

#[test]
fn type_arguments_on_a_monomorphic_callee_are_rejected() {
    let e = bad("fn f(n: Nat) -> Nat { n }
                 fn go(n: Nat) -> Nat { f<Nat>(n) }");
    assert!(e.contains("takes no type arguments"), "{e}");
}

#[test]
fn the_wrong_number_of_type_arguments_is_rejected() {
    let e = bad("fn id<A>(x: A) -> A { x }
                 fn go(n: Nat) -> Nat { id<Nat, Nat>(n) }");
    assert!(e.contains("type argument(s)"), "{e}");
}

// -- it computes, not merely typechecks (axis 1) --------------------------

#[test]
fn a_polymorphic_call_computes() {
    // A closed equation proved by `refl` is the only thing that makes the
    // conversion checker actually reduce `El ⌜Nat⌝` back to `Nat`.
    ok("fn id<A>(x: A) -> A { x }
        theorem inferred(): id(3) = 3 { refl }
        theorem written(): id<Nat>(3) = 3 { refl }");
}

// -- checking position at an open type (axis 3) ---------------------------

#[test]
fn a_proof_at_an_open_type() {
    ok("inductive List<A> { Nil, Cons(A, List<A>) }
        fn len<A>(xs: List<A>) -> Nat {
            match xs { Nil => 0, Cons(x, tl) => Succ(len(tl)) }
        }
        theorem len_nil<A>(): len<A>(Nil<A>) = 0 { refl }");
}

#[test]
fn a_constructor_takes_a_written_instantiation() {
    // `Nil` alone is ambiguous and says so; `Nil<Nat>` is the direct spelling
    // of what `infer_ctor` otherwise has to recover from a field.
    ok("inductive List<A> { Nil, Cons(A, List<A>) }
        fn one() -> List<Nat> { Cons<Nat>(1, Nil<Nat>) }");
}

#[test]
fn a_constructor_with_the_wrong_type_argument_count_is_rejected() {
    let e = bad("inductive List<A> { Nil, Cons(A, List<A>) }
                 fn one() -> List<Nat> { Nil<Nat, Nat> }");
    assert!(e.contains("type argument(s)"), "{e}");
}

// -- container recursion at an open element type (axis 2 + 3) -------------

#[test]
fn recursion_over_a_container_at_an_open_element_type() {
    // The control that found the `wf_branch` shift bug: at a closed element
    // type the constructor encoding's Σ tail mentions no ambient variable, so
    // the wrong substitution context was invisible.
    ok("fn add(a: Nat, b: Nat) -> Nat { match b { Zero => a, Succ(k) => Succ(add(a, k)) } }
        inductive Rose<A> { Node(label: A, len: Nat, kids: [Rose<A>; len]) }
        fn size<A>(r: Rose<A>) -> Nat {
            match r {
                Node(label, len, kids) =>
                    Succ(kids.map(size).fold(0, λ (a: Nat) (b: Nat) => add(a, b))),
            }
        }
        theorem leaf(): size<Nat>(Node(7, 0, [])) = 1 { refl }");
}

// -- the inference boundary, stated as a message (§4.1) -------------------

#[test]
fn an_unannotated_lambda_argument_is_inferred_from_the_call() {
    // Retired-and-replaced (docs/unifier-completeness-design.md §4.1): this
    // was the "annotate its binders" pin — an unannotated lambda argument of
    // an implicit-taking callee was refused unconditionally, because
    // explicit arguments were inferred and a lambda without annotations has
    // nothing to infer from. An unannotated lambda is checking-only, so it
    // is now *deferred*: `xs` solves `A`, the expected type solves `B`, and
    // the retried lambda is checked against the then-meta-free `Nat -> Nat`.
    ok("inductive List<A> { Nil, Cons(A, List<A>) }
        fn map<A, B>(f: A -> B, xs: List<A>) -> List<B> {
            match xs { Nil => Nil, Cons(x, tl) => Cons(f(x), map(f, tl)) }
        }
        fn go(xs: List<Nat>) -> List<Nat> { map(λ x => Succ(x), xs) }");
}

#[test]
fn an_undetermined_unannotated_lambda_is_diagnosed() {
    // The refusal's new home (design §7.2): in inference position nothing
    // solves `B`, so the deferred lambda stays blocked and the message names
    // the argument, the parameter, and both escape hatches.
    let e = bad("inductive List<A> { Nil, Cons(A, List<A>) }
                 fn map<A, B>(f: A -> B, xs: List<A>) -> List<B> {
                     match xs { Nil => Nil, Cons(x, tl) => Cons(f(x), map(f, tl)) }
                 }
                 fn go(xs: List<Nat>) -> Nat { let ys = map(λ x => Succ(x), xs); 0 }");
    assert!(e.contains("was deferred"), "{e}");
    assert!(e.contains("`f`"), "the message should name the parameter: {e}");
}

#[test]
fn an_annotated_lambda_argument_works() {
    ok("inductive List<A> { Nil, Cons(A, List<A>) }
        fn map<A, B>(f: A -> B, xs: List<A>) -> List<B> {
            match xs { Nil => Nil, Cons(x, tl) => Cons(f(x), map(f, tl)) }
        }
        fn go(xs: List<Nat>) -> List<Nat> { map(λ (x: Nat) => Succ(x), xs) }");
}

// -- the two other spellings ----------------------------------------------

#[test]
fn an_at_call_accepts_an_applied_type_argument() {
    // An applied type as a written type argument, under `@`.
    ok("inductive List<A> { Nil, Cons(A, List<A>) }
        fn hd<A>(xs: List<A>, d: A) -> A { match xs { Nil => d, Cons(x, t) => x } }
        fn go(xs: List<List<Nat>>, d: List<Nat>) -> List<Nat> { @hd<List<Nat>>(xs, d) }");
}

#[test]
fn the_method_sugar_reaches_a_polymorphic_callee() {
    ok("fn id<A>(x: A) -> A { x }
        fn go(n: Nat) -> Nat { n.id() }");
}

// -- a `fn` may be named after a built-in eliminator -----------------------

#[test]
fn a_declaration_named_map_can_recurse() {
    // Found by the headline test: `map`'s self-call took the built-in
    // vector-`map` path, because `shadowed` did not count the declaration's
    // own name. Pinned here since it is not about polymorphism.
    ok("fn map(n: Nat) -> Nat { match n { Zero => 0, Succ(k) => Succ(map(k)) } }");
}

// -- the grammar's one ambiguity ------------------------------------------

#[test]
fn less_than_still_parses_as_lt() {
    // `<` is the `Lt` operator too; the speculative type-argument parse must
    // fall back cleanly (docs/surface-polymorphism.md §1).
    //
    // The fallback name was `lt` until 2026-08-16 and is `Lt` now, matching
    // `<=`'s `Le` — `std/nat` declares the relation capitalized
    // (issues/nat-order-kit.md). The assertion is what caught the rename, and
    // what it pins is unchanged: the `<` reached name resolution as an
    // operator rather than dying in the parser as an unterminated `a<b …>`.
    // No module is loaded here, so `Lt` is genuinely absent and the refusal is
    // the resolver's.
    let e = bad("fn go(a: Nat, b: Nat) -> Nat { a < b }");
    assert!(e.contains("Lt"), "should have resolved to the `Lt` call: {e}");
}

// -- the prelude is polymorphic now (issues/at-and-type-arguments.md) -----

#[test]
fn the_prelude_serves_a_declared_type() {
    ok("inductive Bool { True, False }
        theorem at_bool(a: Bool, b: Bool, p: a = b): b = a { sym(p) }
        theorem chain(a: Bool, b: Bool, c: Bool, p: a = b, q: b = c): a = c { trans(p, q) }");
}

// -- a polymorphic function as a first-class argument (D2, ------------------
// docs/unifier-completeness-design.md §5.3: the bare-reference route)

#[test]
fn a_bare_polymorphic_reference_instantiates_at_a_monomorphic_domain() {
    // The issue's repro (issues/elab-unifier-completeness.md, 2026-08-04):
    // died as a bare kernel `LevelMismatch`, because the reference resolved
    // verbatim at `Π (A : Ty 0). …` and no instantiation was ever attempted.
    ok("fn id<A>(x: A) -> A { x }
        fn app1(f: Nat -> Nat, n: Nat) -> Nat { f(n) }
        fn probe(n: Nat) -> Nat { app1(id, n) }");
}

#[test]
fn a_bare_reference_through_compose() {
    // The same shape with three type parameters on the callee: the written
    // instantiation makes every domain concrete, so both bare `id`s go down
    // the checking route.
    ok("fn id<A>(x: A) -> A { x }
        fn compose<A, B, C>(g: B -> C, f: A -> B, x: A) -> C { g(f(x)) }
        fn probe(n: Nat) -> Nat { compose<Nat, Nat, Nat>(id, id, n) }");
}

#[test]
fn a_fully_inferred_compose_of_bare_references_is_diagnosed() {
    // The boundary, pinned: with `compose`'s own `B` determined by *neither*
    // `n` nor the expected type, the deferred `id`s stay blocked — their
    // instantiation would have to flow across call worlds, which is the
    // cross-call postponement this round deliberately does not build
    // (docs/unifier-completeness-design.md §3.1). The failure is the §7.2
    // message naming the argument, not the old kernel `LevelMismatch` on a
    // junk instantiation.
    let e = bad("fn id<A>(x: A) -> A { x }
                 fn compose<A, B, C>(g: B -> C, f: A -> B, x: A) -> C { g(f(x)) }
                 fn probe(n: Nat) -> Nat { compose(id, id, n) }");
    assert!(e.contains("was deferred"), "{e}");
}

#[test]
fn a_bare_reference_in_checking_position_under_a_theorem() {
    // Checking position proper (a theorem statement), not just a `fn` body's
    // computation position.
    ok("fn id<A>(x: A) -> A { x }
        fn app1(f: Nat -> Nat, n: Nat) -> Nat { f(n) }
        theorem probe_id(n: Nat): app1(id, n) = id(n) { refl }");
}

#[test]
fn a_bare_reference_at_an_open_element_type() {
    // The expected domain is `A -> A` for a *bound* type parameter: the
    // instantiation is a variable's code, not a closed type.
    ok("fn id<A>(x: A) -> A { x }
        fn call<A>(f: A -> A, x: A) -> A { f(x) }
        fn go<A>(x: A) -> A { call(id, x) }");
}

#[test]
fn a_bare_reference_at_a_polymorphic_expected_type_is_not_instantiated() {
    // Regression pin (found by the implicit-binders design round's probes):
    // when the expected type itself still quantifies over a type, the
    // parameter wants the polymorphic function *uninstantiated* — insertion
    // would mis-teach (`El ?A ≟ Ty 0` solves `?A := ⌜Type 0⌝`) and reach the
    // kernel as a LevelMismatch on a term nobody wrote. Suppressed: the
    // reference passes verbatim, exactly as before the bare-reference route
    // existed. The skeleton rule of docs/implicit-binders-design.md §5.3
    // refines this once implicitness travels with the type.
    ok("fn myid<A>(x: A) -> A { x }
        fn appnat(f: (A: Type<0>) -> A -> A, n: Nat) -> Nat { f(Nat, n) }
        theorem t(): appnat(myid, 3) = 3 { refl }");
}

#[test]
fn a_bare_reference_in_inference_position_keeps_todays_behavior() {
    // Negative: with no expected type there is nothing to solve from, so the
    // reference still resolves to the polymorphic value verbatim and misuse
    // is still an error (kernel-gated, as before this round).
    let e = bad("fn id<A>(x: A) -> A { x }
                 fn go(n: Nat) -> Nat { let f = id; f(n) }");
    assert!(!e.is_empty(), "{e}");
}

#[test]
fn an_undetermined_bare_reference_gets_an_elaborator_message() {
    // Negative (design §7.1): the expected type (`Nat`) determines nothing,
    // so the failure is the elaborator's message naming the parameter and
    // the escape hatch — not a bare kernel error.
    let e = bad("fn konst<A>(x: A) -> Nat { 0 }
                 fn go() -> Nat { konst }");
    assert!(e.contains("from the expected type here"), "{e}");
    assert!(e.contains("konst<"), "the message should name the escape hatch: {e}");
}

#[test]
fn a_wrongly_harvested_solution_is_still_kernel_gated() {
    // Kernel-gate control (design §8): the harvest pairs `El ?A` with `Nat`
    // first — learn-only never verifies — and the instantiated `id` at
    // `Nat -> Nat` is not a `Nat -> Bool`, which the *kernel* rejects.
    let mut e = Elaborator::with_prelude().expect("prelude");
    let r = e.elab_source(
        "inductive Bool { True, False }
         fn id<A>(x: A) -> A { x }
         fn app_nb(f: Nat -> Bool, n: Nat) -> Bool { f(n) }
         fn go(n: Nat) -> Bool { app_nb(id, n) }",
    );
    // Still gated rather than verified by the harvest; the gate's rejection now
    // arrives as the precise message
    // (issues/check-fallback-discards-expected-type.md).
    let Err(heather_elab::ElabError::Elab { msg, .. }) = r else {
        panic!("expected a rejection, got {r:?}")
    };
    assert!(
        msg.contains("this has type `Nat -> Nat`, but `Nat -> Bool` is expected here"),
        "{msg}"
    );
}

#[test]
fn an_implicit_taking_call_still_checks_its_arguments() {
    // `@sym(a, b, refl)` goes through `apply_implicit` now — the type
    // parameter is still a meta — so the *checking* mode that `refl` and a
    // `?`-hole need had to be restored there. `a` solves the meta before
    // `refl`'s domain is required, which is what makes the order work.
    ok("theorem t(n: Nat): n = n { @sym(n, n, refl) }
        theorem u(n: Nat): n = n { @sym(n, n, ?p) on ?p := refl; }");
}

// -- a recursive self-call at written type arguments -----------------------
//
// `issues/recursive-self-call-type-arguments.md`. The self-name is not a global
// while its own body elaborates, so the type-application path used to report
// that the declaration takes no type arguments — of a declaration that visibly
// takes one, at the one place a reader cannot check the claim against a
// different declaration, since caller and callee are the same text.
//
// The rule the fix states: a self-call is always at the declaration's *own*
// type parameters, because the lowering is an `elim` whose type parameters are
// bound outside the recursion. So the written arguments are checked to be those
// parameters and then dropped, and a different instantiation is refused as the
// polymorphic recursion it is.

#[test]
fn a_self_call_may_write_its_own_type_arguments() {
    ok("fn twice<A>(a: A, n: Nat) -> A \
        { match n { Zero => a, Succ(k) => twice<A>(a, k) } }");
}

#[test]
fn a_type_valued_self_call_may_too() {
    // The shape that found this: a proposition by recursion into `Type`, whose
    // recursive occurrence is the one a carrier mentions. Its failure used to
    // cascade — the head never registered, so every later `Rep<…>` reported the
    // same thing and three declarations looked broken.
    ok("fn Rep<A>(n: Nat) -> Type { match n { Zero => A, Succ(k) => Rep<A>(k) } }
        fn use_rep<B>(b: B, k: Nat) -> B { b }");
}

#[test]
fn the_implicit_spelling_is_unchanged() {
    // The workaround that always worked, kept honest: writing the arguments and
    // omitting them must be the same call.
    ok("fn twice<A>(a: A, n: Nat) -> A \
        { match n { Zero => a, Succ(k) => twice(a, k) } }");
}

#[test]
fn a_self_call_at_type_arguments_still_computes() {
    // Axis 1, and the assertion that the written arguments really are dropped
    // rather than re-elaborated into something else: the lowering is still the
    // recursor, so a closed call reduces.
    ok("fn twice<A>(a: A, n: Nat) -> A \
        { match n { Zero => a, Succ(k) => twice<A>(a, k) } }
        theorem computes(): twice<Nat>(7, 3) = 7 { refl }");
}

#[test]
fn a_self_call_at_a_different_instantiation_is_refused() {
    // Polymorphic recursion, named as such. Permuted parameters and not junk
    // types, because that is the case a reader would expect to work.
    let e = bad("fn swap<A, B>(a: A, b: B, n: Nat) -> A \
                 { match n { Zero => a, Succ(k) => swap<B, A>(a, b, k) } }");
    assert!(e.contains("polymorphic recursion"), "{e}");
}

#[test]
fn the_wrong_number_of_self_type_arguments_is_refused() {
    let e = bad("fn one<A>(a: A, n: Nat) -> A \
                 { match n { Zero => a, Succ(k) => one<A, A>(a, k) } }");
    assert!(e.contains("type argument(s)"), "{e}");
}

#[test]
fn type_arguments_on_a_monomorphic_self_call_are_refused() {
    let e = bad("fn none(n: Nat) -> Nat { match n { Zero => 0, Succ(k) => none<Nat>(k) } }");
    assert!(e.contains("has no type parameters"), "{e}");
}

#[test]
fn a_bare_self_name_at_type_arguments_is_still_not_a_value() {
    // `f<A>` with no call is the self-name used as a value, which it never is:
    // it is the induction hypothesis. The message is the one a bare `f` gets,
    // rather than the arity complaint the type-application path would make.
    let e = bad("fn bare<A>(a: A, n: Nat) -> A \
                 { match n { Zero => a, Succ(k) => bare<A> } }");
    assert!(e.contains("saturated recursive call"), "{e}");
}

#[test]
fn a_self_call_at_type_arguments_is_still_guarded() {
    // The termination analysis is untrusted and can only reject; writing the
    // type arguments must not route around it.
    let e = bad("fn loopy<A>(a: A, n: Nat) -> A { loopy<A>(a, n) }");
    assert!(e.contains("not structurally guarded"), "{e}");
}

#[test]
fn at_and_type_arguments_compose_on_a_self_call() {
    // `<…>` controls type arguments and `@` controls value implicits
    // (issues/at-and-type-arguments.md); a self-call recursing on an *implicit*
    // parameter needs `@`, and the two knobs have to compose there too.
    ok("fn twice<A>(a: A, {n: Nat}) -> A \
        { match n { Zero => a, Succ(k) => @twice<A>(a, k) } }");
}
