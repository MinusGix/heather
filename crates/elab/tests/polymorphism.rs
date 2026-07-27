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
fn an_uninferable_type_argument_is_diagnosed() {
    let e = bad("inductive List<A> { Nil, Cons(A, List<A>) }
                 fn nil<A>() -> List<A> { Nil }
                 fn go() -> List<Nat> { nil() }");
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
fn an_at_call_reads_its_type_arguments_as_types() {
    ok("fn id<A>(x: A) -> A { x }
        fn go(n: Nat) -> Nat { @id(Nat, n) }");
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
            j(p, (y, q) -> y = a, refl)
        }
        theorem use_at_nat(n: Nat, m: Nat, p: n = m): m = n { sym_at(p) }");
}

#[test]
fn a_polymorphic_theorem_serves_two_types() {
    ok("inductive Bool { True, False }
        theorem sym_at<A>({a: A}, {b: A}, p: a = b): b = a {
            j(p, (y, q) -> y = a, refl)
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
fn an_unannotated_lambda_argument_is_diagnosed() {
    let e = bad("inductive List<A> { Nil, Cons(A, List<A>) }
                 fn map<A, B>(f: A -> B, xs: List<A>) -> List<B> {
                     match xs { Nil => Nil, Cons(x, tl) => Cons(f(x), map(f, tl)) }
                 }
                 fn go(xs: List<Nat>) -> List<Nat> { map(λ x => Succ(x), xs) }");
    assert!(e.contains("annotate its binders"), "{e}");
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
    // `List<Nat>` in *expression* position parses as a type application, and
    // a `Ty 0` argument position reads it back as the type it looks like.
    ok("inductive List<A> { Nil, Cons(A, List<A>) }
        fn hd<A>(xs: List<A>, d: A) -> A { match xs { Nil => d, Cons(x, t) => x } }
        fn go(xs: List<List<Nat>>, d: List<Nat>) -> List<Nat> { @hd(List<Nat>, xs, d) }");
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
    // `<` is the `lt` operator too; the speculative type-argument parse must
    // fall back cleanly (docs/surface-polymorphism.md §1).
    let e = bad("fn go(a: Nat, b: Nat) -> Nat { a < b }");
    assert!(e.contains("lt"), "should have resolved to the `lt` call: {e}");
}
