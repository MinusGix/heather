//! Acceptance for implicit binders in function types and lambdas —
//! `{x: A} -> B` and `λ {x: A} => e` — against
//! `docs/language/implicit-binders-design.md` §10. Tracking issue:
//! `issues/implicit-binders-in-function-types.md`.
//!
//! Nothing here touches the kernel: implicitness is a property of the
//! *surface* type, carried as a positional skeleton beside the kernel type
//! and erased at the boundary — the emitted terms are byte-identical to the
//! explicit spelling's. Every positive test elaborates and is re-checked by
//! the real kernel. The tests vary the axes of
//! `docs/testing-generated-terms.md`: literal *and* neutral callee, an open
//! element type, checking *and* computation position, negative controls.

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

// -- positives ---------------------------------------------------------------

// §10-1: neutral head, type implicit and value implicit. Insertion solves
// `A := Nat` off the argument's type.
#[test]
fn a_neutral_skeletal_head_inserts_off_the_argument() {
    elab(
        r#"
        fn app(f: {A: Type<0>} -> A -> A, n: Nat) -> Nat { f(n) }
        "#,
    );
    // The value-implicit analog: `{n: Nat}` solved from the proof argument.
    elab(
        r#"
        fn refl_of(k: Nat) -> k = k { refl }
        fn vapp(g: {n: Nat} -> (p: n = n) -> Nat, k: Nat) -> Nat { g(refl_of(k)) }
        "#,
    );
}

// §10-2: literal head, computation position — the inserted instantiation
// actually reduces, pinned by `refl`; and via a `let`-alias literal.
#[test]
fn a_literal_skeletal_head_computes() {
    elab(
        r#"
        fn app(f: {A: Type<0>} -> A -> A, n: Nat) -> Nat { f(n) }
        theorem t(): app(λ {A: Type<0>} (x: A) => x, 3) = 3 { refl }
        "#,
    );
    elab(
        r#"
        fn go() -> Nat {
            let g = λ {A: Type<0>} (x: A) => x;
            g(3)
        }
        theorem t(): go() = 3 { refl }
        "#,
    );
}

// §10-3: open element type — `A` solved to the open `B`.
#[test]
fn an_open_element_type_solves() {
    elab(
        r#"
        fn h<B>(y: B, f: {A: Type<0>} -> A -> A) -> B { f(y) }
        "#,
    );
}

// §10-4a: a bare skeletal value in checking position — the §5.2 prefix
// route instantiates it against the expected monomorphic type.
#[test]
fn a_bare_skeletal_value_instantiates_in_checking_position() {
    elab(
        r#"
        fn ap1(g: Nat -> Nat, n: Nat) -> Nat { g(n) }
        fn use1(f: {A: Type<0>} -> A -> A, n: Nat) -> Nat { ap1(f, n) }
        theorem t(): use1(λ {A: Type<0>} (x: A) => x, 3) = 3 { refl }
        "#,
    );
}

// §10-4b: the suppression positive (§5.3, the fixed probe-5 shape one level
// up) — a bare skeletal value passed to a parameter that *wants* the
// implicit function arrives verbatim, no insertion.
#[test]
fn a_skeletal_value_passes_verbatim_to_a_skeletal_parameter() {
    elab(
        r#"
        fn twice(f: {A: Type<0>} -> A -> A, n: Nat) -> Nat { f(f(n)) }
        fn use2(g: {A: Type<0>} -> A -> A, n: Nat) -> Nat { twice(g, n) }
        theorem t(): use2(λ {A: Type<0>} (x: A) => x, 3) = 3 { refl }
        "#,
    );
}

// §10-5: insertion inside a *written type's* codomain — the binder
// `elab_ty`'s `Fn` arm pushes carries the domain's skeleton, so `f`'s use in
// the codomain of a dependent function type inserts with no further
// plumbing (§3.1).
#[test]
fn insertion_works_inside_a_written_dependent_type() {
    elab(
        r#"
        theorem st(f: {A: Type<0>} -> A -> A, p: f(0) = 0): f(0) = 0 { p }
        "#,
    );
    // The same line, one level in: a parameter whose type is itself a
    // dependent function type whose codomain uses the skeletal binder.
    elab(
        r#"
        fn d(g: (f: {A: Type<0>} -> A -> A) -> f(0) = 0) -> Nat { 0 }
        "#,
    );
}

// §10-6: record fields. The skeleton is derived on demand from the stored
// surface field type — applied projection, bare projection in checking
// position, an implicit-lambda field in a record literal, and the
// `let { f } = w;` pattern carrying the skeleton onto the alias.
#[test]
fn record_fields_carry_the_skeleton() {
    elab(
        r#"
        record Endo { f: {A: Type<0>} -> A -> A }
        fn apply(w: Endo, n: Nat) -> Nat { w.f(n) }
        fn mk() -> Endo { Endo { f: λ {A: Type<0>} (x: A) => x } }
        theorem t(): apply(mk(), 3) = 3 { refl }
        "#,
    );
    // Bare `w.f` in checking position (the §5.2 route on a projection).
    elab(
        r#"
        record Endo { f: {A: Type<0>} -> A -> A }
        fn ap1(g: Nat -> Nat, n: Nat) -> Nat { g(n) }
        fn use1(w: Endo, n: Nat) -> Nat { ap1(w.f, n) }
        "#,
    );
    // `let { f } = w;` — the alias carries the field's skeleton.
    elab(
        r#"
        record Endo { f: {A: Type<0>} -> A -> A }
        fn use2(w: Endo, n: Nat) -> Nat {
            let { f } = w;
            f(n)
        }
        "#,
    );
}

// §10-7: deferral and hints on a value callee — `f(?)` defers the hole,
// the expected type solves `A`, the retry raises the goal *named after the
// skeleton binder*, and `on x := …` discharges it by that name.
#[test]
fn a_deferred_hole_on_a_value_callee_is_named_from_the_skeleton() {
    elab(
        r#"
        fn use3(f: {A: Type<0>} -> (x: A) -> A) -> Nat {
            f(?)
            on ?x := 3;
        }
        "#,
    );
}

// §10-8: `@` on a skeletal value clears the whole mask — every parameter
// positional, which the erased kernel type supports directly (§7.1).
#[test]
fn at_on_a_skeletal_value_is_fully_positional() {
    elab(
        r#"
        fn app(f: {A: Type<0>} -> A -> A, n: Nat) -> Nat { @f(Nat, n) }
        theorem t(): app(λ {A: Type<0>} (x: A) => x, 3) = 3 { refl }
        "#,
    );
}

// -- negative controls -------------------------------------------------------

// §10-neg-1a: implicit binder where the expected skeleton says explicit
// (§7.3-3). The expected type *has* a skeleton (its head is implicit), so
// the mismatch at the second binder is position-by-position.
#[test]
fn an_implicit_binder_at_an_explicit_position_is_refused() {
    let msg = elab_err(
        r#"
        fn u(f: {A: Type<0>} -> (x: A) -> A) -> Nat { 0 }
        fn go() -> Nat { u(λ {A: Type<0>} {x: A} => x) }
        "#,
    );
    assert!(msg.contains("spells this parameter explicit"), "{msg}");
}

// §10-neg-1b: implicit binder against a plain (skeleton-less) expected type
// (§7.3-2).
#[test]
fn an_implicit_binder_against_a_plain_type_is_refused() {
    let msg = elab_err(
        r#"
        fn u(f: Nat -> Nat) -> Nat { 0 }
        fn go() -> Nat { u(λ {x: Nat} => x) }
        "#,
    );
    assert!(msg.contains("carries no implicitness"), "{msg}");
    // The flip side of the coherence rule: an *explicit* binder is accepted
    // at an implicit position — every pre-existing lambda can inhabit an
    // implicit-skeletal parameter unchanged (§6.2).
    elab(
        r#"
        fn u(f: {A: Type<0>} -> A -> A) -> Nat { 0 }
        fn go() -> Nat { u(λ (A: Type<0>) (x: A) => x) }
        "#,
    );
}

// §10-neg-2: **the degradation, pinned as behavior** — a function type that
// arrives by computation carries no skeleton and offers no insertion. The
// alias below gets its type from an application's result, not from written
// syntax: bare `f(n)` fails with an ordinary error (not a junk
// instantiation), and the explicit spelling succeeds. This is the design's
// contract (docs/language/implicit-binders-design.md §9), not an accident, and this
// test is where it is written down.
#[test]
fn a_computed_function_type_offers_no_insertion() {
    let explicit = r#"
        fn mk() -> (A: Type<0>) -> A -> A { λ (A: Type<0>) (x: A) => x }
        fn go(n: Nat) -> Nat {
            let f = mk();
            f(Nat, n)
        }
        theorem t(): go(3) = 3 { refl }
    "#;
    elab(explicit);
    let bare = r#"
        fn mk() -> (A: Type<0>) -> A -> A { λ (A: Type<0>) (x: A) => x }
        fn go(n: Nat) -> Nat {
            let f = mk();
            f(n)
        }
    "#;
    let mut e = Elaborator::with_prelude().expect("prelude");
    assert!(e.elab_source(bare).is_err(), "the degraded call must not guess");
}

// §10-neg-3: unsolvable implicit on a value — the §7.3-1 message, value
// flavor: the escapes offered are `@f(…)` and eta-expansion, never `f<…>`
// (a value has no `<…>` spelling).
#[test]
fn an_unsolvable_value_implicit_names_the_value_escapes() {
    let msg = elab_err(
        r#"
        fn u(f: {A: Type<0>} -> Nat -> Nat, n: Nat) -> Nat { f(n) }
        "#,
    );
    assert!(msg.contains("cannot infer the type argument `A` of `f`"), "{msg}");
    assert!(msg.contains("@f("), "{msg}");
    assert!(msg.contains("eta-expand"), "{msg}");
    assert!(!msg.contains("f<"), "{msg}");
}

// §10-neg-4: an implicit lambda in a non-`let` inference position is
// refused (§6.3) — and the `let` harvest positive stands beside it.
#[test]
fn an_implicit_lambda_needs_a_checking_position_or_a_let() {
    let msg = elab_err(
        r#"
        fn ap(g: Nat -> Nat, n: Nat) -> Nat { g(n) }
        fn go() -> Nat { ap((λ {A: Type<0>} (x: A) => x)(Nat), 3) }
        "#,
    );
    assert!(msg.contains("needs a checking position, or a `let`"), "{msg}");
    // The harvest: the alias records the skeleton read off the written
    // marks, and the use inserts.
    elab(
        r#"
        fn go() -> Nat {
            let f = λ {A: Type<0>} (x: A) => x;
            f(3)
        }
        theorem t(): go() = 3 { refl }
        "#,
    );
}

// §10-neg-5: shadowing — a local skeletal `f` over a global `f` with
// different parameter metadata uses the *skeleton's* names in messages,
// pinning the §4.2 params-passed-not-recovered refactor.
#[test]
fn a_local_skeleton_never_borrows_a_global_params() {
    let msg = elab_err(
        r#"
        fn f<T>(x: T) -> T { x }
        fn u(f: {B: Type<0>} -> Nat -> Nat, n: Nat) -> Nat { f(n) }
        "#,
    );
    assert!(msg.contains("`B` of `f`"), "{msg}");
    assert!(!msg.contains("`T`"), "{msg}");
}

// §10-neg-6: the grammar edges. `@` on a non-name head stays rejected;
// the record `let`-pattern is untouched; a motive may end in an implicit
// binder type without the arms brace being swallowed.
#[test]
fn grammar_edges_hold() {
    let msg = elab_err("fn go(n: Nat) -> Nat { @(n)(3) }");
    assert!(!msg.is_empty(), "{msg}");
    // Record pattern in statement position is unaffected (§8.2): `{ f`
    // inside a body is the pattern, never a type.
    elab(
        r#"
        record W { f: Nat }
        fn use4(w: W) -> Nat {
            let { f } = w;
            f
        }
        "#,
    );
}
