//! The audit of `issues/el-reader-decode-audit.md`: every structural reader of
//! a **lowered** `Type` in `crates/elab`, against a type that arrived wrapped —
//! `El` of a code (`docs/types-as-expressions.md`) or `El` of a β/δ-**redex**
//! (`docs/record-type-values.md` §4, a type reached through a `Val -> Type`
//! function *value*).
//!
//! `docs/record-type-values.md` §6 is the roster this file pins. Five readers
//! declined the shape and were repaired; the rest are pinned here as
//! already-fine so that "which readers walk a lowered type?" stops being an
//! open question. Every repaired reader has a **negative control** next to it:
//! the audit's whole risk is a reader that reduces too far and quietly builds
//! a term at the wrong type, and a positive test cannot see that.
//!
//! The axes of `docs/testing-generated-terms.md`: the value argument is a
//! literal in some tests and a neutral in others, `an_open_element_type`
//! keeps the element type open, every positive case *uses* what it built
//! (projects, matches, folds, transports) rather than only elaborating it,
//! and both the δ spelling (a named `fn` at `Type`) and the β spelling (a
//! `λ`/parameter of function type) are exercised — the latter is the one
//! conversion cannot pre-collapse.

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

// -- repair 1: `let { … }` destructuring ------------------------------------

// `Stmt::LetRecord` read its right-hand side with `record_of`, the *structural*
// reader — the same one `resolve_dot` had to stop using. So `p.a` worked on a
// receiver whose type came through a `Nat -> Type` value and `let { a } = p;`
// did not, which is exactly the asymmetry `docs/surface-records.md` §5 says
// must not exist ("sugar over `m.a`, and it shares their code").
#[test]
fn a_let_pattern_destructures_a_type_valued_functions_record() {
    elab(
        r#"
        record Pair2(v: Nat) { a: Nat, b: Nat, }

        fn P(v: Nat) -> Type { Pair2(v) }

        // neutral value argument
        fn first(v: Nat, p: P(v)) -> Nat { let { a, b } = p; a }
        // literal value argument
        fn first0(p: P(0)) -> Nat { let { a } = p; a }

        fn mk(v: Nat) -> P(v) { Pair2 { a: 1, b: 2 } }
        theorem destructured(v: Nat): first(v, mk(v)) = 1 { refl }
        theorem agrees_with_dot(v: Nat): first(v, mk(v)) = mk(v).a { refl }
        "#,
    );
}

// The same reader one level down, and through a λ rather than a name: the
// field's own type is the record, and the outer type arrived by **β** (a
// `Nat -> Type` argument applied), which no δ-unfolding can pre-collapse.
#[test]
fn a_let_pattern_destructures_through_a_beta_redex() {
    elab(
        r#"
        record Inner(v: Nat) { val: Nat, }
        record Outer(v: Nat) { inner: Inner(v), }

        fn O(v: Nat) -> Type { Outer(v) }
        fn inner_val(v: Nat, o: O(v)) -> Nat { let { inner } = o; inner.val }

        // the β spelling: the domain is a `Nat -> Type` **value**, applied.
        // `Dom()(n)` is `El` of a β-redex under a δ-redex — no unfolding of a
        // single global can produce the record's code.
        fn Dom() -> Nat -> Type { λ (v: Nat) => Outer(v) }
        fn beta_val(n: Nat, o: Dom()(n)) -> Nat { let { inner } = o; inner.val }

        fn mk(v: Nat) -> O(v) { Outer { inner: Inner { val: 4 } } }
        theorem computes(v: Nat): inner_val(v, mk(v)) = 4 { refl }
        theorem beta_computes(v: Nat): beta_val(v, mk(v)) = 4 { refl }
        "#,
    );
}

// Negative control for repair 1: the fallback reduces *one* type, it does not
// turn everything into a record. A non-record right-hand side, and a record
// with no such field, still get their own messages.
#[test]
fn a_let_pattern_still_rejects_a_non_record() {
    let m = elab_err("fn f(n: Nat) -> Nat { let { a } = n; a }");
    assert!(m.contains("needs a record on the right"), "{m}");

    let m = elab_err(
        r#"
        record Pair2(v: Nat) { a: Nat, b: Nat, }
        fn P(v: Nat) -> Type { Pair2(v) }
        fn f(v: Nat, p: P(v)) -> Nat { let { c } = p; c }
        "#,
    );
    assert!(m.contains("has no field `c`"), "{m}");
}

// -- repair 2: the indexed-family reader ------------------------------------

const VEC: &str = r#"
inductive V<A> : (n: Nat) -> Type {
    VNil : V<A>(0),
    VCons(n: Nat, x: A, xs: V<A>(n)) : V<A>(Succ(n)),
}
"#;

// `indexed_of` reads a type back as `El (elim_Nat …)`. Reached through a
// `Nat -> Type` value the `elim_Nat` sits under a redex, so both the `match`
// dispatch and the constructor check declined.
//
// The fallback here is **not** `whnf`, and that is the point of `indexed_of_at`:
// the whnf of a family at a constructor-headed index reduces the `elim_Nat`
// away, index and all. So the code is stepped one reduction at a time and the
// structural read is retried after each — `F(0)` and `F(Succ(n))` below are the
// two cases a single `whnf` would have destroyed.
#[test]
fn an_indexed_family_survives_a_type_valued_function() {
    elab(&format!(
        "{VEC}
         fn F(n: Nat) -> Type {{ V<Nat>(n) }}

         // constructor at a *literal* index and at a constructor-headed one
         fn empty() -> F(0) {{ VNil }}
         fn push(n: Nat, x: Nat, xs: V<Nat>(n)) -> F(Succ(n)) {{ VCons(n, x, xs) }}

         // `match` at a fully **open** index — the dispatch reader
         fn len(n: Nat, xs: F(n)) -> Nat {{
             match xs {{ VNil => 0, VCons(k, x, t) => Succ(len(k, t)) }}
         }}

         theorem len_empty(): len(0, empty()) = 0 {{ refl }}
         theorem len_one(x: Nat): len(1, push(0, x, VNil)) = 1 {{ refl }}
         // and the wrapper is the family, in both directions
         theorem same(n: Nat, xs: V<Nat>(n)): F(n) {{ xs }}
         theorem same_back(n: Nat, xs: F(n)): V<Nat>(n) {{ xs }}"
    ));
}

// Negative controls for repair 2. The reader may not *invent* a family: a
// constructor of another family, and a family whose index reduced away
// (`docs/inductive-indexed-lowering.md` §6), keep their messages.
#[test]
fn the_indexed_reader_still_declines_what_it_should() {
    let m = elab_err(&format!(
        "{VEC}
         inductive W : (n: Nat) -> Type {{ WNil : W(0), }}
         fn F(n: Nat) -> Type {{ V<Nat>(n) }}
         fn bad() -> F(0) {{ WNil }}"
    ));
    assert!(m.contains("is not the expected type here"), "{m}");

    let m = elab_err(&format!(
        "{VEC}
         fn F(n: Nat) -> Type {{ V<Nat>(n) }}
         fn bad(x: Nat) -> F(0) {{ VCons(0, x, VNil) }}"
    ));
    assert!(m.contains("index"), "{m}");
}

// -- repair 3: the vector-literal reader ------------------------------------

// `elab_vec_lit` is *deliberately* not whnf'd: `Vec` reduces on its length, so
// the whnf of `[T; 0]` is `Unit` and of `[T; 2]` a Σ-chain, and the arm exists
// to see the `Vec`. The repair is therefore `decoded` and not `whnf` — one
// canonical decode, which stops exactly at `Vec`.
//
// The shape reaches here without any β at all: a record's *field* types are
// components of its lowering, and `El ⌜T⌝ ⇝ T` leaves the children wrapped, so
// a vector field of a record read as a code arrives as `El (TmVec …)`.
#[test]
fn a_vector_literal_checks_at_a_coded_vec() {
    elab(
        r#"
        record Buf(v: Nat) { xs: [Nat; 2], }

        fn B(v: Nat) -> Type { Buf(v) }
        fn two(v: Nat) -> B(v) { Buf { xs: [1, 2] } }
        theorem read_back(v: Nat): two(v).xs = [1, 2] { refl }

        // the empty case, whose whnf is `Unit` rather than a Σ-chain — the
        // one a blanket `whnf` would have silently mis-shaped
        record Empty2(v: Nat) { xs: [Nat; 0], }
        fn E(v: Nat) -> Type { Empty2(v) }
        fn none(v: Nat) -> E(v) { Empty2 { xs: [] } }
        theorem none_read_back(v: Nat): none(v).xs = [] { refl }
        "#,
    );
}

// Negative control for repair 3: the length still has to match, and a
// non-container expected type still cannot select a collection literal.
#[test]
fn a_vector_literal_still_checks_its_length() {
    let m = elab_err(
        r#"
        record Buf(v: Nat) { xs: [Nat; 2], }
        fn B(v: Nat) -> Type { Buf(v) }
        fn three(v: Nat) -> B(v) { Buf { xs: [1, 2, 3] } }
        "#,
    );
    assert!(m.contains("3 element(s) but 2 are expected"), "{m}");

    let m = elab_err(
        r#"
        record Buf(v: Nat) { n: Nat, }
        fn B(v: Nat) -> Type { Buf(v) }
        fn bad(v: Nat) -> B(v) { Buf { n: [1, 2] } }
        "#,
    );
    assert!(m.contains("no instance for `CollectionLiteral<Nat>(2)`"), "{m}");
}

// -- repair 4: the vector *receiver* readers --------------------------------

// `map`, `fold` and `cong` each read their receiver's inferred type
// structurally. A vector projected out of a record that arrived as a code has
// type `El (TmVec …)`, so all three declined — `decoded` for the same reason as
// above, since `whnf` would unfold the `Vec` and lose the element type and the
// length these read off it.
#[test]
fn the_vector_receivers_accept_a_coded_vec() {
    elab(
        r#"
        fn add(a: Nat, b: Nat) -> Nat { match b { Zero => a, Succ(k) => Succ(add(a, k)) } }

        record Buf(v: Nat) { xs: [Nat; 2], }
        fn B(v: Nat) -> Type { Buf(v) }
        fn mk(v: Nat) -> B(v) { Buf { xs: [1, 2] } }

        fn bumped(v: Nat, b: B(v)) -> [Nat; 2] { b.xs.map(λ (x: Nat) => Succ(x)) }
        fn total(v: Nat, b: B(v)) -> Nat { b.xs.fold(0, λ (x: Nat) (a: Nat) => add(x, a)) }

        theorem bumped_computes(v: Nat): bumped(v, mk(v)) = [2, 3] { refl }
        theorem total_computes(v: Nat): total(v, mk(v)) = 3 { refl }
        "#,
    );
}

// Negative control for repair 4: a non-vector receiver is still not one.
#[test]
fn the_vector_receivers_still_reject_a_non_vector() {
    let m = elab_err(
        r#"
        record Buf(v: Nat) { n: Nat, }
        fn B(v: Nat) -> Type { Buf(v) }
        fn bad(v: Nat, b: B(v)) -> Nat { b.n.fold(0, λ (x: Nat) (a: Nat) => a) }
        "#,
    );
    assert!(m.contains("receiver has to be a vector"), "{m}");
}

// -- repair 5: the container-proof motive -----------------------------------

const ROSE: &str = r#"
fn add(a: Nat, b: Nat) -> Nat { match b { Zero => a, Succ(k) => Succ(add(a, k)) } }

inductive Rose { Node(label: Nat, len: Nat, kids: [Rose; len]) }

fn size(r: Rose) -> Nat {
    match r {
        Node(l, n, kids) => Succ(kids.map(size).fold(0, λ (a: Nat) (b: Nat) => add(a, b))),
    }
}

fn size_plus(r: Rose) -> Nat {
    match r {
        Node(l, n, kids) =>
            add(kids.map(size_plus).fold(0, λ (a: Nat) (b: Nat) => add(a, b)), 1),
    }
}

theorem cong_fold(n: Nat, {xs: [Nat; n]}, {ys: [Nat; n]}, p: xs = ys):
    xs.fold(0, λ (a: Nat) (b: Nat) => add(a, b))
        = ys.fold(0, λ (a: Nat) (b: Nat) => add(a, b))
{
    j(p, λ y q => xs.fold(0, λ (a: Nat) (b: Nat) => add(a, b))
                       = y.fold(0, λ (a: Nat) (b: Nat) => add(a, b)), refl)
}
"#;

// Phase 3 of `docs/container-proofs.md` asks "is the motive an equation?"
// structurally. A **named statement** — the whole point of
// `docs/types-as-expressions.md` — is `El` of a call, so naming the statement
// of a container induction turned it back into the phase-2 rejection.
//
// `whnf` is the right fallback *here* and only here: `Id` is a weak-head normal
// form, so reducing to find one cannot overshoot. The motive is scoped
// `(Γ₀, z : ⟦D⟧)`, which is why `motive_head` rebuilds that context.
#[test]
fn a_named_statement_can_be_proved_by_container_induction() {
    elab(&format!(
        "{ROSE}
         fn Agree(r: Rose) -> Type {{ size(r) = size_plus(r) }}
         theorem same(r: Rose): Agree(r) {{
             match r {{
                 Node(l, n, kids) => Nat::cong_succ(cong_fold(n, kids.cong(same))),
             }}
         }}"
    ));
}

// The same, through **β**: the statement is parameterized by the two functions
// it relates, so the motive is `El` of an application of a δ-global to
// function *values* — the shape `RefinesOn` has in `lib/ir_v1.hthr`.
#[test]
fn a_parameterized_statement_can_be_proved_by_container_induction() {
    elab(&format!(
        "{ROSE}
         fn Stmt(f: Rose -> Nat, g: Rose -> Nat, r: Rose) -> Type {{ f(r) = g(r) }}
         theorem same(r: Rose): Stmt(size, size_plus, r) {{
             match r {{
                 Node(l, n, kids) => Nat::cong_succ(cong_fold(n, kids.cong(same))),
             }}
         }}"
    ));
}

// **The control that matters** (`docs/container-proofs.md` §9.1): a reader that
// reduces to find a shape can find the *wrong* shape, and a positive proof
// cannot tell. A false theorem of exactly this form, named exactly this way and
// discharged exactly this way, is still rejected by the kernel.
#[test]
fn a_false_named_statement_is_still_rejected() {
    let m = elab_err(&format!(
        "{ROSE}
         fn Wrong(r: Rose) -> Type {{ size(r) = Succ(size_plus(r)) }}
         theorem wrong(r: Rose): Wrong(r) {{
             match r {{
                 Node(l, n, kids) => Nat::cong_succ(cong_fold(n, kids.cong(wrong))),
             }}
         }}"
    ));
    assert!(m.contains("NotConvertible"), "{m}");
}

// …and a named motive that is *not* an equation still gets phase 3's message
// rather than a term: the reader reduces, fails to find an `Id`, and says so.
#[test]
fn a_named_non_equation_motive_still_gets_the_phase_3_message() {
    let m = elab_err(&format!(
        "{ROSE}
         record Wit(r: Rose) {{ n: Nat, pf: n = n, }}
         fn Dep(r: Rose) -> Type {{ Wit(r) }}
         fn f(r: Rose) -> Dep(r) {{ match r {{ Node(l, n, kids) => kids.map(f), }} }}"
    ));
    assert!(m.contains("independent of its argument"), "{m}");
}

// -- the readers that were already fine -------------------------------------

// The rest of the roster, in one file, at a type reached through a
// `Nat -> Type` value. Each of these already normalized its subject (they call
// `whnf` at the top or at every spine step), and this pins that: a regression
// that made any of them structural would show up here rather than in
// `lib/ir_v1.hthr`.
#[test]
fn the_already_normalizing_readers_take_the_shape() {
    elab(
        r#"
        inductive Color { Red, Green(n: Nat), }
        record Box2(v: Nat) { val: Nat, pf: val = val, c: Color, f: (x: Nat) -> Nat, }

        fn B(v: Nat) -> Type { Box2(v) }

        // `build_ctor` / `build_fields`: a record literal, a `refl` at an `Id`
        // component, and a λ at a Π component, all read off a coded expected
        fn mk(v: Nat) -> B(v) { Box2 { val: 5, pf: refl, c: Green(1), f: λ x => x } }

        // `project_field` and `resolve_dot`
        theorem projected(v: Nat): mk(v).val = 5 { refl }
        // `apply_explicit`: calling a Π-typed field of a coded record
        theorem applied(v: Nat): mk(v).f(2) = 2 { refl }
        // `elab_match` / `tag_of` / `spine`: matching a coded record's field
        fn tag(v: Nat, b: B(v)) -> Nat { match b.c { Red => 0, Green(n) => n, } }
        theorem tag_computes(v: Nat): tag(v, mk(v)) = 1 { refl }
        // `elab_match_data` on the coded record itself
        fn val_of(v: Nat, b: B(v)) -> Nat { match b { Box2(x, p, c, f) => x, } }
        theorem val_of_computes(v: Nat): val_of(v, mk(v)) = 5 { refl }
        // `unify_ty`: an implicit endpoint solved against a coded record's field
        theorem symmetric(v: Nat, b: B(v)): b.val = b.val { sym(b.pf) }
        // `j`: transport along a proof projected out of a coded record
        theorem transported(v: Nat, b: B(v)): b.val = b.val
        { j(b.pf, λ y q => b.val = y, refl) }
        "#,
    );
}

// The tier-2 (`Wf`) half of the same list, plus `absurd` and `.inj`, which read
// the *proof's* type rather than the expected one.
#[test]
fn the_recursive_and_equation_readers_take_the_shape() {
    elab(
        r#"
        inductive Color { Red, Green(n: Nat), }
        inductive Tree { Leaf, Node(l: Tree, r: Tree), }

        fn T() -> Type { Tree }
        fn C() -> Type { Color }
        fn Distinct() -> Type { Red = Green(0) }
        fn Same(a: Nat, b: Nat) -> Type { Green(a) = Green(b) }

        // `build_ctor` and `build_elim_wf` at a coded `Wf`
        fn leaf() -> T() { Leaf }
        fn size(t: T()) -> Nat { match t { Leaf => 1, Node(l, r) => Succ(size(l)) } }
        theorem size_leaf(): size(leaf()) = 1 { refl }

        // `build_absurd`: the equation is coded
        fn anything(p: Distinct()) -> C() { absurd(p) }
        // `build_inj`: likewise
        theorem injected(a: Nat, b: Nat, p: Same(a, b)): a = b { p.inj(0) }
        "#,
    );
}

// The **open element type** axis across the repaired readers: `A` is the
// declaration's own parameter, so nothing about the record's lowering is
// closed while it is being read.
#[test]
fn an_open_element_type_reaches_the_repaired_readers() {
    elab(
        r#"
        record Buf<A>(v: Nat) { one: A, xs: [A; 2], }

        fn OpenT<A>(v: Nat) -> Type { Buf<A>(v) }
        fn open_first<A>(v: Nat, b: OpenT<A>(v)) -> A { let { one } = b; one }
        fn open_vec<A>(v: Nat, b: OpenT<A>(v)) -> [A; 2] { b.xs }

        fn NatT(v: Nat) -> Type { Buf<Nat>(v) }
        fn mk(v: Nat) -> NatT(v) { Buf { one: 9, xs: [1, 2] } }
        theorem open_first_computes(v: Nat): open_first<Nat>(v, mk(v)) = 9 { refl }
        theorem open_vec_computes(v: Nat): open_vec<Nat>(v, mk(v)) = [1, 2] { refl }
        "#,
    );
}
