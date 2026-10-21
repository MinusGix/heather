//! Value parameters on `record` — the surface's value-indexed Σ
//! (`docs/surface-value-parameters.md`). Tracking issue:
//! `issues/surface-existential.md`; the feasibility report this implements is
//! `docs/surface-existential-investigation.md`, whose §B.1 hand-built kernel
//! terms (`crates/elab/tests/surface_existential_probe.rs`) are the shapes the
//! generator's output has to match.
//!
//! Nothing here touches the kernel. A value-parameterized record is the same
//! one-constructor tier-0 lowering with the parameters *substituted into the
//! field types*, so every term below is emitted by the generator that already
//! existed and is re-checked by the real kernel.
//!
//! **What the kernel cannot catch, and why half this file is propositional.**
//! The parameter lives in the ambient Γ and must be weakened across the Σ
//! binders the field spine pushes. Get that shift wrong and the record still
//! declares, still checks, and still inhabits — it is just a *different*
//! proposition, usually a trivially inhabited one (`Σ n. dbl n = n` instead of
//! `Σ n. dbl n = m`). That is `docs/surface-existential-investigation.md` §H
//! risk 3, and the only observer for it is a proposition that must **not** be
//! provable: §7 and §8 below. A suite that checked only the encoding would pass
//! against the captured spelling.
//!
//! Per `docs/testing-generated-terms.md` the suite varies: a **literal** and a
//! **neutral** parameter (§1 vs §3), an **open** element/field type (§9's
//! `record Box<A>(k)`), a **checking** position and not only computation (§4,
//! §5), and negative controls at both levels — the encoding (§6) and the
//! proposition (§7, §8).

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

/// The miniature of `docs/surface-existential-investigation.md` §B.1, now
/// written at the surface: a real recursive function, and a record that is a
/// **predicate** over the free value `m`. `dbl` is deliberately a recursive
/// `fn` rather than a constructor, so `dbl(n)` at a neutral `n` is a stuck
/// eliminator inside a *type* — the same shape `eval(n, p)(env, ir)` has in
/// `lib/ir_v1.hthr`, and the one that could have been rejected but is not.
const HALTS: &str = r#"
fn dbl(n: Nat) -> Nat {
    match n { Zero => 0, Succ(k) => Succ(Succ(dbl(k))) }
}

record Halts(m: Nat) { n: Nat, h: dbl(n) = m }
"#;

// -- 1-2: formation and introduction --------------------------------------

/// §1 of the probe: the type **forms** with the parameter open, and the
/// parameter really does reach the second field's type. Both directions are
/// here — a closed parameter (introduction discharged by conversion running
/// `dbl 2 ⇝ 4`) and an open one (the parameter a `theorem` binder, so nothing
/// computes).
#[test]
fn a_value_parameterized_record_forms_and_inhabits() {
    ok(&format!(
        r#"
        {HALTS}
        fn h4() -> Halts(4) {{ Halts(2, refl) }}
        theorem forms_open(m: Nat, c: Halts(m)): Nat {{ c.n }}
        "#
    ));
}

/// The parameter is a *computed* term over the witness, on fully open data —
/// probe §4. Nothing here is closed by evaluation: `dbl(k)` is neutral at a
/// neutral `k`, so the equation is discharged by `refl` at a stuck term on both
/// sides.
#[test]
fn introduction_on_fully_open_data() {
    ok(&format!(
        r#"
        {HALTS}
        fn open(k: Nat) -> Halts(dbl(k)) {{ Halts(k, refl) }}
        "#
    ));
}

// -- 3-4: destruction, at a neutral receiver -------------------------------

/// The consumer shape. `c` is a **binder**, not a literal, so no projection
/// computes: the dependent field's type has to come out right from the Σ tail
/// with the parameter substituted, and `c.h : dbl(c.n) = m` is the observer.
/// Both destructuring forms are exercised — projection, `let { }`, and a match
/// arm — since each walks the spine by its own code path.
#[test]
fn projection_match_and_let_all_see_the_parameter() {
    ok(&format!(
        r#"
        {HALTS}
        theorem by_projection(m: Nat, c: Halts(m)): dbl(c.n) = m {{ c.h }}
        theorem by_let(m: Nat, c: Halts(m)): dbl(c.n) = m {{
            let {{ n, h }} = c;
            h
        }}
        theorem by_match(m: Nat, c: Halts(m)): dbl(c.n) = m {{
            match c {{ Halts(n, h) => h }}
        }}
        "#
    ));
}

/// The payoff shape (probe §5): from `c : Halts(m)` and an open family
/// `f : (k: Nat) -> Q(dbl(k))`, conclude `Q(m)` — by instantiating `f` at the
/// witness and transporting along the equation. `Q` is a *declared* family, so
/// nothing here is discharged by computation; this is the elimination the
/// bounded form cannot express.
#[test]
fn elimination_uses_the_witness_and_the_equation() {
    ok(&format!(
        r#"
        {HALTS}
        record Q(x: Nat) {{ w: Nat, hw: w = x }}
        theorem transport(m: Nat, c: Halts(m), f: (k: Nat) -> Q(dbl(k))): Q(m) {{
            j(c.h, λ y p => Q(y), f(c.n))
        }}
        "#
    ));
}

// -- 5: construction is checking-position only -----------------------------

/// The design decision of `docs/surface-existential-investigation.md` §C.5,
/// closed the recommended way (docs/surface-value-parameters.md §4): a value
/// parameter appears only inside a *field's* type, so nothing in the argument
/// list determines it. Every checking position supplies it — a declared result
/// type, an argument position — and both the call spelling and the
/// record-literal spelling go through the same builder.
///
/// One more checking position, added 2026-08-02: the annotated
/// `let x: T = e;`. It did not parse for *any* type when this test was
/// written, and the reason recorded here was wrong — not "the type grammar has
/// `a = b`" but `expr()`'s comparison rung, reached through `ty_atom`'s
/// fall-through (`docs/let-and-blocks-design.md` §1.1(1)). The annotation now
/// suppresses that rung, so the position works and is exercised below.
#[test]
fn checking_position_supplies_the_parameters() {
    ok(&format!(
        r#"
        {HALTS}
        fn from_result() -> Halts(4) {{ Halts(2, refl) }}
        fn from_literal() -> Halts(4) {{ Halts {{ n: 2, h: refl }} }}
        fn takes(c: Halts(4)) -> Nat {{ c.n }}
        fn from_argument() -> Nat {{ takes(Halts(2, refl)) }}
        fn from_annotated_let() -> Nat {{ let c: Halts(4) = Halts(2, refl); c.n }}
        "#
    ));
}

/// …and where nothing fixes the parameter, a named diagnostic, not a wrong
/// guess: `h`'s argument is `refl`, which only checks, so the field that would
/// fix `m` cannot (docs/surface-value-parameters.md §4.1). Written type
/// arguments do not change that — `<…>` supplies types, and the value
/// arguments are read off the fields either way.
#[test]
fn inference_position_is_refused_by_name() {
    let m = bad(&format!(
        "{HALTS}\nfn inf() -> Nat {{ let c = Halts(2, refl); c.n }}"
    ));
    assert!(m.contains("cannot infer the value argument `m` of `Halts`"), "{m}");
    assert!(m.contains("its field `h` would"), "{m}");
    assert!(m.contains("checking position"), "{m}");
    let m = bad(&format!(
        "{HALTS}\nrecord Box<A>(k: Nat) {{ v: A, n: Nat, h: dbl(n) = k }}\n\
         fn f() -> Nat {{ let x = Box<Nat>(7, 2, refl); x.n }}"
    ));
    assert!(m.contains("cannot infer the value argument `k` of `Box`"), "{m}");
}

/// The same constructions infer once an argument's type carries the
/// parameter — with the type arguments written or not.
#[test]
fn inference_position_reads_the_parameter_off_a_field() {
    ok(&format!(
        r#"
        {HALTS}
        record Box<A>(k: Nat) {{ v: A, n: Nat, h: dbl(n) = k }}
        fn halts_k({{k: Nat}}, c: Halts(k)) -> Nat {{ k }}
        fn box_k<A>({{k: Nat}}, b: Box<A>(k)) -> Nat {{ k }}
        theorem h(k: Nat, n: Nat, p: dbl(n) = k): halts_k(Halts(n, p)) = k {{ refl }}
        theorem b(k: Nat, n: Nat, p: dbl(n) = k): box_k(Box<Nat>(7, n, p)) = k {{ refl }}
        theorem b2<A>(a: A, k: Nat, n: Nat, p: dbl(n) = k): box_k(Box(a, n, p)) = k {{ refl }}
        fn let_bound(n: Nat, p: dbl(n) = 4) -> Nat {{ let c = Halts(n, p); halts_k(c) }}
        theorem lit(n: Nat, p: dbl(n) = 4): let_bound(n, p) = 4 {{ refl }}
        "#
    ));
}

// -- 6: encoding-level negative controls -----------------------------------

/// The arity and shape rejections: a bare `Halts`, the wrong number of value
/// arguments, and the name collisions.
/// Each says what to write instead.
#[test]
fn the_form_errors_carry_their_messages() {
    let m = bad(&format!("{HALTS}\ntheorem t(c: Halts): Nat {{ c.n }}"));
    assert!(m.contains("takes 1 value argument"), "{m}");
    let m = bad(&format!("{HALTS}\ntheorem t(c: Halts(1, 2)): Nat {{ c.n }}"));
    assert!(m.contains("takes 1 value argument(s), found 2"), "{m}");
    // An `inductive` takes them too, since 2026-10-21; its refusals are the
    // non-uniform occurrence and an index beside them
    // (crates/elab/tests/inductive_value_parameters.rs).
    ok("inductive Fine(m: Nat) { A, B }");
    let m = bad("record R(m: Nat, m: Nat) { f: Nat }");
    assert!(m.contains("duplicate value parameter"), "{m}");
    let m = bad("record R<A>(A: Nat) { f: Nat }");
    assert!(m.contains("already a type parameter"), "{m}");
    let m = bad("record R(f: Nat) { f: Nat }");
    assert!(m.contains("both a value parameter and a field"), "{m}");
}

/// A value argument is *checked*, not merely counted: the declared parameter
/// type is what the use site has to satisfy.
#[test]
fn a_value_argument_is_checked_at_its_declared_type() {
    let m = bad(&format!(
        r#"
        {HALTS}
        inductive Bool2 {{ T2, F2 }}
        theorem t(c: Halts(T2)): Nat {{ c.n }}
        "#
    ));
    assert!(!m.is_empty(), "a `Bool2` where a `Nat` is declared must be refused");
}

// -- 7-8: the propositional negative controls ------------------------------

/// **The load-bearing test of the round** (`§H` risk 3). If the parameter were
/// not weakened across the Σ binder it would be captured by the witness field,
/// and `Halts(m)` would silently mean `Σ n. dbl n = n` — which `⟨0, refl⟩`
/// inhabits at *every* `m`. So a proof of `Halts(m)` at an open `m` must be
/// impossible, and specifically these two must fail:
///
/// - `Halts(0, refl)` — the canonical inhabitant of the captured spelling;
/// - `Halts(m, refl)` — the "obvious" witness under capture, since `dbl m = m`
///   would then be what is asked.
///
/// Neither is a type error under the wrong encoding. They are type errors only
/// because the encoding is right, which is exactly why the observer has to be
/// the proposition and not the term shape.
#[test]
fn an_unshifted_parameter_would_be_provable_and_is_not() {
    let m = bad(&format!(
        "{HALTS}\ntheorem trivial(m: Nat): Halts(m) {{ Halts(0, refl) }}"
    ));
    assert!(m.contains("NotConvertible"), "{m}");
    let m = bad(&format!(
        "{HALTS}\ntheorem trivial(m: Nat): Halts(m) {{ Halts(m, refl) }}"
    ));
    assert!(m.contains("NotConvertible"), "{m}");
}

/// A witness for one parameter does not inhabit another — probe §7, the
/// discriminating half. `Halts(4)`'s witness is `2`; at `Halts(5)` the equation
/// `dbl 2 = 5` is false by computation, and at an open `Halts(m)` it is not
/// even closed. Both must be rejections, and the record must not be
/// *coercible* between two parameters either.
#[test]
fn a_witness_for_one_parameter_does_not_inhabit_another() {
    let m = bad(&format!("{HALTS}\nfn wrong() -> Halts(5) {{ Halts(2, refl) }}"));
    assert!(m.contains("NotConvertible"), "{m}");
    let m = bad(&format!(
        "{HALTS}\nfn coerce(c: Halts(4)) -> Halts(5) {{ c }}"
    ));
    // Stated, now that the display shows the parameter the two differ in
    // (issues/width-specific-method-on-other-width.md).
    assert!(m.contains("this has type `Halts(4)`, but `Halts(5)` is expected here"), "{m}");
    // …and the same statement at the *right* parameter is provable, so the two
    // rejections above are about the parameter and not about the spelling.
    ok(&format!("{HALTS}\nfn right() -> Halts(4) {{ Halts(2, refl) }}"));
}

// -- 9-10: composition and levels ------------------------------------------

/// `record R<A>(k: T)` — type parameters and value parameters compose, in that
/// order (docs/surface-value-parameters.md §1). The **open** element type is
/// the axis `docs/testing-generated-terms.md` says hides three defects on its
/// own: `A` is a type parameter here and the field `v: A` is open, while `k` is
/// a value parameter reaching the third field's type.
#[test]
fn type_parameters_and_value_parameters_compose() {
    ok(&format!(
        r#"
        {HALTS}
        record Box<A>(k: Nat) {{ v: A, n: Nat, h: dbl(n) = k }}
        fn mk() -> Box<Nat>(4) {{ Box(7, 2, refl) }}
        theorem open_elem<A>(x: A, c: Box<A>(4)): A {{ c.v }}
        theorem open_param<A>(k: Nat, c: Box<A>(k)): dbl(c.n) = k {{ c.h }}
        "#
    ));
}

/// The level rule (§G): a value parameter is a *term*, so it contributes **no**
/// level; the record's level is still the Σ join of its field levels. A
/// uniformly-level-0 suite cannot see a dropped join
/// (issues/indexed-families.md's 2026-07-30 lesson), so one declaration here
/// carries a `Type`-valued field and therefore lands at level 1.
///
/// The observer is the prelude's `sym`, which is `theorem sym<A>` at
/// `Type<0>`: at a level-1 record it must be a `LevelMismatch`, and at the
/// level-0 `Halts` it must go through. Both halves, since either alone is
/// satisfied by the wrong answer.
#[test]
fn a_value_parameter_contributes_no_level_and_the_join_is_kept() {
    let src = format!(
        r#"
        {HALTS}
        record Wrap(k: Nat) {{ c: Type, w: c, h: dbl(k) = dbl(k) }}
        fn mkwrap() -> Wrap(1) {{ Wrap(Nat, 5, refl) }}
        "#
    );
    ok(&src);
    // level 1: non-cumulative, so a `Type<0>` lemma does not apply.
    let m = bad(&format!(
        "{src}\ntheorem s(x: Wrap(1), y: Wrap(1), h: x = y): y = x {{ sym(h) }}"
    ));
    assert!(m.contains("LevelMismatch"), "{m}");
    // level 0: the same lemma at `Halts` does.
    ok(&format!(
        "{src}\ntheorem s(x: Halts(4), y: Halts(4), h: x = y): y = x {{ sym(h) }}"
    ));
}

/// A value-parameterized record as a **field** of another one, with the outer
/// parameter flowing into the inner's argument. This is the shift discipline at
/// its most exposed: the inner instance is lowered inside the outer's field
/// spine, one binder down, so the outer parameter is weakened once on the way
/// into the inner declaration and again inside *its* spine. A recursive
/// occurrence stays rejected (a record that mentions itself is an `inductive`,
/// and one applied to its own parameter is caught by the nesting scan).
#[test]
fn a_value_parameterized_record_nests_in_another() {
    ok(&format!(
        r#"
        {HALTS}
        record Outer(k: Nat) {{ c: Halts(k), d: Nat }}
        fn mko() -> Outer(4) {{ Outer(Halts(2, refl), 9) }}
        theorem nested(k: Nat, o: Outer(k)): dbl(o.c.n) = k {{ o.c.h }}
        "#
    ));
    let m = bad("record R(m: Nat) { x: R(m) }");
    assert!(!m.is_empty(), "a self-referential record must not lower");
}

/// Value parameters are a **telescope**: parameter `j`'s declared type may
/// mention parameters `0..j`, and a *function-valued* parameter is fine (the
/// `BindInv` shape of `lib/ir_v1.hthr` needs one — `reject_function_fields`
/// keys on self-occurrence, not on shape).
#[test]
fn the_parameter_list_is_a_dependent_telescope() {
    ok(&format!(
        r#"
        {HALTS}
        record Tel(a: Nat, p: dbl(a) = dbl(a)) {{ z: Nat, hz: dbl(z) = dbl(a) }}
        fn mktel() -> Tel(2, refl) {{ Tel(2, refl) }}
        record Fun(f: Nat -> Nat, x: Nat) {{ y: Nat, hy: f(y) = f(x) }}
        fn mkfun(g: Nat -> Nat, x: Nat) -> Fun(g, x) {{ Fun(x, refl) }}
        "#
    ));
}
