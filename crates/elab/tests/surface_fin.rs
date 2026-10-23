//! The surface indexing layer (`docs/surface-fin-indexing-design.md`):
//! `Fin(n)` as a type, `FZ`/`FS(i)` and numerals as its indices, `match` on a
//! `Fin`, and the postfix `xs[i]`.
//!
//! Nothing here touches the kernel — `Type::Fin`, `Inl`/`Inr`/`Case`/
//! `ElimEmpty` and the `nth` schema all predate the round; what was missing was
//! the ability to *write* any of them. So every term below is re-checked by the
//! real kernel, and the suite's job is adequacy: that the surface emits the
//! terms the elaborator's own container machinery already emits.
//!
//! Per `docs/testing-generated-terms.md` the axes are varied per form. Axis 2
//! ("an open element type") is an open **length** here — a closed `Fin(3)`
//! hides every shift — and it is the axis the four `vec.rs` defects were
//! hiding in. Axis 4's negative control is `FZ = FS(FZ)`: a positive test
//! cannot distinguish a type from a quotient of it, so without it an encoding
//! that collapsed the two indices passes everything else.
//!
//! Two tests are **oracle-side pins** (design doc §6.1): `xs[i]` must emit
//! exactly `heather_kernel::term::nth`'s output and a numeral at a `Fin` must
//! emit exactly `wf.rs`'s `fin_index`'s, each asserted by equality against a
//! directly-built term. These fixtures never load `lib/lang/vec_code.hthr`, so the
//! hook declines and the pins hold; they are the left-hand side the port
//! round's cross-checks compare against (in_language_{tabulate,nth}.rs).

use std::sync::Arc as Rc;

use heather_elab::{ElabError, Elaborator};
use heather_kernel::level::Level;
use heather_kernel::term::{nth, GlobalBinding, LocalVar, Term, Type};

fn ok(src: &str) {
    let mut e = Elaborator::with_prelude().expect("prelude");
    if let Err(err) = e.elab_source(src) {
        panic!("expected success, got: {}", err.render(src));
    }
}

fn elab(src: &str) -> Elaborator {
    let mut e = Elaborator::with_prelude().expect("prelude");
    e.elab_source(src).unwrap_or_else(|err| panic!("{}", err.render(src)));
    e
}

fn bad(src: &str) -> String {
    let mut e = Elaborator::with_prelude().expect("prelude");
    match e.elab_source(src) {
        Ok(()) => panic!("expected a rejection, but it elaborated:\n{src}"),
        Err(ElabError::Elab { msg, .. }) => msg,
        Err(other) => format!("{other}"),
    }
}

/// The type and body of the *last* committed binding — the fixture each pin
/// declares last, so no name table is needed.
fn last_binding(e: &Elaborator) -> (Type, Term) {
    match e.psi().bindings.last().expect("a binding") {
        GlobalBinding::Tm { ty, body: Some(b), .. } => ((**ty).clone(), (**b).clone()),
        other => panic!("expected a bodied Tm binding, found {other:?}"),
    }
}

// -- 1: `Fin(n)` as a type --------------------------------------------------

/// The decision of §2.1, and the only way to see it: a `Fin(n)` binder's
/// kernel type is `Type::Fin`, not `El(TmFin n)`. Conversion sees through the
/// difference, so nothing would be *unsound* about the encoding — but
/// `unify_ty`'s `Fin`/`Fin` case would stop firing and every diagnostic would
/// print `El(Fin(n))`.
#[test]
fn a_fin_binder_is_type_fin_and_not_a_decoded_code() {
    let e = elab("fn f(n: Nat, i: Fin(n)) -> Nat { n }");
    let (ty, _) = last_binding(&e);
    // `(n: Nat) -> (i: Fin n) -> Nat`: peel the first Π and look at the
    // second's domain.
    let Type::Pi { cod, .. } = &ty else { panic!("expected a Π") };
    let Type::Pi { dom, .. } = &**cod else { panic!("expected a second Π") };
    assert!(
        matches!(&**dom, Type::Fin { .. }),
        "a `Fin(n)` binder must lower to `Type::Fin`, not to `El` of its code"
    );
}

/// The *expression* spelling, which is what makes §8's coverage-table row
/// honestly say "yes": `Fin(n)` where a term is expected is the code
/// `TmFin n : Ty 0`.
#[test]
fn fin_is_writable_as_a_type_valued_function_body() {
    ok("fn Idx(n: Nat) -> Type { Fin(n) }");
    // …and the abbreviation is usable as a type, through the ordinary decode.
    ok("fn Idx(n: Nat) -> Type { Fin(n) }
        fn g(n: Nat, i: Idx(Succ(n))) -> Nat { n }");
}

/// A `Fin` at a level above 0 is not a thing — `Type::Fin` carries no level —
/// so the code lands at `Ty 0` exactly and `-> Type<1>` must be rejected.
#[test]
fn fin_lives_at_level_zero_only() {
    let msg = bad("fn Idx(n: Nat) -> Type<1> { Fin(n) }");
    assert!(msg.contains("level"), "{msg}");
}

#[test]
fn fin_at_the_wrong_arity_or_the_wrong_length_type_is_rejected() {
    // Arity 0 and 2 fall through the parser's one-argument arm to `OfExpr`,
    // where the elaborator's `Fin` inference arm states the arity.
    for src in [
        "fn f(i: Fin()) -> Nat { 0 }",
        "fn f(n: Nat, i: Fin(n, n)) -> Nat { 0 }",
    ] {
        let msg = bad(src);
        assert!(
            msg.contains("`Fin` takes exactly one argument"),
            "expected the arity diagnostic, got: {msg}"
        );
    }
    // A length that is not a `Nat`.
    let msg = bad("fn f(p: 0 = 0, i: Fin(p)) -> Nat { 0 }");
    assert!(!msg.is_empty(), "a non-`Nat` length must be rejected");
}

/// `Fin` is reserved in *type* position and shadowable in *expression*
/// position, the same asymmetry `map`/`head`/`cons` have (§2.2).
#[test]
fn a_user_fin_still_resolves_in_expression_position() {
    ok("fn Fin2(n: Nat) -> Nat { n }
        fn use_it(n: Nat) -> Nat { Fin2(n) }");
    // A local binder wins in expression position…
    ok("fn shadow(Fin: Nat) -> Nat { Fin }");
}

// -- 2: `FZ`, `FS(i)`, and numerals -----------------------------------------

/// Axis 1, literal: the index computes, so this is adequacy and not merely
/// typing.
///
/// The vector is bound by a `fn` rather than written in the theorem's own
/// statement, because a *statement* is parsed as a type and `[` in **prefix**
/// position there is the vector-type rule `[T; n]` — unchanged by this round,
/// and unrelated to the postfix `[` (§5.1).
#[test]
fn indexing_a_literal_vector_computes() {
    const V: &str = "fn v() -> [Nat; 3] { [10, 20, 30] }\n";
    ok(&format!("{V}theorem t(): v()[1] = 20 {{ refl }}"));
    ok(&format!("{V}theorem t0(): v()[0] = 10 {{ refl }}"));
    ok(&format!("{V}theorem t2(): v()[2] = 30 {{ refl }}"));
    // Postfix on a call result, and chained after a method — both fall out of
    // living in `postfix`'s loop.
    ok(&format!(
        "{V}theorem tm(): v().map(\u{3bb} (n: Nat) => Succ(n))[0] = 11 {{ refl }}"
    ));
}

/// Axis 2, the open **length**: `FZ` still checks against a `Fin` whose length
/// is `Succ(n)` for an ambient `n`, nothing reduces, and the annotations carry
/// it.
#[test]
fn fz_checks_at_an_open_length() {
    ok("fn at(n: Nat, xs: [Nat; Succ(n)]) -> Nat { xs[FZ] }");
    ok("fn at1(n: Nat, xs: [Nat; Succ(Succ(n))]) -> Nat { xs[FS(FZ)] }");
}

/// Axis 2 for the element type as well: the elements are vectors of ambient
/// length, so a wrong shift on the element type shows up here and nowhere in
/// the fixtures above.
#[test]
fn indexing_at_an_open_element_type() {
    ok("fn at2(m: Nat, xs: [[Nat; Succ(m)]; 3]) -> [Nat; Succ(m)] { xs[2] }");
    ok("fn at3(m: Nat, k: Nat, xs: [[Nat; Succ(m)]; Succ(k)]) -> [Nat; Succ(m)] {
            xs[FZ]
        }");
}

/// Axis 3: a **checking** position where nothing reduces — an argument at an
/// open length, and an index checked against `Fin(len)` by `xs[i]` itself. The
/// annotation has to convert with the built index rather than compute it away.
///
/// The *annotated `let`* is the third such position. It could not be written
/// when this test was first added — `let x: T = e;` did not parse for any `T`
/// reaching `ty_atom`'s expression fall-through, `let x: Nat = 0;` included —
/// and the caveat recorded here is retired by
/// `docs/let-and-blocks-design.md` §3, which fixed it. It is exercised below,
/// at an **open** length, so the annotation must convert with the built index
/// rather than compute away.
#[test]
fn an_index_in_checking_position() {
    ok("fn take(n: Nat, i: Fin(Succ(n))) -> Nat { 0 }
        fn call(n: Nat) -> Nat { take(n, FZ) }");
    ok("fn take(n: Nat, i: Fin(Succ(Succ(n)))) -> Nat { 0 }
        fn call(n: Nat) -> Nat { take(n, FS(FZ)) }
        fn call_num(n: Nat) -> Nat { take(n, 1) }");
    // The index of an `xs[i]` is itself a checking position, at the
    // *receiver's* length.
    ok("fn at(n: Nat, xs: [Nat; Succ(Succ(n))]) -> Nat { xs[FS(FZ)] }");
    // The annotated `let`, at an open length — the position the caveat above
    // said was unwritable.
    ok("fn at(n: Nat, xs: [Nat; Succ(n)]) -> Nat { let i: Fin(Succ(n)) = FZ; xs[i] }");
    ok("fn at(n: Nat, xs: [Nat; Succ(Succ(n))]) -> Nat {
            let i: Fin(Succ(Succ(n))) = FS(FZ);
            xs[i]
        }");
}

/// The two inference-position diagnostics, each naming its own form (§3.2).
#[test]
fn fz_and_fs_need_an_expected_type() {
    let msg = bad("fn f() -> Nat { let i = FZ; 0 }");
    assert!(msg.contains("`FZ` needs an expected `Fin` type"), "{msg}");
    let msg = bad("fn f() -> Nat { let i = FS(FZ); 0 }");
    assert!(msg.contains("`FS` needs an expected `Fin` type"), "{msg}");
}

/// The two length-shaped rejections, with their two *distinct* messages: an
/// empty `Fin` has no index at all, whereas an open one has no *canonical*
/// index — a different fact, and the fix is different.
#[test]
fn fz_at_an_empty_and_at_an_open_length() {
    const TAKE: &str = "fn take0(i: Fin(0)) -> Nat { 0 }
                        fn taken(n: Nat, i: Fin(n)) -> Nat { 0 }\n";
    let msg = bad(&format!("{TAKE}fn f() -> Nat {{ take0(FZ) }}"));
    assert!(msg.contains("`Fin(0)` is empty, so it has no index"), "{msg}");
    let msg = bad(&format!("{TAKE}fn f(n: Nat) -> Nat {{ taken(n, FZ) }}"));
    assert!(
        msg.contains("has to reduce to a successor") && msg.contains("no canonical index"),
        "{msg}"
    );
    // Same two for `FS`, since both go through one rule.
    let msg = bad(&format!("{TAKE}fn f(n: Nat) -> Nat {{ taken(n, FS(FZ)) }}"));
    assert!(msg.contains("no canonical index"), "{msg}");
}

/// A numeral that overshoots the length names both the numeral and what the
/// length reduced to.
#[test]
fn a_numeral_past_the_end_is_rejected() {
    let msg = bad("fn f(xs: [Nat; 2]) -> Nat { xs[2] }");
    assert!(msg.contains("`2` is not an index of this `Fin`"), "{msg}");
    let msg = bad("fn f(n: Nat, xs: [Nat; Succ(n)]) -> Nat { xs[1] }");
    assert!(msg.contains("`1` is not an index of this `Fin`"), "{msg}");
}

/// Negative control (c): the index's length must **convert** with the
/// vector's. Two distinct ambient variables are not convertible, and this is
/// the test that they are not silently coerced.
#[test]
fn an_index_of_another_vectors_length_is_rejected() {
    let msg = bad(
        "fn f(n: Nat, m: Nat, xs: [Nat; Succ(n)], i: Fin(Succ(m))) -> Nat { xs[i] }",
    );
    assert!(!msg.is_empty(), "an index at the wrong length must be rejected");
}

/// Negative control (e): a non-vector receiver.
#[test]
fn indexing_a_non_vector_is_rejected() {
    let msg = bad("fn f(n: Nat) -> Nat { n[0] }");
    assert!(msg.contains("an index needs a vector receiver"), "{msg}");
}

/// **Axis 4**, the control a positive test cannot supply: a type is not
/// distinguished from a quotient of it by any amount of well-typing. `FZ` and
/// `FS(FZ)` are distinct indices of `Fin(2)`, so `refl` between them must be
/// rejected — without this, an encoding that collapsed the two passes every
/// test above.
#[test]
fn distinct_indices_are_not_definitionally_equal() {
    // Both endpoints check at `Fin(2)`, and both sides compute — so if the two
    // indices were the same term, `refl` would go through and `7 = 9`.
    let src = "fn pick(i: Fin(2)) -> Nat { match i { FZ => 7, FS(j) => 9 } }
               theorem bad(): pick(FZ) = pick(FS(FZ)) { refl }";
    let msg = bad(src);
    assert!(!msg.is_empty(), "`7 = 9` must not be provable by `refl`");
    // The same through `xs[i]`, where the two indices project different
    // elements of one vector.
    let src = "fn v() -> [Nat; 2] { [10, 20] }
               theorem bad2(): v()[FZ] = v()[FS(FZ)] { refl }";
    assert!(!bad(src).is_empty(), "`10 = 20` must not be provable by `refl`");
}

// -- 3: `match` on a `Fin` --------------------------------------------------

/// `Fin(0) ⇝ Empty⁰` is a whnf step, so `match i { }` at `Fin(0)` *is*
/// `elim_Empty` through the arm that already existed (§1.1 finding 1) — and
/// the existing no-arms error guards it.
#[test]
fn a_match_on_fin_zero_is_elim_empty() {
    let e = elab("fn f(i: Fin(0)) -> Nat { match i { } }");
    let (_, body) = last_binding(&e);
    // `fun (i: Fin 0) => elim_Empty(…)`.
    let Term::Lam { body, .. } = &body else { panic!("expected a λ") };
    assert!(
        matches!(&**body, Term::ElimEmpty { .. }),
        "a `match` with no arms on `Fin(0)` must be `elim_Empty`"
    );
    let msg = bad("fn f(i: Fin(0)) -> Nat { match i { FZ => 0 } }");
    assert!(msg.contains("no constructors"), "{msg}");
}

/// A **literal** length: both arms, and the result *computes* — `conv` against
/// the expected reduct, not merely `check`.
#[test]
fn a_match_on_fin_at_a_literal_length_computes() {
    let src = "fn pick(i: Fin(2)) -> Nat { match i { FZ => 7, FS(j) => 9 } }
               theorem z(): pick(FZ) = 7 { refl }
               theorem s(): pick(FS(FZ)) = 9 { refl }
               theorem n(): pick(1) = 9 { refl }";
    ok(src);
}

/// The axis-1 **neutral** case that matters, and the shape `nth_code` will
/// have: recurse on the *length* with `match`, and inside the successor arm
/// the index becomes matchable while the scrutinee itself stays neutral.
///
/// The predecessor binder is `j`, the natural spelling, and it is the
/// **acceptance test of rule 1** (docs/let-and-blocks-design.md §5.5). Until
/// 2026-08-02 a *use* of a binder named `j` parsed as a `j`-expression and
/// failed at the missing `(`, so this suite spelled it `jx`; `atom` now
/// recognizes the form only when a `(` follows, and the workaround is
/// reverted at the exact site that motivated it.
#[test]
fn a_match_on_fin_inside_a_match_on_the_length() {
    ok("fn at(k: Nat) -> Fin(k) -> Nat {
            match k as λ z => Fin(z) -> Nat {
                Zero => fun (i: Fin(0)) => match i { },
                Succ(zk, ih) => fun (i: Fin(Succ(zk))) =>
                    match i { FZ => 0, FS(j) => Succ(ih(j)) },
            }
        }");
    // The payload `nth_code` itself needs, modulo the slot plumbing: a `Vec`
    // in the motive and the projections in the arms.
    ok("fn nth_by_hand<A>(k: Nat) -> [A; k] -> Fin(k) -> A {
            match k as λ z => [A; z] -> Fin(z) -> A {
                Zero => fun (v: [A; 0]) => fun (i: Fin(0)) => match i { },
                Succ(zk, ih) => fun (v: [A; Succ(zk)]) => fun (i: Fin(Succ(zk))) =>
                    match i {
                        FZ => head(v),
                        FS(j) => ih(tail(v), j),
                    },
            }
        }");
}

/// Axis 3 for `match`: a **dependent** motive in a checking position, so the
/// arm types must convert with the goal rather than be reduced away.
#[test]
fn a_match_on_fin_with_a_dependent_motive() {
    ok("fn pick(i: Fin(2)) -> Nat { match i { FZ => 7, FS(j) => 9 } }
        theorem always(i: Fin(2)): pick(i) = pick(i) {
            match i as λ w => pick(w) = pick(w) {
                FZ => refl,
                FS(j) => refl,
            }
        }");
}

/// The neutral-length rejection of §4.3. Permanent rather than unimplemented
/// (§1.2), so the message names the fix — recursing on the length — and must
/// not read like a TODO.
#[test]
fn a_match_on_fin_at_a_neutral_length_names_the_fix() {
    let msg = bad("fn f(n: Nat, i: Fin(n)) -> Nat { match i { FZ => 0, FS(j) => 1 } }");
    assert!(
        msg.contains("needs its length to reduce to `0` or a successor")
            && msg.contains("here it is `n`")
            && msg.contains("Recurse on the length first")
            && msg.contains("how the index becomes matchable"),
        "{msg}"
    );
    assert!(
        !msg.contains("not supported") && !msg.contains("yet"),
        "the limitation is permanent, so the message must not read like a TODO: {msg}"
    );
}

#[test]
fn the_arm_diagnostics_for_a_fin_match() {
    let msg = bad("fn f(i: Fin(2)) -> Nat { match i { Zero => 0, FS(j) => 1 } }");
    assert!(msg.contains("`Zero` is not an index of a `Fin`"), "{msg}");
    let msg = bad("fn f(i: Fin(2)) -> Nat { match i { FZ => 0, FZ => 1 } }");
    assert!(msg.contains("duplicate arm for `FZ`"), "{msg}");
    let msg = bad("fn f(i: Fin(2)) -> Nat { match i { FZ => 0 } }");
    assert!(msg.contains("needs both an `FZ` and an `FS(i)` arm"), "{msg}");
    let msg = bad("fn f(i: Fin(2)) -> Nat { match i { FZ(x) => 0, FS(j) => 1 } }");
    assert!(msg.contains("`FZ` binds no fields"), "{msg}");
    for arms in ["FZ => 0, FS => 1", "FZ => 0, FS(j, k) => 1"] {
        let msg = bad(&format!("fn f(i: Fin(2)) -> Nat {{ match i {{ {arms} }} }}"));
        assert!(msg.contains("`FS` binds exactly one field"), "{msg}");
    }
}

// -- 4: the oracle-side pins (design doc §6.1) ------------------------------

/// `xs[i]` emits **exactly** `heather_kernel::term::nth`'s output when the
/// hook declines (no lib is loaded here). This pins the left-hand side of
/// in_language_nth.rs's cross-check, so a drift in either direction becomes
/// visible in one suite or the other.
#[test]
fn indexing_emits_exactly_the_kernel_nth_schema() {
    let e = elab("fn at(n: Nat, xs: [Nat; n], i: Fin(n)) -> Nat { xs[i] }");
    let (_, body) = last_binding(&e);
    // Peel the three λs: `n`, `xs`, `i` at de Bruijn 2, 1, 0.
    let mut inner = &body;
    for _ in 0..3 {
        let Term::Lam { body, .. } = inner else { panic!("expected three λs") };
        inner = body;
    }
    let expected = nth(
        &Level::Zero,
        &Rc::new(Type::Nat),
        &Rc::new(Term::Var(LocalVar(2))),
        Rc::new(Term::Var(LocalVar(1))),
        Rc::new(Term::Var(LocalVar(0))),
    );
    assert!(
        *inner == expected,
        "`xs[i]` must emit the kernel `nth` schema verbatim — it is the oracle \
         the in-language `nth_code` will be cross-checked against"
    );
}

/// The numeral sugar emits **exactly** `wf.rs`'s `fin_index` output (§3.3):
/// the surface numeral and the elaborator's own container indices are the same
/// syntax, so nothing can drift between them.
///
/// `fin_index` is not public, so the expected term is spelled here as the doc
/// states it — `inr^t (inl ⟨⟩)`, with every tail annotated **folded** as
/// `Fin(Succ^j(base))` rather than as its unfolded sum. The folded annotation
/// is the property being pinned: it is what a goal reads back as.
#[test]
fn a_numeral_at_a_fin_emits_the_folded_iterated_index() {
    let e = elab("fn at(n: Nat, xs: [Nat; Succ(Succ(n))]) -> Fin(Succ(Succ(n))) { 1 }");
    let (_, body) = last_binding(&e);
    let mut inner = &body;
    for _ in 0..2 {
        let Term::Lam { body, .. } = inner else { panic!("expected two λs") };
        inner = body;
    }
    // base = `n` under two λs.
    let base = Term::Var(LocalVar(1));
    let fin = |k: usize| {
        let mut len = base.clone();
        for _ in 0..k {
            len = Term::Succ(Rc::new(len));
        }
        Rc::new(Type::Fin { len: Rc::new(len) })
    };
    let unit = || Rc::new(Type::Unit { level: Level::Zero });
    let expected = Term::Inr {
        lhs_level: Level::Zero,
        rhs_level: Level::Zero,
        lhs: unit(),
        rhs: fin(1),
        val: Rc::new(Term::Inl {
            lhs_level: Level::Zero,
            rhs_level: Level::Zero,
            lhs: unit(),
            rhs: fin(0),
            val: Rc::new(Term::Triv { level: Level::Zero }),
        }),
    };
    assert!(
        *inner == expected,
        "a numeral at a `Fin` must emit `fin_index`'s term, folded annotations \
         and all"
    );
}

// -- 5: the slots (design doc §7 items 14-15) -------------------------------

// With no template registered — these fixtures never load the lib — `xs[i]`
// and `elab_container_ih` take their Rust/kernel paths: the *silent decline*
// (docs/meta-def-registration-design.md §2.4's use-row). The pins above are
// half of that claim — they assert the kernel schema verbatim, which is only
// true while the hook declines — and `container_proofs.rs`,
// `container_recursion.rs` and `container_fields.rs` staying green is the
// other half, since `elab_container_ih`'s output must be byte-identical.
//
// The hook-taken side of both slots lives in in_language_tabulate.rs and
// in_language_nth.rs since the port round; the once-unreachable "a `for
// vec.nth` template whose payload disagrees" rejection is now tested in
// template_registration.rs.

/// The `Fin` former is reachable from the slot machinery's side too: the
/// vocabulary already declares `ITy::Fin`, and this is the fixture that would
/// notice if `Fin` and the slot spec's `Fin` disagreed about what they build.
#[test]
fn the_container_ih_still_takes_the_rust_path() {
    // A `Rose`-shaped recursion whose arm recurses over the container field —
    // `elab_container_ih`'s phase 2, now routed through `Slot::VecTabulate`
    // with `vec::tabulate` as its fallback. No template claims the slot, so
    // this must elaborate exactly as it did before the call site existed.
    ok("fn add(a: Nat, b: Nat) -> Nat { match b { Zero => a, Succ(k) => Succ(add(a, k)) } }
        inductive Rose { Node(label: Nat, len: Nat, kids: [Rose; len]) }
        fn size(r: Rose) -> Nat {
            match r {
                Node(l, n, kids) =>
                    Succ(kids.map(size).fold(0, λ (a: Nat) (b: Nat) => add(a, b))),
            }
        }");
}

// -- Vector literal lengths are packed ---------------------------------------

/// Every level of a vector literal is annotated with its tail's `[T; k]`, and
/// `k` is spelled as the kernel spells a closed numeral — `NatLit`, `Zero`
/// at the end — not as a `Succ` chain. In unary the annotations alone made
/// the term quadratic in the literal (`issues/elf-mutation-test-shape.md`).
#[test]
fn vector_literal_tail_lengths_are_packed_numerals() {
    let e = elab("fn three() -> [Nat; 3] { [1, 2, 3] }");
    let (_, body) = last_binding(&e);
    let mut at = &body;
    for expected in [Term::NatLit(2u64.into()), Term::NatLit(1u64.into()), Term::Zero] {
        let Term::Pair { snd_ty, snd, .. } = at else { panic!("expected a pair, found {at:?}") };
        let Type::Vec { len, .. } = &**snd_ty else { panic!("expected a Vec tail type, found {snd_ty:?}") };
        assert_eq!(**len, expected, "tail length spelled {len:?}");
        at = snd;
    }
    assert!(matches!(at, Term::Triv { .. }), "expected the empty tail, found {at:?}");
}
