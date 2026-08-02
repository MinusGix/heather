//! The fourth in-language derived artifact (issues/quotation-stage-artifacts.md):
//! `lib/vec_code.hthr`'s `nth_code` kernel-checks at `Layer::Meta`, the
//! evaluation hook routes `xs[i]` through it, and the emitted terms are
//! convertible with the oracle's — adequacy, not just typing.
//!
//! The oracle here is not `crates/elab/src/vec.rs` but the **kernel**'s `nth`
//! schema (`heather_kernel::term::nth`), which is what `elab_vec_nth` emits
//! when no template claims `vec.nth`
//! (docs/surface-fin-indexing-design.md §5.2). That schema is pinned verbatim
//! by `surface_fin.rs::indexing_emits_exactly_the_kernel_nth_schema`, so the
//! left-hand side of every conversion below is nailed down independently and a
//! drift in either direction becomes visible in one suite or the other.
//!
//! Same axes as in_language_fold.rs (docs/testing-generated-terms.md), read for
//! an indexed projection: a literal length *and* a neutral one, an **open**
//! element type, a checking position, a routing control, a mutated-arm control,
//! and the vacuity guard (`ht != rt` before `conv`) that suite introduced.
//! `nth` has one axis of its own — the *index* can be literal or neutral
//! independently of the length — and it is varied below, because a template
//! that shifted the index wrongly would still compute correctly at `FZ`.

use heather_elab::Elaborator;
use heather_kernel::conv::conv_term;
use heather_kernel::layer::Layer;
use heather_kernel::level::Level;
use heather_kernel::term::{CtxBase, GlobalBinding, LocalCtx, Term, Type};

const LIB: &str = include_str!("../../../lib/vec_code.hthr");

fn elab(src: &str) -> Elaborator {
    let mut e = Elaborator::with_prelude().expect("prelude");
    e.elab_source(src).unwrap_or_else(|err| panic!("{}", err.render(src)));
    e
}

fn elab_with_lib(src: &str) -> Elaborator {
    let mut e = Elaborator::with_prelude().expect("prelude");
    e.elab_source(LIB).unwrap_or_else(|err| panic!("{}", err.render(LIB)));
    e.elab_source(src).unwrap_or_else(|err| panic!("{}", err.render(src)));
    e
}

const ADD: &str = "fn add(a: Nat, b: Nat) -> Nat { match b { Zero => a, Succ(k) => Succ(add(a, k)) } }
";

/// The fixtures, one `xs[i]` per axis. Declared identically with and without
/// the lib in scope; the theorems make the literal instances *compute*, so they
/// are adequacy checks and not just typing — and at a non-zero index they are
/// what an unshifted or doubly-shifted `FS` would fail.
fn fixtures() -> String {
    format!(
        "{ADD}
fn second(xs: [Nat; 3]) -> Nat {{ xs[1] }}
theorem second_computes(): second([1, 2, 3]) = 2 {{ refl }}

// The zero index, which a wrong `FS` shift would still get right — kept so the
// pair above and below brackets the shift rather than testing one side of it.
fn first(xs: [Nat; 3]) -> Nat {{ xs[0] }}
theorem first_computes(): first([1, 2, 3]) = 1 {{ refl }}

// A length *and* an index that never reduce: the emitted elim stays neutral and
// must type. This is the case no theorem can decide, and the one the conversion
// cross-check below exists for.
fn at(n: Nat, xs: [Nat; n], i: Fin(n)) -> Nat {{ xs[i] }}
theorem at_computes(): at(3, [1, 2, 3], 2) = 3 {{ refl }}

// An open *element* type: the elements are vectors of ambient length, so a
// wrong shift on the projected type — invisible whenever the element type is
// the closed `Nat` — shows up here.
fn row(m: Nat, xs: [[Nat; Succ(m)]; 2]) -> [Nat; Succ(m)] {{ xs[1] }}

// Checking positions: an annotated `let` at the open element type, and an
// argument position at `Nat`, where the theorem makes it compute.
fn checked(m: Nat, xs: [[Nat; Succ(m)]; 2]) -> [Nat; Succ(m)] {{
    let r: [Nat; Succ(m)] = xs[1];
    r
}}

fn checked_nat(xs: [Nat; 2]) -> Nat {{ add(xs[1], 0) }}
theorem checked_computes(): checked_nat([4, 5]) = 5 {{ refl }}
"
    )
}

/// The body of the *last* committed binding — the fixture each cross-check
/// declares last, so no name table is needed.
fn last_body(e: &Elaborator) -> (Term, Type, Level) {
    match e.psi().bindings.last().expect("a binding") {
        GlobalBinding::Tm { ty, level, body: Some(b), .. } => {
            ((**b).clone(), (**ty).clone(), level.clone())
        }
        other => panic!("expected a bodied Tm binding, found {other:?}"),
    }
}

#[test]
fn the_fixtures_elaborate_and_compute_through_the_hook() {
    elab_with_lib(&fixtures());
}

#[test]
fn the_fixtures_still_elaborate_without_the_lib() {
    // A file that never declares `nth_code` takes the kernel-schema path as
    // before — the silent decline `surface_fin.rs` tested with no template in
    // existence, now tested with one that simply is not in scope.
    elab(&fixtures());
}

/// The cross-check proper: for each fixture, the hook-emitted declaration body
/// and the kernel-schema one are convertible at the declaration's own
/// statement, at `Layer::Prog`. This is what makes the in-language template
/// *the same projection* rather than merely a well-typed function of the right
/// signature; at a neutral length and index the theorems cannot decide it, and
/// conversion can.
#[test]
fn hook_output_is_convertible_with_the_kernel_oracle() {
    for fixture in [
        "fn probe(xs: [Nat; 3]) -> Nat { xs[1] }",
        "fn probe(n: Nat, xs: [Nat; n], i: Fin(n)) -> Nat { xs[i] }",
        "fn probe(n: Nat, xs: [Nat; Succ(n)]) -> Nat { xs[0] }",
        "fn probe(m: Nat, xs: [[Nat; Succ(m)]; 2]) -> [Nat; Succ(m)] { xs[1] }",
    ] {
        let src = format!("{ADD}{fixture}");
        let hooked = elab_with_lib(&src);
        let rust = elab(&src);
        let (ht, hty, hl) = last_body(&hooked);
        let (rt, _, _) = last_body(&rust);
        // The vacuity guard (in_language_fold.rs:132): the cross-check is only
        // sharp if the hook actually fired — a decline would make the two
        // bodies *identical* and conversion trivial. These fixtures use no
        // other routed form, so inequality witnesses `vec.nth` specifically.
        assert!(
            ht != rt,
            "the hook declined on:\n{fixture}\nso the conversion below would \
             compare the kernel term with itself"
        );
        let empty = LocalCtx { base: CtxBase::Nil, entries: vec![] };
        conv_term(hooked.psi(), &empty, Layer::Prog, &ht, &rt, &hty, &hl, 1_000_000)
            .unwrap_or_else(|e| panic!("hook and kernel `nth` disagree on:\n{fixture}\n{e:?}"));
    }
}

// -- negative controls ------------------------------------------------------

/// The rigidity control, and the round's finding.
///
/// docs/surface-fin-indexing-design.md §9 predicted that `nth_code` would have
/// **no writable mutant**: not rigid in `map`'s sense (the result is the bare
/// `A`, which no index pins), but with a step arm forced anyway because the
/// index and the recursion leave nothing else to pick. That is wrong, and the
/// `match` on the index is what makes it wrong: inside the `FS` arm, `head(v)`
/// is in scope at type `A` right beside `ih(tail(v), j)`. Answering `head(v)`
/// in *both* arms is the constant-first-element projection — well typed at the
/// declared signature, and (registration checking the type and never the body,
/// docs/meta-def-registration-design.md §2.2) registered for `vec.nth` exactly
/// as the real template is.
///
/// So adequacy is not carried by the type here, and this test is the proof
/// that the conversion cross-check above can fail.
#[test]
fn a_mutated_arm_checks_but_fails_the_cross_check() {
    let constant_nth = r#"
meta fn nth_code(g: Ctx) for vec.nth -> Code(g |-
    (A: Type<0>) -> (k: Nat) -> (v: [A; k]) -> (i: Fin(k)) -> A
) {
    code {
        fun (A: Type<0>) => fun (k: Nat) =>
            match k as λ z => [A; z] -> Fin(z) -> A {
                Zero => fun (v: [A; 0]) => fun (i: Fin(0)) => match i { },
                Succ(zk, ih) => fun (v: [A; Succ(zk)]) => fun (i: Fin(Succ(zk))) =>
                    match i {
                        FZ => head(v),
                        FS(j) => head(v),
                    },
            }
    }
}
"#;
    let mut e = Elaborator::with_prelude().expect("prelude");
    e.elab_source(constant_nth).unwrap_or_else(|err| {
        panic!("the mutated template itself checks: {}", err.render(constant_nth))
    });

    // At a literal index past zero it computes to the wrong component, so the
    // theorem that pins it fails — adequacy caught by computation. (At `xs[0]`
    // it would agree, which is why the fixtures above index past zero.)
    let computing = "fn second(xs: [Nat; 3]) -> Nat { xs[1] }
         theorem t(): second([1, 2, 3]) = 2 { refl }";
    assert!(
        e.elab_source(computing).is_err(),
        "the constant projection should not return the second component — if this \
         checked, the hook is not routing `xs[i]` through `nth_code`"
    );

    // At a neutral length and index nothing computes and only conversion can
    // tell: the emitted term must *fail* to convert with the kernel oracle's.
    let neutral = "fn probe(n: Nat, xs: [Nat; n], i: Fin(n)) -> Nat { xs[i] }";
    let mut wrong = Elaborator::with_prelude().expect("prelude");
    wrong.elab_source(constant_nth).expect("the mutated template checks");
    wrong
        .elab_source(neutral)
        .unwrap_or_else(|err| panic!("the neutral instance still types: {}", err.render(neutral)));
    let rust = elab(neutral);
    let (wt, wty, wl) = last_body(&wrong);
    let (rt, _, _) = last_body(&rust);
    let empty = LocalCtx { base: CtxBase::Nil, entries: vec![] };
    assert!(
        conv_term(wrong.psi(), &empty, Layer::Prog, &wt, &rt, &wty, &wl, 1_000_000).is_err(),
        "the constant projection is not `nth`: the cross-check must reject it"
    );
}

/// `nth_code` coexists with the templates that were already there: a file that
/// indexes into the result of a `.map` routes each construct to its own slot
/// (docs/meta-def-registration-design.md §8 item 5's positive half). This is
/// the fixture that would notice a hook dispatching on the wrong slot — and it
/// nests them, so a payload applied in the wrong argument order shows up as a
/// type error rather than as a silent wrong answer.
#[test]
fn nth_map_and_fold_route_independently() {
    let src = format!(
        "{ADD}
         fn bumped_second(xs: [Nat; 3]) -> Nat {{ xs.map(λ (n: Nat) => Succ(n))[1] }}
         theorem bs(): bumped_second([1, 2, 3]) = 3 {{ refl }}

         fn total_of_firsts(xs: [[Nat; 2]; 2]) -> Nat {{
             xs.map(λ (r: [Nat; 2]) => r[0]).fold(0, λ (a: Nat) (b: Nat) => add(a, b))
         }}
         theorem tf(): total_of_firsts([[1, 2], [3, 4]]) = 4 {{ refl }}"
    );
    elab_with_lib(&src);
}
