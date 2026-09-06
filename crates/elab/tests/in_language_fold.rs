//! The second in-language derived artifact (issues/quotation-stage-artifacts.md):
//! `lib/vec_code.hthr`'s `fold_code` kernel-checks at `Layer::Meta`, the
//! evaluation hook routes `.fold` through it, and the emitted terms are
//! convertible with the Rust `vec::fold` oracle's — adequacy, not just typing.
//!
//! Same axes as in_language_map.rs (docs/testing-generated-terms.md), plus the
//! one `fold` has and `map` does not: an open **result** type. `fold`'s two
//! type parameters are genuinely independent, so a wrong shift on `B` hides
//! from every fixture whose result is the closed `Nat` — the Rust suite's
//! `map_and_fold_at_an_open_element_type` (vec.rs) makes the same point about
//! the schema this template replaces.
//!
//! One control here has no counterpart in the map suite, and the reason is a
//! finding: `map_code` is rigid at the generic type, `fold_code` is not (an
//! unindexed result type rules out nothing), so the mutated-arm control the
//! map round found unwritable is written below.

use heather_elab::Elaborator;
use heather_kernel::conv::conv_term;
#[cfg(feature = "value-metrics")]
use heather_kernel::conv::conv_term_profiled;
use heather_kernel::layer::Layer;
use heather_kernel::level::Level;
use heather_kernel::term::{GlobalBinding, GlobalCtx, LocalCtx, Term, Type};
#[cfg(feature = "value-metrics")]
use heather_kernel::value::ValueMetrics;

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

/// The fixtures, one `.fold` per axis. Declared identically with and without
/// the lib in scope; the theorems make the literal instances *compute*, so
/// they are adequacy checks and not just typing.
fn fixtures() -> String {
    format!(
        "{ADD}
fn total(xs: [Nat; 3]) -> Nat {{ xs.fold(0, λ (a: Nat) (b: Nat) => add(a, b)) }}
theorem total_computes(): total([1, 2, 3]) = 6 {{ refl }}

// A length that never reduces: the emitted elim stays neutral and must type.
fn total_n(n: Nat, xs: [Nat; n]) -> Nat {{ xs.fold(0, λ (a: Nat) (b: Nat) => add(a, b)) }}
theorem total_n_computes(): total_n(2, [4, 5]) = 9 {{ refl }}

// An open *element* type: the elements are vectors of ambient length, the
// result is still `Nat` (this is the axis a closed-type fixture cannot see).
fn count(m: Nat, xs: [[Nat; Succ(m)]; 2]) -> Nat {{
    xs.fold(0, λ (v: [Nat; Succ(m)]) (b: Nat) => Succ(b))
}}

// An open *result* type — `fold`'s own axis, both parameters open at once:
// the fold's `B` mentions an ambient variable, so a wrong shift on the
// result type (which no `Nat`-result fixture can reach) shows up here.
fn keep_init(m: Nat, z: [Nat; Succ(m)], xs: [[Nat; Succ(m)]; 2]) -> [Nat; Succ(m)] {{
    xs.fold(z, λ (v: [Nat; Succ(m)]) (r: [Nat; Succ(m)]) => r)
}}

// Checking positions: an annotated `let` (at the open result type), and an
// argument position (at `Nat`, where the theorem below makes it compute).
fn checked(m: Nat, z: [Nat; Succ(m)], xs: [[Nat; Succ(m)]; 2]) -> [Nat; Succ(m)] {{
    let r: [Nat; Succ(m)] = xs.fold(z, λ (v: [Nat; Succ(m)]) (s: [Nat; Succ(m)]) => s);
    r
}}

fn checked_nat(xs: [Nat; 2]) -> Nat {{ add(xs.fold(0, λ (a: Nat) (b: Nat) => add(a, b)), 0) }}
theorem checked_computes(): checked_nat([4, 5]) = 9 {{ refl }}
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

/// The Ψ a binding's body is scoped over: every binding *before* it. A body
/// mentions only older globals, and with de Bruijn global indices the newest
/// binding is index 0 — so reading the last binding's body against the full
/// Ψ shifts every global by one (its own `add` resolves to itself). The
/// stored-annotation application rule never consulted Ψ for a head's type and
/// let that pass; the typed rule reads the head's declared type and does not.
fn owning_psi(e: &Elaborator) -> GlobalCtx {
    let mut bindings = e.psi().bindings.to_vec();
    bindings.pop().expect("a binding");
    GlobalCtx::new(bindings)
}

#[test]
fn the_fixtures_elaborate_and_compute_through_the_hook() {
    elab_with_lib(&fixtures());
}

#[test]
fn the_fixtures_still_elaborate_without_the_lib() {
    // A file that never declares `fold_code` takes the Rust path as before.
    elab(&fixtures());
}

/// The cross-check proper: for each fixture, the hook-emitted declaration body
/// and the Rust-emitted one are convertible at the declaration's own statement,
/// at `Layer::Prog`. This is what makes the in-language template *the same
/// fold* — the right one, not the left one — rather than merely a well-typed
/// function; at the neutral length the theorems cannot decide it, conversion
/// can.
#[test]
fn hook_output_is_convertible_with_the_rust_oracle() {
    for fixture in [
        "fn probe(xs: [Nat; 3]) -> Nat { xs.fold(0, λ (a: Nat) (b: Nat) => add(a, b)) }",
        "fn probe(n: Nat, xs: [Nat; n]) -> Nat { xs.fold(0, λ (a: Nat) (b: Nat) => add(a, b)) }",
        "fn probe(m: Nat, xs: [[Nat; Succ(m)]; 2]) -> Nat {
             xs.fold(0, λ (v: [Nat; Succ(m)]) (b: Nat) => Succ(b))
         }",
        "fn probe(m: Nat, z: [Nat; Succ(m)], xs: [[Nat; Succ(m)]; 2]) -> [Nat; Succ(m)] {
             xs.fold(z, λ (v: [Nat; Succ(m)]) (r: [Nat; Succ(m)]) => r)
         }",
    ] {
        let src = format!("{ADD}{fixture}");
        let hooked = elab_with_lib(&src);
        let rust = elab(&src);
        let (ht, hty, hl) = last_body(&hooked);
        let (rt, _, _) = last_body(&rust);
        // The cross-check is only sharp if the hook actually fired: a decline
        // would make the two bodies *identical* and conversion vacuous. The
        // hook's output is a Π-spine application of the template's payload,
        // never the Rust schema's bare `elim_Nat` application, so inequality
        // is the cheap witness — and it covers every axis, including the open
        // result type that the swapped-template control below does not reach.
        assert!(
            ht != rt,
            "the hook declined on:\n{fixture}\nso the conversion below would \
             compare the Rust term with itself"
        );
        let empty = LocalCtx::nil();
        #[cfg(feature = "value-metrics")]
        if std::env::var_os("HEATHER_VALUE_METRICS").is_some() {
            let metrics = ValueMetrics::default();
            conv_term_profiled(
                &owning_psi(&hooked), &empty, Layer::Prog, &ht, &rt, &hty, &hl, 1_000_000, &metrics,
            )
            .unwrap_or_else(|e| panic!("hook and Rust `fold` disagree on:\n{fixture}\n{e:?}"));
            eprintln!("fold oracle metrics: {:?}", metrics.snapshot());
            continue;
        }
        conv_term(&owning_psi(&hooked), &empty, Layer::Prog, &ht, &rt, &hty, &hl, 1_000_000)
            .unwrap_or_else(|e| panic!("hook and Rust `fold` disagree on:\n{fixture}\n{e:?}"));
    }
}

// -- negative controls ------------------------------------------------------

// Two of this suite's original controls **moved** to
// crates/elab/tests/template_registration.rs when the registration seam landed
// (docs/meta-def-registration-design.md §2.2): the short template no longer
// registers at all, and the "swapped" one turned out to be a legal
// *permutation* of the same signature — accepted, and producing the same term,
// which is what the seam promised. The control that stays is the one about the
// template's **body**, which registration deliberately does not police.

/// The control the map round could not write. `map_code` is *rigid* at the
/// generic type — parametricity plus the length index force it to be map, so
/// "a mutated template that still checks but is the wrong function" does not
/// exist there (design doc §7 item 5). `fold_code`'s result type carries no
/// index, so it does exist: dropping the head from the step arm leaves the
/// **constant fold**, which checks as a `meta fn` at exactly the same
/// signature — and, since registration checks the *type* and not the body,
/// registers for `vec.fold` exactly as the real one does (design doc §2.2:
/// this is a typing gate, never a soundness one). Adequacy at the generic type
/// is therefore *not* carried by the types here — the conversion cross-check
/// is doing real work, and this test is what proves it can fail.
#[test]
fn a_mutated_arm_checks_but_fails_the_cross_check() {
    let constant_fold = r#"
meta fn fold_code(g: Ctx) for vec.fold -> Code(g |-
    (A: Type<0>) -> (B: Type<0>) -> (z: B) -> (f: A -> B -> B) -> (k: Nat) -> (v: [A; k]) -> B
) {
    code {
        fun (A: Type<0>) => fun (B: Type<0>) => fun (z: B) =>
            fun (f: A -> B -> B) => fun (k: Nat) =>
                match k as λ w => [A; w] -> B {
                    Zero => fun (v: [A; 0]) => z,
                    Succ(zk, ih) => fun (v: [A; Succ(zk)]) => ih(tail(v)),
                }
    }
}
"#;
    let mut e = Elaborator::with_prelude().expect("prelude");
    e.elab_source(constant_fold).unwrap_or_else(|err| {
        panic!("the mutated template itself checks: {}", err.render(constant_fold))
    });

    // At a literal instance it computes to the wrong answer, so the theorem
    // that pins the sum fails — adequacy caught by computation.
    let computing = format!(
        "{ADD}
         fn total(xs: [Nat; 3]) -> Nat {{ xs.fold(0, λ (a: Nat) (b: Nat) => add(a, b)) }}
         theorem t(): total([1, 2, 3]) = 6 {{ refl }}"
    );
    assert!(
        e.elab_source(&computing).is_err(),
        "the constant fold should not sum a literal vector — if this checked, the \
         hook is not routing `.fold` through `fold_code`"
    );

    // At a neutral length nothing computes and only conversion can tell:
    // the emitted term must *fail* to convert with the Rust oracle's.
    let neutral =
        format!("{ADD}fn probe(n: Nat, xs: [Nat; n]) -> Nat {{ xs.fold(0, λ (a: Nat) (b: Nat) => add(a, b)) }}");
    let mut wrong = Elaborator::with_prelude().expect("prelude");
    wrong.elab_source(constant_fold).expect("the mutated template checks");
    wrong
        .elab_source(&neutral)
        .unwrap_or_else(|err| panic!("the neutral instance still types: {}", err.render(&neutral)));
    let rust = elab(&neutral);
    let (wt, wty, wl) = last_body(&wrong);
    let (rt, _, _) = last_body(&rust);
    let empty = LocalCtx::nil();
    assert!(
        conv_term(&owning_psi(&wrong), &empty, Layer::Prog, &wt, &rt, &wty, &wl, 1_000_000).is_err(),
        "the constant fold is not the right fold: the cross-check must reject it"
    );
}

/// `map_code` and `fold_code` coexist: the lib declares both, and a file that
/// uses both routes each to its own template — two slots, two claims, no
/// interference (docs/meta-def-registration-design.md §8 item 5's positive
/// half). This is the fixture that would notice a hook dispatching on the
/// wrong slot.
#[test]
fn map_and_fold_route_independently() {
    let src = format!(
        "{ADD}
         fn total_bumped(xs: [Nat; 3]) -> Nat {{
             xs.map(λ (n: Nat) => Succ(n)).fold(0, λ (a: Nat) (b: Nat) => add(a, b))
         }}
         theorem tb(): total_bumped([1, 2, 3]) = 9 {{ refl }}"
    );
    elab_with_lib(&src);
}
