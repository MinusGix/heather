//! The first in-language derived artifact, end to end
//! (docs/in-language-map-design.md §7): `lib/lang/vec_code.hthr`'s `map_code`
//! kernel-checks at `Layer::Meta`, the evaluation hook routes `.map` through
//! it, and the emitted terms are convertible with the Rust `vec::map`
//! oracle's — adequacy, not just typing. Fixtures follow
//! docs/testing-generated-terms.md: literal *and* neutral length, an open
//! element type, a checking position. The negative controls moved to
//! crates/elab/tests/template_registration.rs when the registration seam
//! landed (docs/meta-def-registration-design.md) — see the note at the bottom
//! of this file for which, and why they are declaration-time now.

use heather_elab::Elaborator;
use heather_kernel::conv::conv_term;
use heather_kernel::layer::Layer;
use heather_kernel::level::Level;
use heather_kernel::term::{GlobalBinding, GlobalCtx, LocalCtx, Term, Type};

const LIB: &str = include_str!("../../../lib/lang/vec_code.hthr");

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

/// The fixtures, one `.map` per axis. Declared identically with and without
/// the lib in scope; the theorems make the literal instances *compute*, so
/// they are adequacy checks, not just typing.
const FIXTURES: &str = r#"
fn bump(xs: [Nat; 2]) -> [Nat; 2] { xs.map(λ (n: Nat) => Succ(n)) }
theorem bump_computes(): bump([1, 2]) = [2, 3] { refl }

// A length that never reduces: the emitted elim stays neutral and must type.
fn bump_n(n: Nat, xs: [Nat; n]) -> [Nat; n] { xs.map(λ (m: Nat) => Succ(m)) }

// An open element type — the axis closed-type fixtures cannot see
// (docs/testing-generated-terms.md): elements are vectors of ambient length.
fn firsts(m: Nat, xs: [[Nat; Succ(m)]; 2]) -> [Nat; 2] {
    xs.map(λ (v: [Nat; Succ(m)]) => head(v))
}

// A checking position: the map sits under an annotated `let`.
fn checked(xs: [Nat; 2]) -> [Nat; 2] {
    let ys: [Nat; 2] = xs.map(λ (n: Nat) => Succ(n));
    ys
}
theorem checked_computes(): checked([4, 5]) = [5, 6] { refl }
"#;

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
    elab_with_lib(FIXTURES);
}

#[test]
fn the_fixtures_still_elaborate_without_the_lib() {
    // Acceptance §7 item 6: a file that never declares `map_code` takes the
    // Rust path exactly as before.
    elab(FIXTURES);
}

/// Acceptance §7 item 4 — the cross-check proper: for each fixture, the
/// hook-emitted declaration body and the Rust-emitted one are convertible at
/// the declaration's own statement, at `Layer::Prog`. This is what makes the
/// in-language template *the same function*, not merely a well-typed one —
/// at the neutral length the theorems cannot decide it, conversion can.
#[test]
fn hook_output_is_convertible_with_the_rust_oracle() {
    for fixture in [
        "fn probe(xs: [Nat; 2]) -> [Nat; 2] { xs.map(λ (n: Nat) => Succ(n)) }",
        "fn probe(n: Nat, xs: [Nat; n]) -> [Nat; n] { xs.map(λ (m: Nat) => Succ(m)) }",
        "fn probe(m: Nat, xs: [[Nat; Succ(m)]; 2]) -> [Nat; 2] {
             xs.map(λ (v: [Nat; Succ(m)]) => head(v))
         }",
    ] {
        let hooked = elab_with_lib(fixture);
        let rust = elab(fixture);
        let (ht, hty, hl) = last_body(&hooked);
        let (rt, _, _) = last_body(&rust);
        // The cross-check is only sharp if the hook actually fired: a decline
        // would make the two bodies *identical* and conversion vacuous. The
        // hook's output is a Π-spine application of the template's payload,
        // never the Rust schema's bare `elim_Nat` application, so inequality
        // is the cheap witness (back-ported from in_language_fold.rs).
        assert!(
            ht != rt,
            "the hook declined on:\n{fixture}\nso the conversion below would \
             compare the Rust term with itself"
        );
        let empty = LocalCtx::nil();
        conv_term(&owning_psi(&hooked), &empty, Layer::Prog, &ht, &rt, &hty, &hl, 1_000_000)
            .unwrap_or_else(|e| {
                panic!("hook and Rust `map` disagree on:\n{fixture}\n{e:?}")
            });
    }
}

// -- negative controls ------------------------------------------------------
//
// Both of this suite's original controls have **moved** to
// crates/elab/tests/template_registration.rs, and the move is the registration
// round's point (docs/meta-def-registration-design.md §2.2): a template that
// cannot serve `vec.map` is now rejected at its own declaration, so neither
// failure can reach a use site any more.
//
// - The short template ("its Π spine is too short") no longer registers: a
//   template's signature is checked against the slot's, so a use site cannot
//   discover a shape problem the declaration already had.
// - The *swapped* template turns out not to be a control at all. With the
//   binder names carrying the order, `(B: Type<0>) -> (A: Type<0>) -> …` is a
//   legal **permutation** of the same signature and is accepted — and produces
//   the same term, which is exactly what the seam promised. It is now the
//   positive control `a_permuted_template_is_the_same_template` there.
//
// What still proves the routing here is the cross-check above: `ht != rt` says
// the hook fired, and conversion says it fired correctly.
