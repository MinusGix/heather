//! The first in-language derived artifact, end to end
//! (docs/in-language-map-design.md §7): `lib/vec_code.hthr`'s `map_code`
//! kernel-checks at `Layer::Meta`, the evaluation hook routes `.map` through
//! it, and the emitted terms are convertible with the Rust `vec::map`
//! oracle's — adequacy, not just typing. Fixtures follow
//! docs/testing-generated-terms.md: literal *and* neutral length, an open
//! element type, a checking position, and negative controls that prove both
//! the routing and the loud-failure discipline.

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
        let empty = LocalCtx { base: CtxBase::Nil, entries: vec![] };
        conv_term(hooked.psi(), &empty, Layer::Prog, &ht, &rt, &hty, &hl, 1_000_000)
            .unwrap_or_else(|e| {
                panic!("hook and Rust `map` disagree on:\n{fixture}\n{e:?}")
            });
    }
}

// -- negative controls ------------------------------------------------------

/// Routing proof: a template with its element binders swapped still checks
/// as a `meta fn` (it is a well-typed template — of the wrong function type
/// for the hook's argument order), so if `.map` really evaluates it, an
/// `A ≠ B` instance must fail the kernel gate. If the Rust path were still
/// serving these files, this would elaborate.
#[test]
fn a_swapped_template_breaks_an_a_neq_b_instance() {
    let swapped = r#"
meta fn map_code(g: Ctx) -> Code(g |-
    (B: Type<0>) -> (A: Type<0>) -> (A -> B) -> (k: Nat) -> [A; k] -> [B; k]
) {
    code {
        fun (B: Type<0>) => fun (A: Type<0>) => fun (f: A -> B) => fun (k: Nat) =>
            match k as λ z => [A; z] -> [B; z] {
                Zero => fun (v: [A; 0]) => [],
                Succ(zk, ih) => fun (v: [A; Succ(zk)]) =>
                    cons(f(head(v)), ih(tail(v))),
            }
    }
}
"#;
    let a_neq_b = "fn lens(m: Nat, xs: [[Nat; Succ(m)]; 2]) -> [Nat; 2] { \
                       xs.map(λ (v: [Nat; Succ(m)]) => head(v)) \
                   }";
    let mut e = Elaborator::with_prelude().expect("prelude");
    e.elab_source(swapped)
        .unwrap_or_else(|err| panic!("the swapped template itself checks: {}", err.render(swapped)));
    assert!(
        e.elab_source(a_neq_b).is_err(),
        "the swapped template should break an A ≠ B instance — if this elaborated, \
         the hook is not routing `.map` through `map_code`"
    );
    // The same swapped template at A = B is symmetric and must pass — the
    // control is sharp: it is the *routing* that failed above, not the file.
    let a_eq_b = "fn same(xs: [Nat; 2]) -> [Nat; 2] { xs.map(λ (n: Nat) => Succ(n)) }
                  theorem s(): same([1, 2]) = [2, 3] { refl }";
    e.elab_source(a_eq_b)
        .unwrap_or_else(|err| panic!("A = B is symmetric under the swap: {}", err.render(a_eq_b)));
}

/// Loud-failure discipline (§6): a registered template whose Π spine is too
/// short errors at the use site — it never silently falls back to Rust and
/// never emits a half-applied term.
#[test]
fn a_short_template_fails_loudly_not_silently() {
    let short = r#"
meta fn map_code(g: Ctx) -> Code(g |-
    (A: Type<0>) -> (k: Nat) -> [A; k] -> [A; k]
) {
    code {
        fun (A: Type<0>) => fun (k: Nat) => fun (v: [A; k]) => v
    }
}
"#;
    let mut e = Elaborator::with_prelude().expect("prelude");
    e.elab_source(short)
        .unwrap_or_else(|err| panic!("the short template itself checks: {}", err.render(short)));
    let use_site = "fn bump(xs: [Nat; 2]) -> [Nat; 2] { xs.map(λ (n: Nat) => Succ(n)) }";
    let err = e.elab_source(use_site).expect_err("a short template must be a loud error");
    let msg = format!("{err:?}");
    assert!(msg.contains("parameters"), "wrong failure: {msg}");
}
