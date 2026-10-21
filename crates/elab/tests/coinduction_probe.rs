//! Coinductive trees without a kernel change: the library probe of
//! `docs/kernel-coinduction-design.md` §3 (`issues/kernel-coinductive-types.md`).
//! The source is `tests/fixtures/coinduction_probe.hthr`; it is a probe, not a
//! library module, so nothing imports it outside this file.
//!
//!  1. both encodings check: `Nu` (the sum of all coalgebras) and `Lim` (the
//!     limit of the depth cuts), with the coherence of unrolling and the
//!     agreement of the two at every depth, both up to `ITree::Same`;
//!  2. what is definitional: `Nu`'s β rule at an open carrier, step and seed,
//!     and the limit's coherence at a literal depth;
//!  3. what is not (negative controls): the limit's coherence at a neutral
//!     depth, two `Nu` unfoldings of the same tree, and `Nu` through the
//!     library's generic operations, one level up from their parameters.

use std::sync::OnceLock;

use heather_elab::{Elaborator, SemanticImage};

use crate::support;

const MODULES: &[(&str, &str)] = &[
    ("logic", include_str!("../../../lib/std/logic.hthr")),
    ("bool", include_str!("../../../lib/std/bool.hthr")),
    ("nat", include_str!("../../../lib/std/nat.hthr")),
    ("option", include_str!("../../../lib/std/option.hthr")),
    ("pair", include_str!("../../../lib/std/pair.hthr")),
    ("list", include_str!("../../../lib/std/list.hthr")),
    ("itree", include_str!("../../../lib/std/itree.hthr")),
];

const PROBE: &str = include_str!("fixtures/coinduction_probe.hthr");

static BASE: OnceLock<SemanticImage> = OnceLock::new();

fn base() -> Elaborator {
    BASE.get_or_init(|| {
        let mut e = support::semantic_test_base(MODULES);
        check(&mut e, "coinduction_probe", PROBE);
        e.semantic_image()
    })
    .elaborator()
}

fn check(e: &mut Elaborator, name: &str, src: &str) {
    if let Err(err) = e.elab_module_source(name, src) {
        panic!("{}", err.render(src));
    }
}

/// Refused with `needle` in the message: the kernel's `NotConvertible` for a
/// false equation, its `LevelMismatch` for the level a carrier field costs.
fn refused(name: &str, src: &str, needle: &str) {
    let mut e = base();
    match e.elab_module_source(name, src) {
        Ok(()) => panic!("{name} should be refused"),
        Err(err) => {
            let msg = err.render(src);
            assert!(msg.contains(needle), "{name}: {msg}");
        }
    }
}

const IMPORTS: &str = "import logic; import nat; import itree; import coinduction_probe;\n";

#[test]
fn both_encodings_check() {
    let mut e = base();
    let names = [
        "Head::map", "Nu::unfold", "Nu::repack", "Nu::out", "Nu::out_unfold", "Nu::spin", "Nu::spin_out",
        "Nu::approx", "ITree::cut", "ITree::unroll", "ITree::unroll_head", "ITree::unroll_succ",
        "ITree::unroll_head_coh", "ITree::unroll_coh", "Lim::unfold", "Lim::spin", "Lim::spin_two",
        "Nu::approx_head", "Nu::approx_succ", "Nu::approx_unfold_head", "Nu::approx_unfold",
    ];
    let mut src = format!("{IMPORTS} fn kit() → Nat {{\n");
    for (i, name) in names.iter().enumerate() {
        src.push_str(&format!("    let n{i} = {name};\n"));
    }
    src.push_str("    0\n}\n");
    check(&mut e, "coinduction_probe_kit", &src);
}

// Axis 1, literal: at a closed depth the limit's coherence is an equation by
// `refl`, at an open command and open events, through a `Vis`.
#[test]
fn coherence_is_refl_at_a_literal_depth() {
    let mut e = base();
    check(
        &mut e,
        "coinduction_coh_literal",
        &format!(
            "{IMPORTS}
            fn echo_step(E: Events, c: E.Cmd) → Head<False, E.Cmd>(E) {{ HVis(c, λ a => c) }}
            theorem coh_two(E: Events, c: E.Cmd):
                ITree::cut<False>(E, 2, ITree::unroll(E, λ d => echo_step(E, d), 3, c))
                    = ITree::unroll(E, λ d => echo_step(E, d), 2, c) {{ refl }}"
        ),
    );
}

// Axis 1, neutral, and axis 4: at a successor of a variable the first layer
// computes and the rest is stuck under the `Vis`, so coherence is not `refl`;
// the library states it up to `Same`.
#[test]
fn coherence_is_not_refl_at_a_neutral_depth() {
    refused(
        "coinduction_coh_neutral",
        &format!(
            "{IMPORTS}
            fn echo_step(E: Events, c: E.Cmd) → Head<False, E.Cmd>(E) {{ HVis(c, λ a => c) }}
            theorem coh_open(E: Events, n: Nat, c: E.Cmd):
                ITree::cut<False>(E, Succ(n), ITree::unroll(E, λ d => echo_step(E, d), Succ(Succ(n)), c))
                    = ITree::unroll(E, λ d => echo_step(E, d), Succ(n), c) {{ refl }}"
        ),
        "NotConvertible",
    );
}

// The β rule in a checking position: `out` of the spinning tree is a `Tau`
// whose child is the spinning tree itself, at open events and result type.
#[test]
fn nu_beta_in_a_checking_position() {
    let mut e = base();
    check(
        &mut e,
        "coinduction_nu_beta",
        &format!(
            "{IMPORTS}
            fn child<R>(E: Events, h: NuHead<R>(E)) → Nu<R>(E) {{
                match h {{ NRet(r) => Nu::spin(E), NTau(x) => x, NVis(c, k) => Nu::spin(E) }}
            }}
            theorem again<R>(E: Events): child(E, Nu::out(E, Nu::spin<R>(E))) = Nu::spin<R>(E) {{ refl }}"
        ),
    );
}

// Axis 4: two unfoldings of the same tree with different carriers are
// different values. Equality at `Nu` is intensional, as a kernel `M`'s would
// be; the tree they share is a bisimilarity, not an equation.
#[test]
fn nu_equality_is_intensional() {
    refused(
        "coinduction_nu_intensional",
        &format!(
            "{IMPORTS}
            fn count_step<R>(E: Events, n: Nat) → Head<R, Nat>(E) {{ HTau(Succ(n)) }}
            theorem bad<R>(E: Events): Nu::spin<R>(E) = Nu::unfold(E, Nat, λ n => count_step<R>(E, n), 0) {{ refl }}"
        ),
        "NotConvertible",
    );
}

// The level a carrier field costs: `Nu` is one level up from its events, so
// the library's operations, generic over level-zero types, refuse it.
#[test]
fn nu_is_a_level_up_from_the_library() {
    refused(
        "coinduction_nu_level",
        &format!(
            "{IMPORTS}
            fn wrap<R>(E: Events, m: Nu<R>(E)) → ITree<Nu<R>(E)>(E) {{
                ITree::bind<Nu<R>(E), Nu<R>(E)>(E, Ret(m), λ x => Ret(x))
            }}"
        ),
        "LevelMismatch",
    );
}
