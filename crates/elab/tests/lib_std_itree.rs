//! `lib/std/itree/itree.hthr` — interaction trees over container events, cut at
//! fuel (`issues/interaction-trees-container-model.md` Q2, milestone
//! `it-core`; `docs/itree-core-round.md`).
//!
//!  1. the closure checks: the module and the client showcase, which runs
//!     console programs, a loop at enough and too little fuel, factorial as
//!     recursion events, and a handler, all by `refl`;
//!  2. the law kit is *there*, named one by one;
//!  3. the four axes of `docs/testing-generated-terms.md`: the definitional
//!     laws at a literal and at a neutral fuel, an open element type and
//!     open events (the library is generic in both), a law used in a
//!     checking position, and negative controls — a law through `Vis` is not
//!     an equation, `Same` tells different trees apart, and a cut is a cut.

use std::sync::OnceLock;

use heather_elab::{Elaborator, SemanticImage};

use crate::support;

const MODULES: &[(&str, &str)] = &[
    ("logic", include_str!("../../../lib/std/core/logic.hthr")),
    ("bool", include_str!("../../../lib/std/core/bool.hthr")),
    ("nat", include_str!("../../../lib/std/num/nat.hthr")),
    ("option", include_str!("../../../lib/std/core/option.hthr")),
    ("pair", include_str!("../../../lib/std/core/pair.hthr")),
    ("list", include_str!("../../../lib/std/data/list.hthr")),
    ("itree", include_str!("../../../lib/std/itree/itree.hthr")),
];

static BASE: OnceLock<SemanticImage> = OnceLock::new();

fn base() -> Elaborator {
    BASE.get_or_init(|| support::semantic_test_base(MODULES).semantic_image()).elaborator()
}

fn check(e: &mut Elaborator, name: &str, src: &str) {
    if let Err(err) = e.elab_module_source(name, src) {
        panic!("{}", err.render(src));
    }
}

/// Refused by conversion, not by some earlier inference failure: every
/// negative control here is a false equation.
fn refused(name: &str, src: &str) {
    let mut e = base();
    match e.elab_module_source(name, src) {
        Ok(()) => panic!("{name} should be refused"),
        Err(err) => {
            let msg = err.render(src);
            assert!(msg.contains("NotConvertible"), "{name}: {msg}");
        }
    }
}

const IMPORTS: &str = "import logic; import nat; import itree;\n";

#[test]
fn trees_and_their_client_check() {
    let mut e = base();
    check(
        &mut e,
        "itree_client",
        include_str!("../../../docs/showcase/itree_client.hthr"),
    );
}

const LAWS: &[&str] = &[
    // Events.
    "Events::sum", "Events::none", "EventMap::left", "EventMap::right",
    // Trees and their operations.
    "ITree::trigger", "ITree::bind", "ITree::map", "ITree::translate", "ITree::iter",
    "ITree::interp", "ITree::mrec_vis", "ITree::mrec_layer", "ITree::mrec", "ITree::rec",
    // The equivalence.
    "ITree::Same", "ITree::same_refl", "ITree::same_of_eq", "ITree::same_sym", "ITree::same_trans",
    "ITree::same_bind",
    // The definitional laws.
    "ITree::bind_ret_l", "ITree::bind_tau", "ITree::bind_vis", "ITree::bind_cut", "ITree::bind_trigger",
    "ITree::iter_zero", "ITree::iter_succ", "ITree::interp_ret", "ITree::interp_tau", "ITree::interp_vis",
    "ITree::mrec_zero", "ITree::mrec_call", "ITree::mrec_pass",
    // The laws up to `Same`.
    "ITree::bind_ret_r", "ITree::bind_assoc", "ITree::map_id", "ITree::interp_bind", "ITree::interp_trigger",
];

#[test]
fn the_law_kit_is_there() {
    let mut e = base();
    let mut src = format!("{IMPORTS} fn kit() → Nat {{\n");
    for (i, law) in LAWS.iter().enumerate() {
        src.push_str(&format!("    let law{i} = {law};\n"));
    }
    src.push_str("    0\n}\n");
    check(&mut e, "itree_kit", &src);
}

// Axis 1, literal and neutral: the loop unrolls at a literal fuel and at a
// successor of a variable, and is stuck at a bare variable.
#[test]
fn iter_unrolls_at_a_successor_and_is_stuck_at_a_variable() {
    let mut e = base();
    check(
        &mut e,
        "itree_iter_open",
        &format!(
            "{IMPORTS}
            theorem two<A, B>(E: Events, body: A → ITree<Step<A, B>>(E), a: A):
                ITree::iter(E, 2, body, a) = ITree::bind(E, body(a), λ x => match x {{
                    Continue(a2) => Tau(ITree::iter(E, 1, body, a2)),
                    Break(b) => Ret(b),
                }}) {{ refl }}
            theorem open_succ<A, B>(E: Events, n: Nat, body: A → ITree<Step<A, B>>(E), a: A):
                ITree::iter(E, Succ(Succ(n)), body, a) = ITree::bind(E, body(a), λ x => match x {{
                    Continue(a2) => Tau(ITree::iter(E, Succ(n), body, a2)),
                    Break(b) => Ret(b),
                }}) {{ refl }}"
        ),
    );
    refused(
        "itree_iter_neutral",
        &format!(
            "{IMPORTS}
            theorem bad<A, B>(E: Events, n: Nat, body: A → ITree<Step<A, B>>(E), a: A):
                ITree::iter(E, n, body, a) = Cut {{ refl }}"
        ),
    );
}

// Axis 4: no fuel is a cut, not a return.
#[test]
fn no_fuel_is_a_cut() {
    refused(
        "itree_iter_zero_ret",
        &format!(
            "{IMPORTS}
            fn stop<A>(E: Events, x: A) → ITree<Step<A, A>>(E) {{ Ret(Break(x)) }}
            fn done<A>(E: Events, x: A) → ITree<A>(E) {{ Ret(x) }}
            theorem bad<A>(E: Events, a: A): ITree::iter(E, 0, λ x => stop(E, x), a) = done(E, a) {{ refl }}"
        ),
    );
    let mut e = base();
    check(
        &mut e,
        "itree_iter_one_ret",
        &format!(
            "{IMPORTS}
            fn stop<A>(E: Events, x: A) → ITree<Step<A, A>>(E) {{ Ret(Break(x)) }}
            fn done<A>(E: Events, x: A) → ITree<A>(E) {{ Ret(x) }}
            theorem ok<A>(E: Events, a: A): ITree::iter(E, 1, λ x => stop(E, x), a) = done(E, a) {{ refl }}"
        ),
    );
}

// The laws through `Vis` are not equations: right identity at a neutral tree
// is refused by `refl`, and holds up to `Same`.
#[test]
fn right_identity_is_same_not_equal() {
    refused(
        "itree_ret_r_eq",
        &format!(
            "{IMPORTS}
            theorem bad<R>(E: Events, t: ITree<R>(E)): ITree::bind(E, t, λ r => Ret(r)) = t {{ refl }}"
        ),
    );
    // …not even at one `Vis` with an open continuation, where a pointwise
    // fact would need funext.
    refused(
        "itree_ret_r_vis_eq",
        &format!(
            "{IMPORTS}
            theorem bad<R>(E: Events, c: E.Cmd, k: E.Resp(c) → ITree<R>(E)):
                ITree::bind<R, R>(E, Vis(c, k), λ r => Ret(r)) = Vis(c, k) {{ refl }}"
        ),
    );
    // The law in a checking position, then composed: `Same` is transitive
    // through the law and its symmetric form.
    let mut e = base();
    check(
        &mut e,
        "itree_ret_r_same",
        &format!(
            "{IMPORTS}
            theorem roundtrip<R>(E: Events, t: ITree<R>(E)): ITree::Same(E, t, t) {{
                let there: ITree::Same(E, ITree::bind(E, t, λ r => Ret(r)), t) = ITree::bind_ret_r(E, t);
                let back: ITree::Same(E, t, ITree::bind(E, t, λ r => Ret(r))) =
                    ITree::same_sym(E, ITree::bind(E, t, λ r => Ret(r)), t, there);
                ITree::same_trans(E, t, ITree::bind(E, t, λ r => Ret(r)), t, back, there)
            }}"
        ),
    );
}

// `Same` tells different trees apart: different leaves, different shapes.
#[test]
fn same_tells_trees_apart() {
    refused(
        "itree_same_leaf",
        &format!(
            "{IMPORTS}
            theorem bad(E: Events): ITree::Same<Nat>(E, Ret(1), Ret(2)) {{ refl }}"
        ),
    );
    refused(
        "itree_same_shape",
        &format!(
            "{IMPORTS}
            theorem bad(E: Events): ITree::Same<Nat>(E, Ret(1), Cut) {{ refl }}"
        ),
    );
    refused(
        "itree_same_tau",
        &format!(
            "{IMPORTS}
            theorem bad(E: Events): ITree::Same<Nat>(E, Tau(Ret(1)), Ret(1)) {{
                SameTau(Ret(1), refl, refl)
            }}"
        ),
    );
    // The controls.
    let mut e = base();
    check(
        &mut e,
        "itree_same_controls",
        &format!(
            "{IMPORTS}
            theorem leaf(E: Events): ITree::Same<Nat>(E, Ret(1), Ret(1)) {{ refl }}
            theorem tau(E: Events): ITree::Same<Nat>(E, Tau(Ret(1)), Tau(Ret(1))) {{
                SameTau(Ret(1), refl, refl)
            }}
            theorem vis<R>(E: Events, c: E.Cmd, k: E.Resp(c) → ITree<R>(E)):
                ITree::Same(E, ITree::bind<R, R>(E, Vis(c, k), λ r => Ret(r)), Vis(c, k)) {{
                ITree::bind_ret_r(E, Vis(c, k))
            }}"
        ),
    );
}
