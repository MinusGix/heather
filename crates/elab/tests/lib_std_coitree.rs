//! `lib/std/itree/coitree.hthr` — coinductive interaction trees over `codata`
//! (`docs/coitree-design.md`, milestone `it-coinductive`):
//!
//!  1. the module checks from images, and the kit is *there*, named one by
//!     one;
//!  2. the four axes of `docs/testing-generated-terms.md`: observations at a
//!     literal and an open depth, generic results and events throughout, a
//!     client's own corecursive bisimilarity with its observation equations
//!     in checking position, and negative controls — a wrong approximation,
//!     a bisimilarity between different leaves;
//!  3. a goal over `Bisim` names it with its trees.

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
    ("itree_trace", include_str!("../../../lib/std/itree/itree_trace.hthr")),
    ("coitree", include_str!("../../../lib/std/itree/coitree.hthr")),
];

static BASE: OnceLock<SemanticImage> = OnceLock::new();

fn base() -> Elaborator {
    BASE.get_or_init(|| support::semantic_test_base(MODULES).semantic_image()).elaborator()
}

fn check(name: &str, src: &str) {
    let mut e = base();
    if let Err(err) = e.elab_module_source(name, src) {
        panic!("{}", err.render(src));
    }
}

fn refused(name: &str, src: &str) -> String {
    let mut e = base();
    match e.elab_module_source(name, src) {
        Ok(()) => panic!("{name} should be refused"),
        Err(err) => err.render(src),
    }
}

const IMPORTS: &str = "import logic; import nat; import itree; import itree_trace; import coitree;\n";

const KIT: &[&str] = &[
    // Trees, observations, combinators.
    "CoTree::obs", "Obs::tree", "Obs::obs_tree", "CoTree::trigger", "CoTree::spin", "CoTree::bind_obs",
    "CoTree::bind", "CoTree::map", "Obs::bind", "CoTree::translate", "CoTree::iter_obs", "CoTree::iter",
    // Unfolding laws.
    "CoTree::obs_bind_obs", "CoTree::obs_bind", "CoTree::obs_bind_at", "CoTree::obs_spin", "CoTree::bind_ret_obs",
    "CoTree::iter_continue", "CoTree::iter_break",
    // Approximation and programs.
    "CoTree::approx_obs", "CoTree::approx", "CoTree::approx_obs_grows", "CoTree::approx_grows",
    "CoTree::program", "CoTree::spin_never_returns", "CoTree::spin_diverges",
    // Strong bisimilarity and the monad laws up to it.
    "Bisim::refl", "Bisim::sym", "Bisim::trans", "Bisim::step", "Bisim::of_obs", "Bisim::tree_obs",
    "Bisim::approx", "CoTree::bind_ret_l", "CoTree::bind_ret_r", "CoTree::map_id", "CoTree::bind_assoc", "CoTree::bind_cong",
];

#[test]
fn the_kit_is_there() {
    let mut src = format!("{IMPORTS} fn kit() → Nat {{\n");
    for (i, item) in KIT.iter().enumerate() {
        src.push_str(&format!("    let item{i} = {item};\n"));
    }
    src.push_str("    0\n}\n");
    check("coitree_kit", &src);
}

/// A counter loop with no fuel: `iter` goes round until the counter is zero.
const DOWN: &str = "
fn down_body(E: Events, a: Nat) → CoTree<Step<Nat, Nat>>(E) {
    match a { Zero => CRet(Break(0)), Succ(m) => CRet(Continue(m)) }
}
fn down(E: Events, a: Nat) → CoTree<Nat>(E) { CoTree::iter(E, λ x => down_body(E, x), a) }
";

// Observations compute at a literal depth and at an open one, for `spin` and
// for a loop; the wrong approximation is refused by conversion.
#[test]
fn observations_compute() {
    check(
        "coitree_observe",
        &format!(
            "{IMPORTS}{DOWN}
            theorem spin_two<R>(E: Events): CoTree::approx(E, 2, CoTree::spin<R>(E)) = Tau(Tau(Cut)) {{ refl }}
            theorem spin_open<R>(E: Events, n: Nat):
                CoTree::approx(E, Succ(n), CoTree::spin<R>(E)) = Tau(CoTree::approx(E, n, CoTree::spin<R>(E))) {{ refl }}
            theorem down_obs(E: Events): CoTree::obs(E, down(E, 2)) = OTau(down(E, 1)) {{ refl }}
            theorem down_one(E: Events): CoTree::approx(E, 2, down(E, 1)) = Tau(Ret(0)) {{ refl }}
            theorem down_cont(E: Events, n: Nat): CoTree::obs(E, down(E, Succ(n))) = OTau(down(E, n)) {{
                CoTree::iter_continue(E, λ x => down_body(E, x), Succ(n), n, refl)
            }}"
        ),
    );
    let msg = refused(
        "coitree_observe_wrong",
        &format!("{IMPORTS}{DOWN}\ntheorem bad(E: Events): CoTree::approx(E, 2, down(E, 1)) = Tau(Ret(1)) {{ refl }}"),
    );
    assert!(msg.contains("NotConvertible"), "{msg}");
}

// A client's own coinduction: the observation equations of each constructor
// in checking position, by `refl`, and a bisimilarity used through the bridge
// to approximations and through transitivity.
#[test]
fn a_client_proves_bisimilarities() {
    check(
        "coitree_client",
        &format!(
            "{IMPORTS}
            fn spin_self<R>(E: Events) → Bisim<R>(E, CoTree::spin(E), CoTree::spin(E)) {{
                BTau(CoTree::spin(E), CoTree::spin(E), refl, refl, spin_self(E))
            }}
            theorem ret_r_approx<R>(E: Events, n: Nat, t: CoTree<R>(E)):
                ITree::Same(E, CoTree::approx(E, n, CoTree::bind(E, t, λ r => CRet(r))), CoTree::approx(E, n, t))
            {{
                Bisim::approx(E, n, CoTree::bind(E, t, λ r => CRet(r)), t, CoTree::bind_ret_r(E, t))
            }}
            fn ret_r_twice<R>(E: Events, t: CoTree<R>(E)) →
                Bisim<R>(E, CoTree::bind<R, R>(E, CoTree::bind<R, R>(E, t, λ r => CRet(r)), λ r => CRet(r)), t)
            {{
                Bisim::trans(E, CoTree::bind<R, R>(E, CoTree::bind<R, R>(E, t, λ r => CRet(r)), λ r => CRet(r)),
                    CoTree::bind<R, R>(E, t, λ r => CRet(r)), t,
                    CoTree::bind_ret_r(E, CoTree::bind(E, t, λ r => CRet(r))), CoTree::bind_ret_r(E, t))
            }}"
        ),
    );
    let msg = refused(
        "coitree_bisim_wrong",
        &format!("{IMPORTS}\nfn bad(E: Events) → Bisim<Nat>(E, CRet(1), CRet(2)) {{ BRet(1, refl, refl) }}"),
    );
    assert!(msg.contains("NotConvertible"), "{msg}");
}

// A goal over `Bisim` names it with its trees, through the named signature
// (`docs/codata-named-signature-design.md`).
#[test]
fn goals_name_bisimilarity() {
    let msg = refused(
        "coitree_goal",
        &format!(
            "{IMPORTS}\ntheorem g<R>(E: Events, t: CoTree<R>(E), b: Bisim<R>(E, t, CoTree::spin(E))): t = t {{ ?g }}"
        ),
    );
    assert!(msg.contains("b : Bisim<R>(E, t, spin(E))"), "{msg}");
}
