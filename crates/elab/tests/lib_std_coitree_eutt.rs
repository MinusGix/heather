//! `lib/std/coitree_eutt.hthr` — equivalence up to silent steps on
//! coinductive trees (`docs/coitree-design.md` §7, `issues/coitree-eutt.md`,
//! milestone `it-coinductive`):
//!
//!  1. the module checks from images, and the kit is *there*, named one by
//!     one;
//!  2. the four axes of `docs/testing-generated-terms.md`: drop counts at
//!     literal trees and at an open one, generic results and events
//!     throughout, a client's own corecursive `Eutt` with its observation
//!     equations in checking position, and negative controls — different
//!     leaves, and a count too small to reach the leaf;
//!  3. transitivity through silent steps, and the bridge to programs.

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
    ("itree_trace", include_str!("../../../lib/std/itree_trace.hthr")),
    ("coitree", include_str!("../../../lib/std/coitree.hthr")),
    ("coitree_eutt", include_str!("../../../lib/std/coitree_eutt.hthr")),
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

const IMPORTS: &str =
    "import logic; import nat; import itree; import itree_trace; import coitree; import coitree_eutt;\n";

const KIT: &[&str] = &[
    // Dropping silent steps.
    "CoTree::after_obs", "CoTree::after", "Obs::Settled", "CoTree::after_obs_settled", "CoTree::after_settled",
    "CoTree::after_succ", "CoTree::after_obs_join", "CoTree::after_join", "CoTree::after_via", "CoTree::after_drop1",
    // The relation and its first laws.
    "Eutt::of_bisim", "Eutt::refl", "Eutt::sym", "Eutt::tau_l", "Eutt::tau_r",
    "Eutt::bind_ret_l", "Eutt::bind_ret_r", "Eutt::bind_assoc",
    // Moving the counts.
    "Eutt::peel_l", "Eutt::peel_r", "Eutt::drop1_tau", "Eutt::drop1", "Eutt::drop_l",
    // Transitivity.
    "Obs::EuttTo", "Eutt::to0", "Eutt::to", "Eutt::trans",
    // Programs.
    "CoTree::converges_after", "CoTree::converges_nil", "Eutt::traces_ret", "Eutt::TracesAt", "Eutt::traces_vis",
    "Eutt::traces_obs", "Eutt::traces", "Eutt::refines", "Eutt::refined", "Bisim::refines",
];

#[test]
fn the_kit_is_there() {
    let mut src = format!("{IMPORTS} fn kit() → Nat {{\n");
    for (i, item) in KIT.iter().enumerate() {
        src.push_str(&format!("    let item{i} = {item};\n"));
    }
    src.push_str("    0\n}\n");
    check("coitree_eutt_kit", &src);
}

// Counts at literal trees, by `refl` in checking position; a count too small
// to reach the leaf, and different leaves, are refused by conversion.
#[test]
fn counts_drop_silent_steps() {
    check(
        "coitree_eutt_counts",
        &format!(
            "{IMPORTS}
            fn two_taus(E: Events) → Eutt<Nat>(E, CTau(CTau(CRet(1))), CRet(1)) {{ ERet(2, 0, 1, refl, refl) }}
            fn more_than_enough(E: Events) → Eutt<Nat>(E, CRet(1), CTau(CRet(1))) {{ ERet(5, 7, 1, refl, refl) }}
            theorem after_open<R>(E: Events, n: Nat, t: CoTree<R>(E)):
                CoTree::after(E, Succ(n), CTau(t)) = CoTree::after(E, n, t) {{ refl }}"
        ),
    );
    let msg = refused(
        "coitree_eutt_short",
        &format!("{IMPORTS}\nfn bad(E: Events) → Eutt<Nat>(E, CTau(CTau(CRet(1))), CRet(1)) {{ ERet(1, 0, 1, refl, refl) }}"),
    );
    assert!(msg.contains("NotConvertible"), "{msg}");
    let msg = refused(
        "coitree_eutt_wrong",
        &format!("{IMPORTS}\nfn bad(E: Events) → Eutt<Nat>(E, CRet(1), CRet(2)) {{ ERet(0, 0, 1, refl, refl) }}"),
    );
    assert!(msg.contains("NotConvertible"), "{msg}");
}

// A client's own corecursion relates `spin` to itself dropping different
// counts on each side, and to a tree with one more silent step in front; transitivity composes silent steps on both sides, and
// equivalent trees refine each other as programs.
#[test]
fn a_client_composes_equivalences() {
    check(
        "coitree_eutt_client",
        &format!(
            "{IMPORTS}
            fn spin_self<R>(E: Events) → Eutt<R>(E, CoTree::spin(E), CoTree::spin(E)) {{
                ETau(3, 1, CoTree::spin(E), CoTree::spin(E), refl, refl, spin_self(E))
            }}
            fn spin_tau<R>(E: Events) → Eutt<R>(E, CoTree::spin(E), CTau(CoTree::spin(E))) {{
                ETau(0, 1, CoTree::spin(E), CoTree::spin(E), refl, refl, spin_self(E))
            }}
            fn two_off<R>(E: Events, t: CoTree<R>(E)) → Eutt<R>(E, CTau(CTau(t)), t) {{
                Eutt::trans(E, CTau(CTau(t)), CTau(t), t, Eutt::tau_l(E, CTau(t)), Eutt::tau_l(E, t))
            }}
            fn moved<R>(E: Events, t: CoTree<R>(E)) → Eutt<R>(E, CTau(t), CTau(CTau(t))) {{
                Eutt::trans(E, CTau(t), t, CTau(CTau(t)), Eutt::tau_l(E, t), Eutt::sym(E, CTau(CTau(t)), t, two_off(E, t)))
            }}
            theorem two_off_refines<R>(E: Events, t: CoTree<R>(E)):
                Program::Refines(E, CoTree::program(E, CTau(CTau(t))), CoTree::program(E, t))
            {{
                Eutt::refines(E, CTau(CTau(t)), t, two_off(E, t))
            }}
            theorem ret_r_refined<R>(E: Events, t: CoTree<R>(E)):
                Program::Refines(E, CoTree::program(E, t), CoTree::program(E, CoTree::bind(E, t, λ r => CRet(r))))
            {{
                Eutt::refined(E, CoTree::bind(E, t, λ r => CRet(r)), t, Eutt::bind_ret_r(E, t))
            }}"
        ),
    );
}

// A goal over `Eutt` names it with its trees.
#[test]
fn goals_name_equivalence() {
    let msg = refused(
        "coitree_eutt_goal",
        &format!("{IMPORTS}\ntheorem g<R>(E: Events, t: CoTree<R>(E), e: Eutt<R>(E, t, CoTree::spin(E))): t = t {{ ?g }}"),
    );
    assert!(msg.contains("e : Eutt<R>(E, t, spin(E))"), "{msg}");
}
