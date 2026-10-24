//! `lib/std/itree/coitree_bridge.hthr` — coinductive trees against the
//! fuelled programs of the finite library (`docs/coitree-design.md` §8,
//! `issues/coitree-program-bridge.md`, milestone `it-coinductive`):
//!
//!  1. the module checks from images, and the kit is *there*, named one by
//!     one;
//!  2. the four axes of `docs/testing-generated-terms.md`: the embedding's
//!     observations at a literal tree and an open one, by `refl` in checking
//!     position; a literal loop's return reached at fuel on one side and at
//!     depth on the other, carried across both ways and for an open body,
//!     results and events generic; negative controls — too little fuel, too
//!     little depth, a wrong leaf;
//!  3. a `Cut` claims nothing once embedded, and a bind's return carries
//!     over from the bound programs.

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
    ("coitree_eutt", include_str!("../../../lib/std/itree/coitree_eutt.hthr")),
    ("coitree_bridge", include_str!("../../../lib/std/itree/coitree_bridge.hthr")),
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

const IMPORTS: &str = "import logic; import nat; import itree; import itree_trace; import coitree; import coitree_eutt; \
     import coitree_bridge;\n";

const KIT: &[&str] = &[
    // The embedding.
    "CoTree::of_tree", "Program::tree", "CoTree::spin_cut", "CoTree::of_tree_traces", "CoTree::of_tree_converges",
    "CoTree::of_tree_refines", "CoTree::of_tree_refined",
    // Loops.
    "ITree::iter_rest", "CoTree::iter_rest", "ITree::iter_pass_grows", "CoTree::iter_traces", "CoTree::IterFrom",
    "CoTree::iter_pass_converges", "CoTree::iter_converges", "CoTree::iter_refines", "CoTree::iter_refined",
    // Sequencing.
    "CoTree::BindTracesAt", "CoTree::BindConvergesAt", "CoTree::bind_traces_obs", "CoTree::bind_traces",
    "CoTree::bind_converges_obs", "CoTree::bind_converges", "CoTree::bind_refines", "CoTree::bind_refined",
];

#[test]
fn the_kit_is_there() {
    let mut src = format!("{IMPORTS} fn kit() → Nat {{\n");
    for (i, item) in KIT.iter().enumerate() {
        src.push_str(&format!("    let item{i} = {item};\n"));
    }
    src.push_str("    0\n}\n");
    check("coitree_bridge_kit", &src);
}

// The embedding observes as the tree, at a literal and an open tree, and a
// `Cut` as `spin`; a wrong leaf is refused by conversion.
#[test]
fn the_embedding_observes_as_the_tree() {
    check(
        "coitree_bridge_obs",
        &format!(
            "{IMPORTS}
            theorem obs_tau(E: Events): CoTree::obs<Nat>(E, CoTree::of_tree<Nat>(E, Tau(Ret(1)))) = OTau(CoTree::of_tree(E, Ret(1))) {{ refl }}
            theorem obs_open<R>(E: Events, t: ITree<R>(E)): CoTree::obs(E, CoTree::of_tree(E, Tau(t))) = OTau(CoTree::of_tree(E, t)) {{ refl }}
            theorem obs_vis<R>(E: Events, c: E.Cmd, k: E.Resp(c) → ITree<R>(E)):
                CoTree::obs(E, CoTree::of_tree(E, Vis(c, k))) = OVis(c, λ a => CoTree::of_tree(E, k(a))) {{ refl }}
            theorem obs_cut<R>(E: Events): CoTree::obs(E, CoTree::of_tree<R>(E, Cut)) = OTau(CoTree::spin(E)) {{ refl }}"
        ),
    );
    let msg = refused(
        "coitree_bridge_obs_wrong",
        &format!("{IMPORTS}\ntheorem bad(E: Events): CoTree::obs<Nat>(E, CoTree::of_tree<Nat>(E, Ret(1))) = ORet(2) {{ refl }}"),
    );
    assert!(msg.contains("NotConvertible"), "{msg}");
}

// A literal loop: each pass is a silent step and then a `Continue`, so two
// passes and the `Break` take fuel 3 and depth 5 (four silent steps, then
// the leaf). One less of either leaves
// a `Cut` where the return was, whose only trace is the empty one.
const DOWN: &str = "
    fn down(E: Events, a: Nat) → ITree<Step<Nat, Nat>>(E) {
        match a { Zero => Ret(Break(0)), Succ(m) => Tau(Ret(Continue(m))) }
    }
    fn co_down(E: Events, a: Nat) → CoTree<Nat>(E) { CoTree::iter(E, λ x => CoTree::of_tree(E, down(E, x)), a) }
";

#[test]
fn loops_carry_traces_both_ways() {
    check(
        "coitree_bridge_loops",
        &format!(
            "{IMPORTS}{DOWN}
            theorem fuelled(E: Events): Program::Produces<Nat>(E, Program::iter<Nat, Nat>(E, λ x => down(E, x), 2), TRet(0)) {{
                Converges(3, Returned(refl))
            }}
            theorem fuel_free(E: Events): Program::Produces<Nat>(E, CoTree::program(E, co_down(E, 2)), TRet(0)) {{
                Converges(5, Returned(refl))
            }}
            theorem carried(E: Events): Program::Produces<Nat>(E, CoTree::program(E, co_down(E, 2)), TRet(0)) {{
                CoTree::iter_refined<Nat, Nat>(E, λ x => down(E, x), 2, TRet(0), fuelled(E))
            }}
            theorem carried_back(E: Events): Program::Produces<Nat>(E, Program::iter<Nat, Nat>(E, λ x => down(E, x), 2), TRet(0)) {{
                CoTree::iter_refines<Nat, Nat>(E, λ x => down(E, x), 2, TRet(0), fuel_free(E))
            }}
            theorem back<A, B>(E: Events, body: A → ITree<Step<A, B>>(E), a: A, b: B,
                p: Program::Produces<B>(E, CoTree::program<B>(E, CoTree::iter<A, B>(E, λ x => CoTree::of_tree(E, body(x)), a)), TRet(b))):
                Program::Produces(E, Program::iter(E, body, a), TRet(b))
            {{
                CoTree::iter_refines(E, body, a, TRet(b), p)
            }}"
        ),
    );
    let msg = refused(
        "coitree_bridge_short_fuel",
        &format!(
            "{IMPORTS}{DOWN}
            theorem bad(E: Events): Program::Produces<Nat>(E, Program::iter<Nat, Nat>(E, λ x => down(E, x), 2), TRet(0)) {{
                Converges(2, Returned(refl))
            }}"
        ),
    );
    assert!(msg.contains("constructor of `RetTrace`"), "{msg}");
    let msg = refused(
        "coitree_bridge_short_depth",
        &format!(
            "{IMPORTS}{DOWN}
            theorem bad(E: Events): Program::Produces<Nat>(E, CoTree::program(E, co_down(E, 2)), TRet(0)) {{
                Converges(4, Returned(refl))
            }}"
        ),
    );
    assert!(msg.contains("constructor of `RetTrace`"), "{msg}");
}

// An embedded `Cut` returns nothing, and a bind's return carries over from
// the programs it binds.
#[test]
fn cuts_and_binds() {
    check(
        "coitree_bridge_cut_bind",
        &format!(
            "{IMPORTS}
            theorem cut_claims_nothing<R>(E: Events, r: R,
                p: Program::Produces(E, CoTree::program(E, CoTree::of_tree<R>(E, Cut)), TRet(r))): False
            {{
                let c: Program::Produces<R>(E, Program::tree<R>(E, Cut), TRet(r)) = CoTree::of_tree_refines<R>(E, Cut, TRet(r), p);
                absurd(CutTrace::ended<R>(E, TRet(r), c.h))
            }}
            theorem bound(E: Events):
                Program::Produces<Nat>(E, CoTree::program<Nat>(E, CoTree::bind<Nat, Nat>(E, CRet(1), λ r => CTau(CRet(r + 1)))), TRet(2))
            {{
                CoTree::bind_refined<Nat, Nat>(E, CRet(1), λ r => CTau(CRet(r + 1)), TRet(2), Converges(2, Returned(refl)))
            }}
            theorem bind_open<A, B>(E: Events, t: CoTree<A>(E), h: A → CoTree<B>(E), tr: Trace<B>(E),
                p: Program::Produces(E, CoTree::program(E, CoTree::bind(E, t, h)), tr)):
                Program::Produces(E, Program::bind(E, CoTree::program(E, t), λ r => CoTree::program(E, h(r))), tr)
            {{
                CoTree::bind_refines(E, t, h, tr, p)
            }}"
        ),
    );
}
