//! `lib/std/itree/itree_sim.hthr` — simulation between interaction trees over
//! different events, and the loop rule (`docs/itree-simulation-design.md`,
//! `issues/itree-iter-simulation.md`, milestone `it-library`):
//!
//!  1. the module checks from images, and the kit is *there*, named one by
//!     one;
//!  2. the four axes of `docs/testing-generated-terms.md`: loops at a literal
//!     and an open state, generic events throughout, each pass's simulation
//!     in checking position, and negative controls — a spec that leaves with
//!     another value, and a source call the spec does not make;
//!  3. a loop with silent passes refines one that leaves at once, and a loop
//!     that calls refines another whose state has a different type;
//!  4. up to a continuation (`ITree::SimK`, `ITree::simk_iter`): a loop whose
//!     every pass makes two calls is simulated by one making one call a pass,
//!     at twice the fuel, with the invariant asking that fuel of the spec.

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
    ("itree_sim", include_str!("../../../lib/std/itree/itree_sim.hthr")),
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

/// Refused by conversion: every negative control is a false equation.
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

const IMPORTS: &str = "import logic; import nat; import itree; import itree_trace; import itree_sim;\n";

const KIT: &[&str] = &[
    // Reading a trace through a map, and contracts.
    "TraceMap::id", "Trace::along", "Trace::along_id", "Contract::none", "Trace::Valid", "Trace::Owes",
    "Trace::valid_none",
    // The spec's next move.
    "IsTrace::of_next", "Next::bind", "ITree::next_bind", "Next::Below", "ITree::below_next",
    // Simulation and its laws.
    "ITree::Sim", "SimRet::moved", "SimVis::moved", "ITree::sim_next", "SimRet::below", "ITree::sim_below",
    "ITree::sim_bind", "ITree::sim_trace_vis", "ITree::sim_trace_ret", "ITree::sim_trace",
    // Programs.
    "Program::Simulates", "Program::simulates_of_trees", "Program::refines_of_simulates",
    // Loops.
    "Step::Rel", "ITree::stay", "ITree::PassSim", "ITree::sim_iter_next", "ITree::sim_iter",
    "Program::simulates_iter",
    // Up to a continuation.
    "ITree::SimK", "ITree::simk_bind", "ITree::StepK", "ITree::simk_iter_next", "ITree::simk_iter",
    "Program::simulates_at",
];

#[test]
fn the_kit_is_there() {
    let mut src = format!("{IMPORTS} fn kit() → Nat {{\n");
    for (i, item) in KIT.iter().enumerate() {
        src.push_str(&format!("    let item{i} = {item};\n"));
    }
    src.push_str("    0\n}\n");
    check("itree_sim_kit", &src);
}

/// A countdown whose passes make no call, against a loop that leaves at once
/// from a state of another type.
const DOWN: &str = "
fn down_body(E: Events, a: Nat) → ITree<Step<Nat, Nat>>(E) {
    match a { Zero => Ret(Break(0)), Succ(m) => Ret(Continue(m)) }
}
fn now_body(E: Events, u: True) → ITree<Step<True, Nat>>(E) { Ret(Break(0)) }
";

// Silent passes are simulated by the spec staying where it is, at an open
// state and so at every literal one; the whole loop then refines the spec's.
#[test]
fn silent_passes_refine_a_loop_that_leaves_at_once() {
    check(
        "itree_sim_down",
        &format!(
            "{IMPORTS}{DOWN}
            theorem down_pass(E: Events, a: Nat, u: True):
                ITree::PassSim<Nat, True, Nat>(E, E, TraceMap::id(E), Contract::none(E), λ x y => True,
                    λ x => down_body(E, x), λ y => now_body(E, y), a, u)
            {{
                match a {{
                    Zero => Inl(SimRet(Break(0), refl, refl)),
                    Succ(_) => Inr(SimRet(Continue(u), refl, trivial)),
                }}
            }}
            theorem down_refines(E: Events, a: Nat):
                Program::Refines<Nat>(E, Program::iter<Nat, Nat>(E, λ x => down_body(E, x), a),
                    Program::iter<True, Nat>(E, λ y => now_body(E, y), trivial))
            {{
                Program::refines_of_simulates(E, Program::iter<Nat, Nat>(E, λ x => down_body(E, x), a),
                    Program::iter<True, Nat>(E, λ y => now_body(E, y), trivial),
                    Program::simulates_iter(E, E, TraceMap::id(E), Contract::none(E), λ x y => True,
                        λ x => down_body(E, x), λ y => now_body(E, y), λ x y r => down_pass(E, x, y), a, trivial, trivial))
            }}
            theorem down_three(E: Events):
                Program::Refines<Nat>(E, Program::iter<Nat, Nat>(E, λ x => down_body(E, x), 3),
                    Program::iter<True, Nat>(E, λ y => now_body(E, y), trivial))
            {{
                down_refines(E, 3)
            }}"
        ),
    );
    refused(
        "itree_sim_down_wrong",
        &format!(
            "{IMPORTS}{DOWN}
            fn one_body(E: Events, u: True) → ITree<Step<True, Nat>>(E) {{ Ret(Break(1)) }}
            theorem bad(E: Events): ITree::PassSim<Nat, True, Nat>(E, E, TraceMap::id(E), Contract::none(E), λ x y => True,
                λ x => down_body(E, x), λ y => one_body(E, y), 0, trivial)
            {{
                Inl(SimRet(Break(1), refl, refl))
            }}"
        ),
    );
}

/// One call and then a break with the state, on both sides; the states are
/// related by equality.
const CALL: &str = "
fn call_body(E: Events, c: E.Cmd, a: Nat) → ITree<Step<Nat, Nat>>(E) {
    ITree::bind(E, ITree::trigger(E, c), λ x => Ret(Break(a)))
}
";

// A pass that calls: the spec makes the same call, and every answer leaves
// with related values. A source call the spec does not make is refused.
#[test]
fn a_calling_pass_is_simulated_call_for_call() {
    check(
        "itree_sim_call",
        &format!(
            "{IMPORTS}{CALL}
            theorem call_pass(E: Events, c: E.Cmd, a: Nat, a2: Nat, r: a = a2):
                ITree::PassSim<Nat, Nat, Nat>(E, E, TraceMap::id(E), Contract::none(E), λ x y => x = y,
                    λ x => call_body(E, c, x), λ y => call_body(E, c, y), a, a2)
            {{
                Inl(SimVis(trivial, λ x => Ret(Break(a2)), refl, λ x v => SimRet(Break(a2), refl, r)))
            }}
            theorem call_simulates(E: Events, c: E.Cmd, a: Nat):
                Program::Simulates<Nat>(E, E, TraceMap::id(E), Contract::none(E),
                    Program::iter<Nat, Nat>(E, λ x => call_body(E, c, x), a), Program::iter<Nat, Nat>(E, λ y => call_body(E, c, y), a))
            {{
                Program::simulates_iter(E, E, TraceMap::id(E), Contract::none(E), λ x y => x = y,
                    λ x => call_body(E, c, x), λ y => call_body(E, c, y), λ x y r => call_pass(E, c, x, y, r), a, a, refl)
            }}"
        ),
    );
    refused(
        "itree_sim_call_wrong",
        &format!(
            "{IMPORTS}{CALL}
            theorem bad(E: Events, c: E.Cmd, a: Nat):
                ITree::Sim<Step<Nat, Nat>, Step<Nat, Nat>>(E, E, TraceMap::id(E), Contract::none(E), λ x y => x = y,
                    call_body(E, c, a), Ret(Break(a)))
            {{
                SimVis(trivial, λ x => Ret(Break(a)), refl, λ x v => SimRet(Break(a), refl, refl))
            }}"
        ),
    );
}

/// A countdown whose passes each make two calls, and one whose passes each
/// make one, from twice the state and one more. `TwiceAt(k, a, v)`: `k`
/// source passes left at `a`, the spec at `v` two passes behind each of them,
/// with the fuel for them.
const TWICE: &str = "
fn countdown(a: Nat) → Step<Nat, Nat> { match a { Zero => Break(0), Succ(m) => Continue(m) } }
fn twice_body(E: Events, c: E.Cmd, a: Nat) → ITree<Step<Nat, Nat>>(E) {
    ITree::bind(E, ITree::trigger(E, c), λ x => ITree::bind(E, ITree::trigger(E, c), λ y => Ret(countdown(a))))
}
fn once_body(E: Events, c: E.Cmd, b: Nat) → ITree<Step<Nat, Nat>>(E) {
    ITree::bind(E, ITree::trigger(E, c), λ x => Ret(countdown(b)))
}
fn once_tree(E: Events, c: E.Cmd, fuel, b: Nat) → ITree<Nat>(E) { ITree::iter(E, fuel, λ y => once_body(E, c, y), b) }

// `k` passes of two calls left: the spec one call per pass, two passes
// behind each of the source's, with the fuel for them.
record TwiceAt(E: Events, c: E.Cmd, k, a: Nat, v: ITree<Nat>(E)) {
    fuel: Nat,
    enough: k.twice() <= fuel,
    at: ITree::next(E, v) = ITree::next(E, once_tree(E, c, fuel, Succ(a.twice()))),
}

fn twice_after(E: Events, c: E.Cmd, k: Nat) → Step<Nat, Nat> → ITree<Nat>(E) → Type {
    λ x w => ITree::StepK(E, λ a v => TwiceAt(E, c, k, a, v), λ r v => SimRet<Nat>(E, v, λ y => r = y), x, w)
}
";

// One source pass is two spec passes: `simk_iter` with an invariant indexed
// by the source's fuel left, at an open state and at a literal one, with the
// spec at `twice` the source's fuel (`simulates_at`). Leaving with another
// value is refused.
#[test]
fn a_pass_of_two_calls_is_two_spec_passes() {
    check("itree_sim_twice", &format!("{IMPORTS}{TWICE}{TWICE_PROOFS}"));
    refused("itree_sim_twice_wrong", &format!("{IMPORTS}{TWICE}{}",
        TWICE_PROOFS.replace("λ y v => SimRet(0, refl, refl)", "λ y v => SimRet(1, refl, refl)")));
}

const TWICE_PROOFS: &str = "
theorem twice_second(E: Events, c: E.Cmd, k, a: Nat, f1: Nat, x: E.Resp(c)): Succ(k.twice()) <= f1 →
    ITree::SimK(E, E, TraceMap::id(E), Contract::none(E), twice_after(E, c, k),
        ITree::bind(E, ITree::trigger(E, c), λ y => Ret(countdown(a))), Tau(once_tree(E, c, f1, a.twice())))
{
    match f1 {
        Zero => λ (no: False) => false_elim(no),
        Succ(f2) => λ enough => match a {
            Zero => SimVis(trivial, λ y => Ret(0), refl, λ y v => SimRet(0, refl, refl)),
            Succ(m) => SimVis(trivial, λ y => Tau(once_tree(E, c, f2, Succ(m.twice()))), refl,
                λ y v => TwiceAt(f2, enough, refl)),
        },
    }
}

theorem twice_pass(E: Events, c: E.Cmd, k, a: Nat, v: ITree<Nat>(E), i: TwiceAt(E, c, Succ(k), a, v)):
    ITree::SimK(E, E, TraceMap::id(E), Contract::none(E), twice_after(E, c, k), twice_body(E, c, a), v)
{
    (match i.fuel as λ f => Succ(k).twice() <= f → ITree::next(E, v) = ITree::next(E, once_tree(E, c, f, Succ(a.twice()))) →
            ITree::SimK(E, E, TraceMap::id(E), Contract::none(E), twice_after(E, c, k), twice_body(E, c, a), v) {
        Zero => λ (no: False) at => false_elim(no),
        Succ(f1) => λ enough at => SimVis(trivial, λ x => Tau(once_tree(E, c, f1, a.twice())), at,
            λ x valid => twice_second(E, c, k, a, f1, x, enough)),
    })(i.enough, i.at)
}

theorem twice_sim(E: Events, c: E.Cmd, n, a: Nat):
    ITree::Sim<Nat, Nat>(E, E, TraceMap::id(E), Contract::none(E), λ x y => x = y,
        ITree::iter(E, n, λ x => twice_body(E, c, x), a), once_tree(E, c, n.twice(), Succ(a.twice())))
{
    let head: TwiceAt(E, c, n, a, once_tree(E, c, n.twice(), Succ(a.twice()))) = TwiceAt(n.twice(), n.twice().le_refl(), refl);
    ITree::simk_iter(E, E, TraceMap::id(E), Contract::none(E), λ x => twice_body(E, c, x), λ k x w => TwiceAt(E, c, k, x, w),
        λ r w => SimRet<Nat>(E, w, λ y => r = y), λ k x w i => twice_pass(E, c, k, x, w, i), n, a,
        once_tree(E, c, n.twice(), Succ(a.twice())), head)
}

theorem twice_simulates(E: Events, c: E.Cmd, a: Nat):
    Program::Simulates<Nat>(E, E, TraceMap::id(E), Contract::none(E),
        Program::iter<Nat, Nat>(E, λ x => twice_body(E, c, x), a), Program::iter<Nat, Nat>(E, λ y => once_body(E, c, y), Succ(a.twice())))
{
    Program::simulates_at(E, E, TraceMap::id(E), Contract::none(E),
        Program::iter<Nat, Nat>(E, λ x => twice_body(E, c, x), a), Program::iter<Nat, Nat>(E, λ y => once_body(E, c, y), Succ(a.twice())),
        λ n => n.twice(), λ n => twice_sim(E, c, n, a))
}

theorem twice_three(E: Events, c: E.Cmd):
    Program::Simulates<Nat>(E, E, TraceMap::id(E), Contract::none(E),
        Program::iter<Nat, Nat>(E, λ x => twice_body(E, c, x), 3), Program::iter<Nat, Nat>(E, λ y => once_body(E, c, y), 7))
{
    twice_simulates(E, c, 3)
}
";
