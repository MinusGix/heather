//! `lib/std/itree_trace.hthr` and `lib/std/itree_state.hthr` — traces and
//! refinement of interaction trees, and a state handler into world threading
//! (`issues/interaction-trees-container-model.md` Q2–Q3, milestone
//! `it-refinement`; `docs/itree-refinement-round.md`).
//!
//!  1. the closure checks: the modules and the client showcase, which builds
//!     a console trace, shows a loop refines itself at more fuel, and threads
//!     a counter by `refl`;
//!  2. the kit is *there*, named one by one;
//!  3. the four axes of `docs/testing-generated-terms.md`: a closed and an
//!     open state, generic events throughout, traces in checking position,
//!     and negative controls — a trace the tree cannot produce, a cut that
//!     returns, a tree below a cut, a wrong threaded state.

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
    ("itree_state", include_str!("../../../lib/std/itree_state.hthr")),
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

const IMPORTS: &str =
    "import logic; import nat; import option; import pair; import itree; import itree_trace; import itree_state;\n";

#[test]
fn traces_and_their_client_check() {
    let mut e = base();
    check(
        &mut e,
        "itree_refinement_client",
        include_str!("../../../docs/showcase/itree_refinement_client.hthr"),
    );
}

const KIT: &[&str] = &[
    // Traces.
    "IsTrace", "IsTrace::nil", "IsTrace::of_same", "IsTrace::of_below", "IsTrace::up",
    "IsTrace::fuel_monotone", "IsTrace::ret_unique", "IsTrace::bind", "Trace::seq",
    // The case lemmas the recursions call.
    "RetTrace::returns", "VisTrace::never_returns", "VisTrace::map", "VisTrace::seq", "CutTrace::ended",
    // The approximation order and growing families.
    "ITree::Below", "ITree::below_refl", "ITree::below_bind", "ITree::iter_next", "ITree::iter_grows",
    "ITree::Grows", "ITree::iter_family_grows",
    // Convergence and refinement.
    "Converges::at", "Converges::ret_unique", "ITree::Refines", "ITree::refines_refl",
    "ITree::refines_trans", "ITree::refines_of_same", "ITree::refines_shift",
    // Recursion grows with fuel too.
    "ITree::mrec_vis_below", "ITree::mrec_layer_below", "ITree::mrec_grows", "ITree::rec_family_grows",
    // Programs: families carrying their growth.
    "Program::pure", "Program::iter", "Program::rec", "Program::bind", "Program::Produces",
    "Program::Refines", "Program::refines_refl", "Program::refines_trans", "Program::refines_of_families",
    "Program::families_of_refines", "Program::ret_unique", "Program::Diverges", "ITree::spin_step",
    "ITree::spin_never_returns", "Program::spin", "Program::spin_diverges", "Program::pure_not_diverges",
    // The state handler.
    "Events::state", "ITree::state_vis", "ITree::run_state", "ITree::state_vis_bind",
    "ITree::run_state_bind", "ITree::returned", "ITree::thread", "ITree::returned_of_trace",
];

#[test]
fn the_kit_is_there() {
    let mut e = base();
    let mut src = format!("{IMPORTS} fn kit() → Nat {{\n");
    for (i, item) in KIT.iter().enumerate() {
        src.push_str(&format!("    let item{i} = {item};\n"));
    }
    src.push_str("    0\n}\n");
    check(&mut e, "itree_trace_kit", &src);
}

/// A console with one command, so traces are short to spell.
const CONSOLE: &str = "
inductive Cmd { Ask, Say(n: Nat) }
fn Resp(c: Cmd) → Type { match c { Ask => Nat, Say(_) => True } }
fn C() → Events { Events(Cmd, λ c => Resp(c)) }
fn ask() → ITree<Nat>(C()) { ITree::trigger(C(), Ask) }
";

// A trace in checking position, and the one next to it that the tree cannot
// produce.
#[test]
fn a_trace_is_what_the_tree_can_do() {
    let mut e = base();
    check(
        &mut e,
        "itree_trace_ok",
        &format!(
            "{IMPORTS}{CONSOLE}
            theorem ok(): IsTrace<Nat>(C(), ask(), TAns(Ask, 4, TRet(4))) {{ Answered(4, TRet(4), refl, Returned(refl)) }}
            theorem prefix(): IsTrace<Nat>(C(), ask(), TEnd) {{ IsTrace::nil(C(), ask()) }}"
        ),
    );
    refused(
        "itree_trace_wrong_return",
        &format!(
            "{IMPORTS}{CONSOLE}
            theorem bad(): IsTrace<Nat>(C(), ask(), TAns(Ask, 4, TRet(5))) {{ Answered(4, TRet(5), refl, Returned(refl)) }}"
        ),
    );
    refused(
        "itree_trace_wrong_command",
        &format!(
            "{IMPORTS}{CONSOLE}
            theorem bad(): IsTrace<Nat>(C(), ask(), TCall(Say(1))) {{ Pending(refl) }}"
        ),
    );
}

// A cut claims only the empty prefix, and a tree is not below a cut.
#[test]
fn a_cut_claims_nothing() {
    refused(
        "itree_cut_returns",
        &format!(
            "{IMPORTS}
            theorem bad(E: Events): IsTrace<Nat>(E, Cut, TRet(1)) {{ Ended(refl) }}"
        ),
    );
    refused(
        "itree_below_cut",
        &format!(
            "{IMPORTS}
            theorem bad(E: Events): ITree::Below<Nat>(E, Ret(1), Cut) {{ refl }}"
        ),
    );
    let mut e = base();
    check(
        &mut e,
        "itree_cut_controls",
        &format!(
            "{IMPORTS}
            theorem empty(E: Events): IsTrace<Nat>(E, Cut, TEnd) {{ Ended(refl) }}
            theorem below<R>(E: Events, t: ITree<R>(E)): ITree::Below(E, Cut, t) {{ trivial }}"
        ),
    );
}

// Threading computes at a literal and at an open state, and refuses a wrong
// final state.
#[test]
fn threading_computes_at_an_open_state() {
    let src = "
fn Counter() → Events { Events::sum(Events::state<Nat>(), Events::none()) }
fn tick() → ITree<Nat>(Counter()) {
    ITree::bind(Counter(), ITree::trigger(Counter(), Inl(Get)), λ n =>
        ITree::bind(Counter(), ITree::trigger(Counter(), Inl(Put(Succ(n)))), λ u => Ret(n)))
}
";
    let mut e = base();
    check(
        &mut e,
        "itree_thread_open",
        &format!(
            "{IMPORTS}{src}
            theorem lit(): ITree::thread(tick(), 2) = Some(Pair(3, 2)) {{ refl }}
            theorem opened(s: Nat): ITree::thread(tick(), s) = Some(Pair(Succ(s), s)) {{ refl }}"
        ),
    );
    refused(
        "itree_thread_wrong",
        &format!(
            "{IMPORTS}{src}
            theorem bad(s: Nat): ITree::thread(tick(), s) = Some(Pair(s, s)) {{ refl }}"
        ),
    );
}

// Binds nested to the left thread in time quadratic in their depth, not
// `2^d` (issues/tier2-left-nested-bind-cost.md): every `Vis` a `bind` builds
// reads its child once for the tree and once for the proof, and those two
// reads now share one evaluation.
#[test]
fn left_nested_binds_thread() {
    let src = "
fn Counter() → Events { Events::sum(Events::state<Nat>(), Events::none()) }
fn tick() → ITree<Nat>(Counter()) {
    ITree::bind(Counter(), ITree::trigger(Counter(), Inl(Get)), λ n =>
        ITree::bind(Counter(), ITree::trigger(Counter(), Inl(Put(Succ(n)))), λ u => Ret(n)))
}
fn lticks(k: Nat) → ITree<Nat>(Counter()) {
    match k { Zero => Ret(0), Succ(j) => ITree::bind(Counter(), lticks(j), λ n => tick()) }
}
";
    let mut e = base();
    check(
        &mut e,
        "itree_left_nested",
        &format!(
            "{IMPORTS}{src}
            theorem deep(): ITree::thread(lticks(24), 0) = Some(Pair(24, 23)) {{ refl }}"
        ),
    );
    refused(
        "itree_left_nested_wrong",
        &format!(
            "{IMPORTS}{src}
            theorem bad(): ITree::thread(lticks(24), 0) = Some(Pair(24, 24)) {{ refl }}"
        ),
    );
}

// A program built by `rec` grows with fuel and is a `Program`; the spin
// proof's induction goes through for a loop that only goes round and is
// refused for one that breaks.
#[test]
fn programs_grow_and_divergence_is_returning_at_no_fuel() {
    let mut e = base();
    check(
        &mut e,
        "itree_program_ok",
        &format!(
            "{IMPORTS}{CONSOLE}
            fn body(c: Cmd) → ITree<Resp(c)>(Events::sum(C(), C())) {{
                match c {{ Ask => Ret(7), Say(_) => Ret(trivial) }}
            }}
            fn asks() → Program<Nat>(C()) {{ Program::rec(C(), C(), λ c => body(c), Ask) }}
            theorem asks_grows(n: Nat): ITree::Below(C(), asks().at(n), asks().at(Succ(n))) {{ asks().grows(n) }}
            theorem asks_seven(): Program::Produces<Nat>(C(), asks(), TRet(7)) {{ Converges(1, Returned(refl)) }}
            theorem twice(): Program::Produces<Nat>(C(), Program::bind(C(), asks(), λ a => Program::pure(C(), a + a)), TRet(14)) {{
                Converges(1, Returned(refl))
            }}"
        ),
    );
    // At a breaking loop the step is a `Ret`, not the loop at one less fuel,
    // so the recursive call has the wrong type: a mismatch the elaborator
    // reports before any conversion is attempted.
    let src = format!(
        "{IMPORTS}
        fn stop(u: True) → ITree<Step<True, True>>(Events::none()) {{ Ret(Break(u)) }}
        theorem bad(n: Nat, r: True):
            IsTrace(Events::none(), ITree::iter<True, True>(Events::none(), n, λ u => stop(u), trivial), TRet(r)) → False
        {{
            match n {{
                Zero => λ w => absurd(CutTrace::ended<True>(Events::none(), TRet(r), w)),
                Succ(m) => λ h => bad(m, r, h),
            }}
        }}"
    );
    let mut e = base();
    match e.elab_module_source("itree_spin_breaks", &src) {
        Ok(()) => panic!("itree_spin_breaks should be refused"),
        Err(err) => {
            let msg = err.render(&src);
            assert!(msg.contains("is expected here"), "itree_spin_breaks: {msg}");
        }
    }
}

