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

use std::cell::OnceCell;
use std::sync::Mutex;

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

static PREFIX_LOAD: Mutex<()> = Mutex::new(());

thread_local! {
    static BASE: OnceCell<SemanticImage> = const { OnceCell::new() };
}

fn base() -> Elaborator {
    BASE.with(|base| {
        base.get_or_init(|| {
            let _serial = PREFIX_LOAD.lock().unwrap_or_else(|poisoned| poisoned.into_inner());
            support::semantic_test_base(MODULES).semantic_image()
        })
        .elaborator()
    })
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
