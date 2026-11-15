//! `lib/std/itree/itree_trace.hthr` and `itree_state.hthr`
//! (`docs/itrees/itree-refinement-round.md`): the refusals that need the checker.
//! What the language can state is
//! `lib/_tests/std/itree/itree_trace_tests.hthr`, which the whole-library
//! gate checks (`crates/cli/tests/library.rs`): traces in checking position,
//! cuts (with `¬` theorems that a cut does not return and that no leaf is
//! below a cut), threading at a literal and an open state, and programs. The
//! client showcase is a CLI-tier row of `docs/showcase/showcases.tsv`
//! (docs/test-value-audit.md §3.4, §3.5).

use std::sync::OnceLock;

use heather_elab::{Elaborator, SemanticImage};

use crate::support::{self, Refusal};

const MODULES: &[(&str, &str)] = &[
    ("logic", include_str!("../../../lib/std/core/logic.hthr")),
    ("bool", include_str!("../../../lib/std/core/bool.hthr")),
    ("nat", include_str!("../../../lib/std/num/nat.hthr")),
    ("option", include_str!("../../../lib/std/core/option.hthr")),
    ("pair", include_str!("../../../lib/std/core/pair.hthr")),
    ("list", include_str!("../../../lib/std/data/list.hthr")),
    ("itree", include_str!("../../../lib/std/itree/itree.hthr")),
    ("itree_trace", include_str!("../../../lib/std/itree/itree_trace.hthr")),
    ("itree_state", include_str!("../../../lib/std/itree/itree_state.hthr")),
];

static BASE: OnceLock<SemanticImage> = OnceLock::new();

fn base() -> Elaborator {
    BASE.get_or_init(|| support::semantic_test_base(MODULES).semantic_image()).elaborator()
}

const IMPORTS: &str =
    "import logic; import nat; import option; import pair; import itree; import itree_trace; import itree_state;\n";

/// A console with one command, so traces are short to spell.
const CONSOLE: &str = "
inductive Cmd { Ask, Say(n: Nat) }
fn Resp(c: Cmd) → Type { match c { Ask => Nat, Say(_) => True } }
fn C() → Events { Events(Cmd, λ c => Resp(c)) }
fn ask() → ITree<Nat>(C()) { ITree::trigger(C(), Ask) }
";

/// Traces the tree cannot produce: a wrong return after the right answer, and
/// a pending command it never issues (`answered` in the probes is the trace
/// it does produce).
#[test]
fn a_trace_is_what_the_tree_can_do() {
    for (name, case) in [
        ("itree_trace_wrong_return", "theorem bad(): IsTrace<Nat>(C(), ask(), TAns(Ask, 4, TRet(5))) { Answered(4, TRet(5), refl, Returned(refl)) }"),
        ("itree_trace_wrong_command", "theorem bad(): IsTrace<Nat>(C(), ask(), TCall(Say(1))) { Pending(refl) }"),
    ] {
        support::assert_refused(&mut base(), name, &format!("{IMPORTS}{CONSOLE}{case}"), Refusal::Kernel);
    }
}

/// The spin proof's induction goes through for a loop that only goes round
/// (`Program::spin_diverges`) and is refused for one that breaks.
#[test]
fn divergence_is_refused_for_a_loop_that_breaks() {
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
    support::assert_refused(&mut base(), "itree_spin_breaks", &src, Refusal::Mismatch);
}
