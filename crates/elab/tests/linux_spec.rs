//! Linux's calls as a container of events, trees over it, and `Sim`
//! (`issues/native-linux-spec.md`, round S1 of
//! `docs/native/native-program-logic-design.md`; submilestone `hih-pl-spec`).
//!
//!  1. the closure checks: `linux_calls` under the re-founded
//!     `linux_x86_64_io` and determinism, `linux_trees`, `linux_x86_64_sim`,
//!     `stream_filter_spec`, and the client showcase, which runs `tr`'s spec
//!     on one byte, sizes its reads, and reads stdout off a machine's run;
//!  2. the kit is *there*, named one by one;
//!  3. the four axes of `docs/testing-generated-terms.md`: literal and open
//!     answers and bytes, a size-free and a sized container, traces in
//!     checking position, and negative controls — an answer longer than the
//!     read, a filter trace that writes the wrong bytes or exits 0 after a
//!     failure, and a read of no bytes passed off as implementing a spec.

use std::cell::OnceCell;
use std::sync::Mutex;

use heather_elab::{Elaborator, SemanticImage};

use crate::read_loop_fixture::checker_with;

const MODULES: &[(&str, &str)] = &[
    ("x86_64_step_forms", include_str!("../../../lib/std/arch/x86_64/x86_64_step_forms.hthr")),
    ("linux_x86_64_determinism", include_str!("../../../lib/std/os/linux/linux_x86_64_determinism.hthr")),
    ("itree", include_str!("../../../lib/std/itree/itree.hthr")),
    ("itree_trace", include_str!("../../../lib/std/itree/itree_trace.hthr")),
    ("call_system", include_str!("../../../lib/std/itree/call_system.hthr")),
    ("linux_trees", include_str!("../../../lib/std/os/linux/linux_trees.hthr")),
    ("itree_sim", include_str!("../../../lib/std/itree/itree_sim.hthr")),
    ("linux_trees_sim", include_str!("../../../lib/std/os/linux/linux_trees_sim.hthr")),
    ("linux_x86_64_sim", include_str!("../../../lib/std/os/linux/linux_x86_64_sim.hthr")),
    ("stream_filter", include_str!("../../../lib/native/stream_filter.hthr")),
    ("stream_filter_spec", include_str!("../../../lib/native/stream_filter_spec.hthr")),
];

static PREFIX_LOAD: Mutex<()> = Mutex::new(());

thread_local! {
    static BASE: OnceCell<SemanticImage> = const { OnceCell::new() };
}

fn base() -> Elaborator {
    BASE.with(|base| {
        base.get_or_init(|| {
            let _serial = PREFIX_LOAD.lock().unwrap_or_else(|poisoned| poisoned.into_inner());
            checker_with(MODULES).semantic_image()
        })
        .elaborator()
    })
}

fn check(e: &mut Elaborator, name: &str, src: &str) {
    if let Err(err) = e.elab_module_source(name, src) {
        panic!("{}", err.render(src));
    }
}

/// Refused where it is wrong: a proof that does not prove the statement,
/// not a missing name or a parse.
fn refused(name: &str, src: &str) {
    let mut e = base();
    match e.elab_module_source(name, src) {
        Ok(()) => panic!("{name} should be refused"),
        Err(err) => {
            let msg = err.render(src);
            assert!(msg.contains("NotConvertible") || msg.contains("is expected here"), "{name}: {msg}");
            assert!(!msg.contains("unbound") && !msg.contains("ambiguous") && !msg.contains("parse"), "{name}: {msg}");
        }
    }
}

const IMPORTS: &str = "import linux_calls; import linux_x86_64_io; import linux_x86_64_determinism; import linux_trees; \
    import linux_x86_64_sim; import stream_filter; import stream_filter_spec; import itree; import itree_trace; \
    import x86_64; import bitvec; import list; import logic; import nat;\n";

#[test]
fn the_spec_and_its_client_check() {
    let mut e = base();
    check(&mut e, "linux_spec_client", include_str!("../../../docs/showcase/linux_spec_client.hthr"));
}

const KIT: &[&str] = &[
    // Calls, answers, events.
    "LinuxCmd::Resp", "LinuxCmd::Answers", "LinuxCmd::sent", "LinuxCmd::received", "sent_to", "received_from",
    // How a process makes a call, and how Linux resumes it.
    "LinuxAsks", "LinuxBuffers", "LinuxRequests", "LinuxLeaves", "linux_answered", "LinuxResumes", "LinuxAnswered",
    "LinuxExits", "linux_leaves_nil", "linux_resumes_mono", "linux_answered_respects", "LinuxRuns", "linux_runs_call",
    // Determinism over the shared definitions.
    "LinuxResumed", "LinuxRun", "SameAnswer", "call_meets", "linux_meets", "runs_as_determined", "linux_runs_determine", "linux_runs_every",
    // The containers and their traces.
    "Events::linux", "Events::linux_spec", "Trace::LinuxValid", "Trace::linux_events", "Trace::sent", "Trace::received",
    "Trace::sent_events", "Trace::received_events", "Trace::Returns", "Trace::ReturnsWith", "Trace::returns_of_with",
    "ITree::next",
    // Size-free specs.
    "LinuxCmd::forget", "LinuxCmd::forget_answer", "Trace::forget", "Trace::AsksSome", "Trace::forget_sent",
    "Trace::forget_received", "Trace::forget_returns_with", "ITree::Implements", "Program::Implements",
    "Program::implements_of_trees", "ITree::implements_trace", "LinuxCmd::sized", "EventMap::linux_sized",
    "ITree::sized", "ITree::implements_sized",
    // The judgment.
    "RunsAs", "Sim", "SimProgram", "SimNext", "runs_as_back", "sim_back", "sim_cut", "sim_tau", "sim_ret", "sim_vis",
    "sim_of_next", "sim_of_traces", "sim_of_below", "sim_of_same", "Program::sim_produces", "Program::sim_refines",
    "runs_as_linux_runs", "linux_runs_runs_as", "sim_linux_runs", "sim_every_run", "sim_run_sends",
    // Its converse: a run is the tree's, up to a cut.
    "IsCutTrace", "IsTrace::of_cut", "asks_meet", "exits_not_asks", "linux_runs_valid", "SimRelated", "RunOf",
    "sim_related_run", "sim_run_of", "Program::sim_run_at", "Program::sim_linux_runs_at", "Program::sim_run_produces",
    // A filter's spec.
    "filter_pass", "filter_tree", "filter_spec", "tr_spec", "filter_sends", "filter_spec_sends", "tr_sends",
    "filter_implementation_sends",
];

#[test]
fn the_kit_is_there() {
    let mut e = base();
    let mut src = format!("{IMPORTS} fn kit() → Nat {{\n");
    for (i, item) in KIT.iter().enumerate() {
        src.push_str(&format!("    let item{i} = {item};\n"));
    }
    src.push_str("    0\n}\n");
    check(&mut e, "linux_spec_kit", &src);
}

// Linux answers a read with as many bytes as it asked for or fewer, at a
// literal size and at an open one; never more.
#[test]
fn a_read_is_answered_up_to_its_size() {
    let mut e = base();
    check(
        &mut e,
        "linux_read_answers",
        &format!(
            "{IMPORTS}
            theorem whole(fd: BitVec(64), b: BitVec(8)): ReadCmd(fd, 2).Answers(ReadBytes([b, b])) {{ trivial }}
            theorem short(fd: BitVec(64), b: BitVec(8)): ReadCmd(fd, 2).Answers(ReadBytes([b])) {{ trivial }}
            theorem end(fd: BitVec(64), max: Nat): ReadCmd(fd, max).Answers(ReadBytes(Nil)) {{ trivial }}
            theorem forgets(fd: BitVec(64), max: Nat): ReadCmd(fd, max).forget() = ReadCmd(fd, trivial) {{ refl }}"
        ),
    );
    refused(
        "linux_read_overlong",
        &format!(
            "{IMPORTS}
            theorem bad(fd: BitVec(64), b: BitVec(8)): ReadCmd(fd, 1).Answers(ReadBytes([b, b])) {{ trivial }}"
        ),
    );
}

const ONE_BYTE: &str = "
fn wrong(f: BitVec(8) → BitVec(8), x: BitVec(8)) → Trace<BitVec(64)>(Events::linux_spec()) {
    TAns(ReadCmd(BitVec::ofNat(0), trivial), ReadBytes([x]),
        TAns(WriteCmd(BitVec::ofNat(1), [x]), Wrote(1),
            TAns(ReadCmd(BitVec::ofNat(0), trivial), ReadBytes(Nil), TRet(filter_ok()))))
}
fn failed(x: BitVec(8)) → Trace<BitVec(64)>(Events::linux_spec()) {
    TAns(ReadCmd(BitVec::ofNat(0), trivial), ReadFailed(5), TRet(filter_ok()))
}
";

// The spec writes the mapped bytes, at an open byte map and byte, and exits 1
// after a failed read; the trace next to each that the tree cannot produce is
// refused.
#[test]
fn tr_writes_what_it_mapped() {
    refused(
        "linux_tr_writes_unmapped",
        &format!(
            "{IMPORTS}{ONE_BYTE}
            theorem bad(f: BitVec(8) → BitVec(8), x: BitVec(8)): IsTrace(Events::linux_spec(), tr_spec(f).at(4), wrong(f, x)) {{
                let end: Trace<BitVec(64)>(Events::linux_spec()) = TRet(filter_ok());
                let wrote: Trace<BitVec(64)>(Events::linux_spec()) = TAns(ReadCmd(BitVec::ofNat(0), trivial), ReadBytes(Nil), end);
                let read: Trace<BitVec(64)>(Events::linux_spec()) = TAns(WriteCmd(BitVec::ofNat(1), [x]), Wrote(1), wrote);
                Answered(ReadBytes([x]), read, refl, Answered(Wrote(1), wrote, refl, Answered(ReadBytes(Nil), end, refl, Returned(refl))))
            }}"
        ),
    );
    refused(
        "linux_tr_failure_exits_zero",
        &format!(
            "{IMPORTS}{ONE_BYTE}
            theorem bad(f: BitVec(8) → BitVec(8), x: BitVec(8)): IsTrace(Events::linux_spec(), tr_spec(f).at(2), failed(x)) {{
                Answered(ReadFailed(5), TRet(filter_ok()), refl, Returned(refl))
            }}"
        ),
    );
    let mut e = base();
    check(
        &mut e,
        "linux_tr_failure_exits_one",
        &format!(
            "{IMPORTS}
            theorem ok(f: BitVec(8) → BitVec(8)): IsTrace(Events::linux_spec(), tr_spec(f).at(1),
                TAns(ReadCmd(BitVec::ofNat(0), trivial), ReadFailed(5), TRet(filter_failed()))) {{
                Answered(ReadFailed(5), TRet(filter_failed()), refl, Returned(refl))
            }}"
        ),
    );
}

// A spec's reads are sized only by a count of at least one byte: a read of
// none answers empty without the input having ended.
#[test]
fn a_read_of_nothing_implements_nothing() {
    refused(
        "linux_sized_zero",
        &format!(
            "{IMPORTS}
            theorem bad(f: BitVec(8) → BitVec(8), n: Nat): ITree::Implements(ITree::sized(0, tr_spec(f).at(n)), tr_spec(f).at(n)) {{
                ITree::implements_sized(0, trivial, tr_spec(f).at(n))
            }}"
        ),
    );
}

// The machine side: a cut claims nothing, and a returned tree claims an exit
// with its status, which `Sim` passes to the run of its one trace.
#[test]
fn sim_at_a_cut_and_a_return() {
    let mut e = base();
    check(
        &mut e,
        "linux_sim_rules",
        &format!(
            "{IMPORTS}
            theorem cut<M>(io: LinuxIo<M>, s: MachineState<M>): Sim<M>(io, Cut, s) {{ sim_cut(io, s) }}
            theorem exits<M>(io: LinuxIo<M>, s: MachineState<M>, status: BitVec(64), sim: Sim<M>(io, Ret(status), s)):
                LinuxRuns(io, [ExitEvent(status)], s) {{
                sim_linux_runs(io, Ret(status), s, sim, TRet(status), Returned(refl), trivial, trivial)
            }}"
        ),
    );
}

// The loop rule for Linux (`linux_trees_sim`): a source loop whose passes
// make no call implements a spec loop that leaves at once, the source's
// state a counter and the spec's of another type; a spec that leaves with
// another status is refused.
#[test]
fn a_silent_loop_implements_a_spec_that_leaves() {
    const DOWN: &str = "
        fn down_body(a: Nat) → ITree<Step<Nat, Nat>>(Events::linux()) {
            match a { Zero => Ret(Break(0)), Succ(m) => Ret(Continue(m)) }
        }
        fn now_body(u: True) → ITree<Step<True, Nat>>(Events::linux_spec()) { Ret(Break(0)) }
    ";
    let mut e = base();
    check(
        &mut e,
        "linux_sim_loop",
        &format!(
            "{IMPORTS} import itree_sim; import linux_trees_sim;{DOWN}
            theorem down_pass(a: Nat, u: True):
                ITree::PassSim<Nat, True, Nat>(Events::linux(), Events::linux_spec(), TraceMap::linux_forget(),
                    Contract::linux(), λ x y => True, λ x => down_body(x), λ y => now_body(y), a, u)
            {{
                match a {{
                    Zero => Inl(SimRet(Break(0), refl, refl)),
                    Succ(_) => Inr(SimRet(Continue(u), refl, trivial)),
                }}
            }}
            theorem down_implements(a: Nat):
                Program::Implements<Nat>(Program::iter<Nat, Nat>(Events::linux(), λ x => down_body(x), a),
                    Program::iter<True, Nat>(Events::linux_spec(), λ y => now_body(y), trivial))
            {{
                Program::implements_iter(λ x y => True, λ x => down_body(x), λ y => now_body(y),
                    λ x y r => down_pass(x, y), a, trivial, trivial)
            }}"
        ),
    );
    refused(
        "linux_sim_loop_wrong",
        &format!(
            "{IMPORTS} import itree_sim; import linux_trees_sim;{DOWN}
            fn one_body(u: True) → ITree<Step<True, Nat>>(Events::linux_spec()) {{ Ret(Break(1)) }}
            theorem bad(): ITree::PassSim<Nat, True, Nat>(Events::linux(), Events::linux_spec(), TraceMap::linux_forget(),
                Contract::linux(), λ x y => True, λ x => down_body(x), λ y => one_body(y), 0, trivial)
            {{
                Inl(SimRet(Break(1), refl, refl))
            }}"
        ),
    );
}
