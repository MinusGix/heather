//! One computed weakest precondition over the label assembler's items, and
//! the loop rule over it (`issues/native-one-wp.md`,
//! `issues/native-loop-rule.md`; round S2 of
//! `docs/native-program-logic-design.md`).
//!
//!  1. the modules check: `Syscall` and `Proved` in `x86_64_asm`, the
//!     computed `Wp` with `wp_runs`/`wp_sound`/`loop_at`
//!     (`linux_x86_64_wp`), and the page and frame views
//!     (`linux_x86_64_views`);
//!  2. the I/O loop control, a few hand-written items proved through
//!     `loop_at` and measured by its trace: read stdin to its end, exit 0;
//!  3. a negative control: its exit claimed with the wrong status.
//!
//! The pure loop control is `linux_wp_count.rs`, a file (and so a test
//! process, under its own CPU rail) of its own: this one's pass is the
//! elaborator's whnf workload (`issues/elab-whnf-copies-straight-continuations.md`)
//! and takes most of the rail by itself.

use crate::read_loop_fixture::checker_with;

pub(crate) const MODULES: &[(&str, &str)] = &[
    ("x86_64_step_forms", include_str!("../../../lib/std/arch/x86_64/x86_64_step_forms.hthr")),
    ("linux_x86_64_determinism", include_str!("../../../lib/linux_x86_64_determinism.hthr")),
    ("itree", include_str!("../../../lib/std/itree.hthr")),
    ("itree_trace", include_str!("../../../lib/std/itree_trace.hthr")),
    ("linux_trees", include_str!("../../../lib/linux_trees.hthr")),
    ("linux_x86_64_sim", include_str!("../../../lib/linux_x86_64_sim.hthr")),
    ("x86_64_stack", include_str!("../../../lib/std/arch/x86_64/x86_64_stack.hthr")),
    ("x86_64_asm", include_str!("../../../lib/std/arch/x86_64/x86_64_asm.hthr")),
    ("x86_64_asm_runs", include_str!("../../../lib/std/arch/x86_64/x86_64_asm_runs.hthr")),
    ("linux_x86_64_wp", include_str!("../../../lib/linux_x86_64_wp.hthr")),
    ("linux_x86_64_views", include_str!("../../../lib/linux_x86_64_views.hthr")),
];

const DRAIN: &str = include_str!("fixtures/linux_wp_drain.hthr");

/// Refused where it is wrong: the first error is the kernel's or the
/// checker's refusal, not a missing name or a parse. Later errors cascade
/// from the refused declaration.
pub(crate) fn assert_refused(name: &str, msg: &str) {
    let first = msg.split("error:").nth(1).unwrap_or(msg);
    assert!(first.contains("NotConvertible") || first.contains("is expected here"), "{name}: {msg}");
    assert!(!first.contains("unbound") && !first.contains("ambiguous") && !first.contains("parse"), "{name}: {msg}");
}

// The loop reads to the end of its input and exits 0; claimed to exit 1, the
// same exit proof is refused.
#[test]
fn the_io_loop_reads_to_the_end_and_exits() {
    let mut e = checker_with(MODULES);
    if let Err(err) = e.elab_module_source("linux_wp_drain", DRAIN) {
        panic!("{}", err.render(DRAIN));
    }
    let start = DRAIN.find("// The exit:").expect("the exit's comment");
    let end = DRAIN[start..].find("\n}\n").map(|i| start + i + 3).expect("the exit's end");
    let wrong = format!("import linux_wp_drain;\n{}\n{}",
        DRAIN[..start].lines().filter(|l| l.starts_with("import")).collect::<Vec<_>>().join("\n"),
        DRAIN[start..end].replace("theorem drain_exit(", "theorem drain_exit_one(")
            .replace("Sim(io_linux(), Ret(BitVec::ofNat(0)), state)", "Sim(io_linux(), Ret(BitVec::ofNat(1)), state)")
            .replace("Ret(BitVec::ofNat(0)), page, state", "Ret(BitVec::ofNat(1)), page, state"));
    match e.elab_module_source("linux_wp_drain_exit_one", &wrong) {
        Ok(()) => panic!("an exit 0 passed off as exit 1 should be refused"),
        Err(err) => assert_refused("linux_wp_drain_exit_one", &err.render(&wrong)),
    }
}
