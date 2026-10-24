//! One computed weakest precondition over the label assembler's items, and
//! the loop rule over it (`issues/native-one-wp.md`,
//! `issues/native-loop-rule.md`; round S2 of
//! `docs/native-program-logic-design.md`).
//!
//!  1. the modules check: `Syscall` and `Proved` in `x86_64_asm`, the
//!     computed `Wp` with `wp_runs`/`wp_sound`/`loop_at`
//!     (`linux_x86_64_wp`), and the process image on the byte memory model
//!     with a program's view of its page or frame (`linux_x86_64_image`,
//!     `linux_x86_64_byte_memory`);
//!  2. the I/O loop control, a few hand-written items proved through
//!     `loop_at` and measured by its trace: read stdin to its end, exit 0,
//!     from the head and from the entry of the process Linux loads;
//!  3. negative controls: its exit claimed with the wrong status, and its
//!     entry claimed past a header one byte short.
//!
//! The pure loop control is `linux_wp_count.rs`, a file (and so a test
//! process, under its own CPU rail) of its own: on a cold image store each
//! process elaborates the Linux prefix itself (`issues/linux-wp-cold-rail.md`).

use crate::read_loop_fixture::checker_with;

// The byte model's modules come last, so the list up to `linux_x86_64_wp`
// stays the prefix other targets replay.
pub(crate) const MODULES: &[(&str, &str)] = &[
    ("x86_64_step_forms", include_str!("../../../lib/std/arch/x86_64/x86_64_step_forms.hthr")),
    ("linux_x86_64_determinism", include_str!("../../../lib/std/os/linux/linux_x86_64_determinism.hthr")),
    ("itree", include_str!("../../../lib/std/itree/itree.hthr")),
    ("itree_trace", include_str!("../../../lib/std/itree/itree_trace.hthr")),
    ("linux_trees", include_str!("../../../lib/std/os/linux/linux_trees.hthr")),
    ("linux_x86_64_sim", include_str!("../../../lib/std/os/linux/linux_x86_64_sim.hthr")),
    ("x86_64_asm", include_str!("../../../lib/std/arch/x86_64/x86_64_asm.hthr")),
    ("x86_64_asm_runs", include_str!("../../../lib/std/arch/x86_64/x86_64_asm_runs.hthr")),
    ("linux_x86_64_wp", include_str!("../../../lib/std/os/linux/linux_x86_64_wp.hthr")),
    ("result", include_str!("../../../lib/std/core/result.hthr")),
    ("vector", include_str!("../../../lib/std/data/vector.hthr")),
    ("bitvec_bytes", include_str!("../../../lib/std/bitvec/bitvec_bytes.hthr")),
    ("memory", include_str!("../../../lib/std/machine/memory.hthr")),
    ("x86_64_byte_memory", include_str!("../../../lib/std/arch/x86_64/x86_64_byte_memory.hthr")),
    ("linux_x86_64_byte_memory", include_str!("../../../lib/std/os/linux/linux_x86_64_byte_memory.hthr")),
    ("linux_x86_64_image", include_str!("../../../lib/std/os/linux/linux_x86_64_image.hthr")),
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

// The theorem after `comment` in the drain fixture, changed by `edit`, as a
// module of its own over the fixture.
fn drain_variant(comment: &str, edit: impl Fn(&str) -> String) -> String {
    let start = DRAIN.find(comment).expect("the theorem's comment");
    let end = DRAIN[start..].find("\n}\n").map(|i| start + i + 3).expect("the theorem's end");
    format!("import linux_wp_drain;\n{}\n{}",
        DRAIN[..start].lines().filter(|l| l.starts_with("import")).collect::<Vec<_>>().join("\n"),
        edit(&DRAIN[start..end]))
}

// The loop reads to the end of its input and exits 0, from its head and from
// the loaded process's entry; claimed to exit 1, the same exit proof is
// refused, and so is the entry proof past a header one byte short.
#[test]
fn the_io_loop_reads_to_the_end_and_exits() {
    let mut e = checker_with(MODULES);
    if let Err(err) = e.elab_module_source("linux_wp_drain", DRAIN) {
        panic!("{}", err.render(DRAIN));
    }
    let wrong = drain_variant("// The exit:", |s| s.replace("theorem drain_exit(", "theorem drain_exit_one(")
        .replace("Sim(X86Profile::io().linux(), Ret(BitVec::ofNat(0)), state)", "Sim(X86Profile::io().linux(), Ret(BitVec::ofNat(1)), state)")
        .replace("Ret(BitVec::ofNat(0)), page, state", "Ret(BitVec::ofNat(1)), page, state"));
    match e.elab_module_source("linux_wp_drain_exit_one", &wrong) {
        Ok(()) => panic!("an exit 0 passed off as exit 1 should be refused"),
        Err(err) => assert_refused("linux_wp_drain_exit_one", &err.render(&wrong)),
    }
    let short = drain_variant("// The entry:", |s| s.replace("theorem drain_entry(", "theorem drain_entry_short(")
        .replace("long: header.len() = 232", "long: header.len() = 231"));
    match e.elab_module_source("linux_wp_drain_entry_short", &short) {
        Ok(()) => panic!("an entry past a 231-byte header should be refused"),
        Err(err) => assert_refused("linux_wp_drain_entry_short", &err.render(&short)),
    }
}
