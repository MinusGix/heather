use crate::{common, support};

// The read-once process shape and what it stands on
// (docs/native-first-program-design.md): fetched execution, the basic Linux
// trace, the profile's memory view, and the process theorem itself.
pub const READ_LOOP: &[(&str, &str)] = &[
    ("x86_64_structured_block", include_str!("../../../../lib/std/arch/x86_64/x86_64_structured_block.hthr")),
    ("x86_64_data_read", include_str!("../../../../lib/std/arch/x86_64/x86_64_data_read.hthr")),
    ("x86_64_access_code", include_str!("../../../../lib/std/arch/x86_64/x86_64_access_code.hthr")),
    ("x86_64_access_memory", include_str!("../../../../lib/std/arch/x86_64/x86_64_access_memory.hthr")),
    ("bitvec_nat", include_str!("../../../../lib/std/bitvec/bitvec_nat.hthr")),
    ("function_ir_loop", include_str!("../../../../lib/function_ir_loop.hthr")),
    ("function_ir_loop_x86", include_str!("../../../../lib/function_ir_loop_x86.hthr")),
    ("function_ir_loop_trace", include_str!("../../../../lib/function_ir_loop_trace.hthr")),
    ("omega", include_str!("../../../../lib/std/omega.hthr")),
    ("x86_64_fetch", include_str!("../../../../lib/std/arch/x86_64/x86_64_fetch.hthr")),
    ("x86_64_fetched_code", include_str!("../../../../lib/std/arch/x86_64/x86_64_fetched_code.hthr")),
    ("x86_64_layout", include_str!("../../../../lib/std/arch/x86_64/x86_64_layout.hthr")),
    ("elf64", include_str!("../../../../lib/elf64.hthr")),
    ("linux_x86_64_entry", include_str!("../../../../lib/linux_x86_64_entry.hthr")),
    ("x86_64_store", include_str!("../../../../lib/std/arch/x86_64/x86_64_store.hthr")),
    ("linux_calls", include_str!("../../../../lib/linux_calls.hthr")),
    ("linux_x86_64_io", include_str!("../../../../lib/linux_x86_64_io.hthr")),
    ("elf64_io", include_str!("../../../../lib/elf64_io.hthr")),
];

pub fn checker() -> heather_elab::Elaborator { checker_with(&[]) }

// The x86 prefix, then `READ_LOOP`, then `extra`, in that order: checked
// library modules, replayed from the shared semantic test images
// (`support::semantic_test_base`) instead of elaborated from source by every
// test (issues/suite-tests-reelaborate-library-modules.md). A cold or
// changed list is checked from source once, by the first test to ask for
// it, and stored; the full lane's exact policy re-checks every one with
// the current frontend. What a test elaborates after this — its client,
// generated pieces, mutants — reaches the real kernel as before.
pub fn checker_with(extra: &[(&str, &str)]) -> heather_elab::Elaborator {
    let modules: Vec<(&str, &str)> = common::MODULES.iter().chain(READ_LOOP).chain(extra).copied().collect();
    support::semantic_test_base(&modules)
}
