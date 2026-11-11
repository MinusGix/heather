use crate::{common, support};

// What the native tests stand on past the x86 prefix: FunctionIR's loops,
// fetched execution, the store and stack forms, the Linux I/O model (whose
// steps are both), and the set laws function_ir_eval registers. Generated
// from the imports: edit the roots on the marker, then run
// `scripts/lib-closures --fix`.
// lib-closure: x86_64_data_read function_ir_loop x86_64_fetch x86_64_layout elf64 linux_x86_64_io set_ops minus x86_64_block function_ir
pub const READ_LOOP: &[(&str, &str)] = &[
    ("x86_64_data_read", include_str!("../../../../lib/std/arch/x86_64/x86_64_data_read.hthr")),
    ("function_ir_loop", include_str!("../../../../lib/native/function_ir/function_ir_loop.hthr")),
    ("x86_64_fetch", include_str!("../../../../lib/std/arch/x86_64/x86_64_fetch.hthr")),
    ("bitvec_nat", include_str!("../../../../lib/std/bitvec/bitvec_nat.hthr")),
    ("bitvec_signed", include_str!("../../../../lib/std/bitvec/bitvec_signed.hthr")),
    ("transition", include_str!("../../../../lib/std/relation/transition.hthr")),
    ("x86_64_fetched_code", include_str!("../../../../lib/std/arch/x86_64/x86_64_fetched_code.hthr")),
    ("x86_64_layout", include_str!("../../../../lib/std/arch/x86_64/x86_64_layout.hthr")),
    ("elf64", include_str!("../../../../lib/std/os/linux/elf64.hthr")),
    ("linux_calls", include_str!("../../../../lib/std/os/linux/linux_calls.hthr")),
    ("linux_x86_64_entry", include_str!("../../../../lib/std/os/linux/linux_x86_64_entry.hthr")),
    ("x86_64_store", include_str!("../../../../lib/std/arch/x86_64/x86_64_store.hthr")),
    ("result", include_str!("../../../../lib/std/core/result.hthr")),
    ("vector", include_str!("../../../../lib/std/data/vector.hthr")),
    ("bitvec_bytes", include_str!("../../../../lib/std/bitvec/bitvec_bytes.hthr")),
    ("dec_set", include_str!("../../../../lib/std/data/set/dec_set.hthr")),
    ("span_set", include_str!("../../../../lib/std/data/set/span_set.hthr")),
    ("memory", include_str!("../../../../lib/std/machine/memory.hthr")),
    ("x86_64_stack", include_str!("../../../../lib/std/arch/x86_64/x86_64_stack.hthr")),
    ("linux_x86_64_io", include_str!("../../../../lib/std/os/linux/linux_x86_64_io.hthr")),
    ("set_solve", include_str!("../../../../lib/std/data/set/set_solve.hthr")),
    ("set_ops", include_str!("../../../../lib/std/data/set/set_ops.hthr")),
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
