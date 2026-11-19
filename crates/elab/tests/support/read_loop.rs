use crate::{common, support};

// What the native tests stand on past the x86 prefix: FunctionIR's loops,
// fetched execution, the store and stack forms, the Linux I/O model (whose
// steps are both), and the set laws and the simp set function_ir_eval
// registers (`simp_laws`). Generated
// from the imports: edit the roots on the marker, then run
// `scripts/lib-closures --fix`.
// lib-closure: x86_64_data_read function_ir_loop x86_64_fetch x86_64_layout elf64 linux_x86_64_io set_ops simp_laws minus x86_64_block function_ir
pub const READ_LOOP: &[(&str, &str)] = &[
    ("x86_64_data_read", include_str!("../../../../lib/std/arch/x86_64/x86_64_data_read.hthr")),
    ("function_ir_loop", include_str!("../../../../lib/native/function_ir/function_ir_loop.hthr")),
    ("x86_64_fetch", include_str!("../../../../lib/std/arch/x86_64/x86_64_fetch.hthr")),
    ("transition", include_str!("../../../../lib/std/relation/transition.hthr")),
    ("x86_64_fetched_code", include_str!("../../../../lib/std/arch/x86_64/x86_64_fetched_code.hthr")),
    ("x86_64_layout", include_str!("../../../../lib/std/arch/x86_64/x86_64_layout.hthr")),
    ("elf64", include_str!("../../../../lib/std/os/linux/elf64.hthr")),
    ("linux_calls", include_str!("../../../../lib/std/os/linux/linux_calls.hthr")),
    ("linux_x86_64_entry", include_str!("../../../../lib/std/os/linux/linux_x86_64_entry.hthr")),
    ("x86_64_store", include_str!("../../../../lib/std/arch/x86_64/x86_64_store.hthr")),
    ("result", include_str!("../../../../lib/std/core/result.hthr")),
    ("dec_set", include_str!("../../../../lib/std/data/set/dec_set.hthr")),
    ("span_set", include_str!("../../../../lib/std/data/set/span_set.hthr")),
    ("memory", include_str!("../../../../lib/std/machine/memory.hthr")),
    ("x86_64_stack", include_str!("../../../../lib/std/arch/x86_64/x86_64_stack.hthr")),
    ("linux_x86_64_io", include_str!("../../../../lib/std/os/linux/linux_x86_64_io.hthr")),
    ("set_solve", include_str!("../../../../lib/std/data/set/set_solve.hthr")),
    ("set_ops", include_str!("../../../../lib/std/data/set/set_ops.hthr")),
    ("bitvec_concat", include_str!("../../../../lib/std/bitvec/bitvec_concat.hthr")),
    ("bitvec_shift_nat", include_str!("../../../../lib/std/bitvec/bitvec_shift_nat.hthr")),
    ("simp_laws", include_str!("../../../../lib/std/tactic/simp_laws.hthr")),
];

pub fn checker() -> heather_elab::Elaborator { checker_with(&[]) }

// The operation rows the lowering reads (`function_ir_operation_x86`) past
// the read loop's modules and what a block leaves (`x86_64_kept`), which a
// test lists ahead of them. Generated from the imports.
// lib-closure: function_ir_operation_x86 minus x86_64_data_read function_ir_loop x86_64_fetch x86_64_layout elf64 linux_x86_64_io set_ops simp_laws x86_64_block function_ir x86_64_kept
pub const OPERATION_ROWS: &[(&str, &str)] = &[
    ("bitvec_ring", include_str!("../../../../lib/std/bitvec/bitvec_ring.hthr")),
    ("bitvec_reciprocal", include_str!("../../../../lib/std/bitvec/bitvec_reciprocal.hthr")),
    ("function_ir_operation_x86", include_str!("../../../../lib/native/function_ir/function_ir_operation_x86.hthr")),
];

// The x86 prefix, then `READ_LOOP`, then `extra`, in that order: checked
// library modules, replayed from the shared semantic test images
// (`support::semantic_test_base`) instead of elaborated from source by every
// test (issues/suite-tests-reelaborate-library-modules.md). A cold or
// changed list is checked from source once, by the first test to ask for
// it, and stored; the full lane's exact policy re-checks every one with
// the current frontend. What a test elaborates after this — its client,
// generated pieces, mutants — reaches the real kernel as before.
/// The modules, with `OPERATION_ROWS` ahead of the lowering
/// (`function_ir_lower`), which reads them, where it is one of them.
pub fn with_operation_rows<'a>(modules: impl Iterator<Item = (&'a str, &'a str)>) -> Vec<(&'a str, &'a str)> {
    let mut out = Vec::new();
    for (name, source) in modules {
        if name == "function_ir_lower" {
            out.extend(OPERATION_ROWS.iter().copied());
        }
        out.push((name, source));
    }
    out
}

pub fn checker_with(extra: &[(&str, &str)]) -> heather_elab::Elaborator {
    support::semantic_test_base(&with_operation_rows(common::MODULES.iter().chain(READ_LOOP).chain(extra).copied()))
}
