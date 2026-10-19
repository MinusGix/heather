// The per-file command's library (lib/elf64_command.hthr) and everything it
// stands on, in dependency order. Cold, the whole list is more than one
// process's CPU rail, so `semantic_command_warmup` populates it in two
// bounded processes before the suite's parallel phase: the filter half (to
// the stat pass), then the rest. A test then replays the list, or the list
// without its last module when it re-checks a changed copy of the command.
pub const COMMAND_PREFIX: &[(&str, &str)] = &[
    ("logic", include_str!("../../../../lib/std/logic.hthr")),
    ("bool", include_str!("../../../../lib/std/bool.hthr")),
    ("nat", include_str!("../../../../lib/std/nat.hthr")),
    ("option", include_str!("../../../../lib/std/option.hthr")),
    ("pair", include_str!("../../../../lib/std/pair.hthr")),
    ("list", include_str!("../../../../lib/std/list.hthr")),
    ("algebra", include_str!("../../../../lib/std/algebra.hthr")),
    ("int", include_str!("../../../../lib/std/int.hthr")),
    ("bitvec", include_str!("../../../../lib/std/bitvec.hthr")),
    ("omega", include_str!("../../../../lib/std/omega.hthr")),
    ("bitvec_nat", include_str!("../../../../lib/std/bitvec/bitvec_nat.hthr")),
    ("bitvec_omega", include_str!("../../../../lib/std/bitvec/bitvec_omega.hthr")),
    ("relation", include_str!("../../../../lib/std/relation.hthr")),
    ("relation_props", include_str!("../../../../lib/std/relation_props.hthr")),
    ("location", include_str!("../../../../lib/std/location.hthr")),
    ("certified_lookup", include_str!("../../../../lib/std/certified_lookup.hthr")),
    ("x86_64", include_str!("../../../../lib/std/arch/x86_64/x86_64.hthr")),
    ("x86_64_fetch", include_str!("../../../../lib/std/arch/x86_64/x86_64_fetch.hthr")),
    ("x86_64_store", include_str!("../../../../lib/std/arch/x86_64/x86_64_store.hthr")),
    ("decimal_line", include_str!("../../../../lib/decimal_line.hthr")),
    ("command_program", include_str!("../../../../lib/command_program.hthr")),
    ("x86_64_block", include_str!("../../../../lib/std/arch/x86_64/x86_64_block.hthr")),
    ("linux_x86_64_entry", include_str!("../../../../lib/linux_x86_64_entry.hthr")),
    ("x86_64_structured_block", include_str!("../../../../lib/std/arch/x86_64/x86_64_structured_block.hthr")),
    ("x86_64_data_read", include_str!("../../../../lib/std/arch/x86_64/x86_64_data_read.hthr")),
    ("x86_64_access_code", include_str!("../../../../lib/std/arch/x86_64/x86_64_access_code.hthr")),
    ("x86_64_access_memory", include_str!("../../../../lib/std/arch/x86_64/x86_64_access_memory.hthr")),
    ("x86_64_fetched_code", include_str!("../../../../lib/std/arch/x86_64/x86_64_fetched_code.hthr")),
    ("linux_x86_64_io", include_str!("../../../../lib/linux_x86_64_io.hthr")),
    ("function_ir_loop", include_str!("../../../../lib/function_ir_loop.hthr")),
    ("elf64_io", include_str!("../../../../lib/elf64_io.hthr")),
    ("function_ir", include_str!("../../../../lib/function_ir.hthr")),
    ("x86_64_control_block", include_str!("../../../../lib/std/arch/x86_64/x86_64_control_block.hthr")),
    ("x86_64_control_flow", include_str!("../../../../lib/std/arch/x86_64/x86_64_control_flow.hthr")),
    ("function_ir_x86_support", include_str!("../../../../lib/function_ir_x86_support.hthr")),
    ("function_ir_loop_x86", include_str!("../../../../lib/function_ir_loop_x86.hthr")),
    ("function_ir_loop_trace", include_str!("../../../../lib/function_ir_loop_trace.hthr")),
    ("x86_64_layout", include_str!("../../../../lib/std/arch/x86_64/x86_64_layout.hthr")),
    ("elf64_read_pieces", include_str!("../../../../lib/elf64_read_pieces.hthr")),
    ("elf64_print_pieces", include_str!("../../../../lib/elf64_print_pieces.hthr")),
    ("stream_filter", include_str!("../../../../lib/stream_filter.hthr")),
    ("filter_step_piece", include_str!("../../../../lib/filter_step_piece.hthr")),
    ("elf64_write_loop", include_str!("../../../../lib/elf64_write_loop.hthr")),
    ("elf64_read_filter", include_str!("../../../../lib/elf64_read_filter.hthr")),
    ("x86_64_asm", include_str!("../../../../lib/std/arch/x86_64/x86_64_asm.hthr")),
    ("elf64_runs", include_str!("../../../../lib/elf64_runs.hthr")),
    ("elf64_format_width", include_str!("../../../../lib/elf64_format_width.hthr")),
    ("elf64_arg_scan", include_str!("../../../../lib/elf64_arg_scan.hthr")),
    ("elf64_operand_cursor", include_str!("../../../../lib/elf64_operand_cursor.hthr")),
    ("elf64_stretch", include_str!("../../../../lib/elf64_stretch.hthr")),
    ("elf64_stat_width", include_str!("../../../../lib/elf64_stat_width.hthr")),
    ("elf64_command_events", include_str!("../../../../lib/elf64_command_events.hthr")),
    ("elf64_command_output", include_str!("../../../../lib/elf64_command_output.hthr")),
    ("elf64_frame", include_str!("../../../../lib/elf64_frame.hthr")),
    ("elf64_straight", include_str!("../../../../lib/elf64_straight.hthr")),
    ("elf64_row_fields", include_str!("../../../../lib/elf64_row_fields.hthr")),
    ("elf64_command", include_str!("../../../../lib/elf64_command.hthr")),
];

/// The first warm-up process's share: the list through this module. Named
/// rather than counted, so a module inserted earlier in the list cannot
/// silently move the split (an index did, by one module, in #39). It sits
/// before the stat pass, which with the command itself dominates a cold run;
/// that leaves the two processes about even, each well inside one rail.
#[allow(dead_code)]
pub const FILTER_HALF_THROUGH: &str = "elf64_operand_cursor";

/// The list through `FILTER_HALF_THROUGH`.
#[allow(dead_code)]
pub fn filter_half() -> &'static [(&'static str, &'static str)] {
    let end = COMMAND_PREFIX
        .iter()
        .position(|&(name, _)| name == FILTER_HALF_THROUGH)
        .expect("FILTER_HALF_THROUGH names a module of COMMAND_PREFIX");
    &COMMAND_PREFIX[..=end]
}
