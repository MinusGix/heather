// Bundled model sources shared by native compilation and certificate controls.
pub(super) const SUPPORT: &[(&str, &str)] = &[
    ("logic", include_str!("../../../../lib/std/logic.hthr")),
    ("bool", include_str!("../../../../lib/std/bool.hthr")),
    ("nat", include_str!("../../../../lib/std/nat.hthr")),
    ("option", include_str!("../../../../lib/std/option.hthr")),
    ("pair", include_str!("../../../../lib/std/pair.hthr")),
    ("list", include_str!("../../../../lib/std/list.hthr")),
    ("algebra", include_str!("../../../../lib/std/algebra.hthr")),
    ("int", include_str!("../../../../lib/std/int.hthr")),
    ("bitvec", include_str!("../../../../lib/std/bitvec.hthr")),
    ("relation", include_str!("../../../../lib/std/relation.hthr")),
    ("location", include_str!("../../../../lib/std/location.hthr")),
    ("certified_lookup", include_str!("../../../../lib/std/certified_lookup.hthr")),
    ("x86_64", include_str!("../../../../lib/std/arch/x86_64/model.hthr")),
    ("x86_64_block", include_str!("../../../../lib/std/arch/x86_64/block.hthr")),
    ("x86_64_control_block", include_str!("../../../../lib/std/arch/x86_64/control_block.hthr")),
    ("x86_64_control_flow", include_str!("../../../../lib/std/arch/x86_64/control_flow.hthr")),
    ("function_ir", include_str!("../../../../lib/function_ir.hthr")),
    ("function_ir_x86_support", include_str!("../../../../lib/function_ir_x86_support.hthr")),
    ("elf64", include_str!("../../../../lib/elf64.hthr")),
    ("linux_x86_64_entry", include_str!("../../../../lib/linux_x86_64_entry.hthr")),
    ("x86_64_fetch", include_str!("../../../../lib/std/arch/x86_64/fetch.hthr")),
    ("x86_64_fetch_block", include_str!("../../../../lib/std/arch/x86_64/fetch_block.hthr")),
    ("elf64_load", include_str!("../../../../lib/elf64_load.hthr")),
    ("x86_64_calls", include_str!("../../../../lib/std/arch/x86_64/calls.hthr")),
    ("x86_64_call_frame", include_str!("../../../../lib/std/arch/x86_64/call_frame.hthr")),
    ("x86_64_call_summary", include_str!("../../../../lib/std/arch/x86_64/call_summary.hthr")),
    ("elf64_calls", include_str!("../../../../lib/elf64_calls.hthr")),
    ("linux_x86_64_fetch", include_str!("../../../../lib/linux_x86_64_fetch.hthr")),
];

pub(super) const BUFFER_SUPPORT: &[(&str, &str)] = &[
    ("byte_cursor", include_str!("../../../../lib/std/byte_cursor.hthr")),
    ("x86_64_buffer_cursor", include_str!("../../../../lib/std/arch/x86_64/buffer_cursor.hthr")),
];

pub(super) const SCAN_SUPPORT: &[(&str, &str)] = &[
    ("byte_cursor", include_str!("../../../../lib/std/byte_cursor.hthr")),
    ("x86_64_buffer_cursor", include_str!("../../../../lib/std/arch/x86_64/buffer_cursor.hthr")),
    ("byte_scan", include_str!("../../../../lib/std/byte_scan.hthr")),
    ("x86_64_scan_body", include_str!("../../../../lib/std/arch/x86_64/scan_body.hthr")),
    ("x86_64_scan_gate", include_str!("../../../../lib/std/arch/x86_64/scan_gate.hthr")),
];
