use crate::common;

// The read-once process shape and what it stands on
// (docs/native-first-program-design.md): fetched execution, the basic Linux
// trace, the profile's memory view, and the process theorem itself.
pub fn checker() -> heather_elab::Elaborator {
    let mut elab = common::base_image(common::MODULES.len());
    for (name, source) in [
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
        ("elf64", include_str!("../../../../lib/elf64.hthr")),
        ("linux_x86_64_entry", include_str!("../../../../lib/linux_x86_64_entry.hthr")),
        ("x86_64_store", include_str!("../../../../lib/std/arch/x86_64/x86_64_store.hthr")),
        ("linux_x86_64_io", include_str!("../../../../lib/linux_x86_64_io.hthr")),
        ("elf64_io", include_str!("../../../../lib/elf64_io.hthr")),
    ] { elab.elab_module_source(name, source).unwrap_or_else(|e| panic!("{}", e.render(source))); }
    elab
}
