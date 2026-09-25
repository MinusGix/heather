use crate::common;
use heather_elab::function_ir_source::{generate_elaborated_loop_x86, NativeLoopPlacement};
use heather_elab::function_ir_x86_lower::Gpr;

// The read-once process shape and what it stands on
// (docs/native-first-program-design.md): fetched execution, the basic Linux
// trace, the profile's memory view, and the process theorem itself.
fn checker() -> heather_elab::Elaborator {
    let mut elab = common::base_image(common::MODULES.len());
    for (name, source) in [
        ("x86_64_structured_block", include_str!("../../../lib/std/arch/x86_64/structured_block.hthr")),
        ("x86_64_data_read", include_str!("../../../lib/std/arch/x86_64/data_read.hthr")),
        ("x86_64_access_code", include_str!("../../../lib/std/arch/x86_64/access_code.hthr")),
        ("x86_64_access_memory", include_str!("../../../lib/std/arch/x86_64/access_memory.hthr")),
        ("bitvec_nat", include_str!("../../../lib/std/bitvec/nat.hthr")),
        ("function_ir_loop", include_str!("../../../lib/function_ir_loop.hthr")),
        ("function_ir_loop_x86", include_str!("../../../lib/function_ir_loop_x86.hthr")),
        ("function_ir_loop_trace", include_str!("../../../lib/function_ir_loop_trace.hthr")),
        ("omega", include_str!("../../../lib/std/omega.hthr")),
        ("x86_64_fetch", include_str!("../../../lib/std/arch/x86_64/fetch.hthr")),
        ("x86_64_fetched_code", include_str!("../../../lib/std/arch/x86_64/fetched_code.hthr")),
        ("elf64", include_str!("../../../lib/elf64.hthr")),
        ("linux_x86_64_entry", include_str!("../../../lib/linux_x86_64_entry.hthr")),
        ("x86_64_store", include_str!("../../../lib/std/arch/x86_64/store.hthr")),
        ("linux_x86_64_io", include_str!("../../../lib/linux_x86_64_io.hthr")),
        ("elf64_io", include_str!("../../../lib/elf64_io.hthr")),
    ] { elab.elab_module_source(name, source).unwrap_or_else(|e| panic!("{}", e.render(source))); }
    elab
}

const PROCESS: &str = include_str!("../../../lib/elf64_read_loop.hthr");

#[test]
fn read_loop_library_checks() {
    let mut elab = checker();
    elab.elab_module_source("elf64_read_loop", PROCESS).unwrap_or_else(|e| panic!("{}", e.render(PROCESS)));
}

// Each change to the process shape is refused where it is wrong, not by a
// missing name: the claim can't be restated over a program that reads
// elsewhere, asks for more than the page, issues another syscall, reads
// another descriptor, or hands the loop the wrong buffer.
#[test]
fn slow_acceptance_read_loop_refusals() {
    let library = checker().semantic_image();
    for (name, from, to) in [
        ("buffer_outside_page", "MovRI(Rsi, BitVec::ofNat(0x401000)),\n", "MovRI(Rsi, BitVec::ofNat(0x402000)),\n"),
        ("capacity_past_page", "fn read_capacity() → Nat { 4096 }", "fn read_capacity() → Nat { 4097 }"),
        ("read_number", "[MovRI(Rax, BitVec::ofNat(0)), MovRI(Rdi", "[MovRI(Rax, BitVec::ofNat(1)), MovRI(Rdi"),
        ("descriptor", "MovRI(Rdi, BitVec::ofNat(0)), MovRI(Rsi", "MovRI(Rdi, BitVec::ofNat(1)), MovRI(Rsi"),
        ("exit_number", "MovRI(Rax, BitVec::ofNat(60))", "MovRI(Rax, BitVec::ofNat(61))"),
        ("loop_base", "MovRI(Rdi, BitVec::ofNat(0x401000)), MovRI(Rcx", "MovRI(Rdi, BitVec::ofNat(0x401001)), MovRI(Rcx"),
    ] {
        let bad = PROCESS.replacen(from, to, 1);
        assert_ne!(bad, PROCESS, "{name}");
        let error = library.elaborator().elab_module_source("elf64_read_loop", &bad).expect_err(name).render(&bad);
        assert!(!error.contains("unbound") && !error.contains("ambiguous"), "{name}: {error}");
    }
}

fn search_placement() -> NativeLoopPlacement {
    NativeLoopPlacement {
        base: Gpr::Rdi, length: Gpr::Rbp, needle: Gpr::Rcx, cursor: Gpr::Rsi, budget: Gpr::R12,
        carry: Gpr::R11, flag: Gpr::R13, step: Gpr::Rbx,
        address: Gpr::R8, byte: Gpr::R9, payload: Gpr::Rax, next_cursor: Gpr::R10, next_budget: Gpr::R14,
        extra: vec![Gpr::Rdx, Gpr::R15],
    }
}

// The whole counting loop, fetched: the published certificate composed with
// the library bridge (docs/native-first-program-design.md §3), wherever its
// bytes are resident. `resident` is the one premise the bridge adds.
fn count_fetched(resident: &str) -> String {
    format!("import count_native; import count_pieces; import readonly_loops; import function_ir_loop; import function_ir_loop_trace; \
        import x86_64; import x86_64_fetch; import x86_64_data_read; import x86_64_access_code; import x86_64_fetched_code; \
        import bitvec; import nat; import logic; import list;
theorem count_fetched<M>(fetch: FetchAccess<M>, access: ByteReadAccess<M>, before: MachineState<M>,
    buffer: ReadonlyBytes, needle: BitVec(8), budget, cursor, carry: Nat,
    bounded: LoopAddressBound(64, buffer), low: buffer.base + buffer.length <= Nat::pow(2, 47),
    head: LoopHead<M, Nat>(count_placement(), loop_nat_rep, access, buffer, needle, before, cursor, budget, carry),
    readable: LoopReadable(budget, count_loop_region(), buffer, needle, cursor, carry),
    fits: loop_fits(cursor, budget, carry), resident: {resident}):
    Exists<MachineState<M>>(λ after => (FetchedSteps(fetch, access, before, after) ∧
        after.rip = next_rip(before.rip, count_bytes().len())) ∧
        LoopObserved<M, Nat>(count_placement(), loop_nat_rep, after,
            readonly_loops::count_occurrences(buffer, needle, budget, cursor, carry))) {{
    let native = count_native(access, before, buffer, needle, budget, cursor, carry, bounded, low, head, readable, fits);
    Exists(native.witness, ⟨access_artifact_fetched(fetch, access, count_code(), count_bytes(), before, native.witness,
        native.proof.left, resident), native.proof.right⟩)
}}")
}

// The counting certificate, fetched; the bridge needs the whole span, at
// the loop's own start.
#[test]
fn counting_loop_runs_fetched() {
    let mut elab = checker();
    let source = include_str!("../../../examples/function-ir/readonly-loops.hthr");
    elab.elab_module_source("readonly_loops", source).unwrap_or_else(|e| panic!("{}", e.render(source)));
    elab.elab_module_source("loop_clients", "import function_ir_loop; import function_ir_loop_x86; import readonly_loops; import bitvec; import bool;").unwrap();
    let emission = generate_elaborated_loop_x86(&elab, "count", "readonly_loops::count_occurrences", &search_placement(),
        Some("readonly_loops::count_body_advances")).unwrap_or_else(|e| panic!("{e:?}"));
    elab.elab_module_source("count_pieces", &emission.pieces).unwrap_or_else(|e| panic!("{}", e.render(&emission.pieces)));
    elab.elab_module_source("count_native", &emission.text).unwrap_or_else(|e| panic!("{}", e.render(&emission.text)));
    let fetched = count_fetched("CodeResident(fetch, before.memory, count_bytes(), before.rip)");
    elab.semantic_image().elaborator().elab_module_source("count_fetched", &fetched).unwrap_or_else(|e| panic!("{}", e.render(&fetched)));
    let short = format!("CodeResident(fetch, before.memory, count_bytes().take({}), before.rip)", emission.bytes.len() - 1);
    for (name, resident) in [
        ("short_span", short.as_str()),
        ("shifted_start", "CodeResident(fetch, before.memory, count_bytes(), next_rip(before.rip, 1))"),
    ] {
        let bad = count_fetched(resident);
        let error = elab.semantic_image().elaborator().elab_module_source(name, &bad).expect_err(name).render(&bad);
        assert!(!error.contains("unbound") && !error.contains("ambiguous"), "{name}: {error}");
    }
}
