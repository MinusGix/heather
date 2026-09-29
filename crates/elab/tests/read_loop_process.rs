use crate::read_loop_fixture::checker;
use heather_elab::function_ir_source::{generate_elaborated_loop_x86, NativeLoopPlacement};
use heather_elab::function_ir_x86_lower::Gpr;

const PROCESS: &str = include_str!("../../../lib/elf64_read_loop.hthr");

#[test]
fn read_loop_library_checks() {
    let mut elab = checker();
    elab.elab_module_source("elf64_read_loop", PROCESS).unwrap_or_else(|e| panic!("{}", e.render(PROCESS)));
}

// Each change to the process shape is refused where it is wrong, not by a
// missing name: the claim can't be restated over a program that reads
// elsewhere, asks for more than the page, issues another syscall, reads
// another descriptor, or hands the loop the wrong buffer; nor over one that
// restarts the count at every chunk, keeps it where the next chunk's setup
// overwrites it, tests another register for the end of file, exits with the
// register SYSCALL clobbers, or jumps back to somewhere other than the read
// (docs/native-read-until-eof-design.md); nor over one that takes another
// errno for EINTR, exits 0 on a failed read, loses the count on a retry, or
// jumps to the failure path from the wrong distance
// (docs/native-syscall-failures-design.md).
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
        ("count_reset", "MovRI(Rsi, BitVec::ofNat(0)), MovRR(R11, R13)]", "MovRI(Rsi, BitVec::ofNat(0)), MovRI(R11, BitVec::ofNat(0))]"),
        ("count_saved_where_setup_writes", "{ [MovRR(R13, R11)] }", "{ [MovRR(R12, R11)] }"),
        ("end_tested_elsewhere", "[TestRR(Rax, Rax)]", "[TestRR(Rdx, Rdx)]"),
        ("exit_with_clobbered", "[MovRR(Rdi, R13), MovRI(Rax", "[MovRR(Rdi, R11), MovRI(Rax"),
        ("back_span", "(((((read_entry_len() + 2) + eof_test_len())", "(((((read_entry_len() + 3) + eof_test_len())"),
        ("eintr_tested_as_other", "fn eof_retry_block() → List<Instruction> { [MovRI(Rbx, BitVec::ofNat(4))",
            "fn eof_retry_block() → List<Instruction> { [MovRI(Rbx, BitVec::ofNat(5))"),
        ("failure_exits_zero", "fn eof_fail_block() → List<Instruction> { [MovRI(Rdi, BitVec::ofNat(1))",
            "fn eof_fail_block() → List<Instruction> { [MovRI(Rdi, BitVec::ofNat(0))"),
        ("retry_clobbers_count", "[MovRI(Rbx, BitVec::ofNat(4)), AddRR(Rax, Rbx)]", "[MovRI(R13, BitVec::ofNat(4)), AddRR(Rax, R13)]"),
        ("failure_span", "    ((eof_setup_len(needle) + loop_bytes.len()) + eof_save_len()) + 5\n}",
            "    ((eof_setup_len(needle) + loop_bytes.len()) + eof_save_len()) + 4\n}"),
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
    head: LoopHead<M, Nat>(count_placement(), loop_in(count_placement().carry, loop_nat_rep), access, buffer, needle, before, cursor, budget, carry),
    readable: LoopReadable(budget, count_loop_region(), buffer, needle, cursor, carry),
    fits: loop_fits(cursor, budget, carry), resident: {resident}):
    Exists<MachineState<M>>(λ after => (FetchedSteps(fetch, access, before, after) ∧
        after.rip = next_rip(before.rip, count_bytes().len())) ∧
        LoopObserved<M, Nat>(count_placement(), loop_in(count_placement().carry, loop_nat_rep), after,
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
