//! The stream filter's process (docs/native-stream-filter-design.md §4): the
//! library checks over what it stands on, and each change to its shape is
//! refused where it is wrong, not by a missing name.
use crate::read_loop_fixture::checker_with;

const READ_PIECES: &str = include_str!("../../../lib/elf64_read_pieces.hthr");
const DECIMAL: &str = include_str!("../../../lib/decimal_line.hthr");
const PRINT: &str = include_str!("../../../lib/elf64_print_pieces.hthr");
const WRITE: &str = include_str!("../../../lib/elf64_write_loop.hthr");
const BV_OMEGA: &str = include_str!("../../../lib/std/bitvec/bitvec_omega.hthr");
const STREAM: &str = include_str!("../../../lib/stream_filter.hthr");
const STEP_PIECE: &str = include_str!("../../../lib/filter_step_piece.hthr");
const PROCESS: &str = include_str!("../../../lib/elf64_read_filter.hthr");
const ASM: &str = include_str!("../../../lib/std/arch/x86_64/x86_64_asm.hthr");
const RUNS: &str = include_str!("../../../lib/elf64_runs.hthr");
const STRETCH: &str = include_str!("../../../lib/elf64_stretch.hthr");

// Everything the filter process stands on: the read driver, the write loop,
// the labelled program and its stretches, what a filter computes, and the
// step's contract.
const BASE: &[(&str, &str)] = &[("elf64_read_pieces", READ_PIECES), ("bitvec_omega", BV_OMEGA), ("decimal_line", DECIMAL),
    ("elf64_print_pieces", PRINT), ("elf64_write_loop", WRITE), ("x86_64_asm", ASM), ("elf64_runs", RUNS), ("elf64_stretch", STRETCH),
    ("stream_filter", STREAM)];

fn base() -> heather_elab::Elaborator { checker_with(BASE) }
fn with_step_piece(mut elab: heather_elab::Elaborator, source: &str) -> heather_elab::Elaborator {
    elab.elab_module_source("filter_step_piece", source).unwrap_or_else(|e| panic!("{}", e.render(source)));
    elab
}

#[test]
fn read_filter_library_checks() {
    checker_with(&[BASE, &[("filter_step_piece", STEP_PIECE), ("elf64_read_filter", PROCESS)]].concat());
}

// The claim can't be restated over a store at the read cursor instead of the
// write cursor, an advance that forgets the flag, a close that leaves the
// page's base in the length, an empty chunk that jumps into the write loop,
// a byte loop that jumps back once the chunk is done, or a step piece that
// may write the write cursor.
#[test]
fn slow_acceptance_read_filter_refusals() {
    let library = checker_with(&[BASE, &[("filter_step_piece", STEP_PIECE)]].concat()).semantic_image();
    for (name, from, to) in [
        ("store_at_read", "ByteStore(base := Rdi, source := Rdx)", "ByteStore(base := Rsi, source := Rdx)"),
        ("flag_forgotten", "[AddRR(Rdi, Rbx), AddRR(Rsi, R12), SubRR(Rcx, R12)]", "[AddRR(Rdi, R12), AddRR(Rsi, R12), SubRR(Rcx, R12)]"),
        ("base_left_in", "[MovRR(R10, Rdi), MovRI(R9, BitVec::ofNat(io_page_base())), SubRR(R10, R9)]",
            "[MovRR(R10, Rdi), MovRI(R9, BitVec::ofNat(io_page_base())), SubRR(R10, Rcx)]"),
        ("quiet_into_write", "quiet: near_branch_target(eof_rip(fc_at_cjz(c, p)), 6, jumps.cd) = eof_rip(ar),",
            "quiet: near_branch_target(eof_rip(fc_at_cjz(c, p)), 6, jumps.cd) = eof_rip(fc_at_write(c, p)),"),
        ("loop_on_zero", "fn lf_jnz(p: Nat) → Prog { then(lf_advance(p), Jcc(NE, tf_load())) }", "fn lf_jnz(p: Nat) → Prog { then(lf_advance(p), Jcc(E, tf_load())) }"),
    ] {
        let bad = PROCESS.replacen(from, to, 1);
        assert_ne!(bad, PROCESS, "{name}");
        let error = library.elaborator().elab_module_source("elf64_read_filter", &bad).expect_err(name).render(&bad);
        assert!(!error.contains("unbound") && !error.contains("ambiguous"), "{name}: {error}");
    }
    let clobbering = STEP_PIECE.replacen("[Rax, Rdx, Rbx, R9, R10, R11, Rbp, R13, R14, R15, R8]",
        "[Rax, Rdx, Rbx, R9, R10, R11, Rbp, R13, R14, R15, R8, Rdi]", 1);
    assert_ne!(clobbering, STEP_PIECE);
    let error = with_step_piece(base(), &clobbering).elab_module_source("elf64_read_filter", PROCESS)
        .expect_err("a step piece writing the write cursor").render(PROCESS);
    assert!(error.contains("Kept(filter_step_scratch, Rdi)") && !error.contains("unbound"), "{error}");
}
