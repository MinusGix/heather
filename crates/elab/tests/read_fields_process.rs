use crate::function_ir_loop_trace::wc_record_loop;
use crate::read_loop_fixture::checker;
use crate::read_state_process::WC_PROCESS;

const READ_PIECES: &str = include_str!("../../../lib/elf64_read_pieces.hthr");
const STATE: &str = include_str!("../../../lib/elf64_read_state.hthr");
const BV_OMEGA: &str = include_str!("../../../lib/std/bitvec/bitvec_omega.hthr");
const DECIMAL: &str = include_str!("../../../lib/decimal_line.hthr");
const FIELD: &str = include_str!("../../../lib/field_line.hthr");
const PRINT: &str = include_str!("../../../lib/elf64_print_pieces.hthr");
const WRITE: &str = include_str!("../../../lib/elf64_write_loop.hthr");
const FIELDS: &str = include_str!("../../../lib/elf64_read_fields.hthr");

// Everything the three-field tail stands on (docs/native-wc-design.md §5).
fn base() -> heather_elab::Elaborator {
    let mut elab = checker();
    for (name, source) in [("elf64_read_pieces", READ_PIECES), ("elf64_read_state", STATE), ("bitvec_omega", BV_OMEGA),
        ("decimal_line", DECIMAL), ("field_line", FIELD), ("elf64_print_pieces", PRINT), ("elf64_write_loop", WRITE)] {
        elab.elab_module_source(name, source).unwrap_or_else(|e| panic!("{name}: {}", e.render(source)));
    }
    elab
}

#[test]
fn read_fields_library_checks() {
    let mut elab = base();
    elab.elab_module_source("elf64_read_fields", FIELDS).unwrap_or_else(|e| panic!("{}", e.render(FIELDS)));
}

// wc's facts for the three-field tail: its first three fields are the counts
// in R13, R14 and R15. The formatter's certificates are parameters here;
// field_line_format checks the generated ones against `FieldsFormat`.
const WC_FIELDS: &str = r#"
import elf64_read_fields; import elf64_write_loop; import elf64_print_pieces; import elf64_read_state; import elf64_read_pieces; import field_line;
import elf64_io; import linux_x86_64_io; import linux_x86_64_entry; import x86_64_structured_block;
import function_ir_loop; import function_ir_loop_trace; import x86_64; import x86_64_fetch; import x86_64_fetched_code;
import bitvec; import bitvec_nat; import bool; import list; import logic; import nat;
// `wc_bytes` is also the program's byte count; here it is the loop's code.
import wc; import wc_pieces; import wc_native::{wc_bytes}; import wc_process;

theorem wc_counts(gprs: Gprs, carry: WcState, placed: wc_rep(gprs, carry)):
    (read_gpr(R13, gprs) = bitvec_nat::word_of_nat(64, carry.lines)) ∧ ((read_gpr(R14, gprs) = bitvec_nat::word_of_nat(64, carry.words)) ∧
    (read_gpr(R15, gprs) = bitvec_nat::word_of_nat(64, carry.bytes))) {
    ⟨sym(loop_nat_placed(read_gpr(R13, gprs), carry.lines, placed.left)), ⟨sym(loop_nat_placed(read_gpr(R14, gprs), carry.words, placed.right.left)),
        sym(loop_nat_placed(read_gpr(R15, gprs), carry.bytes, placed.right.right.left))⟩⟩
}

// Any file holding the process's code: for every history of reads and
// writes, a run that prints the line of the state folded over the input.
theorem wc_prints(file: List<BitVec(8)>, needle: BitVec(8), jumps: EofJumps,
    exit_reads: jumps.ed.sign_extend(32).toNat() = state_exit_skip(needle, wc_bytes()),
    fail_reads: jumps.sd.sign_extend(32).toNat() = state_fail_skip(needle, wc_bytes()),
    back_closes: state_loop_span(needle, wc_bytes()) + 5 + jumps.bd.sign_extend(32).toNat() = Nat::pow(2, 64),
    retry_closes: state_retry_span(needle, wc_bytes()) + 6 + jumps.rd.sign_extend(32).toNat() = Nat::pow(2, 64),
    low, high: StructuredCode, low_keeps, high_keeps: Gpr → Type, format: FieldsFormat(low, high, low_keeps, high_keeps), pj: PrintJumps,
    write_fail_reads: pj.sd.sign_extend(32).toNat() = print_fail_skip(),
    write_exit_reads: pj.zd.sign_extend(32).toNat() = print_exit_skip(),
    write_back_closes: print_loop_span() + 5 + pj.bd.sign_extend(32).toNat() = Nat::pow(2, 64),
    write_retry_closes: print_retry_span() + 6 + pj.rd.sign_extend(32).toNat() = Nat::pow(2, 64),
    resident: (page: Nat → BitVec(8)) → CodeResident(io_fetch_access(), IoMemory(file, page),
        read_fields_code(needle, wc_bytes(), jumps, low, high, pj), BitVec::ofNat(0x4000e8)),
    chunks: List<ReadStep>, ok: EofChunks(chunks), ending: ReadEnding, ending_ok: EofEnding(ending),
    room: eof_input(chunks).len() + 4096 < Nat::pow(2, 64),
    small: (step_fold(wc_loop_region(), needle, eof_input(chunks), WcState(0, 0, 0, False)).lines < 10000000) ∧
        ((step_fold(wc_loop_region(), needle, eof_input(chunks), WcState(0, 0, 0, False)).words < 10000000) ∧
        (step_fold(wc_loop_region(), needle, eof_input(chunks), WcState(0, 0, 0, False)).bytes < 10000000)),
    writes: List<WriteStep>,
    writes_ok: WriteSteps(writes)(three_fields_line(step_fold(wc_loop_region(), needle, eof_input(chunks), WcState(0, 0, 0, False)).lines,
        step_fold(wc_loop_region(), needle, eof_input(chunks), WcState(0, 0, 0, False)).words,
        step_fold(wc_loop_region(), needle, eof_input(chunks), WcState(0, 0, 0, False)).bytes)),
    written: WriteEnding, written_ok: WriteEndingOk(written),
    page: Nat → BitVec(8), gprs: Gprs, flags: Flags):
    LinuxRuns(io_linux(), eof_events(chunks, ending, write_events(three_fields_line(
        step_fold(wc_loop_region(), needle, eof_input(chunks), WcState(0, 0, 0, False)).lines,
        step_fold(wc_loop_region(), needle, eof_input(chunks), WcState(0, 0, 0, False)).words,
        step_fold(wc_loop_region(), needle, eof_input(chunks), WcState(0, 0, 0, False)).bytes), writes, written)),
        io_initial(file, page, gprs, flags)) {
    read_fields_runs(file, wc_placement(), ReadStatePlacement(refl, refl, refl, refl, refl), wc_rep, wc_fits, wc_framed(),
        wc_loop_region(), wc_code(), wc_bytes(), count_wc, needle,
        λ buffer needle budget cursor carry => wc_loop_source_agreement(buffer, needle, budget, cursor, carry),
        λ access before buffer needle budget cursor carry bounded low head readable fits =>
            wc_native(access, before, buffer, needle, budget, cursor, carry, bounded, low, head, readable, fits),
        wc_body_folds(), WcState(0, 0, 0, False), wc_initialised(),
        λ seen budget fits => wc_room(needle, WcState(0, 0, 0, False), ⟨refl, ⟨refl, refl⟩⟩, seen, budget, fits),
        λ (s: WcState) => s.lines, λ (s: WcState) => s.words, λ (s: WcState) => s.bytes, wc_counts,
        low, high, low_keeps, high_keeps, format, jumps, exit_reads, fail_reads, back_closes, retry_closes,
        pj, write_fail_reads, write_exit_reads, write_back_closes, write_retry_closes, resident,
        chunks, ok, ending, ending_ok, room, small, writes, writes_ok, written, written_ok, page, gprs, flags)
}
"#;

// wc's record loop, its process facts and the three-field tail compose into
// the printing claim.
#[test]
fn wc_fields_process_composes() {
    let mut elab = base();
    elab.elab_module_source("elf64_read_fields", FIELDS).unwrap_or_else(|e| panic!("{}", e.render(FIELDS)));
    wc_record_loop(&mut elab);
    elab.elab_module_source("wc_process", WC_PROCESS).unwrap_or_else(|e| panic!("{}", e.render(WC_PROCESS)));
    elab.elab_module_source("wc_fields", WC_FIELDS).unwrap_or_else(|e| panic!("{}", e.render(WC_FIELDS)));
}

// Each change to the tail is refused where it is wrong, not by a missing
// name: the claim can't be restated over a tail that stores another
// register, formats one count twice, lets two fields overlap, ends the line
// with another separator, writes another length or from elsewhere, stores
// the high word one byte early, or hands the high word its tail in another
// register than its certificate reads. The write loop's blocks are
// elf64_print_pieces's, refused there.
#[test]
fn slow_acceptance_read_fields_refusals() {
    let library = base().semantic_image();
    for (name, from, to) in [
        ("stored_register", "WordStore(R9, Rax)", "WordStore(R9, R10)"),
        ("count_twice", "field_code(R14, 8, 32, low, high, field_code(R15", "field_code(R13, 8, 32, low, high, field_code(R15"),
        ("fields_overlap", "field_code(R14, 8, 32, low, high, field_code(R15", "field_code(R14, 4, 32, low, high, field_code(R15"),
        ("last_separator", "field_code(R15, 16, 10, low, high,\n", "field_code(R15, 16, 32, low, high,\n"),
        ("line_length", "MovRI(R10, BitVec::ofNat(24))", "MovRI(R10, BitVec::ofNat(23))"),
        ("line_start", "[MovRI(R9, BitVec::ofNat(0x410000)), MovRI(R10", "[MovRI(R9, BitVec::ofNat(0x410001)), MovRI(R10"),
        ("high_early", "BitVec::ofNat(0x410000 + (offset + 4)))] }", "BitVec::ofNat(0x410000 + (offset + 3)))] }"),
        ("tail_elsewhere", "MovRI(R10, BitVec::ofNat(16777216 * separator))", "MovRI(R12, BitVec::ofNat(16777216 * separator))"),
    ] {
        let bad = FIELDS.replacen(from, to, 1);
        assert_ne!(bad, FIELDS, "{name}");
        let error = library.elaborator().elab_module_source("elf64_read_fields", &bad).expect_err(name).render(&bad);
        assert!(!error.contains("unbound") && !error.contains("ambiguous"), "{name}: {error}");
    }
}
