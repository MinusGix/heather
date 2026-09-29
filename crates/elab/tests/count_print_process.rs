use crate::read_loop_fixture::checker;
use heather_elab::function_ir_source::{generate_elaborated_loop_x86, NativeLoopPlacement};
use heather_elab::function_ir_x86_lower::Gpr;

const READ_PIECES: &str = include_str!("../../../lib/elf64_read_pieces.hthr");
const STATE: &str = include_str!("../../../lib/elf64_read_state.hthr");
const BV_OMEGA: &str = include_str!("../../../lib/std/bitvec/bitvec_omega.hthr");
const DECIMAL: &str = include_str!("../../../lib/decimal_line.hthr");
const PRINT: &str = include_str!("../../../lib/elf64_print_pieces.hthr");
const WRITE: &str = include_str!("../../../lib/elf64_write_loop.hthr");
const COUNT: &str = include_str!("../../../lib/elf64_count_print.hthr");
const WC_L: &str = include_str!("../../../examples/x86-native/wc_l.hthr");

// Everything the count process and its printing tail stand on.
fn base() -> heather_elab::Elaborator {
    let mut elab = checker();
    for (name, source) in [("elf64_read_pieces", READ_PIECES), ("elf64_read_state", STATE), ("bitvec_omega", BV_OMEGA),
        ("decimal_line", DECIMAL), ("elf64_print_pieces", PRINT), ("elf64_write_loop", WRITE)] {
        elab.elab_module_source(name, source).unwrap_or_else(|e| panic!("{name}: {}", e.render(source)));
    }
    elab
}

// The read profile's counting loop over the state process: the count in R13,
// where the state's first register is, and the loop's flag in R11, which only
// the loop uses.
pub(crate) fn count_placement() -> NativeLoopPlacement {
    NativeLoopPlacement {
        base: Gpr::Rdi, length: Gpr::Rbp, needle: Gpr::Rcx, cursor: Gpr::Rsi, budget: Gpr::R12,
        carry: Gpr::R13, flag: Gpr::R11, step: Gpr::Rbx,
        address: Gpr::R8, byte: Gpr::R9, payload: Gpr::Rax, next_cursor: Gpr::R10, next_budget: Gpr::R14,
        extra: vec![Gpr::Rdx, Gpr::R15],
    }
}

// `wc -l`'s loop at that placement, composed into the exit claim and the
// printing claim over any file holding the code; the formatter's
// certificates are parameters (read_print_process checks decimal_line's).
const WC_L_COUNT: &str = r#"
import elf64_count_print; import elf64_write_loop; import elf64_print_pieces; import elf64_read_state; import elf64_read_pieces;
import elf64_io; import linux_x86_64_io; import linux_x86_64_entry; import x86_64_structured_block;
import function_ir_loop; import function_ir_loop_trace; import x86_64; import x86_64_fetch; import x86_64_fetched_code;
import bitvec; import bitvec_nat; import bool; import list; import logic; import nat;
import decimal_line; import wc_l; import lines_pieces; import lines_native;

theorem lines_exit(file: List<BitVec(8)>, jumps: EofJumps,
    exit_reads: jumps.ed.sign_extend(32).toNat() = state_exit_skip(newline(), lines_bytes()),
    fail_reads: jumps.sd.sign_extend(32).toNat() = state_fail_skip(newline(), lines_bytes()),
    back_closes: state_loop_span(newline(), lines_bytes()) + 5 + jumps.bd.sign_extend(32).toNat() = Nat::pow(2, 64),
    retry_closes: state_retry_span(newline(), lines_bytes()) + 6 + jumps.rd.sign_extend(32).toNat() = Nat::pow(2, 64),
    resident: (page: Nat → BitVec(8)) → CodeResident(io_fetch_access(), IoMemory(file, page), read_state_code(newline(), lines_bytes(), jumps),
        BitVec::ofNat(0x4000e8)),
    chunks: List<ReadStep>, ok: EofChunks(chunks), ending: ReadEnding, ending_ok: EofEnding(ending),
    room: eof_input(chunks).len() + 4096 < Nat::pow(2, 64), page: Nat → BitVec(8), gprs: Gprs, flags: Flags):
    LinuxRuns(io_linux(), eof_events(chunks, ending, [ExitEvent(bitvec_nat::word_of_nat(64, wc_l(eof_input(chunks))))]),
        io_initial(file, page, gprs, flags)) {
    read_count_runs(file, lines_placement(), ReadStatePlacement(refl, refl, refl, refl, refl),
        lines_loop_region(), lines_code(), lines_bytes(), count_lines, newline(), wc_l,
        λ buffer needle budget cursor carry => lines_loop_source_agreement(buffer, needle, budget, cursor, carry),
        λ access before buffer needle budget cursor carry bounded low head readable fits =>
            lines_native(access, before, buffer, needle, budget, cursor, carry, bounded, low, head, readable, fits),
        count_lines_input, line_body_folds(), line_body_advances(),
        jumps, exit_reads, fail_reads, back_closes, retry_closes, resident, chunks, ok, ending, ending_ok, room, page, gprs, flags)
}

theorem lines_print(file: List<BitVec(8)>, jumps: EofJumps,
    exit_reads: jumps.ed.sign_extend(32).toNat() = state_exit_skip(newline(), lines_bytes()),
    fail_reads: jumps.sd.sign_extend(32).toNat() = state_fail_skip(newline(), lines_bytes()),
    back_closes: state_loop_span(newline(), lines_bytes()) + 5 + jumps.bd.sign_extend(32).toNat() = Nat::pow(2, 64),
    retry_closes: state_retry_span(newline(), lines_bytes()) + 6 + jumps.rd.sign_extend(32).toNat() = Nat::pow(2, 64),
    word, start, length: StructuredCode, word_keeps, start_keeps, length_keeps: Gpr → Type,
    format: ReadPrintFormat(word, start, length, word_keeps, start_keeps, length_keeps), pj: PrintJumps,
    write_fail_reads: pj.sd.sign_extend(32).toNat() = print_fail_skip(),
    write_exit_reads: pj.zd.sign_extend(32).toNat() = print_exit_skip(),
    write_back_closes: print_loop_span() + 5 + pj.bd.sign_extend(32).toNat() = Nat::pow(2, 64),
    write_retry_closes: print_retry_span() + 6 + pj.rd.sign_extend(32).toNat() = Nat::pow(2, 64),
    resident: (page: Nat → BitVec(8)) → CodeResident(io_fetch_access(), IoMemory(file, page),
        read_count_code(newline(), lines_bytes(), jumps, word, start, length, pj), BitVec::ofNat(0x4000e8)),
    chunks: List<ReadStep>, ok: EofChunks(chunks), ending: ReadEnding, ending_ok: EofEnding(ending),
    room: eof_input(chunks).len() + 4096 < Nat::pow(2, 64), small: wc_l(eof_input(chunks)) < 10000,
    writes: List<WriteStep>, writes_ok: WriteSteps(writes)(decimal_line(wc_l(eof_input(chunks)))),
    written: WriteEnding, written_ok: WriteEndingOk(written), page: Nat → BitVec(8), gprs: Gprs, flags: Flags):
    LinuxRuns(io_linux(), eof_events(chunks, ending, write_events(decimal_line(wc_l(eof_input(chunks))), writes, written)),
        io_initial(file, page, gprs, flags)) {
    read_count_print_runs(file, lines_placement(), ReadStatePlacement(refl, refl, refl, refl, refl),
        lines_loop_region(), lines_code(), lines_bytes(), count_lines, newline(), wc_l,
        λ buffer needle budget cursor carry => lines_loop_source_agreement(buffer, needle, budget, cursor, carry),
        λ access before buffer needle budget cursor carry bounded low head readable fits =>
            lines_native(access, before, buffer, needle, budget, cursor, carry, bounded, low, head, readable, fits),
        count_lines_input, line_body_folds(), line_body_advances(),
        word, start, length, word_keeps, start_keeps, length_keeps, format,
        jumps, exit_reads, fail_reads, back_closes, retry_closes, pj, write_fail_reads, write_exit_reads, write_back_closes,
        write_retry_closes, resident, chunks, ok, ending, ending_ok, room, small, writes, writes_ok, written, written_ok, page, gprs, flags)
}
"#;

#[test]
fn wc_l_count_process_composes() {
    let mut elab = base();
    elab.elab_module_source("elf64_count_print", COUNT).unwrap_or_else(|e| panic!("{}", e.render(COUNT)));
    elab.elab_module_source("wc_l", WC_L).unwrap_or_else(|e| panic!("{}", e.render(WC_L)));
    elab.elab_module_source("lines_context", "import function_ir_loop; import function_ir_loop_x86; import wc_l; import bitvec; import bool;").unwrap();
    let emission = generate_elaborated_loop_x86(&elab, "lines", "wc_l::count_lines", &count_placement(), Some("wc_l::line_body_advances"))
        .unwrap_or_else(|e| panic!("{e:?}"));
    elab.elab_module_source("lines_pieces", &emission.pieces).unwrap_or_else(|e| panic!("{}", e.render(&emission.pieces)));
    elab.elab_module_source("lines_native", &emission.text).unwrap_or_else(|e| panic!("{}", e.render(&emission.text)));
    elab.elab_module_source("lines_count", WC_L_COUNT).unwrap_or_else(|e| panic!("{}", e.render(WC_L_COUNT)));
}
