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
const LINES_CONTEXT: &str = "import function_ir_loop; import function_ir_loop_x86; import wc_l; import bitvec; import bool; import nat;
fn count_lines(buffer: ReadonlyBytes, needle: BitVec(8), budget: Nat, cursor: Nat, count: Nat) → LoopOutcome<Nat> {
    bounded_readonly<Nat>(buffer, needle, budget, cursor, count, line_body)
}";

// Everything the count process and its printing tail stand on.
fn base() -> heather_elab::Elaborator {
    let mut elab = checker();
    for (name, source) in [("elf64_read_pieces", READ_PIECES), ("elf64_read_state", STATE), ("bitvec_omega", BV_OMEGA),
        ("decimal_line", DECIMAL), ("elf64_print_pieces", PRINT), ("elf64_write_loop", WRITE)] {
        elab.elab_module_source(name, source).unwrap_or_else(|e| panic!("{name}: {}", e.render(source)));
    }
    elab
}

// The read profile's counting loop over the state process: the count one
// field, in R13, where the state's first register is.
pub(crate) fn count_placement() -> NativeLoopPlacement {
    NativeLoopPlacement {
        base: Gpr::Rdi, length: Gpr::Rbp, needle: Gpr::Rcx, cursor: Gpr::Rsi, budget: Gpr::R12,
        flag: Gpr::R10, step: Gpr::Rbx, byte: Gpr::R9,
        fields: vec![Gpr::R13], scratch: vec![Gpr::R11, Gpr::Rax, Gpr::Rdx],
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
import decimal_line; import wc_l; import lines_context; import lines_pieces; import lines_native;

// The facts the count gives the process, as the producer states them.
theorem lines_framed(): StateFramed(lines_rep) { λ before after carry kept placed => lines_rep_moves(before, after, carry, kept.left, placed) }
fn lines_init() → Nat { 0 }
theorem lines_initialised(): StateInitialised(lines_rep, lines_init()) { λ state => refl }
theorem lines_word_0(gprs: Gprs, carry: Nat, placed: lines_rep(gprs, carry)): read_gpr(R13, gprs) = bitvec_nat::word_of_nat(64, carry) {
    sym(loop_nat_placed(read_gpr(R13, gprs), carry, placed))
}

// The loop's contract and where the count starts, as the producer states
// them.
fn lines_state_shape() → StateShape<Nat> {
    StateShape(lines_placement(), lines_rep, lines_fits, lines_loop_region(), lines_code(), lines_bytes(), count_lines, newline())
}
fn lines_state_loop() → StateLoop<Nat>(lines_state_shape()) {
    StateLoop(ReadStatePlacement(refl, refl, refl, refl, refl), lines_framed(),
        λ buffer needle budget cursor carry => lines_loop_source_agreement(buffer, needle, budget, cursor, carry),
        λ access before buffer needle budget cursor carry bounded low head readable fits =>
            lines_native(access, before, buffer, needle, budget, cursor, carry, bounded, low, head, readable, fits),
        line_body_folds())
}
fn lines_state_start() → StateStart<Nat>(lines_state_shape(), 0) {
    StateStart(lines_initialised(), λ seen budget fits => lines_room(newline(), lines_init(), refl, seen, budget, fits))
}

theorem lines_exit(file: List<BitVec(8)>, jumps: EofJumps, facts: StateJumpFacts(newline(), lines_bytes(), jumps),
    resident: (page: Nat → BitVec(8)) → CodeResident(io_fetch_access(), IoMemory(file, page), read_state_code(newline(), lines_bytes(), jumps),
        BitVec::ofNat(0x4000e8)),
    chunks: List<EofStep<True>>, ok: EofChunks(chunks), ending: EofEnd<False>, ending_ok: EofEnding(ending),
    room: eof_input(chunks).len() + 4096 < Nat::pow(2, 64), page: Nat → BitVec(8), gprs: Gprs, flags: Flags):
    LinuxRuns(io_linux(), eof_events(chunks, ending, [ExitEvent(bitvec_nat::word_of_nat(64, wc_l(eof_input(chunks))))]),
        io_initial(file, page, gprs, flags)) {
    read_count_runs(file, lines_state_shape(), lines_state_loop(), wc_l, count_lines_input, lines_state_start(), lines_word_0,
        jumps, facts, resident, chunks, ok, ending, ending_ok, room, page, gprs, flags)
}

theorem lines_print(file: List<BitVec(8)>, jumps: EofJumps, facts: StateJumpFacts(newline(), lines_bytes(), jumps),
    codes: PrintCodes, format: PrintFormat(codes), pj: PrintJumps, print_facts: PrintJumpFacts(pj),
    resident: (page: Nat → BitVec(8)) → CodeResident(io_fetch_access(), IoMemory(file, page),
        read_count_code(newline(), lines_bytes(), jumps, codes.word, codes.start, codes.length, pj), BitVec::ofNat(0x4000e8)),
    chunks: List<EofStep<True>>, ok: EofChunks(chunks), ending: EofEnd<False>, ending_ok: EofEnding(ending),
    room: eof_input(chunks).len() + 4096 < Nat::pow(2, 64), small: wc_l(eof_input(chunks)) < 10000,
    writes: List<WriteStep>, writes_ok: WriteSteps(writes)(decimal_line(wc_l(eof_input(chunks)))),
    written: WriteEnding, written_ok: WriteEndingOk(written), page: Nat → BitVec(8), gprs: Gprs, flags: Flags):
    LinuxRuns(io_linux(), eof_events(chunks, ending, write_events(decimal_line(wc_l(eof_input(chunks))), writes, written)),
        io_initial(file, page, gprs, flags)) {
    read_count_print_runs(file, lines_state_shape(), lines_state_loop(), wc_l, count_lines_input, lines_state_start(), lines_word_0, codes, format,
        jumps, facts, pj, print_facts, resident, chunks, ok, ending, ending_ok, room, small, writes, writes_ok, written, written_ok, page, gprs, flags)
}
"#;

#[test]
fn wc_l_count_process_composes() {
    let mut elab = base();
    elab.elab_module_source("elf64_count_print", COUNT).unwrap_or_else(|e| panic!("{}", e.render(COUNT)));
    elab.elab_module_source("wc_l", WC_L).unwrap_or_else(|e| panic!("{}", e.render(WC_L)));
    // The step as the loop over one chunk, as the read profile's producer
    // writes it beside a program (`count_lines`).
    elab.elab_module_source("lines_context", LINES_CONTEXT).unwrap_or_else(|e| panic!("{}", e.render(LINES_CONTEXT)));
    let emission = generate_elaborated_loop_x86(&elab, "lines", "lines_context::count_lines", &count_placement(), Some("wc_l::line_body_advances"))
        .unwrap_or_else(|e| panic!("{e:?}"));
    elab.elab_module_source("lines_pieces", &emission.pieces).unwrap_or_else(|e| panic!("{}", e.render(&emission.pieces)));
    elab.elab_module_source("lines_native", &emission.text).unwrap_or_else(|e| panic!("{}", e.render(&emission.text)));
    elab.elab_module_source("lines_count", WC_L_COUNT).unwrap_or_else(|e| panic!("{}", e.render(WC_L_COUNT)));
}
