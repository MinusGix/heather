use crate::function_ir_loop_trace::{wc_placement, WC_SOURCE};
use crate::read_loop_fixture::checker;
use heather_elab::function_ir_source::generate_elaborated_record_loop_x86;

const READ_LOOP: &str = include_str!("../../../lib/elf64_read_loop.hthr");
const PROCESS: &str = include_str!("../../../lib/elf64_read_state.hthr");

// The Nat process, whose blocks and read trace this one reuses.
fn base() -> heather_elab::Elaborator {
    let mut elab = checker();
    elab.elab_module_source("elf64_read_loop", READ_LOOP).unwrap_or_else(|e| panic!("{}", e.render(READ_LOOP)));
    elab
}

#[test]
fn read_state_library_checks() {
    let mut elab = base();
    elab.elab_module_source("elf64_read_state", PROCESS).unwrap_or_else(|e| panic!("{}", e.render(PROCESS)));
}

// What `wc` supplies beside its loop certificate (docs/native-wc-design.md
// §4.8): its step folds, its placement moves with the state registers, init's
// zeros place the zero state, its state fits every chunk, and the line count
// is in R13 for the exit.
pub(crate) const WC_PROCESS: &str = r#"
import elf64_read_state; import elf64_read_loop; import elf64_io; import linux_x86_64_io; import linux_x86_64_entry;
import function_ir_loop; import function_ir_loop_trace; import x86_64; import x86_64_fetch; import x86_64_fetched_code;
import bitvec; import bitvec_nat; import bool; import list; import logic; import nat;
import wc_loop; import wc_pieces; import wc_native;

theorem wc_body_folds(): LoopFolds(wc_loop_region()) {
    λ needle cursor byte s => match space_byte(byte) as λ sp => match sp as λ _ => LoopStep<WcState> {
            True => match newline_byte(byte) as λ _ => LoopStep<WcState> {
                True => Continue(WcState(Succ(s.lines), s.words, Succ(s.bytes), False)),
                False => Continue(WcState(s.lines, s.words, Succ(s.bytes), False)),
            },
            False => match s.inside as λ _ => LoopStep<WcState> {
                True => Continue(WcState(s.lines, s.words, Succ(s.bytes), True)),
                False => Continue(WcState(s.lines, Succ(s.words), Succ(s.bytes), True)),
            },
        } = Continue(loop_step_payload(match sp as λ _ => LoopStep<WcState> {
            True => match newline_byte(byte) as λ _ => LoopStep<WcState> {
                True => Continue(WcState(Succ(s.lines), s.words, Succ(s.bytes), False)),
                False => Continue(WcState(s.lines, s.words, Succ(s.bytes), False)),
            },
            False => match s.inside as λ _ => LoopStep<WcState> {
                True => Continue(WcState(s.lines, s.words, Succ(s.bytes), True)),
                False => Continue(WcState(s.lines, Succ(s.words), Succ(s.bytes), True)),
            },
        })) {
        True => match newline_byte(byte) as λ nl => match nl as λ _ => LoopStep<WcState> {
                True => Continue(WcState(Succ(s.lines), s.words, Succ(s.bytes), False)),
                False => Continue(WcState(s.lines, s.words, Succ(s.bytes), False)),
            } = Continue(loop_step_payload(match nl as λ _ => LoopStep<WcState> {
                True => Continue(WcState(Succ(s.lines), s.words, Succ(s.bytes), False)),
                False => Continue(WcState(s.lines, s.words, Succ(s.bytes), False)),
            })) { True => refl, False => refl },
        False => match s.inside as λ i => match i as λ _ => LoopStep<WcState> {
                True => Continue(WcState(s.lines, s.words, Succ(s.bytes), True)),
                False => Continue(WcState(s.lines, Succ(s.words), Succ(s.bytes), True)),
            } = Continue(loop_step_payload(match i as λ _ => LoopStep<WcState> {
                True => Continue(WcState(s.lines, s.words, Succ(s.bytes), True)),
                False => Continue(WcState(s.lines, Succ(s.words), Succ(s.bytes), True)),
            })) { True => refl, False => refl },
    }
}

theorem wc_framed(): StateFramed(wc_rep) {
    λ before after carry kept placed =>
        wc_rep_moves(before, after, carry, kept.left, kept.right.left, kept.right.right.left, kept.right.right.right, placed)
}
theorem wc_initialised(): StateInitialised(wc_rep, WcState(0, 0, 0, False)) { λ state => ⟨refl, ⟨refl, ⟨refl, refl⟩⟩⟩ }
theorem wc_lines_word(gprs: Gprs, carry: WcState, placed: wc_rep(gprs, carry)):
    read_gpr(R13, gprs) = bitvec_nat::word_of_nat(64, carry.lines) {
    sym(loop_nat_placed(read_gpr(R13, gprs), carry.lines, placed.left))
}

// Any file holding the process's code: for every history of reads, a run
// that exits with the lines of the state folded over the input.
theorem wc_runs(file: List<BitVec(8)>, needle: BitVec(8), jumps: EofJumps,
    exit_reads: jumps.ed.sign_extend(32).toNat() = state_exit_skip(needle, wc_bytes()),
    fail_reads: jumps.sd.sign_extend(32).toNat() = state_fail_skip(needle, wc_bytes()),
    back_closes: state_loop_span(needle, wc_bytes()) + 5 + jumps.bd.sign_extend(32).toNat() = Nat::pow(2, 64),
    retry_closes: state_retry_span(needle, wc_bytes()) + 6 + jumps.rd.sign_extend(32).toNat() = Nat::pow(2, 64),
    resident: (page: Nat → BitVec(8)) → CodeResident(io_fetch_access(), IoMemory(file, page), read_state_code(needle, wc_bytes(), jumps),
        BitVec::ofNat(0x4000e8)),
    chunks: List<ReadStep>, ok: EofChunks(chunks), ending: ReadEnding, ending_ok: EofEnding(ending),
    room: eof_input(chunks).len() + 4096 < Nat::pow(2, 64), page: Nat → BitVec(8), gprs: Gprs, flags: Flags):
    LinuxRuns(io_linux(), eof_events(chunks, ending,
        [ExitEvent(bitvec_nat::word_of_nat(64, step_fold(wc_loop_region(), needle, eof_input(chunks), WcState(0, 0, 0, False)).lines))]),
        io_initial(file, page, gprs, flags)) {
    read_state_runs(file, wc_placement(), ReadStatePlacement(refl, refl, refl, refl, refl), wc_rep, wc_fits, wc_framed(),
        wc_loop_region(), wc_code(), wc_bytes(), count_wc, needle,
        λ buffer needle budget cursor carry => wc_loop_source_agreement(buffer, needle, budget, cursor, carry),
        λ access before buffer needle budget cursor carry bounded low head readable fits =>
            wc_native(access, before, buffer, needle, budget, cursor, carry, bounded, low, head, readable, fits),
        wc_body_folds(), WcState(0, 0, 0, False), wc_initialised(),
        λ seen budget fits => wc_room(needle, WcState(0, 0, 0, False), ⟨refl, ⟨refl, refl⟩⟩, seen, budget, fits),
        λ (s: WcState) => s.lines, wc_lines_word,
        jumps, exit_reads, fail_reads, back_closes, retry_closes, resident, chunks, ok, ending, ending_ok, room, page, gprs, flags)
}
"#;

// wc's record loop, generated, then the process library at `process`; the
// caller checks the client module.
fn wc_with(process: &str) -> Result<heather_elab::Elaborator, String> {
    let mut elab = base();
    elab.elab_module_source("elf64_read_state", process).map_err(|e| e.render(process))?;
    elab.elab_module_source("wc_loop", WC_SOURCE).unwrap_or_else(|e| panic!("{}", e.render(WC_SOURCE)));
    elab.elab_module_source("wc_context", "import function_ir_loop; import function_ir_loop_x86; import wc_loop; import bitvec; import bool;").unwrap();
    let emission = generate_elaborated_record_loop_x86(&elab, "wc", "wc_loop::count_wc", &wc_placement(), "wc_loop::wc_body_advances")
        .unwrap_or_else(|e| panic!("{e:?}"));
    elab.elab_module_source("wc_pieces", &emission.pieces).unwrap_or_else(|e| panic!("{}", e.render(&emission.pieces)));
    elab.elab_module_source("wc_native", &emission.text).unwrap_or_else(|e| panic!("{}", e.render(&emission.text)));
    Ok(elab)
}

// The record loop's certificate, the state generator's two lemmas and wc's
// facts compose into the process claim.
#[test]
fn wc_state_process_composes() {
    let mut elab = wc_with(PROCESS).unwrap_or_else(|e| panic!("{e}"));
    elab.elab_module_source("wc_process", WC_PROCESS).unwrap_or_else(|e| panic!("{}", e.render(WC_PROCESS)));
}

// Each change to the process shape is refused where it is wrong, not by a
// missing name: the claim can't be restated over a setup that writes a state
// register, a jump back or a failure jump from the wrong distance, a program
// that leaves out init, or an exit that reads another register than the
// status premise names; nor, for wc, over an init that zeroes the wrong
// register.
#[test]
fn slow_acceptance_read_state_refusals() {
    let library = base().semantic_image();
    for (name, from, to) in [
        ("setup_writes_state", "     MovRI(Rsi, BitVec::ofNat(0))]\n}", "     MovRI(Rsi, BitVec::ofNat(0)), MovRI(R15, BitVec::ofNat(0))]\n}"),
        ("setup_base", "MovRI(Rdi, BitVec::ofNat(0x410000)), MovRI(Rcx", "MovRI(Rdi, BitVec::ofNat(0x410001)), MovRI(Rcx"),
        ("back_span", "(((((read_entry_len() + 2) + eof_test_len())", "(((((read_entry_len() + 3) + eof_test_len())"),
        ("failure_span", "    (state_setup_len(needle) + loop_bytes.len()) + 5\n}", "    (state_setup_len(needle) + loop_bytes.len()) + 4\n}"),
        ("init_left_out", "    canonical_block_bytes(state_init_block()) ++ (canonical_block_bytes(read_entry_block())",
            "    (canonical_block_bytes(read_entry_block())"),
        ("status_elsewhere", "rep(gprs, carry) → read_gpr(R13, gprs) = bitvec_nat::word_of_nat(64, status(carry)),\n    total: C,",
            "rep(gprs, carry) → read_gpr(R14, gprs) = bitvec_nat::word_of_nat(64, status(carry)),\n    total: C,"),
    ] {
        let bad = PROCESS.replacen(from, to, 1);
        assert_ne!(bad, PROCESS, "{name}");
        let error = library.elaborator().elab_module_source("elf64_read_state", &bad).expect_err(name).render(&bad);
        assert!(!error.contains("unbound") && !error.contains("ambiguous"), "{name}: {error}");
    }
    let bad = PROCESS.replacen("MovRI(R8, BitVec::ofNat(0))]", "MovRI(R9, BitVec::ofNat(0))]", 1);
    assert_ne!(bad, PROCESS);
    let mut elab = wc_with(&bad).unwrap_or_else(|e| panic!("{e}"));
    let error = elab.elab_module_source("wc_process", WC_PROCESS).expect_err("init_misses_state").render(WC_PROCESS);
    assert!(error.contains("wc_initialised") && !error.contains("unbound"), "{error}");
}
