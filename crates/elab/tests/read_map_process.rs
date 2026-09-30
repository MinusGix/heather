use crate::read_loop_fixture::checker;
use heather_elab::function_ir_source::generate_elaborated_typed_x86;
use heather_elab::function_ir_x86_lower::{Gpr, Placements};

const READ_PIECES: &str = include_str!("../../../lib/elf64_read_pieces.hthr");
const DECIMAL: &str = include_str!("../../../lib/decimal_line.hthr");
const PRINT: &str = include_str!("../../../lib/elf64_print_pieces.hthr");
const WRITE: &str = include_str!("../../../lib/elf64_write_loop.hthr");
const BV_OMEGA: &str = include_str!("../../../lib/std/bitvec/bitvec_omega.hthr");
const PROCESS: &str = include_str!("../../../lib/elf64_read_map.hthr");

// Everything the map process stands on (docs/native-tr-design.md §3).
fn base() -> heather_elab::Elaborator {
    let mut elab = checker();
    for (name, source) in [("elf64_read_pieces", READ_PIECES), ("bitvec_omega", BV_OMEGA), ("decimal_line", DECIMAL),
        ("elf64_print_pieces", PRINT), ("elf64_write_loop", WRITE)] {
        elab.elab_module_source(name, source).unwrap_or_else(|e| panic!("{name}: {}", e.render(source)));
    }
    elab
}

// `tr a-z A-Z`'s byte map, as the example program spells it.
const BYTE_MAPS: &str = r#"import bitvec; import bool;
fn lower_byte(b: BitVec(8)) → Bool {
    match b.unsigned_lt_bit(BitVec::ofNat(0x61)) { True => False, False => b.unsigned_lt_bit(BitVec::ofNat(0x7b)) }
}
fn upcase(b: BitVec(8)) → BitVec(8) { match lower_byte(b) { True => b.sub(BitVec::ofNat(0x20)), False => b } }
"#;

// The map piece at the map loop's registers: the byte in RAX, its image in
// RDX, and the scratch the loop leaves free.
fn upcase_piece(elab: &mut heather_elab::Elaborator, temporaries: &[Gpr]) {
    elab.elab_module_source("byte_maps", BYTE_MAPS).unwrap_or_else(|e| panic!("{}", e.render(BYTE_MAPS)));
    let emission = generate_elaborated_typed_x86(elab, "upcase", "byte_maps::upcase", &Placements::from([(0, Gpr::Rax)]),
        temporaries, &Placements::from([(1, Gpr::Rdx)])).unwrap_or_else(|e| panic!("{e}"));
    elab.elab_module_source("upcase_publication", &emission.text).unwrap_or_else(|e| panic!("{}", e.render(&emission.text)));
}

// The piece's typed artifact is a `MapPiece`, what it keeps covers the loop's
// registers, and the process claim and what stdout receives follow for any
// file holding the code.
const UPCASE_PROCESS: &str = r#"
import elf64_read_map; import elf64_write_loop; import elf64_print_pieces; import elf64_read_pieces;
import elf64_io; import linux_x86_64_io; import linux_x86_64_entry; import x86_64_structured_block;
import x86_64; import x86_64_fetch; import x86_64_fetched_code;
import bitvec; import bitvec_nat; import bool; import list; import logic; import nat;
import byte_maps; import upcase_publication;

theorem upcase_map_piece(): MapPiece(upcase, upcase_code(), upcase_Protected) { λ before b placed => upcase_typed_artifact(b, before, placed) }
theorem upcase_keeps(): MapKeeps(upcase_Protected) { MapKeeps(trivial, trivial, trivial, trivial, trivial) }

fn upcase_map_byte() → MapByte(upcase) { MapByte(upcase_code(), upcase_Protected, upcase_map_piece(), upcase_keeps()) }

theorem upcase_runs(file: List<BitVec(8)>, jumps: MapJumps, pj: PrintJumps, facts: MapJumpFacts(upcase_bytes().len(), jumps, pj),
    resident: (page: Nat → BitVec(8)) → CodeResident(io_fetch_access(), IoMemory(file, page), map_code(upcase_code(), jumps, pj),
        BitVec::ofNat(0x4000e8)),
    steps: List<EofStep<List<WriteStep>>>, ok: MapSteps(upcase, steps), ending: EofEnd<WriteFailure>, ending_ok: MapEndingOk(upcase, ending),
    page: Nat → BitVec(8), gprs: Gprs, flags: Flags):
    LinuxRuns(io_linux(), map_events(upcase, steps, ending), io_initial(file, page, gprs, flags)) {
    read_map_runs(file, upcase, upcase_map_byte(), jumps, pj, facts, resident, steps, ok, ending, ending_ok, page, gprs, flags)
}

theorem upcase_sends(steps: List<EofStep<List<WriteStep>>>, ok: MapSteps(upcase, steps)):
    sent_to(BitVec::ofNat(1), map_events(upcase, steps, AtEnd)) = map_input(steps).map(upcase) {
    map_sends(upcase, steps, ok)
}
"#;

#[test]
fn upcase_map_process_composes() {
    let mut elab = base();
    elab.elab_module_source("elf64_read_map", PROCESS).unwrap_or_else(|e| panic!("{}", e.render(PROCESS)));
    upcase_piece(&mut elab, &[Gpr::Rdx, Gpr::Rbx, Gpr::Rdi, Gpr::R8]);
    elab.elab_module_source("upcase_process", UPCASE_PROCESS).unwrap_or_else(|e| panic!("{}", e.render(UPCASE_PROCESS)));
    // A piece that may overwrite the loop's step register is not a piece the
    // loop can keep going over.
    let mut clobbering = base();
    clobbering.elab_module_source("elf64_read_map", PROCESS).unwrap_or_else(|e| panic!("{}", e.render(PROCESS)));
    upcase_piece(&mut clobbering, &[Gpr::Rdx, Gpr::R11, Gpr::Rbx, Gpr::Rdi]);
    let error = clobbering.elab_module_source("upcase_process", UPCASE_PROCESS).expect_err("a piece clobbering R11").render(UPCASE_PROCESS);
    assert!(error.contains("but `False` is expected") && !error.contains("unbound"), "{error}");
    // Nor does stdout receive the input under another map.
    let other = UPCASE_PROCESS.replace("= map_input(steps).map(upcase) {", "= map_input(steps).map(lower_image) {")
        .replace("theorem upcase_sends(", "fn lower_image(b: BitVec(8)) → BitVec(8) { b.bor(BitVec::ofNat(0x20)) }\ntheorem upcase_sends(");
    let error = elab.elab_module_source("upcase_other", &other).expect_err("another map").render(&other);
    assert!(!error.contains("unbound") && !error.contains("ambiguous"), "{error}");
}

// Each change to the process is refused where it is wrong, not by a missing
// name: a step that moves the cursor by the wrong amount, a store at another
// register's byte, a JNZ that tests the other way, a write that starts past
// the page, or a layout that measures the store a byte short.
#[test]
fn slow_acceptance_read_map_refusals() {
    let library = base().semantic_image();
    for (name, from, to) in [
        ("step_by_two", "MovRI(R11, BitVec::ofNat(1))]", "MovRI(R11, BitVec::ofNat(2))]"),
        ("store_elsewhere", "fn map_store() → ByteStore { ByteStore(base := Rsi, source := Rdx) }",
            "fn map_store() → ByteStore { ByteStore(base := Rsi, source := Rax) }"),
        ("jnz_inverted", "near_control_bytes(JumpIfNear(NE, jumps.ld)), write_loop_code(pj)]", "near_control_bytes(JumpIfNear(E, jumps.ld)), write_loop_code(pj)]"),
        ("write_past_page", "MovRI(R9, BitVec::ofNat(io_page_base()))", "MovRI(R9, BitVec::ofNat(0x410001))"),
        ("store_measured_short", "map_load_len(), p, 3, map_step_len()", "map_load_len(), p, 2, map_step_len()"),
    ] {
        let bad = PROCESS.replacen(from, to, 1);
        assert_ne!(bad, PROCESS, "{name}");
        let error = library.elaborator().elab_module_source("elf64_read_map", &bad).expect_err(name).render(&bad);
        assert!(!error.contains("unbound") && !error.contains("ambiguous"), "{name}: {error}");
    }
}
