use crate::read_loop_fixture::checker;

const READ_PIECES: &str = include_str!("../../../lib/elf64_read_pieces.hthr");
const BV_OMEGA: &str = include_str!("../../../lib/std/bitvec/bitvec_omega.hthr");
const DECIMAL: &str = include_str!("../../../lib/decimal_line.hthr");
const FIELD: &str = include_str!("../../../lib/field_line.hthr");
const PRINT: &str = include_str!("../../../lib/elf64_print_pieces.hthr");
const WRITE: &str = include_str!("../../../lib/elf64_write_loop.hthr");
const FIELDS: &str = include_str!("../../../lib/elf64_read_fields.hthr");

// Everything the three-field tail stands on (docs/native-wc-design.md §5).
fn base() -> heather_elab::Elaborator {
    let mut elab = checker();
    for (name, source) in [("elf64_read_pieces", READ_PIECES), ("bitvec_omega", BV_OMEGA),
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

// Each change to the tail is refused where it is wrong, not by a missing
// name: the tail's claim can't be proved over a tail that stores another
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
