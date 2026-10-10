//! Changes to the row writer's code (elf64_row_fields), each refused where it
//! is wrong (row_fields_process.rs checks the library itself).
use crate::row_fields_process::{base, ROW};

// The claim can't be proved when the gap is not a space, an unselected slot
// is printed, the space goes before the first field, every field after the
// first is left without its space, R12 strides two slots, the bit is not
// doubled, or the back jump lands past the selection test.
#[test]
fn slow_acceptance_row_fields_refusals() {
    let library = base().semantic_image();
    for (name, from, to) in [
        ("gap_not_space", "[MovRI(R11, BitVec::ofNat(32))]", "[MovRI(R11, BitVec::ofNat(9))]"),
        ("unselected_printed", "then(lr_head(), Jcc(E, tr_skip()))", "then(lr_head(), Jcc(NE, tr_skip()))"),
        ("leading_space", "then(lr_lead(), Jcc(NE, tr_field()))", "then(lr_lead(), Jcc(E, tr_field()))"),
        ("first_never_cleared", "[MovRI(R9, word_zero()), MovRR(Rdx, R14)]", "[MovRI(R9, BitVec::ofNat(1)), MovRR(Rdx, R14)]"),
        ("two_slot_stride", "[AddRI8(R12, eight_byte()),", "[AddRI8(R12, BitVec::ofNat(16)),"),
        ("bit_not_doubled", "AddRR(R15, R15)", "AddRR(R15, R13)"),
        ("back_past_test", "then(lr_skip(), Jcc(NE, tr_head()))", "then(lr_skip(), Jcc(NE, tr_field()))"),
    ] {
        let bad = ROW.replacen(from, to, 1);
        assert_ne!(bad, ROW, "{name}");
        let error = library.elaborator().elab_module_source("elf64_row_fields", &bad).expect_err(name).render(&bad);
        assert!(!error.contains("unbound") && !error.contains("ambiguous"), "{name}: {error}");
    }
}
