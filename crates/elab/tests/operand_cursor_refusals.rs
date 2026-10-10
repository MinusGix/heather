//! Changes to the operand cursor's code (elf64_operand_cursor), each refused
//! where it is wrong (stat_width_process.rs checks the library itself).
use crate::stat_width_process::{base, CURSOR};

// The cursor's claim can't be proved when `--` leaves the options open or a
// lone `-` is passed over as an option.
#[test]
fn slow_acceptance_operand_cursor_refusals() {
    let library = base().semantic_image();
    for (name, from, to) in [
        ("dashes_leave_open", "{ [MovRI(R12, BitVec::ofNat(1))] }", "{ [MovRI(R12, BitVec::ofNat(0))] }"),
        ("lone_dash_skipped", "then(lc_second_nul(), Jcc(E, tc_end()))", "then(lc_second_nul(), Jcc(NE, tc_end()))"),
    ] {
        let bad = CURSOR.replacen(from, to, 1);
        assert_ne!(bad, CURSOR, "{name}");
        let error = library.elaborator().elab_module_source("elf64_operand_cursor", &bad).expect_err(name).render(&bad);
        assert!(!error.contains("unbound") && !error.contains("ambiguous"), "{name}: {error}");
    }
}
