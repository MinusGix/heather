//! Changes to the stat pass's code (elf64_stat_width), each refused where it
//! is wrong (stat_width_process.rs checks the library itself).
use crate::stat_width_process::{base, CURSOR, STAT};

// The pass's claim can't be proved when it fstats descriptor 1 for `-`,
// stats a path against no directory, reads the size from the mode's word,
// counts a failed stat as made-and-sized, adds a file of another kind and
// marks a regular one, forgets a stat was made (so stdin is stat'ed after
// the operands too), or widens to 8.
#[test]
fn slow_acceptance_stat_width_refusals() {
    let mut elab = base();
    elab.elab_module_source("elf64_operand_cursor", CURSOR).unwrap_or_else(|e| panic!("{}", e.render(CURSOR)));
    let library = elab.semantic_image();
    for (name, from, to) in [
        ("fstat_fd_1", "MovRI(Rdi, word_zero()), MovRI(Rsi, page_word())", "MovRI(Rdi, BitVec::ofNat(1)), MovRI(Rsi, page_word())"),
        ("no_dirfd", "MovRI(Rdi, at_fdcwd())", "MovRI(Rdi, word_zero())"),
        ("size_from_mode", "[MovRI(Rdi, size_word())]", "[MovRI(Rdi, mode_word())]"),
        ("failed_counted", "near_control_bytes(JumpIfNear(NE, wj_failed()))", "near_control_bytes(JumpIfNear(E, wj_failed()))"),
        ("kinds_swapped", "near_control_bytes(JumpIfNear(NE, wj_other()))", "near_control_bytes(JumpIfNear(E, wj_other()))"),
        ("made_forgotten", "[MovRI(R15, BitVec::ofNat(1)), MovRI(R11, word_zero())", "[MovRI(R15, BitVec::ofNat(0)), MovRI(R11, word_zero())"),
        ("widens_to_8", "{ [MovRI(Rsi, BitVec::ofNat(7))] }", "{ [MovRI(Rsi, BitVec::ofNat(8))] }"),
    ] {
        let bad = STAT.replacen(from, to, 1);
        assert_ne!(bad, STAT, "{name}");
        let error = library.elaborator().elab_module_source("elf64_stat_width", &bad).expect_err(name).render(&bad);
        assert!(!error.contains("unbound") && !error.contains("ambiguous"), "{name}: {error}");
    }
}
