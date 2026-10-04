//! Changes to the per-file driver's code (elf64_command), each refused where
//! it is wrong (the warm-up checks the library itself, and
//! command_process.rs composes it).
use crate::command_prefix::COMMAND_PREFIX;
use crate::support;

// The claim can't be proved when a failed open leaves the status clean, the
// total row is printed after one operand, the read head reads the
// descriptor open did not return, or the name is written with a length
// measured from elsewhere.
#[test]
fn slow_acceptance_command_refusals() {
    // Everything the command stands on, replayed without the command itself.
    let (stands_on, command) = COMMAND_PREFIX.split_at(COMMAND_PREFIX.len() - 1);
    let library = support::semantic_test_base(stands_on).semantic_image();
    let command = command[0].1;
    for (name, from, to) in [
        ("failed_open_clean", "[MovRI(Rax, BitVec::ofNat(1)), MovRI(R11, slot_at(18))]", "[MovRI(Rax, BitVec::ofNat(0)), MovRI(R11, slot_at(18))]"),
        ("total_after_one", "[MovRI(R11, BitVec::ofNat(2)), CmpRR(Rax, R11)]", "[MovRI(R11, BitVec::ofNat(1)), CmpRR(Rax, R11)]"),
        ("reads_another_fd", "[MovRR(Rsp, Rax), MovRI(Rax, BitVec::ofNat(1))", "[MovRR(Rsp, Rdi), MovRI(Rax, BitVec::ofNat(1))"),
        ("name_length_elsewhere", "[MovRR(R9, Rsi), MovRR(R10, Rdx), SubRR(R10, Rsi)]", "[MovRR(R9, Rsi), MovRR(R10, Rdi), SubRR(R10, Rsi)]"),
    ] {
        let bad = command.replacen(from, to, 1);
        assert_ne!(bad, command, "{name}");
        let error = library.elaborator().elab_module_source("elf64_command", &bad).expect_err(name).render(&bad);
        assert!(!error.contains("unbound") && !error.contains("ambiguous"), "{name}: {error}");
    }
}
