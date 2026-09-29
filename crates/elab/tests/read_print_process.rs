use crate::read_loop_fixture::checker;

// A process of its own: each refusal re-checks the print pieces and what
// stands on them.
const READ_PIECES: &str = include_str!("../../../lib/elf64_read_pieces.hthr");
const STATE: &str = include_str!("../../../lib/elf64_read_state.hthr");
const PRINT: &str = include_str!("../../../lib/elf64_print_pieces.hthr");
const BV_OMEGA: &str = include_str!("../../../lib/std/bitvec/bitvec_omega.hthr");
const DECIMAL: &str = include_str!("../../../lib/decimal_line.hthr");
const WRITE: &str = include_str!("../../../lib/elf64_write_loop.hthr");
const COUNT: &str = include_str!("../../../lib/elf64_count_print.hthr");

// The print pieces (design §10.3) are refused where they are used, the write
// loop (elf64_write_loop) or the count's tail (elf64_count_print): the claim
// can't be restated over a program that writes with another syscall, to
// another descriptor, from the length register or with the start as the
// length, stores its word off the page or stores another register, exits
// nonzero, or formats a count other than the state's; nor over a write loop
// that advances by the length instead of what was sent, never counts down, or
// jumps from the wrong distance (docs/native-syscall-failures-design.md).
#[test]
fn slow_acceptance_read_print_refusals() {
    let mut elab = checker();
    for (name, source) in [("elf64_read_pieces", READ_PIECES), ("elf64_read_state", STATE), ("bitvec_omega", BV_OMEGA), ("decimal_line", DECIMAL)] {
        elab.elab_module_source(name, source).unwrap_or_else(|e| panic!("{name}: {}", e.render(source)));
    }
    let library = elab.semantic_image();
    for (name, from, to) in [
        ("write_number", "MovRI(Rdi, BitVec::ofNat(1)), MovRI(Rax, BitVec::ofNat(1))]", "MovRI(Rdi, BitVec::ofNat(1)), MovRI(Rax, BitVec::ofNat(2))]"),
        ("write_descriptor", "MovRI(Rdi, BitVec::ofNat(1)), MovRI(Rax", "MovRI(Rdi, BitVec::ofNat(2)), MovRI(Rax"),
        ("write_buffer", "[MovRR(Rsi, R9), ", "[MovRR(Rsi, R10), "),
        ("write_length", "MovRR(Rdx, R10), ", "MovRR(Rdx, R9), "),
        ("store_outside_page", "MovRI(R8, BitVec::ofNat(0x410000))", "MovRI(R8, BitVec::ofNat(0x411000))"),
        ("stored_register", "WordStore(R8, Rax)", "WordStore(R8, R9)"),
        ("exit_status", "MovRI(Rdi, BitVec::ofNat(0)), MovRI(Rax, BitVec::ofNat(60))", "MovRI(Rdi, BitVec::ofNat(1)), MovRI(Rax, BitVec::ofNat(60))"),
        ("count_from_elsewhere", "[MovRR(R11, R13), MovRI(R8", "[MovRR(R11, R12), MovRI(R8"),
        ("advance_by_length", "[AddRR(R9, Rax), SubRR(R10, Rax)]", "[AddRR(R9, R10), SubRR(R10, Rax)]"),
        ("remaining_not_counted", "[AddRR(R9, Rax), SubRR(R10, Rax)]", "[AddRR(R9, Rax), SubRR(R10, R10)]"),
        ("exit_span", "{ (((5 + eof_retry_len()) + 6) + eof_fail_len()) + 2 }", "{ (((5 + eof_retry_len()) + 6) + eof_fail_len()) + 3 }"),
        ("write_back_span", "{ ((((print_write_len() + 2) + eof_test_len())", "{ ((((print_write_len() + 1) + eof_test_len())"),
    ] {
        let bad = PRINT.replacen(from, to, 1);
        assert_ne!(bad, PRINT, "{name}");
        let mut elab = library.elaborator();
        let error = match elab.elab_module_source("elf64_print_pieces", &bad) {
            Err(error) => error.render(&bad),
            Ok(_) => match elab.elab_module_source("elf64_write_loop", WRITE) {
                Err(error) => error.render(WRITE),
                Ok(_) => elab.elab_module_source("elf64_count_print", COUNT).expect_err(name).render(COUNT),
            },
        };
        assert!(!error.contains("unbound") && !error.contains("ambiguous"), "{name}: {error}");
    }
}
