use crate::read_loop_fixture::checker;

// A process of its own: the refusals re-check the print module seven times,
// and beside read_loop_process's tests they passed the CPU rail.
const PROCESS: &str = include_str!("../../../lib/elf64_read_loop.hthr");
const PRINT: &str = include_str!("../../../lib/elf64_read_print.hthr");
const BV_OMEGA: &str = include_str!("../../../lib/std/bitvec/omega.hthr");
const DECIMAL: &str = include_str!("../../../lib/decimal_line.hthr");

// The print profile (design §10.3), refused the same way: the claim can't be
// restated over a program that writes with another syscall, to another
// descriptor, from the length register or with the start as the length,
// stores its word off the page or stores another register, exits nonzero, or
// formats a count other than the loop's total.
#[test]
fn slow_acceptance_read_print_refusals() {
    let mut elab = checker();
    elab.elab_module_source("elf64_read_loop", PROCESS).unwrap_or_else(|e| panic!("{}", e.render(PROCESS)));
    elab.elab_module_source("bitvec_omega", BV_OMEGA).unwrap_or_else(|e| panic!("{}", e.render(BV_OMEGA)));
    elab.elab_module_source("decimal_line", DECIMAL).unwrap_or_else(|e| panic!("{}", e.render(DECIMAL)));
    let library = elab.semantic_image();
    library.elaborator().elab_module_source("elf64_read_print", PRINT).unwrap_or_else(|e| panic!("{}", e.render(PRINT)));
    for (name, from, to) in [
        ("write_number", "MovRI(Rdi, BitVec::ofNat(1)), MovRI(Rax, BitVec::ofNat(1))]", "MovRI(Rdi, BitVec::ofNat(1)), MovRI(Rax, BitVec::ofNat(2))]"),
        ("write_descriptor", "MovRI(Rdi, BitVec::ofNat(1)), MovRI(Rax", "MovRI(Rdi, BitVec::ofNat(2)), MovRI(Rax"),
        ("write_buffer", "[MovRR(Rsi, R9), ", "[MovRR(Rsi, R10), "),
        ("write_length", "MovRR(Rdx, R10), ", "MovRR(Rdx, R9), "),
        ("store_outside_page", "MovRI(R8, BitVec::ofNat(0x401000))", "MovRI(R8, BitVec::ofNat(0x402000))"),
        ("stored_register", "WordStore(R8, Rax)", "WordStore(R8, R9)"),
        ("exit_status", "MovRI(Rdi, BitVec::ofNat(0)), MovRI(Rax, BitVec::ofNat(60))", "MovRI(Rdi, BitVec::ofNat(1)), MovRI(Rax, BitVec::ofNat(60))"),
        ("count_from_elsewhere", "[MovRR(R11, R13), MovRI(R8", "[MovRR(R11, R12), MovRI(R8"),
    ] {
        let bad = PRINT.replacen(from, to, 1);
        assert_ne!(bad, PRINT, "{name}");
        let error = library.elaborator().elab_module_source("elf64_read_print", &bad).expect_err(name).render(&bad);
        assert!(!error.contains("unbound") && !error.contains("ambiguous"), "{name}: {error}");
    }
}
