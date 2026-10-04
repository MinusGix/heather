//! The command model's hand test (docs/native-wc-command-design.md §10, C1):
//! a process written by hand opens argv[1], reads it to end of file through
//! the read driver with the fd held in RSP, closes it and exits 0, or exits 1
//! when the open fails; its claim checks over the library, and each change to
//! it is refused where it is wrong, not by a missing name.
use crate::read_loop_fixture::checker;

const READ_PIECES: &str = include_str!("../../../lib/elf64_read_pieces.hthr");
const PROCESS: &str = include_str!("fixtures/open_read_close.hthr");

fn base() -> heather_elab::Elaborator {
    let mut elab = checker();
    elab.elab_module_source("elf64_read_pieces", READ_PIECES).unwrap_or_else(|e| panic!("{}", e.render(READ_PIECES)));
    elab
}

#[test]
fn open_read_close_checks() {
    let mut elab = base();
    elab.elab_module_source("open_read_close", PROCESS).unwrap_or_else(|e| panic!("{}", e.render(PROCESS)));
}

// The claim can't be proved over a program that opens argv[0] instead of
// argv[1], keeps the fd where the read loop clobbers it, closes the open's
// result register instead of the fd, or exits 0 when the open failed.
#[test]
fn slow_acceptance_open_read_close_refusals() {
    let library = base().semantic_image();
    for (name, from, to) in [
        ("opens_argv0", "AddRI8(Rbx, BitVec::ofNat(16))", "AddRI8(Rbx, BitVec::ofNat(8))"),
        ("fd_clobbered", "[MovRR(Rsp, Rax)]", "[MovRR(Rbp, Rax)]"),
        ("closes_rax", "[MovRR(Rdi, Rsp), MovRI(Rax, BitVec::ofNat(3))]", "[MovRR(Rdi, Rax), MovRI(Rax, BitVec::ofNat(3))]"),
        ("failed_open_exits_0", "canonical_block_bytes(orc_exit_block(1))]", "canonical_block_bytes(orc_exit_block(0))]"),
    ] {
        let bad = PROCESS.replacen(from, to, 1);
        assert_ne!(bad, PROCESS, "{name}");
        let error = library.elaborator().elab_module_source("open_read_close", &bad).expect_err(name).render(&bad);
        assert!(!error.contains("unbound") && !error.contains("ambiguous"), "{name}: {error}");
    }
}
