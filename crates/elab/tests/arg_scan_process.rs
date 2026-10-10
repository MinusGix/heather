//! The command line, scanned once at entry (docs/native-wc-command-design.md
//! §6.1): the library scan checks over what it stands on, runs wherever a
//! program places it against any argv layout, agrees with `parse_args` on
//! GNU's cases, and each change to its code is refused where it is wrong, not
//! by a missing name.
use crate::read_loop_fixture::checker;

const BV_OMEGA: &str = include_str!("../../../lib/std/bitvec/bitvec_omega.hthr");
const DECIMAL: &str = include_str!("../../../lib/decimal_line.hthr");
const ASM: &str = include_str!("../../../lib/std/arch/x86_64/x86_64_asm.hthr");
const FORMAT: &str = include_str!("../../../lib/elf64_format_width.hthr");
const PROGRAM: &str = include_str!("../../../lib/command_program.hthr");
const SCAN: &str = include_str!("../../../lib/elf64_arg_scan.hthr");

fn base() -> heather_elab::Elaborator {
    let mut elab = checker();
    for (name, source) in [("bitvec_omega", BV_OMEGA), ("decimal_line", DECIMAL), ("x86_64_asm", ASM), ("elf64_format_width", FORMAT), ("command_program", PROGRAM)] {
        elab.elab_module_source(name, source).unwrap_or_else(|e| panic!("{name}: {}", e.render(source)));
    }
    elab
}

// The scan placed past any header in the file, entered with RSP at any argv
// layout: the client supplies only the placement. Then `parse_args` on
// `wc`'s letters (l, w, m, c; default lines, words and bytes) over §2's
// command lines.
const CLIENT: &str = "import elf64_arg_scan; import command_program; import elf64_format_width; import elf64_io; import linux_x86_64_io;
import x86_64; import x86_64_fetched_code; import bitvec; import bitvec_nat; import list; import logic; import nat; import option;
theorem scan_after_header(header: List<BitVec(8)>, letters: List<BitVec(8)>, default: BitVec(64),
    fits: header.len() + scan_code(letters, default).len() <= 65536, frame: Nat → BitVec(8), rest: BitVec(64) → Option<BitVec(8)>,
    page: Nat → BitVec(8), argv: List<List<BitVec(8)>>, state: MachineState<IoMemory>,
    memory_is: state.memory = IoMemory(IoImage(header ++ scan_code(letters, default), frame, rest), page),
    rip_is: state.rip = bitvec_nat::word_of_nat(64, 0x400000 + header.len()),
    argv_at: ArgvAt(io_data_access(), IoMemory(IoImage(header ++ scan_code(letters, default), frame, rest), page), read_gpr(Rsp, state.gprs), argv)):
    ScanResult(IoImage(header ++ scan_code(letters, default), frame, rest), page, bitvec_nat::word_of_nat(64, 0x400000 + header.len()), state.gprs,
        parse_args(letters, default, argv), state) {
    scan_runs(IoImage(header ++ scan_code(letters, default), frame, rest), letters, default, bitvec_nat::word_of_nat(64, 0x400000 + header.len()),
        λ any => io_code_resident(header, scan_code(letters, default), frame, rest, any, fits), page, argv, state, memory_is, rip_is, argv_at)
}
fn b(n: Nat) → BitVec(8) { BitVec::ofNat(n) }
fn wc_letters() → List<BitVec(8)> { [b(108), b(119), b(109), b(99)] }
fn wc_default() → BitVec(64) { BitVec::ofNat(11) }
fn wc() → List<BitVec(8)> { [b(119), b(99)] }
// wc -lc f1 is lines and bytes over f1.
theorem lines_bytes(): parse_args(wc_letters(), wc_default(), [wc(), [b(45), b(108), b(99)], [b(102)]]) = Scanned(BitVec::ofNat(9), [[b(102)]]) { refl }
// wc -c -m f1: chars and bytes are separate columns.
theorem chars_bytes(): parse_args(wc_letters(), wc_default(), [wc(), [b(45), b(99)], [b(45), b(109)], [b(102)]]) = Scanned(BitVec::ofNat(12), [[b(102)]]) { refl }
// wc f1 -x is refused, though the bad option comes last.
theorem bad_letter(): parse_args(wc_letters(), wc_default(), [wc(), [b(102)], [b(45), b(120)]]) = Refused { refl }
// wc -- -l -: after `--` both are operands, and nothing selected means the default.
theorem ended(): parse_args(wc_letters(), wc_default(), [wc(), [b(45), b(45)], [b(45), b(108)], [b(45)]]) =
    Scanned(BitVec::ofNat(11), [[b(45), b(108)], [b(45)]]) { refl }
// wc --lines is a long option, which this command refuses.
theorem long_option(): parse_args(wc_letters(), wc_default(), [wc(), [b(45), b(45), b(108)]]) = Refused { refl }
// wc, and a run with no argv at all: no operand, the default.
theorem no_operands(): parse_args(wc_letters(), wc_default(), [wc()]) = Scanned(BitVec::ofNat(11), Nil) { refl }
theorem no_argv(): parse_args(wc_letters(), wc_default(), Nil) = Scanned(BitVec::ofNat(11), Nil) { refl }
// wc f1 -l: options may follow operands, and a repeated letter selects once.
theorem permuted(): parse_args(wc_letters(), wc_default(), [wc(), [b(102)], [b(45), b(108), b(108)]]) = Scanned(BitVec::ofNat(1), [[b(102)]]) { refl }
// The code is the same length whatever the letters and default.
theorem scan_length(letters: List<BitVec(8)>, default: BitVec(64)): scan_code(letters, default).len() = 602 { scan_code_len(letters, default) }
";

#[test]
fn arg_scan_library_checks() {
    let mut elab = base();
    elab.elab_module_source("elf64_arg_scan", SCAN).unwrap_or_else(|e| panic!("{}", e.render(SCAN)));
    elab.elab_module_source("scan_client", CLIENT).unwrap_or_else(|e| panic!("{}", e.render(CLIENT)));
}

// The claim can't be proved over a letter table whose bits are shifted one
// column, a `--` that leaves the options open, an options-ended test that
// reads the flag the wrong way round, a refusal that exits 0, a default
// chosen by the operand count rather than the selection, a scan that skips
// argv[1] as well as argv[0], or a letter loop whose back jump falls through
// to the operand code.
#[test]
fn slow_acceptance_arg_scan_refusals() {
    let library = base().semantic_image();
    for (name, from, to) in [
        ("bit_shifted", "[MovRI(R11, column_bit(i)), OrRR(Rdx, R11)]", "[MovRI(R11, column_bit(Succ(i))), OrRR(Rdx, R11)]"),
        ("dashes_leave_open", "{ [MovRI(R10, BitVec::ofNat(1))] }", "{ [MovRI(R10, BitVec::ofNat(0))] }"),
        ("ended_inverted", "then(ls_ended(), Jcc(NE, ts_operand()))", "then(ls_ended(), Jcc(E, ts_operand()))"),
        ("refusal_exits_0", "[MovRI(Rdi, BitVec::ofNat(1)), MovRI(Rax, BitVec::ofNat(60))]", "[MovRI(Rdi, BitVec::ofNat(0)), MovRI(Rax, BitVec::ofNat(60))]"),
        ("default_by_count", "[MovRI(R11, word_zero()), CmpRR(R8, R11)]", "[MovRI(R11, word_zero()), CmpRR(R9, R11)]"),
        ("skips_two", "[MovRR(Rbx, Rsp), AddRI8(Rbx, eight_byte()),", "[MovRR(Rbx, Rsp), AddRI8(Rbx, BitVec::ofNat(16)),"),
        ("letters_fall_out", "then(ls_select(), Jmp(ts_letters()))", "then(ls_select(), Jmp(ts_operand()))"),
    ] {
        let bad = SCAN.replacen(from, to, 1);
        assert_ne!(bad, SCAN, "{name}");
        let error = library.elaborator().elab_module_source("elf64_arg_scan", &bad).expect_err(name).render(&bad);
        assert!(!error.contains("unbound") && !error.contains("ambiguous"), "{name}: {error}");
    }
}
