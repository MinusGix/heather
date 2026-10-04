//! `%*d` for any 64-bit count (docs/native-wc-command-design.md §7): the
//! library formatter checks over what it stands on, runs wherever a program
//! places it, and each change to its code is refused where it is wrong, not
//! by a missing name.
use crate::read_loop_fixture::checker;

const BV_OMEGA: &str = include_str!("../../../lib/std/bitvec/bitvec_omega.hthr");
const DECIMAL: &str = include_str!("../../../lib/decimal_line.hthr");
const FORMAT: &str = include_str!("../../../lib/elf64_format_width.hthr");

fn base() -> heather_elab::Elaborator {
    let mut elab = checker();
    for (name, source) in [("bitvec_omega", BV_OMEGA), ("decimal_line", DECIMAL)] {
        elab.elab_module_source(name, source).unwrap_or_else(|e| panic!("{name}: {}", e.render(source)));
    }
    elab
}

// The formatter placed past any header in the file, entered with any count,
// width and cursor that leave room in the page: the client supplies only the
// placement, and the library's claim does the rest.
const CLIENT: &str = "import elf64_format_width; import elf64_io; import linux_x86_64_io; import decimal_line;
import x86_64; import x86_64_fetched_code; import bitvec; import bitvec_nat; import list; import logic; import nat; import option;
theorem format_after_header(header: List<BitVec(8)>, fits: header.len() + format_code().len() <= 65536,
    frame: Nat → BitVec(8), rest: BitVec(64) → Option<BitVec(8)>, page: Nat → BitVec(8), w, o: Nat,
    state: MachineState<IoMemory>, memory_is: state.memory = IoMemory(IoImage(header ++ format_code(), frame, rest), page),
    rip_is: state.rip = bitvec_nat::word_of_nat(64, 0x400000 + header.len()),
    rdx: read_gpr(Rdx, state.gprs).toNat() = w, rdi: read_gpr(Rdi, state.gprs).toNat() = io_page_base() + o,
    room: o + padded_decimal(w, read_gpr(Rax, state.gprs).toNat()).len() <= 4096):
    Exists<MachineState<IoMemory>>(λ after => LinuxSteps(io_linux(), state, after) ∧
        FmtOut(IoImage(header ++ format_code(), frame, rest), page, o, padded_decimal(w, read_gpr(Rax, state.gprs).toNat()),
            next_rip(bitvec_nat::word_of_nat(64, 0x400000 + header.len()), format_len()), state.gprs, after)) {
    format_runs(IoImage(header ++ format_code(), frame, rest), bitvec_nat::word_of_nat(64, 0x400000 + header.len()),
        λ any => io_code_resident(header, format_code(), frame, rest, any, fits), page, w, o, state, memory_is, rip_is, rdx, rdi, room)
}
// Zero prints one digit, at width one as POSIX `%d` does.
theorem prints_zero(): padded_decimal(1, 0) = [BitVec::ofNat(48)] { refl }
// The code is the same bytes every time, and its length is closed.
theorem format_length(): format_len() = 1588 { refl }
";

#[test]
fn format_width_library_checks() {
    let mut elab = base();
    elab.elab_module_source("elf64_format_width", FORMAT).unwrap_or_else(|e| panic!("{}", e.render(FORMAT)));
    elab.elab_module_source("format_client", CLIENT).unwrap_or_else(|e| panic!("{}", e.render(CLIENT)));
}

// The claim can't be proved over a padding loop that runs while the width
// is reached rather than exceeded (one space too many), a count that starts
// at no places, a place skipped by what is left of the count rather than the
// whole count (a zero inside a count dropped), a digit counted from '/'
// rather than '0', a units digit taken from the whole count, or a digit loop
// whose exit lands one byte past the store.
#[test]
fn slow_acceptance_format_width_refusals() {
    let library = base().semantic_image();
    for (name, from, to) in [
        ("pad_one_more", "JumpIfNear(AE, BitVec::ofNat(26))", "JumpIfNear(A, BitVec::ofNat(26))"),
        ("count_from_zero", "[MovRR(Rbx, Rax), MovRI(Rsi, BitVec::ofNat(1))]", "[MovRR(Rbx, Rax), MovRI(Rsi, BitVec::ofNat(0))]"),
        ("skip_by_rest", "[MovRI(R11, place_word(i)), CmpRR(Rbx, R11)]", "[MovRI(R11, place_word(i)), CmpRR(Rax, R11)]"),
        ("digit_from_slash", "fn emit_zero_block() → List<Instruction> { [MovRI(Rcx, BitVec::ofNat(48))] }",
            "fn emit_zero_block() → List<Instruction> { [MovRI(Rcx, BitVec::ofNat(47))] }"),
        ("units_from_whole", "[MovRI(Rcx, BitVec::ofNat(48)), AddRR(Rcx, Rax)]", "[MovRI(Rcx, BitVec::ofNat(48)), AddRR(Rcx, Rbx)]"),
        ("exit_past_store", "JumpIfNear(B, BitVec::ofNat(12))", "JumpIfNear(B, BitVec::ofNat(13))"),
    ] {
        let bad = FORMAT.replacen(from, to, 1);
        assert_ne!(bad, FORMAT, "{name}");
        let error = library.elaborator().elab_module_source("elf64_format_width", &bad).expect_err(name).render(&bad);
        assert!(!error.contains("unbound") && !error.contains("ambiguous"), "{name}: {error}");
    }
}
