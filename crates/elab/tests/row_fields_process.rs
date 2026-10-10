//! A row's counts (docs/native-wc-command-design.md §6.1 `row`): the library
//! row writer checks over what it stands on, runs wherever a program places
//! it against counts anywhere outside the page, and agrees with GNU's row
//! layout on §2's cases. Each change to its code is refused where it is
//! wrong, not by a missing name, in `row_fields_refusals.rs` (a file of its
//! own, so each shard fits the suite's CPU rail).
use crate::read_loop_fixture::checker;

const BV_OMEGA: &str = include_str!("../../../lib/std/bitvec/bitvec_omega.hthr");
const DECIMAL: &str = include_str!("../../../lib/decimal_line.hthr");
const ASM: &str = include_str!("../../../lib/std/arch/x86_64/x86_64_asm.hthr");
const RUNS: &str = include_str!("../../../lib/elf64_runs.hthr");
const FORMAT: &str = include_str!("../../../lib/elf64_format_width.hthr");
const PROGRAM: &str = include_str!("../../../lib/command_program.hthr");
const SCAN: &str = include_str!("../../../lib/elf64_arg_scan.hthr");
pub(crate) const ROW: &str = include_str!("../../../lib/elf64_row_fields.hthr");

pub(crate) fn base() -> heather_elab::Elaborator {
    let mut elab = checker();
    for (name, source) in [("bitvec_omega", BV_OMEGA), ("decimal_line", DECIMAL), ("x86_64_asm", ASM), ("elf64_runs", RUNS), ("elf64_format_width", FORMAT), ("command_program", PROGRAM),
        ("elf64_arg_scan", SCAN)] {
        elab.elab_module_source(name, source).unwrap_or_else(|e| panic!("{name}: {}", e.render(source)));
    }
    elab
}

// The writer placed past any header in the file, its counts anywhere the
// client keeps them: the client supplies only the placement. Then
// `row_counts` on wc's columns (lines, words, chars, bytes; default lines,
// words and bytes) over §2's rows.
const CLIENT: &str = "import elf64_row_fields; import command_program; import decimal_line; import elf64_format_width; import elf64_io;
import linux_x86_64_io; import x86_64; import x86_64_fetched_code; import bitvec; import bitvec_nat; import list; import logic; import nat;
import option;
theorem row_after_header(header: List<BitVec(8)>, fits: header.len() + row_code().len() <= 65536, frame: Nat → BitVec(8),
    rest: BitVec(64) → Option<BitVec(8)>, page0: Nat → BitVec(8), width: Nat, mask, slots: BitVec(64), counts: Nat → BitVec(64),
    held: CountsAt(IoImage(header ++ row_code(), frame, rest), slots, counts), o: Nat, state: MachineState<IoMemory>,
    memory_is: state.memory = IoMemory(IoImage(header ++ row_code(), frame, rest), page0),
    rip_is: state.rip = bitvec_nat::word_of_nat(64, 0x400000 + header.len()),
    rdi: read_gpr(Rdi, state.gprs).toNat() = io_page_base() + o, r12: read_gpr(R12, state.gprs) = slots,
    r13: read_gpr(R13, state.gprs) = mask, r14: read_gpr(R14, state.gprs).toNat() = width, room: o + 8 * (width + 21) <= 4096):
    Exists<MachineState<IoMemory>>(λ after => LinuxSteps(io_linux(), state, after) ∧
        RowOut(IoImage(header ++ row_code(), frame, rest), page0, bitvec_nat::word_of_nat(64, 0x400000 + header.len()), o,
            row_counts(width, mask, counts), state.gprs, after)) {
    row_runs(IoImage(header ++ row_code(), frame, rest), bitvec_nat::word_of_nat(64, 0x400000 + header.len()),
        λ any => io_code_resident(header, row_code(), frame, rest, any, fits), page0, width, mask, slots, counts, held, o, state, memory_is,
        rip_is, rdi, r12, r13, r14, room)
}
fn b(n: Nat) → BitVec(8) { BitVec::ofNat(n) }
// f1's counts by column: 2 lines, 3 words, 6 chars, 6 bytes.
fn f1(i: Nat) → BitVec(64) { match i { Zero => BitVec::ofNat(2), Succ(j) => match j { Zero => BitVec::ofNat(3), Succ(_) => BitVec::ofNat(6) } } }
// wc f1: the default columns, width 1.
theorem default_row(): row_counts(1, BitVec::ofNat(11), f1) = [b(50), b(32), b(51), b(32), b(54)] { refl }
// wc f1 f2: width 2, every field padded.
theorem padded_row(): row_counts(2, BitVec::ofNat(11), f1) = [b(32), b(50), b(32), b(32), b(51), b(32), b(32), b(54)] { refl }
// wc -lc f1 and wc -c -m f1: selected columns only, in column order.
theorem lines_bytes(): row_counts(1, BitVec::ofNat(9), f1) = [b(50), b(32), b(54)] { refl }
theorem chars_bytes(): row_counts(1, BitVec::ofNat(12), f1) = [b(54), b(32), b(54)] { refl }
// A count wider than the width prints in full.
fn wide(i: Nat) → BitVec(64) { BitVec::ofNat(123) }
theorem overflowing(): row_counts(1, BitVec::ofNat(1), wide) = [b(49), b(50), b(51)] { refl }
// The code is the same length wherever it goes.
theorem row_length_is(): row_code().len() = 1712 { row_code_len() }
";

#[test]
fn row_fields_library_checks() {
    let mut elab = base();
    for (name, source) in [("elf64_row_fields", ROW), ("row_client", CLIENT)] {
        elab.elab_module_source(name, source).unwrap_or_else(|e| panic!("{name}: {}", e.render(source)));
    }
}
