//! The stat pass and the width (docs/native-wc-command-design.md §2, §6.1):
//! the operand cursor and the stat pass check over what they stand on, run
//! wherever a program places them against any argv layout and any answers
//! Linux gives, and agree with GNU's width rule on §2's cases. Each change to
//! their code is refused where it is wrong, not by a missing name, in
//! `operand_cursor_refusals.rs` and `stat_width_refusals.rs`: a file each, so
//! each shard fits the suite's CPU rail.
use crate::read_loop_fixture::checker;

const BV_OMEGA: &str = include_str!("../../../lib/std/bitvec/bitvec_omega.hthr");
const DECIMAL: &str = include_str!("../../../lib/decimal_line.hthr");
const ASM: &str = include_str!("../../../lib/std/arch/x86_64/x86_64_asm.hthr");
const RUNS: &str = include_str!("../../../lib/elf64_runs.hthr");
const FORMAT: &str = include_str!("../../../lib/elf64_format_width.hthr");
const PROGRAM: &str = include_str!("../../../lib/command_program.hthr");
const SCAN: &str = include_str!("../../../lib/elf64_arg_scan.hthr");
pub(crate) const CURSOR: &str = include_str!("../../../lib/elf64_operand_cursor.hthr");
pub(crate) const STAT: &str = include_str!("../../../lib/elf64_stat_width.hthr");

pub(crate) fn base() -> heather_elab::Elaborator {
    let mut elab = checker();
    for (name, source) in [("bitvec_omega", BV_OMEGA), ("decimal_line", DECIMAL), ("x86_64_asm", ASM), ("elf64_runs", RUNS), ("elf64_format_width", FORMAT), ("command_program", PROGRAM),
        ("elf64_arg_scan", SCAN)] {
        elab.elab_module_source(name, source).unwrap_or_else(|e| panic!("{name}: {}", e.render(source)));
    }
    elab
}

// The pass placed past any header in the file, entered with RSP at any argv
// whose pointers hold at every page: the client supplies only the placement.
// Then the spec on §2's cases: which targets are stat'ed, what a stat says,
// and the width.
const CLIENT: &str = "import elf64_stat_width; import elf64_operand_cursor; import command_program; import decimal_line;
import elf64_format_width; import elf64_io; import linux_x86_64_io; import x86_64; import x86_64_fetched_code; import bitvec; import bitvec_nat;
import list; import logic; import nat; import option;
theorem stat_after_header(header: List<BitVec(8)>, fits: header.len() + stat_code().len() <= 65536, frame: Nat → BitVec(8),
    rest: BitVec(64) → Option<BitVec(8)>, page: Nat → BitVec(8), argv: List<List<BitVec(8)>>, pointers: List<BitVec(64)>,
    results: List<StatResult>, fit: StatsFit(stat_targets(operands_from(False, command_args(argv))), results), after: List<LinuxEvent>,
    state: MachineState<IoMemory>,
    memory_is: state.memory = IoMemory(IoImage(header ++ stat_code(), frame, rest), page),
    rip_is: state.rip = bitvec_nat::word_of_nat(64, 0x400000 + header.len()),
    stays: ArgvStaysAt(IoImage(header ++ stat_code(), frame, rest), read_gpr(Rsp, state.gprs), argv, pointers),
    then: StatThen(IoImage(header ++ stat_code(), frame, rest), bitvec_nat::word_of_nat(64, 0x400000 + header.len()), state.gprs,
        stat_width(results.map(stat_seen)), after)):
    LinuxRuns(io_linux(), stat_events(stat_targets(operands_from(False, command_args(argv))), results) ++ after, state) {
    stat_runs(IoImage(header ++ stat_code(), frame, rest), bitvec_nat::word_of_nat(64, 0x400000 + header.len()),
        λ any => io_code_resident(header, stat_code(), frame, rest, any, fits), page, argv, pointers, results, fit, after, state, memory_is,
        rip_is, stays, then)
}
fn b(n: Nat) → BitVec(8) { BitVec::ofNat(n) }
fn size(n: Nat) → BitVec(64) { BitVec::ofNat(n) }
// The operands walked again: options and `--` passed over, `-` kept, and
// everything after `--` an operand.
theorem walked(): operands_from(False, [[b(45), b(108)], [b(102)], [b(45)], [b(45), b(45)], [b(45), b(99)], [b(45), b(45)]]) =
    [[b(102)], [b(45)], [b(45), b(99)], [b(45), b(45)]] { refl }
// wc: stdin, by fstat(0). wc - f: fstat(0), then f. wc -- --: a path.
theorem stdin_once(): stat_targets(Nil) = [StatFd(BitVec::zero())] { refl }
theorem dash_and_path(): stat_targets([[b(45)], [b(102)]]) = [StatFd(BitVec::zero()), StatPath([b(102)])] { refl }
theorem dashes_a_path(): stat_targets([[b(45), b(45)]]) = [StatPath([b(45), b(45)])] { refl }
// A struct stat with `st_mode` and `st_size` where x86-64 puts them.
fn zeros(n: Nat, rest: List<BitVec(8)>) → List<BitVec(8)> { match n { Zero => rest, Succ(k) => Cons(b(0), zeros(k, rest)) } }
fn sample(mode_low, mode_high, size_low: Nat) → List<BitVec(8)> {
    zeros(24, Cons(b(mode_low), Cons(b(mode_high), zeros(22, Cons(b(size_low), zeros(95, Nil))))))
}
theorem sample_length(): sample(0, 0, 0).len() = stat_length() { refl }
// A regular file (0o100644) of 7 bytes, a pipe (0o10600), a failed stat.
theorem regular_seen(): stat_seen(Stated(sample(164, 129, 7))) = Regular(size(7)) { refl }
theorem pipe_seen(): stat_seen(Stated(sample(128, 17, 0))) = Other { refl }
theorem failed_seen(): stat_seen(StatFailed(2)) = Unstated { refl }
// The width: the digits of the regular files' total; a failed stat adds
// nothing, first or not (`wc nosuch big` pads to big's size); another kind
// of file makes it at least 7, and a total wider than 7 stays as wide. (The
// sizes are small: `decimal` is unary arithmetic under `refl`.)
theorem one_regular(): stat_width([Regular(size(123))]) = 3 { refl }
theorem summed(): stat_width([Regular(size(99)), Regular(size(1))]) = 3 { refl }
theorem failed_first(): stat_width([Unstated, Regular(size(12))]) = 2 { refl }
theorem only_failed(): stat_width([Unstated]) = 1 { refl }
theorem pipe(): stat_width([Other, Regular(size(12))]) = 7 { refl }
theorem wide_stays(): widened(True, 9) = 9 { refl }
// The code is the same length wherever it goes.
theorem stat_length_is(): stat_code().len() = 1023 { stat_code_len() }
";

#[test]
fn stat_width_library_checks() {
    let mut elab = base();
    for (name, source) in [("elf64_operand_cursor", CURSOR), ("elf64_stat_width", STAT), ("stat_client", CLIENT)] {
        elab.elab_module_source(name, source).unwrap_or_else(|e| panic!("{name}: {}", e.render(source)));
    }
}
