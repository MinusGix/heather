//! wc as a command, per file (docs/native-wc-command-design.md §6): the
//! driver is part of the replayed prefix, and its claim composes with the
//! stdout and status corollaries into one process theorem over any step
//! piece the filter's facts hold of, and the spec agrees with GNU on §2's
//! cases. Each change to the driver's code is refused where it is wrong, not
//! by a missing name, in `command_refusals.rs`.
use crate::command_prefix::COMMAND_PREFIX;
use crate::support;

// The command's library and everything it stands on, replayed: the warm-up
// (semantic_command_warmup) populated it in two bounded processes.
pub(crate) fn library() -> heather_elab::Elaborator {
    support::semantic_test_base(COMMAND_PREFIX)
}

// The step piece is any one the filter's facts hold of: the claim is stated
// over `FilterFacts`, so the client composes the process with no code of its
// own, and the generated piece (C4) is one instance.
const CLIENT: &str = r#"import elf64_command_output; import elf64_command_events; import elf64_command; import elf64_read_filter; import elf64_read_pieces;
import elf64_print_pieces; import elf64_write_loop; import elf64_stat_width; import elf64_operand_cursor; import elf64_io; import elf64_frame; import command_program;
import stream_filter; import linux_x86_64_io; import x86_64; import x86_64_structured_block; import bitvec; import bitvec_nat; import bool;
import list; import logic; import nat; import option;

// The claim and both corollaries together: for any file holding the command
// at the entry, over any step piece the filter's facts hold of, the process
// runs the history's events, and a run whose writes finish sends
// `command_stdout` and exits with `command_status`.
theorem command_prints<C>(file: IoImage, letters: List<BitVec(8)>, default: BitVec(64), spill: Nat → StateReg, shape: FilterShape<C>,
    facts: FilterFacts<C>(shape), jumps: FilterJumps, pj: PrintJumps, placed: CommandPlaced(file, letters, default, spill, shape.code, jumps, pj),
    targets: CoreTargets(ca_core(), ca_head(), structured_bytes(shape.code).len(), jumps, pj), column: Nat → C → BitVec(64),
    spilled: (i: Nat) → i < 8 → (g: Gprs) → (s: C) → shape.rep(g, s) → read_gpr(state_gpr(spill(i)), g) = column(i)(s),
    argv: List<List<BitVec(8)>>, pointers: List<BitVec(64)>, history: CommandHistory,
    ok: CommandHistoryOk(shape, column, letters, default, argv, history), written: CommandWritten(letters, default, argv, history),
    page: Nat → BitVec(8), gprs: Gprs, flags: Flags, stays: ArgvStaysAt(file, read_gpr(Rsp, gprs), argv, pointers),
    argc: argv.len() < Nat::pow(2, 31)):
    LinuxRuns(io_linux(), command_events(shape, column, letters, default, argv, history), io_initial(file, page, gprs, flags)) ∧
        ((sent_to(BitVec::ofNat(1), command_events(shape, column, letters, default, argv, history)) =
            command_stdout(shape, column, letters, default, argv, history)) ∧
        EndsIn(command_events(shape, column, letters, default, argv, history), ExitEvent(command_status(letters, default, argv, history)))) {
    ⟨command_runs(file, letters, default, spill, shape, facts, jumps, pj, placed, targets, column, spilled, argv, pointers, history, ok, page,
        gprs, flags, stays, argc),
     ⟨command_sends(shape, column, letters, default, argv, history, ok, written),
      command_exits(shape, column, letters, default, argv, history, ok, written)⟩⟩
}

// The spec on §2's cases, over a lines-and-bytes counter: `l` selects slot
// 0 (lines), `c` slot 1 (bytes), both by default.
record Lb { lines: Nat, bytes: Nat }
fn lb_step(s: Lb, b: BitVec(8)) → Filtered<Lb> {
    match b.eq_bit(BitVec::ofNat(10)) { True => Filtered(Lb(Succ(s.lines), Succ(s.bytes)), None), False => Filtered(Lb(s.lines, Succ(s.bytes)), None) }
}
fn lb_shape() → FilterShape<Lb> {
    FilterShape(step := lb_step, init := Lb(0, 0), counts := [λ s => s.lines, λ s => s.bytes], rep := λ _ _ => True, code := CodeBlock(Nil))
}
fn lb_column(i: Nat) → Lb → BitVec(64) {
    match i { Zero => λ s => word_of_nat(64, s.lines), Succ(_) => λ s => word_of_nat(64, s.bytes) }
}
fn b(n: Nat) → BitVec(8) { BitVec::ofNat(n) }
fn letters() → List<BitVec(8)> { [b(108), b(99), b(0), b(0), b(0), b(0), b(0), b(0)] }
fn wc() → List<BitVec(8)> { [b(119), b(99)] }
fn f1() → List<BitVec(8)> { [b(102), b(49)] }
fn f2() → List<BitVec(8)> { [b(102), b(50)] }
fn done() → RowWrite { RowWrite(Nil, Finished) }
fn read(fd: Nat, chunks: List<List<BitVec(8)>>, ending: EofEnd<WriteFailure>) → OperandRun {
    OperandRun(opened := Opened(fd), steps := chunks.map(λ c => Chunk(c, Nil)), ending := ending, counts := done(), name := done(),
        newline := done(), closed := Closed)
}
fn history(stats: List<StatResult>, runs: List<OperandRun>) → CommandHistory { CommandHistory(stats, runs, done()) }
// "a\nb\n" and "x\n" (two reads)
fn two_lines() → List<List<BitVec(8)>> { [[b(97), b(10), b(98), b(10)]] }
fn one_line() → List<List<BitVec(8)>> { [[b(120)], [b(10)]] }

// wc -l f1: one count, one operand, no stat, width 1: "2 f1\n".
theorem lines_one(): command_stdout(lb_shape(), lb_column, letters(), BitVec::ofNat(3), [wc(), [b(45), b(108)], f1()],
    history(Nil, [read(3, two_lines(), AtEnd)])) = [b(50), b(32), b(102), b(49), b(10)] { refl }
// wc -l f1 f2, both stats failed (width 1): rows, then the total.
theorem lines_two(): command_stdout(lb_shape(), lb_column, letters(), BitVec::ofNat(3), [wc(), [b(45), b(108)], f1(), f2()],
    history([StatFailed(2), StatFailed(2)], [read(3, two_lines(), AtEnd), read(3, one_line(), AtEnd)])) =
    [b(50), b(32), b(102), b(49), b(10), b(49), b(32), b(102), b(50), b(10), b(51), b(32), b(116), b(111), b(116), b(97), b(108), b(10)] { refl }
// wc with no operand: stdin's row, unnamed, both counts: "2 4\n".
theorem stdin_row_both(): command_stdout(lb_shape(), lb_column, letters(), BitVec::ofNat(3), [wc()],
    history([StatFailed(9)], [read(0, two_lines(), AtEnd)])) = [b(50), b(32), b(52), b(10)] { refl }
// A failed open makes no row and exit 1; a failed read still prints the row
// of what it read, and exits 1.
theorem open_failed(): command_status(letters(), BitVec::ofNat(3), [wc(), [b(45), b(108)], f1()],
    history(Nil, [OperandRun(opened := OpenFailed(2), steps := Nil, ending := AtEnd, counts := done(), name := done(), newline := done(),
        closed := Closed)])) = BitVec::ofNat(1) { refl }
theorem read_failed_row(): command_stdout(lb_shape(), lb_column, letters(), BitVec::ofNat(3), [wc(), [b(45), b(108)], f1()],
    history(Nil, [read(3, one_line(), FailedWith(5))])) = [b(49), b(32), b(102), b(49), b(10)] { refl }
theorem read_failed_status(): command_status(letters(), BitVec::ofNat(3), [wc(), [b(45), b(108)], f1()],
    history(Nil, [read(3, one_line(), FailedWith(5))])) = BitVec::ofNat(1) { refl }
theorem clean_status(): command_status(letters(), BitVec::ofNat(3), [wc(), [b(45), b(108)], f1()],
    history(Nil, [read(3, two_lines(), AtEnd)])) = BitVec::ofNat(0) { refl }
// An unknown letter: nothing printed, exit 1.
theorem refused(): command_stdout(lb_shape(), lb_column, letters(), BitVec::ofNat(3), [wc(), [b(45), b(120)]], history(Nil, Nil)) = Nil { refl }
theorem refused_status(): command_status(letters(), BitVec::ofNat(3), [wc(), [b(45), b(120)]], history(Nil, Nil)) = BitVec::ofNat(1) { refl }
"#;

#[test]
fn command_process_composes() {
    let mut elab = library();
    elab.elab_module_source("command_client", CLIENT).unwrap_or_else(|e| panic!("{}", e.render(CLIENT)));
}
