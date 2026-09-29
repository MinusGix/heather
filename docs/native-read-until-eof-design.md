# Read until end of file — design

Status: **landed 2026-09-27.** Probes in §6; the suite and the built programs are in §7. Owner:
`issues/native-read-until-eof.md`. It builds on
`docs/native-first-program-design.md` (the read-once `wc -l`, its trace, its
memory view and its print slice), and replaces that program's single read.

## 1. What changes

The read-once program reads stdin once, up to 4096 bytes. On a pipe, or on a
file over one page, it counts a prefix. This round makes the program loop:
read a chunk, stop at the empty read, otherwise count the chunk into a running
total and read again. The read-once profile goes (decision 2026-09-27): one
process shape, and `--read-loop`/`--print` build this one.

Nothing in the trace model changes. `LinuxRuns` already takes any number of
events, and a read is a rule of its own, so a loop around `read` is an
induction in the process proof, over the chunks the reads return
(`issues/linux-syscall-trace-model.md`'s "syscalls inside loops" is this).

## 2. The claim

For the built file `F`, every list of chunks `cs` where each chunk is 1 to 4096
bytes, and every page, register file and flags:

```text
LinuxRuns(io_linux(), eof_events(cs, tail(spec(eof_input(cs)))), io_initial(F, page, gprs, flags))
```

`eof_events(cs, tail)` is `ReadEvent(0, c)` for each chunk, then
`ReadEvent(0, [])` (end of file), then `tail`. `eof_input(cs)` is the chunks
concatenated. The exit profile's tail is `[ExitEvent(word_of_nat(64, n))]`.
The print profile's is `[WriteEvent(1, decimal_line(n)), ExitEvent(0)]`, still
under its `n < 10000` bound. The exit profile needs `n + 4096 < 2^64`, so no
count wraps (§4).

A read that returns fewer bytes than asked is not the end: only the empty read
is. So the claim covers every way Linux may split the input, whether that's a
regular file, a pipe fed in bursts, or a terminal.

## 3. The program

```text
init:   mov r13, 0
read:   mov rax,0; mov rdi,0; mov rsi,0x401000; mov rdx,4096; syscall
        test rax, rax
        jz done                      ; near, rel32
setup:  rbp, r12 ← rax; rdi ← 0x401000; rcx ← needle; rsi ← 0; r11 ← r13
loop:   the counting loop, unchanged
save:   mov r13, r11
        jmp read                     ; near, rel32, backward
done:   the tail (exit: rdi ← r13, rax ← 60, syscall;
              print: r11 ← r13, then the slice-4 formatter, write and exit)
```

**The count lives in R13 between reads.** The loop keeps it in R11
(`ReadLoopPlacement`), and SYSCALL clobbers R11 (the `Read` rule quantifies
over it). R13 is the loop's `flag` scratch register, but that doesn't matter:
the count is copied into R11 before the loop and saved back after it, so R13
only has to survive the syscall. Every other register is in the loop's
placement. The loop certificate and its placement are unchanged.

## 4. The contract a program proves

**Superseded 2026-09-28** by the fold contract (`docs/native-wc-design.md`
§3): a program proves its step folds and its specification is the fold from
zero; `--adds` and additivity are gone, and the room premise is on the
input's length. The additive version, as it landed:

- `ReadEofComputes(source, needle, spec)`: from **any** count `c`, the loop
  over a buffer holding `bytes` ends at `End(|bytes|, 0, c + spec(bytes))`.
  That's `ReadLoopComputes` with the count opened up. `wc_l`'s general lemma
  (`count_lines_reads`) already states it.
- `spec(a ++ b) = spec(a) + spec(b)`, so counting chunk by chunk counts the
  input.

This covers any byte counter. A non-additive fold (a checksum, a maximum)
would need `f(f(c, a), b) = f(c, a ++ b)` and a bound on every intermediate
state. It's left until a program wants it.

The loop's `loop_fits(0, n, c)` is `c + n < 2^64`. With `c ≤ total` and
`n ≤ 4096`, `total + 4096 < 2^64` gives every iteration's bound.

## 5. Library shape (`lib/elf64_read_loop.hthr`)

- `eof_counts`: setup and loop from the count in R13. It's
  `read_loop_counts` with the carry opened up, and replaces it; the print
  profile uses it too.
- `eof_chunk`: one non-empty chunk. TEST, JZ not taken, `eof_counts`, save,
  JMP back: from the read's return to the read label, the chunk stored, the
  count plus the chunk's in R13. It closes through `eof_chunk_close`, which
  takes the count's run as an argument (§6, the `let` trap).
- `eof_from`: the loop, by structural recursion on the chunks. Its end is an
  `EofTail`: any run from the done label, the count in R13, any page. The
  exit and print profiles each prove their tail, and the tail's code starts
  at `eof_at_done`.
- Targets: `JZ done` and `JMP read` are hypotheses in `eof_from`'s
  statement (`exit_target`, `back_target`). Library lemmas derive them from a
  closed fact about each displacement, through `near_branch_forward` and
  `near_branch_returns`, and the producer proves that fact at the written
  bytes.
- `test_self_zero`/`test_self_nonzero` (`x86_64_fetched_code`, beside
  `near_taken_rip`): TEST of a
  register with itself sets ZF exactly when its value is 0.

## 6. Probes (2026-09-27, `probes/eof/t_eof.hthr`)

- **V1, one iteration: holds.** `eof_chunk` checks over the real
  `ReadLoopCertificate`, `eof_counts` costs the same as `read_loop_counts`,
  and the zero flag costs about 11K steps (`eof_test_clear`).
- **V2, the loop: holds.** `eof_from` checks by structural recursion, with
  the tail abstract. A recursive theorem needs the recursion's list as a
  named parameter (a leading `λ` isn't guarded), and `Cons` binds no `ih`.
- **The `let` trap, again.** The first `eof_chunk` cost 5M kernel steps (7 s).
  `counted`, the 26-argument `eof_counts` call, was a `let` used about eight
  times, and a `let` is inlined at every use (`native-first-program-design.md`
  §10.3). Passing it once into `eof_chunk_close` took it to 73K steps
  (0.15 s).
- **`omega` along the way** (dogfooding, see the issue log). It keeps closed
  `of_bit(True)` as an atom, and it treats `spec(Nil ++ Nil)`,
  `spec(eof_input(Nil))` and `spec(Nil)` as three atoms. Each needed an
  annotated restatement (gone since issues/omega-atoms-up-to-computation.md
  made atoms equal up to computation). In `eof_from`'s context it also failed with "could
  not spell a natural expression", so `eof_room`/`eof_later` hold that
  arithmetic.

## 7. Producer and tests

- `crates/cli/src/native/read_loop.rs`: the new layout, both displacements
  computed from the pieces' lengths, the written bytes stated piece by piece
  as before, and `eof_*` instantiated. `--computes` names a
  `ReadEofComputes` theorem, and a new `--adds` names the additivity theorem.
- `examples/x86-native/wc_l.hthr`: `count_lines_input` from any count, and
  `wc_l_append`.
- `crates/cli/tests/native_read_loop.rs`: inputs past one page (the counts
  now cover them), and a pipe written in several bursts, each compared with
  the newline count of the whole input.
- Refusals (`crates/elab/tests/read_loop_process.rs`, `read_print_process.rs`):
  the setup resetting the count (`mov r11, 0`), the save to another register,
  the backward jump to the wrong place, the test on the wrong register, as
  well as the existing ones that still apply.

Landed as above. The exit build is 645 bytes and the print build 2780, and
both match the system's `wc -l` on every input of the test, the 9999-line
three-read input and the burst pipe included. The last refusal became a
mis-stated back-jump span (`eof_loop_span`), since the displacement itself is
the producer's closed fact (`_back_closes`). A new test,
`read_loop_needs_its_additivity`, checks that `--adds` is required.
