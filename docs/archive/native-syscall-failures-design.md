# Syscall failures in the trace and in `wc -l` — design

> **Burned in B1 (2026-10-21).** The code this document describes was deleted with the
> hand-proved process stack (`docs/native-program-logic-design.md` §3.1); the document
> stays for its reasoning. The last commit with the code is `189659d` (tag `native-v0`).

Status: **landed 2026-09-27.** The probes' results are in §10; the amendments
made while building are in §9 and override the sections above them. Owner:
`issues/linux-syscall-trace-model.md` (decisions logged there 2026-09-27).
Builds on `docs/native-read-until-eof-design.md@4acf2fe` (the program and its claim)
and `docs/archive/native-first-program-design.md` §4 (the basic trace).

## 1. What changes, and why now

`LinuxRuns` has rules for a successful read, a complete write, and exit.
Nothing else has a rule, so the claim says nothing about a run where a read
fails or a write is short. The binary is also wrong there. It tests only
`RAX = 0`, so `-EINTR` (the word `2^64 − 4`) goes to the counting loop as a
byte count.

Decisions (2026-09-27, with the user; do not relitigate):

1. **Shape.** `LinuxRuns` stays a relation over an event list, not
   tier-2 plus container ITrees first (`docs/interaction-trees-fit.md` §7
   needs function-typed inductive fields, which are unscheduled). Each event
   is a command together with its response, so the later move to
   `Cmd`/`Resp` is a re-grouping, not a redesign.
2. **Policy.** EINTR on read or write retries the call; any other error exits
   with status 1; a short write loops until the rest is written.
3. **Determinism** is not this round. The claim stays "a run with this
   trace exists", and uniqueness is a separate `FetchedStep` theorem.

## 2. The trace model (`lib/std/os/linux/linux_x86_64_io.hthr`)

The responses:

```text
inductive ReadResult  { ReadBytes(bytes: List<BitVec(8)>), ReadFailed(errno: Nat) }
inductive WriteResult { Wrote(count: Nat), WriteFailed(errno: Nat) }

inductive LinuxEvent {
    ReadEvent(fd: BitVec(64), result: ReadResult),
    WriteEvent(fd: BitVec(64), bytes: List<BitVec(8)>, result: WriteResult),
    ExitEvent(status: BitVec(64)),
}
```

`WriteEvent` carries what was *asked* (`bytes`, the buffer's contents at
`RSI` for `RDX`) and what happened. The bytes that actually left are
`bytes.take(count)`. An observer's output is the concatenation of those
prefixes, and `sent(events)` computes it.

The rules. RCX and R11 are quantified in each, as today.

| event | condition at the SYSCALL | state after |
|---|---|---|
| `ReadEvent(fd, ReadBytes(bs))` | as today: `|bs| ≤ RDX`, span writable | as today |
| `ReadEvent(fd, ReadFailed(e))` | `1 ≤ e ≤ 4095`, span writable | `RAX = 2^64 − e`; **memory: any `junk` with `|junk| ≤ RDX` stored at RSI** (quantified) |
| `WriteEvent(fd, bs, Wrote(k))` | `RDX = |bs|`, `bs` readable at RSI, `k ≤ |bs|` | `RAX = k`, memory unchanged |
| `WriteEvent(fd, bs, WriteFailed(e))` | same, `1 ≤ e ≤ 4095` | `RAX = 2^64 − e`, memory unchanged |
| `ExitEvent(s)` | as today | — |

Being conservative where Linux is loose:

- **A failed read may have written into the buffer.** Linux does not promise
  it did not. Quantifying over `junk` means the program can't rely on the
  buffer after a failure. `wc -l` doesn't; it exits or re-reads.
- **`Wrote(0)` for a non-empty write is allowed.** A program that loops on
  it may run forever. That is a liveness question, and this claim is about
  finite traces (§3).
- Which errno values Linux may return for which fd is not modelled. Any
  `1 ≤ e ≤ 4095` is possible. The program's claim covers all of them, so no
  list is needed.

`linux_runs_read`/`_write`/`_exit` keep their names and gain `_failed` and
`_short` siblings. A `Wrote(|bs|)` write is today's complete-write rule,
restated.

## 3. The claim

The environment's behaviour is a **history**: a list of read outcomes, then
a list of write outcomes. It's well-formed when it ends where the program
stops.

```text
inductive ReadOutcome  { Chunk(bytes), Interrupted, Failed(errno), EndOfFile }
inductive WriteOutcome { Sent(count), WriteInterrupted, WriteFailed(errno) }
```

- **Reads:** `Chunk` has 1 to 4096 bytes. `Failed(e)` has
  `1 ≤ e ≤ 4095, e ≠ 4`. The list ends at its only `EndOfFile` or `Failed`.
- **Writes** (the print profile, after `EndOfFile`): `Sent(k)` with
  `k ≤` what remains. The list ends when the sent counts total the line's
  length, or at its only `WriteFailed`.

For every well-formed history `h`, every page, register file and flags:

```text
LinuxRuns(io_linux(), wc_events(h), io_initial(F, page, gprs, flags))
```

`wc_events` is the program's trace as a function of `h`: each `Interrupted`
is a `ReadEvent(0, ReadFailed(4))` followed by the same read again, and so
on. **Corollaries** stated in the library, so no reader has to unfold
`wc_events`:

- The run exits 0 exactly when the reads ended at `EndOfFile` and the writes
  did not fail. Then `sent(events) = decimal_line(spec(input(h)))`, where
  `input(h)` is the `Chunk`s concatenated.
- Otherwise it exits 1, and its last read or write event is the failure.

The print profile's `spec(input) < 10000` bound stays. The exit profile
(count as status) keeps its shape: it exits 1 on a read failure, and its
trace shows which case happened.

## 4. The program

```text
read:   (as today) ... syscall
        test rax, rax
        jz done
        js failed                     ; NEW: near, rel32
        setup / loop / save / jmp read (unchanged)
failed: mov rbx, -4                   ; RBX is free between reads
        cmp rax, rbx
        jz read                       ; EINTR: retry, count untouched in R13
        mov rdi, 1; mov rax, 60; syscall
done:   print tail (below) or exit tail (unchanged)
```

Print tail, a loop around `write`. The offset lives in R12 and the length in
RBP; SYSCALL preserves both.

```text
        (format decimal_line(n) at the page, length in rbp, as today)
        mov r12, 0
wloop:  rsi ← buf + r12; rdx ← rbp − r12; rax ← 1; rdi ← 1; syscall
        test rax, rax
        js wfailed
        add r12, rax
        cmp r12, rbp
        jz exit0
        jmp wloop
wfailed: mov rbx, -4; cmp rax, rbx; jz wloop; exit 1
exit0:  exit 0
```

**`JumpSignNear` is new** (`0F 88 rel32`) in `NearControl`, beside
`JumpZeroNear`, with its decode and uniqueness facts. `TEST rax, rax` already
sets SF to the sign bit (`model.hthr`). A return word is negative exactly when
it is an error, because a successful count is at most 4096.

## 5. Library shape

- `lib/std/os/linux/linux_x86_64_io.hthr`: §2, and `sent`.
- `lib/elf64_read_loop.hthr`: `eof_from` recurses on `List<ReadOutcome>`,
  not chunks. `Interrupted` is one more arm, which returns to the read label
  with R13 unchanged, and `Failed` ends at the failure block. `EofChunks`
  becomes the well-formedness predicate.
- A write-loop lemma, `write_from`, by recursion on `List<WriteOutcome>`, with
  R12 as offset. Its invariant is `sent so far = line.take(r12)`, and it ends
  at `exit0` or the failure exit. It is shaped like `eof_from` and lives in
  `elf64_read_print`.
- Refusals (mutations the library must reject): `js` replaced by `jz` or
  dropped; the EINTR compare against `-1`; the write loop advancing by `rdx`
  instead of `rax`; the offset kept in RCX (clobbered); the failure exit with
  status 0.

## 6. Cost to watch

`eof_from` grows two arms, and the write loop is a second induction of the
same shape. The read-until-EOF build is about 13 s (exit) and 30 s (print)
cold. The failure blocks are short and straight-line, so the rough
expectation is that the print build stays under 2×. `native_read_loop` is
already the suite's slowest target, so the refusal set goes in the
`slow_acceptance_` tests, as today.

## 7. Probes, first hour (stop and report if one refutes the design)

- **V1 `JumpSignNear`.** Add the form and decode it. `test rax, rax; js`
  taken at `2^64 − 4`, not taken at 4096, both through `execute_near_control`.
- **V2 failed-read rule.** `linux_runs_read_failed` states, and one
  `Interrupted` step of `eof_from` checks over the real certificate: back at
  the read label, R13 kept, memory the quantified junk.
- **V3 the junk is harmless.** The next read's `ReadBytes` overwrites a
  prefix only. Check that `io_suffix_resident` (code residency) is unaffected
  by a junk store into the RW page. It should be, since the page is disjoint
  from code, but it is the one place a quantified store could leak into a
  fetch.
- **V4 write loop.** `write_from` at one `Sent(k < len)` step and one
  `WriteInterrupted`, with a `decimal_line`-sized buffer.
- **V5 the claim statement.** `wc_events` and the exit-0 corollary on a
  two-chunk, one-EINTR, two-partial-write history, by `refl` on the events
  and by the corollary on `sent`.

## 8. Not in this round

- Determinism (decision 3): file `fetched-step-deterministic`.
- `EAGAIN` on a non-blocking stdin is just another error here, and it exits 1.
  Real `wc` would block rather than see it, so it is fine.
- An error message on stderr (the user chose exit 1 without one).
- Signals delivered as anything but EINTR, `SA_RESTART` semantics, and other
  syscalls.

## 9. As built (2026-09-27): amendments

Each amendment overrides the section it names.

- **§3, the history's shape.** It is not one outcome list ending at a
  terminal. It is steps plus an ending: `List<ReadStep>` (`Chunk`,
  `Interrupted`) and `ReadEnding` (`AtEnd`, `FailedWith(errno)`), and for the
  print profile `List<WriteStep>` (`Partial(count)`, `WriteInterrupted`) and
  `WriteEnding` (`Finished`, `WriteFailedWith(errno)`). Well-formedness is
  then only per step (`EofChunks`, `WriteSteps(steps)(bytes)`: a partial
  count is below what is left) and per ending (`EofEnding`, `WriteEndingOk`:
  an errno, and not EINTR). The recursions (`eof_from`, `write_from`) are on
  the steps, and each `Nil` arm cases on the ending.
- **§3, the corollary.** `prints_the_line` (`lib/elf64_read_print.hthr`)
  proves that stdout, `sent_to(1, …)` over the whole trace, is exactly
  `decimal_line(n)` on a run that ends at `AtEnd` and `Finished`. The
  failure corollary is the trace itself: `eof_events` and `write_events` end
  in `ExitEvent(1)` right after the failing event.
- **§4, the EINTR test.** The test is `mov rbx, 4; add rax, rbx; jz`, not
  `cmp rax, rbx` against `-4`. CMP's ZF is zero of `rax - rbx`, and that
  subtraction borrows whenever the errno is above 4, so it needs an
  `(a - b) + b = a` law the bitvector library does not have. With ADD the
  sum overflows only for errno 1 to 4, which are closed evaluations, and
  above 4 it is a no-overflow `toNat_add` (`other_errno_plus_four`). RAX is
  dead on the failure path, so clobbering it costs nothing.
- **§2, the rules' names.** No `_short` sibling. `linux_runs_write` takes
  the count sent, `count <= |bytes|`, so a whole write and a short one are
  the same rule. The failure rules are `linux_runs_read_failed` and
  `linux_runs_write_failed`.
- **§2, the errno word.** `errno_word(e)` is `BitVec::ofNat(2^64 - e)`, not
  `word_of_nat`. `word_of_nat` is iterated increment, and evaluating it at a
  closed `2^64 - 4` runs out of fuel. `ofNat` is width-recursive.
- **§4, the write loop's registers.** No offset register. R9 (the formatter's
  start) is the write pointer and R10 (its length) is what is left. The
  advance block is `add r9, rax; sub r10, rax`, and SUB's ZF is the
  "nothing left" test. The loop's invariant (`WriteFrom`) is that the
  remaining bytes are readable at R9 and R10 counts them, so a short write
  continues with `bytes.drop(count)` and no offset arithmetic enters the
  proof.
- **§5, where things live.** The SF and ZF readings of a word
  (`sign_bit_small/large`, `zero_bits_of_zero/pos`, `band_self_value`,
  `test_self_negative/nonnegative`, `near_sign_*_rip`) are in
  `lib/std/arch/x86_64/x86_64_fetched_code.hthr`. The errno facts (`errno_value`,
  `errno_negative`, `errno_nonzero`, `eintr_plus_four`,
  `other_errno_plus_four`) are in `lib/std/os/linux/linux_x86_64_io.hthr`.
- **§5, arithmetic in the loops.** Every Nat step inside `write_from`'s arms
  is a small lemma (`all_sent`, `left_after`, `rest_room`, …), the
  `eof_room` pattern. `omega` inside those arms meets facts it cannot spell
  and refuses the whole call (issues/omega-inside-match-arms.md), and Nat
  truncated subtraction needs `sub_add_cancel` stated first.

## 10. Probe results and cost (2026-09-27)

- **V1 holds.** `JumpSignNear` decodes and executes. After `TEST RAX, RAX`,
  JS is taken at every errno word and not taken at any count up to 4096.
- **V2 holds.** `linux_runs_read_failed` states, and `eof_from`'s
  `Interrupted` arm checks over the real certificate.
- **V3 holds by construction.** `IoMemory` fetches only from the file (the
  page is not executable), and `eof_from` already quantifies over every
  page. A junk store is another page.
- **V4 holds.** `write_from` checks for short writes, EINTR and failures.
- **V5 holds.** `prints_the_line` checks.
- **Found:** `bv_omega` overflows the stack on `word_of_nat` at an open value
  (filed, issues/bv-omega-stack-overflow-word-of-nat.md).
- **Cost.**
  - Library: `eof_from` and `write_from` are each about the cost of
    `eof_counts` or less, and the cold check of the whole print module stays
    dominated by the loop trace and the counting loop.
  - Build: the exit build grew from 645 to 692 bytes and the print build
    from 2780 to 2894. The cold print build is about 1.3× the
    read-until-EOF one.
  - Tests: the refusal sets gained four read-side and four print-side
    mutations.
