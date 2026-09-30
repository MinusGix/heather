# `tr`: output inside the read loop — design

Status: **decisions taken 2026-09-30 (§6); probe V2 §4.1.** Owner: `issues/native-tr.md`.
Builds on `docs/native-wc-design.md` (the state process, §4.8; the write loop
at an offset, §5.2), `docs/native-syscall-failures-design.md` (failure paths
and histories) and `docs/fetched-step-determinism-design.md` (claims universal
over runs).

## 1. Why this program

`wc -l` and `wc` read everything, then write once. `tr` breaks that shape in
two ways:

1. **It writes after every chunk.** The write loop runs inside the read loop,
   so the read and write histories interleave. When all of a chunk has been
   sent, the write loop jumps back to the read instead of exiting.
2. **It stores for every byte.** Each byte is translated in the buffer before
   the chunk is written back. Today's certified loops execute through
   `ExecuteAccess`, whose `AccessCode` has no store, and `LoopHead` requires
   memory to be unchanged across an iteration. A program's stores exist only
   as single `StoreStep`s in process proofs, as the formatter's word store.
   Stores are also word-sized only (`mov qword [base], source`).

A third property falls out: `tr` keeps no state across bytes or chunks, so
its claim has **no bound on the input**. `wc` needs its counts to fit in 64
bits and in seven columns; `tr` needs nothing.

## 2. The target

For any history of reads and writes, the built file's runs (via
`_runs_every`) are exactly the ones that read each chunk, write its
translation to stdout, and after end of file exit 0. They exit 1 at a failed
read or write other than EINTR, which is retried. On a run that ends well:

```text
sent_to(stdout, events) = input.map(f)
```

`f` is a byte function the program defines, fixed at build time: there is no
argv. The example program (`examples/x86-native/tr.hthr`) is `tr a-z A-Z`:

```text
fn upcase(b: BitVec(8)) → BitVec(8) { match lower_byte(b) { True => b.sub(0x20), False => b } }
```

The test compares the built file against host `tr a-z A-Z` on random input,
including sizes that straddle chunks. `f` is compiled by the structured
lowering (§4), so it is written the way the reflector reads it: byte tests,
bitwise operations and, after slice N, 8-bit add and subtract. A `tr` over
arbitrary literal sets (`translate(SET1, SET2)`, a list recursion) isn't
reflectable, and isn't this round's.

## 3. The code

```text
top:    read(0, page, 4096)                     read_entry_block, SYSCALL
        TEST RAX; JZ exit0; JS failed           as the state process
        R9 := page, R10 := RAX, RSI := page, RCX := RAX
map:    MOVZX RAX, byte [RSI]                   ByteLoad
        <the byte map: RDX := f(RAX)>           §4, generated, a parameter
        MOV byte [RSI], DL                      new: ByteStore
        ADD RSI, 1; ADD RCX, -1; JNZ map        AddRI8, JumpIfNear(NE)
        write loop over (R9, R10)               elf64_write_loop, done → top
failed: EINTR test, JZ top; exit(1)             as the state process
exit0:  exit(0)
```

The map runs in place, over the page the read filled. A chunk is never empty
there (JZ took the empty read), so the loop tests at its bottom. The loop is
**library code, proved once** by induction on what is left of the chunk, over
`LinuxSteps` (fetched steps and stores). It is not a loop generator loop:
there is no state, and the generator's contract (`ReadonlyLoop`,
`ExecuteAccess`) stays read-only. The per-byte work is the only
program-specific piece, and it enters as a certificate (§4). The invariant at
`map` after `i` bytes: the page's first `i` bytes are `chunk[0..i].map(f)`,
the rest are still the chunk's, RSI = page + i and RCX = n − i.

### 3.1 Pieces

- **A byte store** (slice A). `MOV r/m8, r8` into `[base]` (`88 /r`, always
  with a REX so the low byte of every register is encodable), beside
  `WordStore` in `x86_64_store`. `StoreStep` becomes either store. The step
  decoder and the determinism proof gain the form (`FormByteStore`); it is
  told apart from the word store by REX.W and the opcode.
- **The write loop with a continuation** (slice B). Today `wl_from` ends in
  `write_events(bytes, steps, ending)`, whose `Finished` case is
  `[…, ExitEvent(0)]`. It becomes `write_events_then(bytes, steps, ending,
  after)`, with the JZ-when-done target and a continuation proof as
  parameters. `write_events` is the instance `after = [ExitEvent(0)]` at the
  adjacent exit block, so existing clients don't change. `tr`'s EOF jump
  reuses that exit block.
- **The map process** (slice C, `lib/elf64_read_map.hthr`). Histories:

  ```text
  inductive MapStep   { Mapped(bytes, writes: List<WriteStep>), Interrupted }
  inductive MapEnding { AtEnd, ReadFailedWith(errno),
                        WriteFailedAt(bytes, writes, errno) }
  ```

  `map_events(f, steps, ending)` interleaves each chunk's read with its
  write events, and `map_sends` proves `sent_to(1, …AtEnd) =
  map_input(steps).map(f)`. The claim `read_map_runs` is universal over
  histories, and its only premises are about the code: residency, jump
  displacements and the byte map's certificate. It has no input bound.
- **The program and profile** (slice D). `build-x86 … --map NAME` names
  `f`. The CLI emits the image, the certificate and `_runs_every`, and the
  tests compare against host `tr`, with refusal controls and a mutation
  control.

## 4. The byte map

The loop needs one fact from its middle piece: from a state at the piece
with RAX = `b` zero-extended, the piece's code runs to its end with RDX =
`f(b)` zero-extended, keeping RSI, RCX, R9, R10 and memory. That is the typed
generator's `StructuredArtifact`, as the formatter's words are certified
(`PrintWord`). The library takes it as a parameter (`MapPiece(code, keeps)`
plus the four `keeps` facts), and the CLI generates it with
`generate_elaborated_typed_x86(…, inputs {b: RAX}, temporaries [RDX, RBX,
RDI, R8], outputs {RDX})`. The output must be a temporary, and it can't be
the input's register.

### 4.1 Probe V2 (2026-09-30)

`upcase` and ROT13 at those registers, through the typed generator, checked
in a scratch test:

- **8-bit add and subtract are refused** (`UnsupportedWidth`): the lowering
  takes widths 0–64 for constants, copies, bitwise operations and unsigned
  comparisons, but narrow add/subtract has no normalisation rule. This is
  `issues/function-ir-narrow-arithmetic.md`, open since 2026-09-20.
- With the subtraction spelled as `b.band(0xdf)` (for a lowercase byte the
  same value), everything else goes through. The piece is 98 bytes, and its
  certificate checks in about a second.

So the round gains **slice N**: narrow add/subtract in the lowering (a word
operation, then a mask to the width), certified by a generic zero-extension
law, as the bitwise operations are. That closes the add/subtract half of the
issue; signed comparisons stay open there. The example is then spelled
`b.sub(0x20)`, not around the gap.

## 5. What is not in this round

- `tr -d` and `tr -s`. Delete makes the output shorter than the input, so
  the store needs its own cursor. Squeeze keeps state across bytes and
  chunks. Both are emitting loops with state: the general form is the
  loop generator gaining stores (`AccessCode` with a store, `LoopHead` over
  changing memory, output pieces). That is a round of its own, filed as
  `native-loop-emitting-stores`.
- Sets from argv. The model has no argv. This is a build-time `tr`.
- Partial runs, as for every program (`linux-syscall-trace-model`).

## 6. Decisions (2026-09-30, with the user)

1. **Scope: translate only.** -d and -s wait for the generator's emitting
   loop (§5), filed.
2. **The byte map is lowered through the compiler**, not tabulated. The table
   (the build evaluates `f` at all 256 bytes and the loop does one indexed
   load) would take any total `f` with a library-only proof. It is recorded
   here as the alternative, and `MapPiece` is the parameter it would meet too.
3. **Order.** N (narrow add/subtract) → A (byte store) → B (write loop
   continuation) → C (the process, tested at an abstract file as
   `read_state_process` was) → D (program, profile). V1 is done: `AddRI8`'s
   flags give the JNZ, since `execute_add_immediate` sets `add_flags` as
   `AddRR` does.
