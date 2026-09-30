# First real program: `wc -l` as a certified static executable — design

Status: **slices A–C landed 2026-09-24 (§8): `wc -l` builds as a certified
executable and runs.** Amendments from probing and building are folded into
§3–§5 and listed in §8. **Slice 4 landed 2026-09-25 (§10): `build-x86
--read-loop --print` writes the count in decimal to stdout, and the
certificate states that write.**
**Superseded in part 2026-09-27:** the single read is now a loop to the end
of file, and the read-once profile is gone
(`docs/native-read-until-eof-design.md`). §3 (fetched execution), §4 (the
trace) and §10's formatter still stand as written. §5's code, the claims in
§2 and §10, and the `read_loop_*` theorem names describe the read-once program.
Addresses here are as designed: the RW page moved from `0x401000` to
`0x410000` on 2026-09-29 (`docs/native-wc-design.md` §5.1).
Owner: `issues/native-first-program.md`. Follow-up owner for the syscall
model's proper form: `issues/linux-syscall-trace-model.md`.

## 1. What exists, and what this adds

Every native certificate so far covers either a fragment or a closed program:

- `build-x86` (`docs/x86-64-static-elf.md`) writes a standalone ELF, but its
  two inputs are baked in with `--arg`. The process claim is a fetched
  straight-line trace ending in `LinuxExitRequest`, and exit is the only
  syscall it models.
- The call profile (`docs/x86-64-calls.md`, `lib/elf64_calls.hthr`) adds a
  zero-filled RW page at `0x401000` and fetched CALL/RET. Its traces are still
  flat instruction lists (`FetchedCallTrace`).
- The bounded-loop certificates (`docs/native-bounded-loops-design.md`) state
  a loop's exit against a named source function (`count_occurrences`,
  `first_match`). Their execution relation, `ExecuteAccess`, is **structural**:
  it follows the `AccessCode` tree, and bytes and layout sit beside it in
  `AccessArtifact`. Nothing fetches the loop's instructions from memory.

This round adds a program that takes input from outside: read stdin once,
count the newlines with the certified counting loop, exit with the count as
status. It needs three new things:

1. **A fetched process step** covering every form the compiler emits, and a
   library theorem turning a structural `AccessCode` execution into fetched
   steps when the code's bytes are resident and its layout holds (§3). This is
   the piece that outlives `wc -l`: afterwards any loop or branch certificate
   runs inside a loaded image.
2. **A basic Linux trace**: `read` and `exit` as events, with the bytes a read
   returns quantified over (§4).
3. **The program**: a Heather spec, the entry/setup/exit glue, and a profile
   for `build-x86` (§5).

Writing to stdout needs byte stores and decimal formatting. That is the
milestone's second slice (§8), not this one.

## 2. The claim

For the built file `F`, and every input `bytes` with
`bytes.len() ≤ read_capacity()` (4096, the length the read asks for):

```text
LinuxRuns(io_linux(), [ReadEvent(0, bytes), ExitEvent(word_of_nat(64, wc_l(bytes)))],
    io_initial(F, page, gprs, flags))
```

`wc_l(bytes)` is an ordinary Heather function, the number of bytes equal to
10. `io_initial` is the loaded image at its entry, with arbitrary registers,
flags and page contents. The exit event carries the full request word, as
`LinuxExitRequest` does, and the parent observes its low eight bits. The
generated theorem is `count_lines_native_runs` in the build's certificate.

What this says: for every response the environment may give to the one read,
there is a run of the file that consumes it and exits with that status. It
doesn't say the run is the only one; §6 covers that.

## 3. Fetched execution of `AccessCode`

### 3.1 One step relation for the emitted subset

`FetchedStep(fetch, data, before, after)` holds when the bytes at
`before.rip` are fetched and are the canonical encoding of one of:

- an `Instruction` (the ALU forms), executing by `execute_normal`;
- a `ByteLoad`, executing by `ByteLoadStep` over the `data` read access;
- a `ShortControl` or a `NearControl`, executing by their `execute_*`.

`FetchedSteps` is its reflexive-transitive closure, stated with `ExecuteSteps`
style composition so traces concatenate. Calls (`CallInstruction`) join later
as another case. This is the first slice of the canonical step that
`issues/x86-64-machine-model.md` asks for, restricted to what the compiler
emits. It is **not** a second instruction semantics: each case is the existing
relation plus a fetch witness, as `ExecuteFetched` already is for ALU forms.

### 3.2 Residency

`CodeResident(fetch, memory, bytes, start)`: every byte of `bytes` reads
back at its address and is executable, and no address after a byte wraps.
Unlike `ReadableBytes`, the no-wrap fact follows every byte, the last one
included. That uniform tail makes append splitting (`resident(a ++ b, s) →
resident(a, s) ∧ resident(b, s + |a|)`) a plain induction.
`resident_readable` gives the `ReadableBytes` a `FetchedFrom` needs.

The ELF side proves residency of the whole program once, by induction over
the code as an open list (`elf64_io`'s `io_suffix_resident`): a byte at file
offset `k` below the page is at address `word_of_nat(64, 0x400000 + k)`, and
`next_rip` of that is the next offset's word *definitionally*. The one
bit-level fact, no carry out of `+1`, comes from `carry_add_bit`'s arithmetic
characterisation. No byte is evaluated. An evaluated Bool check (sound, proved
once) was tried first and dropped: see §8.

### 3.3 The bridge

```text
access_fetched : AccessLayout(code) → before.rip = start
  → CodeResident(fetch, before.memory, start, access_bytes(code))
  → ExecuteAccess(data, code, before, after)
  → FetchedSteps(fetch, data, before, after) ∧ after.rip = next_rip(start, |access_bytes(code)|)
```

The proof is by induction on `code`, with an inner induction on `LoopRuns`
for `AccessLoop`, and the same for `StructuredCode` underneath `AccessPure`.
Two facts make it close:

- Memory is unchanged by any `ExecuteAccess` (`access_memory`), so residency
  proved at the start holds at every later state, including the back edge.
- The structural relation already moves `rip`: canonical instructions advance
  it, and control forms set it to their targets. What layout adds is that
  those targets are the starts of the children, so residency of the child's
  bytes at the new `rip` follows by the append law.

The final `rip` equation is what lets the next fetched block start after the
code. Every loop and branch certificate then gets its fetched form from this
one theorem, with no generated fetch evidence.

## 4. The basic Linux trace

```text
inductive LinuxEvent { ReadEvent(fd: BitVec(64), bytes: List<BitVec(8)>), ExitEvent(status: BitVec(8)) }

record LinuxIo<M> {
    fetch: FetchAccess<M>, data: ByteReadAccess<M>,
    writable: M → BitVec(64) → Bool,
    store: M → BitVec(64) → List<BitVec(8)> → M,
}

inductive LinuxRuns<M>(io: LinuxIo<M>): MachineState<M> → List<LinuxEvent> → Type {
    Step:  FetchedStep(io.fetch, io.data, s, s') → LinuxRuns(s', events) → LinuxRuns(s, events),
    Read:  syscall bytes fetched at s.rip, rax = 0, rdi = fd, rsi = buf, rdx = cap,
           bytes.len() ≤ cap.toNat(), [buf, buf + len) writable,
           LinuxRuns(read_return(io, s, bytes), events)
           → LinuxRuns(s, Cons(ReadEvent(fd, bytes), events)),
    Exit:  syscall bytes fetched at s.rip, rax = 60
           → LinuxRuns(s, [ExitEvent(read_gpr(Rdi, s.gprs).take_low(8, 56))]),
}
```

`read_return` stores `bytes` at `buf`, sets `rax` to the length, and moves
`rip` past the two syscall bytes. RCX and R11 are clobbered. **The rule
quantifies over both universally** (§7 V4): the run must continue for every
value the kernel might leave there, so the program can't depend on them. That's
weaker than what Linux promises (return `rip`, `rflags`) and needs no flags
encoding.

It is deliberately small. Out of scope, and owned by
`issues/linux-syscall-trace-model.md`: error returns (negative `rax`), which
this model gives no rule; `write`; other syscalls; signals and `EINTR`;
determinism of the run; and whether the trace becomes an interaction tree.
Everything omitted is an **absent rule**, not an assumption that it can't
happen: the theorem is silent about a run that meets an error.

The existing `LinuxExitRequest` states the same thing as the `Exit` rule. A
one-line lemma turns one into the other. The old profile keeps its theorem.

## 5. The program

**Memory.** The call profile's *image*: the RX file at `0x400000` and the
zero-filled RW page at `0x401000`, here used whole as the input buffer
(capacity 4096). The header and `CallElfImage` are reused unchanged. The
*logical view* is new (amended by V3): `IoMemory { file, page: Nat → BitVec(8) }`
classifies an address by its `toNat`, not its bits. `io_read` checks
`0x401000 ≤ a < 0x402000` and reads `page(a − 0x401000)`, else falls back to
`static_elf64_read`, and `io_store` writes at a page offset. `CallMemory`'s
`stack_page` and file lookup are bit-level (`drop_low`, `is_zero_bits`).
Proving them at an open address `0x401000 + i` needs slicing lemmas the
bitvec library doesn't have, and Nat facts close by `omega` and run
arithmetic. The file is read the same way (`io_file_read`): the static
profile's 64-KiB window at `0x400000`, `nth` at `address − 0x400000`. That's
the mapping `static_elf64_read` states, by value rather than by bit slices. Read agreement is `io_read_stored`: after a store at offset 0,
`io_read(word_of_nat(64, 0x401000 + i)) = Some(byte)` when
`bytes.nth(i) = Some(byte)` and `i < 4096`.

**Code.** Four pieces, laid out in one file:

```text
entry:  mov rax,0; mov rdi,0; mov rsi,0x401000; mov rdx,4096; syscall
setup:  length, budget ← rax; base ← 0x401000; needle ← 10; cursor, carry ← 0
loop:   the count_occurrences loop, unchanged, at its existing placement
exit:   mov rdi, carry; mov rax, 60; syscall
```

Entry, setup and exit are straight-line and already expressible as fetched
blocks. The loop is `access_fetched` applied to the existing certificate.

**Spec and client lemma.** `examples/x86-native/wc_l.hthr` defines `wc_l(bytes) → Nat` by structural recursion, and
proves `count_occurrences(buffer_of(bytes), 10, n, 0, 0) = End(…, wc_l(bytes))`
for `n = bytes.len()`, where `buffer_of` builds the `ReadonlyBytes` whose
`read` is `bytes.nth`. That's a source-level fact, the client's own, like
`count_body_advances`. The program carries its own step (`line_body`, the
counting step) rather than importing the `readonly_loops` fixture: it's the
program's source. The lemma is `count_lines_input`, in the shape the library
names `ReadLoopComputes`. A program imports only `function_ir_loop`: the
CLI's loader resolves imports through `-L` directories, and the x86 modules
are bundled under harness names, so the `loop_run` outcome equations the
lemma uses moved from `function_ir_loop_trace` to `function_ir_loop`, where
the source contract lives. The loop's premises at entry are then: `LoopReadable`
from the read-agreement lemma, `loop_fits` from `n ≤ 4096`,
`LoopAddressBound` and the 2^47 bound from the constant base.

**Composition.** A library theorem `linux_read_loop_exit` takes the four
pieces' facts and returns the `LinuxRuns` of §2, over any loop artifact whose
`LoopObserved` exit places a Nat carry. It isn't `wc -l`-specific: it's the
read-once, loop, exit-with-carry process shape. The generator only emits the
instantiation: the placement, the pieces' names, and the source spec.

**CLI.** `build-x86 <file> <loop source> --read-loop --needle <byte>
--advance <theorem> --spec <function> --computes <theorem> -o <executable>`
(`crates/cli/src/native/read_loop.rs`). The producer runs the shared loop
generator at the profile's placement, checks the loop's pieces as their own
module, lays out entry, setup, loop and exit, and instantiates
`read_loop_runs` at the written file. The certificate also states the written
bytes piece by piece (`_written`, `_loop_written`) and the header against the
ELF model (`_file_correct`). The profile is a process shape, and there's no
application template.

## 6. What the claim leaves open

- **Determinism.** `LinuxRuns` is existential over steps, like every current
  process claim (`LinuxFetchedTrace` too). A proof that each supported
  byte sequence decodes one way, so the run is unique, is what turns
  "there is a run" into "the run". The decoders' soundness/completeness
  theorems are most of it. Owned by the trace issue.
- **One read.** For a regular file on stdin, a single read returns
  `min(size, 4096)` bytes; on a pipe it may return less. The claim is exactly
  about the bytes the read returned, so it's true either way. A
  read-until-EOF program needs a loop whose body is a syscall, which is the
  trace issue's second step.
- **Linux itself.** Loading, the entry state, and syscall delivery stay
  environment assumptions, stated in `docs/x86-64-static-elf.md`'s terms.

## 7. Verification items — results (2026-09-24)

Probed on `probes/fp/*.hthr` with the release CLI (≈8 s load baseline).

- **V1: holds.** `count_native<M>` is generic in `M` and returns an
  `AccessArtifact` plus `LoopObserved` against `count_occurrences`, so it
  feeds `access_fetched` directly. What it asks for shaped §5:
  `LoopHead.memory_agrees` quantifies over **every** address, so the loop's
  `ReadonlyBytes` is the memory's own read view (`read := λ a => io_read(m,
  word_of_nat(64, a))`, through `word_of_nat_toNat`), with `base`/`length`
  marking the region. Placement: base `Rdi`, length `Rbp`, needle `Rcx`,
  cursor `Rsi`, budget `R12`, carry `R11`.
- **V2: holds, loop included.** The whole bridge (`x86_64_fetched_code`:
  steps, residency, blocks, structured branches, reads, sequences, access
  branches, and the loop by induction on `LoopRuns`) checks in about 6 s
  over the baseline. The hypothesis held: layout plus `access_memory` is
  enough, with no per-instruction fetch evidence. Branch lemmas are stated
  once over byte lists (`branch_bytes`) and shared by `StructuredCode` and
  `AccessCode`.
- **V3: holds, with the memory amendment of §5.** The call-profile view would
  need bit-slicing lemmas at an open address. `IoMemory` makes it Nat:
  `io_read_stored` checks, with the closed bound `0x402000 ≤ 2^64` decided by
  run arithmetic (`leb_sound(…, trivial)`).
- **V4: resolved in the design, no probe.** RCX/R11 are universal in the
  `Read` rule (§4).
- **V5: fits.** The counting loop is 290 bytes. Entry (42), setup (46) and
  exit (15) bring the code to about 393, and the file to about 625 of the
  4096 the page allows.

Two small surface findings along the way: `let x: A = B = C` needs the
annotation parenthesised (known), and `let t = A ∧ B;` (a type-valued let)
is refused with "`And` takes 2 argument(s), found 0".

### The original items

- **V1: the counting certificate composes at a fixed memory type.**
  `count_occurrences_native` is generic in `M`. Instantiate it at the call
  profile's memory, with base `0x401000`, and check it on a probe `.hthr`.
- **V2: the bridge's shape, small first.** Hand-prove `access_fetched` for
  `AccessPure(CodeBlock)` and `AccessBranch` on a probe. Check the induction
  passes the structural check and the gate is cheap, before the `AccessLoop`
  case. Hypothesis to test: layout plus `access_memory` is enough, with no
  per-instruction literal fetch witness.
- **V3: read agreement over an open input.** Prove `call_memory_read` after
  `store(0x401000, bytes)` returns `bytes[i]` for `i < len`, open in `bytes`.
  Check that the file walk doesn't expand.
- **V4: the Read rule's RCX/R11 choice.** Write both variants and pick the
  one whose `read_return` state the setup block's proof doesn't have to look
  through.
- **V5: sizes.** The loop is roughly 350 bytes, plus about 60 of entry, setup
  and exit, well inside the 4096 − 232 file bound. Confirm from the real
  generator.

## 8. Slices

- **A — fetched execution, landed.** `lib/std/arch/x86_64/x86_64_fetched_code.hthr`
  (`x86_64_fetched_code`): `FetchedStep`/`FetchedSteps`, `CodeResident` and its
  split law, the branch lemmas once over byte lists (`branch_bytes`),
  `structured_fetched`, `access_fetched` with the loop by induction on
  `LoopRuns`, and `access_artifact_fetched`. Tests
  (`crates/elab/tests/read_loop_process.rs`, `counting_loop_runs_fetched`):
  the real counting certificate composed into a fetched run over open memory,
  and refusals of a span one byte short and a start shifted by one. They sit
  in their own member rather than `function_ir_loop_trace.rs`, whose seven
  tests were already near the member's CPU rail.
- **B — the basic trace, landed.** `lib/linux_x86_64_io.hthr` (`LinuxEvent`,
  `LinuxIo`, `linux_read_return`, `LinuxRuns` by recursion on the event list,
  constructors, and `linux_exit_request_runs` from the exit profile's request)
  and `lib/elf64_io.hthr` (the memory view, the `LinuxIo` instance,
  read-back, `io_buffer` and its agreement, code residency).
- **C — `wc -l`, landed.** `examples/x86-native/wc_l.hthr`,
  `lib/elf64_read_loop.hthr` (`read_loop_runs`, the process shape), the CLI
  profile, and the tests. `crates/cli/tests/native_read_loop.rs` builds with an
  empty `PATH` and runs 16 inputs: empty, no newline, 255/256/257 newlines,
  4096 newlines, random bytes at 1–9000 bytes, and a newline at the last byte
  read and just past it. It compares the status with the newline count of the
  first `min(len, 4096)` bytes, plus a pipe. The build refuses a needle its
  specification doesn't count. `crates/elab/tests/read_loop_process.rs`
  refuses six mutations of the process shape: the buffer outside the page, a
  capacity past it, the read and exit numbers, the descriptor, and the loop's
  base.

Amendments made while building:

- **Residency is proved, not evaluated.** The first certificate decided
  residency with an evaluated check (`code_resident_check`, sound once). It ran
  out of the 2^20 per-declaration fuel at about 40 bytes. Per byte, `nth` into
  the file chain cost roughly 65 evaluator steps per element walked (the
  232-byte header first), and `static_elf64_read`'s bit slicing about 20K. The
  check was removed. `io_suffix_resident` proves the whole span by induction
  instead, and the build checks in about 36 s.
- **The file is compared piece by piece.** A 626-byte chain compared against
  the model file ran out of fuel too. As in the call profile, the file is
  `header ++ read_loop_code(…)`: only the 232-byte header is compared against
  the ELF model, and the written code is linked to the model per block.
- **`read_capacity()` names the read's length** and bounds the claim's
  inputs, so the claim covers every length the read may return. Changing the
  capacity is refused rather than silently narrowing the claim.
- The exit event carries the 64-bit status word (§2), as `LinuxExitRequest`
  does.
- **Next milestone slice (not this round).** Byte stores from the program
  (`byte-memory-access-model`'s write subset), decimal formatting as a loop
  that writes, and a `WriteEvent`. That turns the status into `wc -l`'s output.

## 9. Decisions for discussion

1. `FetchedStep` as the first slice of the canonical step (a union of the
   emitted forms, calls to follow), rather than a loop-specific fetched relation.
2. The process claim stays existential. Determinism is the trace issue's.
3. Reuse the call profile's RW page as the buffer (4 KiB), rather than a new
   ELF profile with a sized `.bss`. A sized buffer is a small follow-up once a
   program needs more.
4. A failed read has no rule, so the theorem is silent about it, rather than a
   modelled error path the program must handle. The trace issue owns errors,
   and a program that checks `rax` is a branch we can already compile.

## 10. Slice 4: printing the count

The program's output becomes `wc -l`'s: the count in decimal and a newline on
stdout, then exit 0. The claim:

```text
LinuxRuns(io_linux(), [ReadEvent(0, bytes), WriteEvent(1, decimal(wc_l(bytes)) ++ [10]),
    ExitEvent(0)], io_initial(F, page, gprs, flags))
```

`decimal(n)` is an ordinary Heather function (digits by division by ten).

### 10.1 Compiler: word-valued helpers and crossing certificates (landed)

The model has no multiply, divide or shift, so the digits come from a
restoring chain: 16 steps `place(state, threshold, weight)`, each subtracting a
threshold (8000, 4000, … 1) from the value left in the state's low 16 bits
when it fits and adding the digit's weight to the ASCII bytes above. Written
as source, that is 16 nested calls of a branching helper. Two things were
missing, and both are general:

- **Word-valued helpers.** The reflector composed only Bool helpers (a match
  scrutinee). It now composes any scalar helper, as the result or as another
  helper's argument; a structured argument is produced first and bound for the
  ones after it, and a literal argument is substituted into the body rather
  than taking a register. Lowering prefers non-byte registers for wide
  composed results, leaving `SETcc` its byte registers.
- **Certificates that cost what their links cost.** A 16-link chain's
  certificate ran out of kernel fuel at every level from about the sixth.
  Attributed item by item (probes under `probes/dec`), there were four
  mechanisms, each fixed at the generator:
  1. A comparison's one-bit value was spelled `cons_bit(k, lt(…), zero(k))`
     where `NodeHolds` says `ofBool(lt(…))`; reconciling the two evaluated the
     comparison and, through it, the chain below (graph checks doubled per
     level). Spelled as `ofBool` at width one, and a branch reads the
     comparison's own Boolean (`_test_N`).
  2. A passthrough `0 | x` was compared with the source's `x`; the kernel
     decides that bit by bit, forcing `x`. Passthroughs are spelled `x` in
     both the certificate and the source expansion.
  3. Source agreement was one `refl` between two independently built
     expansions of the whole chain, exponential in depth. Now each composed
     helper call records its source spelling (`function_ir_cert::SourceValue`,
     `ReflectedStructuredFunction::sources`), and a composition **crosses** at
     it: the continuation is certified over its own valuation, and used at
     `{n}_carry(values)`, which carries `{n}_source(values) = helper(args)`;
     `{n}_link` equates the prefix's result with that call by one `refl`, the
     one place the helper's body meets the machine code. A produced argument
     is spelled by its own crossing's name, so no link compares an expansion.
     The source expansion and the typed observation cross at the same call.
  4. Byte lengths, decodes and branch layout converted
     `structured_bytes(subtree).len()` to a literal at every level, evaluating
     every encoding below. Lengths now compose from the children's
     `_byte_length` lemmas (`List::len_append`), and facts at a literal length
     are transported along them (`j`); `{n}_rip` gives the artifact's
     `rip_correct`. The exported bytes are the leaves' literal pieces in the
     code's shape (`{n}_lit`, `{n}_bytes_are`), since one comparison against a
     flat 1.5 KB literal also exceeds the fuel.

The formatter (`place` ×16, 1562 bytes) compiles and certifies with
`compile-x86` in about 35 s, and agrees with a C reference on every n below
10 000. At that point two residues remained: a link cost about 40K steps more per level, since
the continuation's instantiation walks the chain once (quadratic overall, 432K
at the root, within fuel); and a valuation lookup cost about 1.3K steps per
peeled `Succ` of the port id at a `BitVec(64)` result, whatever the entries
were. Every valuation now dispatches with a balanced `Nat::leb` tree instead,
and with it the per-level growth went: a link costs the same at every depth,
to 32 and beyond. Port ids
grow with depth, so the growth was most likely the lookup's (the 40K figure
predates the tree; the old binary was not re-measured). The underlying
width-dependent case cost was subsequently removed: the bit-transducer
classifier declines an unrelated neutral step before walking its result
type. Ordinary nested lookup now pays a constant cost per successor,
independent of result width; balanced generator dispatch remains in place
([valuation-lookup-case-step-cost](../issues/valuation-lookup-case-step-cost.md)). One link still
unfolded a whole helper. Nested helpers (`raise` → `times256` → `double`)
share their result port, and only the innermost body was kept for it, so the
`raise` crossing had no meaning over its child and compared all 40 doublings
by one `refl`. A port now keeps every layer's body (`SourceBodies`), and the
crossing reads the one over its child
(`issues/crossing-link-quadratic-cost.md`, closed).

### 10.2 The formatter's meaning (landed)

`lib/decimal_line.hthr` holds both sides.

- **The source functions the compiler emits.** `line_word(n)` is `n` moved
  above bit 40 by five `times256` calls, each eight `double` calls. The move
  is written as calls because a `let` copies its bound term into every use, so
  a chain of `let x = y + y` would double the term at each step. Sixteen
  `place` steps follow: while `r·2^40 + bytes` holds, subtract `c·2^40` when
  it fits and add the digit's weight, with no mask needed. `leading_zeros(n)`
  is `below(n, 10) + below(n, 100) + below(n, 1000)`, and `line_start` and
  `line_length` follow from it. Those are flat sums of one-level comparisons,
  because a three-deep tail tree ran out of byte registers.
- **The meaning.** `decimal(n)` is the digits of `n / 10` then `n % 10`, with
  explicit fuel (`decimal_digits(n, n)`): a `decreases` body matching on
  `le_dec` gets no unfolding equation
  (`issues/unfolding-computed-scrutinee.md`). For `n < 10000`:
  - `line_word_bytes`: the word's eight bytes are `line_bytes(n)`;
  - `line_start_value` and `line_length_value`: `0x401000 + line_skip(n)` and
    `5 - line_skip(n)`;
  - `line_in_word`: `decimal_line(n)` is those bytes from `line_skip(n)`, and
    has that length.
- **Proof shape.** The value goes through a generic `place_step`, where `q` is
  whether the threshold fitted, and a generic `four_steps` per digit group.
  All arithmetic is in Nat-only lemmas checked by `omega`. `bitvec_nat` gained
  `toNat_sub` (no borrow) and `toNat_take_drop` (a value splits at its low
  bits), and bytes read back through the second. `omega` dominates the
  module's check, and its certificate grows with every atom in scope. So each
  group's facts are a `GroupFacts` record, whose division laws come from
  `Nat::div_mul_add_mod` and `Nat::mod_lt`, and `omega` is used only for
  bounds and sums. Each digit also gets its own lemma, holding only the
  hypotheses it uses.
- **`omega` along the way.** A GCD-divided row was rendered without its
  trailing zeros, so the kernel refused certificates over nested division.
  That is fixed in `omega_cert.rs` by padding the row. `omega` also re-spells a
  context atom without an implicit it needs, which is open as
  `issues/omega-respells-atoms-without-implicits.md`; the proofs order their
  facts around it. Nested truncated subtraction stays an atom: the proofs
  state sums instead.

### 10.3 Stores, the write event, the process (landed)

- **`x86_64_store`.** `mov qword [base], source` for a base with no SIB byte or
  displacement (`store_base_plain`), writing `word_bytes(value)` low byte
  first through a `ByteWrites` model. `FetchedStep` stays the read-only bridge
  relation. `LinuxStep` is `FetchedStep ∨ StoreStep` over the profile's
  write model, and `LinuxRuns` runs over its closure. The fetched-step
  constructors lift (`linux_steps_of_fetched`), so the read-once proofs are
  unchanged.
- **`WriteEvent(fd, bytes)`.** RAX is 1, RDI the descriptor, and RDX's value the
  length. `LinuxWritesFrom` says every byte reads back at `rsi + i`, counted by
  value. RAX returns the length, and RCX and R11 are universal. A short write
  has no rule.
- **The process.** `elf64_read_loop`'s setup and loop are factored into
  `read_loop_counts`, which both profiles use. `lib/elf64_read_print.hthr`
  lays out entry, read, setup, loop, the base in R8, the three formatter
  artifacts (word to RAX, start to R9, length to R10, each keeping what later
  steps read), the store, `write(1, R9, R10)`, and exit 0. `read_print_runs`
  proves the trace of §10 from the program's `ReadLoopComputes` and one bound,
  `spec(bytes) < 10000`.
- **What made it check.** Three shapes were far past budget at first, and each
  one is general:
  - A `let` is inlined at every use, so a proof built as a long chain of
    `let`s is checked as one term the size of the chain. `read_print_after_read`
    split into `print_formats`, `print_sends` and `print_writes`, and its check
    fell by two orders of magnitude.
  - Deep `.right` projections through a large conjunction re-check the whole
    conjunction at every step. Records with named fields replace them
    (`GroupFacts`, `ReadPrintFormat`, `PrintFormatted`).
  - Large Nat length comparisons originally exceeded the kernel's depth
    budget, reported as `OutOfFuel`. Nat-prefix conversion now walks its tail
    iteratively (`issues/closed-nat-equality-depth-budget.md`); the image size
    and closed jump equalities use `refl`.
  A fresh `--print` build costs more than the exit-status build, mostly in
  `decimal_line`'s `omega` lemmas. It stays within one test process's CPU
  rail, but only just, so the native print test is acceptance-class (skipped
  by `scripts/test --fast`).
- **CLI.** `--print --bound <theorem>` on the read-loop profile. The producer
  generates the formatter with the typed generator at the fixed registers,
  checks each artifact as its own module, and states the written file piece by
  piece (`_code_written` through the formatters' `_bytes_are`).
