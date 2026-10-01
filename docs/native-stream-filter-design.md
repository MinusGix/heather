# One program shape: the stream filter

Status: **landed 2026-10-01** (F0–F5 in one round; §10 lists how it was
built). Anchor issue:
`issues/native-loop-emitting-stores.md` (step 2 of the line agreed in
`docs/automatic-author-surface-design.md`; step 3 is
`issues/native-one-program-logic.md`).

## 1. What this round does

The read profile has three program shapes, each with its own bundle, process
library and producer path:

| shape | bundle | process | programs |
|---|---|---|---|
| one count | `CountProgram` | `elf64_read_state` + `elf64_count_print` | `wc -l` |
| record of counts | `FieldsProgram` | `elf64_read_state` + `elf64_read_fields` | `wc` |
| byte map | a bare `fn` (picked by arity) | `elf64_read_map` | `tr` |

None of them can express a program whose output per byte depends on state
and may be empty: `tr -s`, `tr -d`, `cat -s`. This round replaces all three
with **one** shape. A program is a step that folds a state over stdin and
emits at most one byte per input byte, plus a finish that prints from the
final state. Its claim is `stdout = spec(stdin)` for every run that ends at
end of file. After the round, `wc`, `wc -l`, `tr`, `tr -s` and `tr -d` are
all instances, and the three old processes are deleted.

The user's calls (2026-10-01):

- **Library loop.** The per-byte loop with its store is a library loop around
  a generated straight-line step piece, as `tr`'s map loop is. The generator
  does not learn to store. Step 3's effectful code tree is where stores
  enter generated code.
- **At most one byte per input byte, in place.** Output is written into the
  one RW page behind the read cursor. Expanding filters (`unix2dos`, and
  `dos2unix`, whose held `\r` may emit two bytes) are filed for later.
- **Everything migrates; the old processes go.** `wc -l`'s exit-status form
  goes with them: every program now writes stdout and exits 0.

## 2. The program, as its author writes it

### 2.1 Semantics (`lib/stream_filter.hthr`, no x86)

```heather
// What one byte does: the next state, and the byte it emits, if any.
record Filtered<C> { next: C, emit: Option<BitVec(8)> }

fn filter_state<C>(step: C → BitVec(8) → Filtered<C>, bytes: List<BitVec(8)>) → C → C
fn filter_emitted<C>(step: C → BitVec(8) → Filtered<C>, bytes: List<BitVec(8)>) → C → List<BitVec(8)>

// What the program prints after end of file, from the final state: nothing,
// one decimal line, or three `%7d` fields (the library's proved tails).
inductive Finish<C> { Quiet, Line(count: C → Nat), Fields(first, second, third: C → Nat) }
fn finish_bytes<C>(finish: Finish<C>, state: C) → List<BitVec(8)>   // Nil / decimal_line / three_fields_line
fn FinishFits<C>(finish: Finish<C>, state: C) → Type               // True / < 10^4 / each < 10^7

fn filter_output<C>(step, init, finish, bytes) → List<BitVec(8)> {
    filter_emitted(step, bytes, init) ++ finish_bytes(finish, filter_state(step, bytes, init))
}
```

Both folds recurse on `bytes`, with the state as a λ-bound accumulator, the
same shape as `fold_bytes`. The library proves the append laws once
(`filter_state_append`, `filter_emitted_append`), and two helpers turn the
old shapes into steps:

- `counting(g: C → BitVec(8) → C)` is `λ s b => Filtered(g(s, b), None)`.
  Its lemmas say that `filter_state` is `fold_bytes(g)` and that nothing is
  emitted. `wc` and `wc -l` keep their `fold_bytes` proofs unchanged.
- `mapping(f: BitVec(8) → BitVec(8))` over `Stateless` (an empty record) is
  `λ s b => Filtered(s, Some(f(b)))`. Its lemma says the output is
  `bytes.map(f)`.

### 2.2 The bundle (`lib/read_program.hthr`, rewritten)

```heather
record Filter<C>(step: C → BitVec(8) → Filtered<C>, init: C, counts: List<C → Nat>,
    finish: Finish<C>, spec: List<BitVec(8)> → List<BitVec(8)>) {
    advances: (state: C) → (byte: BitVec(8)) → counts_advance(counts, step(state, byte).next, state) := { split_all; all_goals { omega } },
    computes: (bytes: List<BitVec(8)>) → spec(bytes) = filter_output(step, init, finish, bytes),
}
```

- **`counts`** are the state's Nat fields in order, as `FieldsProgram`'s
  were. A filter with no Nat fields writes `Nil`. They are what must fit a
  word, and `advances` is how they are shown to fit.
- **`spec`** is the whole of stdout. For `wc` it is
  `λ bytes => three_fields_line(wc_lines(bytes), wc_words(bytes), wc_bytes(bytes))`,
  so the claim says what a reader means by "wc prints this", not three
  separate equations.
- `CountProgram`, `FieldsProgram`, `SpecsCounted` and `fold_body` are deleted.

### 2.3 The programs

- **`tr -s 'x'`**: the state is the last byte emitted, and whether one has
  been. Emit unless the byte is the squeezed one and equals the last.
- **`tr -d 'x'`**: `Stateless`; emit unless the byte is the deleted one.
- **`tr a-z A-Z`**: `mapping(upcase)`.
- **`wc -l`**: `counting(line_step)` over `Nat`, `Line(λ c => c)`.
- **`wc`**: `counting(wc_step)` over `WcState`,
  `Fields(λ s => s.lines, λ s => s.words, λ s => s.bytes)`.

Which bytes `tr -s`/`-d` act on is fixed in the source. There are no
command-line arguments: there is no argv model yet.

### 2.4 Probe findings (2026-10-01, `probes/filter/`)

- `Filtered<C>`, `Stateless {}` and a `tr -d` spec proof over
  `filter_emitted` elaborate as written above.
- **The `advances` default worked only by accident of wc's shape.** It closes
  a goal that splits into `∧`. With `counts = Nil` the leaf is
  `counts_advance(Nil, …)`, which `omega` refuses because it reduces to
  `True`. With one count, the leaf `counts_advance([c], …)` is not unfolded
  to `c(next) <= Succ(c(state))`. Fix: `omega` takes its goal to weak head
  normal form before reading it, and closes `True`. Slice F0.

## 3. The claim

For the built executable, for every history of reads and writes:

- chunks and EINTRs on the read side;
- each chunk's short writes and EINTRs on the write side;
- an ending: the empty read, a failed read, or a failed write;

the file has a run that produces the events `filter_events(...)`. On a run
that ends at the empty read and whose finish fits:

```
sent_to(1, filter_events(...)) = spec(eof_input(steps))
```

and the run exits 0. The premises:

- **`FilterRoom(counts, input)`.** For `Nil` this is `True`; otherwise it is
  `input.len() + 4096 < 2^64`, so `tr`, `tr -s` and `tr -d` keep an
  unbounded claim.
- **`FinishFits(finish, filter_state(step, input, init))`**, which carries
  today's `< 10000` and `< 10^7` bounds.

`_runs_every` (determinism) is kept as it is.

### 3.1 The driver gives the body the state carried in

A filter's output for a chunk depends on the state at the chunk's start.
For `tr -s` that is the last byte of the previous chunk. Today
`eof_run(body, …)` calls `body(bytes, x, after)` with no access to what was
read before, and `ok(bytes, x)` constrains the history without it either. So
`eof_run`, `EofSteps`, `EofEndOk`, `EofBody` and `EofBodyEnds` gain the
prefix read so far (`seen`) as the body's first argument:

```
body: List<BitVec(8)> → List<BitVec(8)> → X → List<LinuxEvent> → List<LinuxEvent>
```

The filter's body is then:

```
λ seen bytes writes after => filter_writes(filter_emitted(step, bytes, filter_state(step, seen, init)), writes, after)
// filter_writes(Nil, _, after) = after;  filter_writes(out, writes, after) = write_events_then(out, writes, Finished, after)
```

A chunk that emits nothing makes no write: the code jumps straight back to
the read, and `ok` requires `writes = Nil`. `write_events_then(Nil, …)` is
not `after`: it records a zero-length write (V5). So the empty case is
`filter_writes`'s own. The `stdout` lemma composes the chunks by
`filter_emitted_append`. The filter is the driver's only client after the
round, so nothing else changes shape.

## 4. The process (`lib/elf64_read_filter.hthr`)

### 4.1 Code

```
init:   zero the state registers (R13, R14, R15, R8)            ← state_init_block, moved here
read:   read head (elf64_read_pieces)          JZ → finish, JS → failure tail
setup:  RSI = page, RCX = RAX, RDI = page, R12 = 1
loop:   MOVZX RAX, [RSI]                          (ByteLoad Rax ← [Rsi])
        step piece                                (generated: state in place, RDX = byte, RBX = flag)
        MOV [RDI], DL                             (ByteStore base Rdi, source Rdx)
        ADD RDI, RBX ; ADD RSI, R12 ; SUB RCX, R12
        JNZ loop
close:  R10 = RDI ; R9 = page ; SUB R10, R9       JZ → read (nothing emitted)
write:  write loop (elf64_write_loop) on R9, R10, continuing at read
fail:   failure tail
finish: Quiet: exit(0) | Line: count tail | Fields: fields tail
```

**The store is branchless.** It always stores, and the out cursor advances
by the flag (0 or 1). At byte `i` the out cursor `o` satisfies `o ≤ i`, so
`page[o]` is either the next free output slot or the input byte already
loaded into RAX. Bytes after `i` are untouched. The loop invariant (`FilterAt`):

- `page[0..o)` is the chunk's output so far, `filter_emitted(step, bytes[0..i), s₀)`;
- `page[k] = bytes[k]` for `k ≥ i`;
- the state registers hold `filter_state(step, bytes[0..i), s₀)`;
- RSI = page + i, RCX + i = n, RDI = page + o, R12 = 1.

Two facts give `o ≤ i`: `filter_emitted` of `i` bytes has at most `i`
bytes, and `o` is its length.

**Registers.** The store's base must not be RBP or R13 (their mod=00 form
encodes RIP-relative addressing) and must not be RSP or R12 (they need a SIB
byte). That puts the out cursor in RDI. The step piece reads the state
registers and RAX, writes the state registers in place plus RDX and RBX, and
may use RAX, RDX, RBX, R9, R10, R11 and RBP as scratch. RSI, RCX, RDI and
R12 are the loop's, and the piece's contract keeps them. The write loop
must keep R8 and R13–R15, so **`WriteThen` gains a kept-registers
premise** (a `WriteKept`, as `ReadKept` is for the read). Its block writes
RSI, RDX, RDI, RAX and RBX; Linux clobbers RCX and R11; R9 and R10 advance.

**Tails** are reused: `count_tail_runs` (decimal line of R13) and
`fields_tail_runs` (R13–R15), each restated over the filter's `rep`.
`Quiet` is the write loop's `exit(0)` block on its own.

### 4.2 Proof structure

- The per-byte loop is modelled on `elf64_read_map`'s `map_byte` /
  `map_loop` / `map_chunk`, which `docs/native-tr-design.md` §8 says cost
  minutes until each sub-step was `have`-bound into a record of its own.
  Keep that discipline from the first draft: `FilterLoaded`,
  `FilterStepped`, `FilterStored` and `FilterAdvanced` are records, and
  `filter_byte` chains them.
- **Nat fields fit.** The step piece's contract needs each Nat field of the
  next state below 2^64. With init at zero and `advances`, each count after
  `k` bytes is at most `k`. The library proves `counts_bounded` once, by
  induction over `filter_state`, and `FilterRoom` gives
  `seen.len() + bytes.len() < 2^64`.
- The process is an `EofProcess` for `eof_from` (`elf64_read_pieces`), with
  the invariant `rep(gprs, filter_state(step, seen, init))`, and with `X` and
  `Y` as the map's (`List<WriteStep>`, `WriteFailure`).

## 5. The step piece and the generator

### 5.1 Contract (`lib/elf64_read_filter.hthr`, beside the loop that consumes it)

```heather
// From a state whose registers hold `s` (`rep`) with the byte in RAX, the
// piece runs to its end with the next state in the same registers, the
// emitted byte's flag in RBX and its byte in RDX, memory untouched, and every
// register outside `scratch` and the state's as it was.
fn StepPiece<C>(code: StructuredCode, rep: Gprs → C → Type, fits: C → Type,
    step: C → BitVec(8) → Filtered<C>, scratch: List<Gpr>) → Type {
    (before: MachineState<IoMemory>) → (s: C) → (b: BitVec(8)) →
        rep(before.gprs, s) → read_gpr(Rax, before.gprs) = b.zero_extend(56) → fits(step(s, b).next) →
        StepRan(code, before, rep, step(s, b), scratch)
}
// StepRan: the execution, layout, decoding, rip and memory facts of a
// StructuredArtifact, plus rep(after.gprs, next), flag = emitted_bit(emit),
// (emit = Some(x) → imm_byte0(RDX) = x), and Kept for the rest.
```

`rep` and `fits` are the generator's `{p}_rep` and `{p}_fits` restricted to
the state, as the state loop already emits them. Bool fields use
`loop_bit`, Nat fields `LoopWord`, and BitVec fields are equal as words.

### 5.2 Generator work (Rust)

- **Reflection.** The reflector recognises `stream_filter::Filtered` by its
  resolved identity, as it does `LoopStep`. A result `Filtered<C>` flattens
  to output ports: C's fields (or C itself when it is a scalar), then the
  flag (a Bool port), then the byte (`BitVec(8)`). In a constructor
  application `Filtered(n, None)`, the flag is `False` and the byte is a
  literal 0. In `Filtered(n, Some(e))`, the flag is `True` and the byte is
  `e`. The step is either a resolved global, or `counting(g)` /
  `mapping(f)`, recognised as `fold_body(g)` is today.
- **Lowering.** The emit ports are lowered first, while the state is intact,
  into RDX and RBX. Then the state ports are written in place in
  `write_order`. That machinery exists in `loop_native.rs` and moves to a
  shared module. The composition proof that `{p}_body_step` builds over the
  per-field typed artifacts becomes a published `{p}_step_piece:
  StepPiece<C>(…)`.
- **Retired.** The `bounded_readonly` reflection keeps search loops
  (`Break`). The `fold_body` path, `ReadProgramKind` and the needle go,
  which closes `issues/fold-programs-carry-a-needle.md` by deletion.

## 6. Producer (`crates/cli/src/native/`)

- `profile_of`: a bundle whose written type's head is `Filter` is the only
  read profile. `Map`, `Count` and `Fields` go, and so does the
  "one-parameter function is a map" rule. `--print` goes, since the finish
  says how the program prints.
- **`read_filter.rs`** replaces `read_map.rs`, the Count/Fields half of
  `read_loop.rs`, and `read_fields.rs`'s certify. It takes the parts that
  are shared today (`claims`, `image_facts`, `read_head`/`fail_tail`,
  `write_loop`, `Layout`), and the formatter generation for `Line` and
  `Fields` (`print_format_*`, `fields_format_*` modules, unchanged). It
  emits the context module, the step piece, the layout and jump facts, the
  claim `{prefix}_runs`, `{prefix}_runs_every`, and `{prefix}_sends` (the
  stdout lemma at the program).
- The producer still validates `init` (its Nat fields are zero) and `counts`
  (the Nat fields, in order). For `Line` and `Fields` it checks that the
  printed counts are the first one or three fields, which the tails read
  from R13–R15.

## 7. Deleted

These are deleted, each after its last client has moved:

- **Library:** `lib/elf64_read_state.hthr`, `lib/elf64_read_map.hthr`, and
  `elf64_count_print`'s process half (its tail stays).
- **Library helpers:** `function_ir_loop`'s `fold_body`, `fold_body_*`,
  `SpecsCounted`/`specs_counted` and `LoopCountsAdvance`, if nothing else
  uses them.
- **Producer:** the Count/Fields/Map paths.
- **Tests:** `read_state_process`, `read_map_process`, `count_print_process`
  and `read_loop_process`'s program half. They are replaced by a
  `read_filter_process` test that composes `tr -s` and `wc` at an abstract
  file, plus their refusal controls.

`elf64_read_fields`'s tail half stays (`fields_tail_runs`) with
`field_line`.

Before deleting anything that isn't a `fn`, `theorem` or `record`, grep for
its users. The dead-declaration pruner once swept an `inductive`.

## 8. Slices

| slice | content | done when |
|---|---|---|
| F0 | `omega` normalises its goal and closes `True`; the `advances` default works for 0 and 1 counts | probe `t_filter_progs` checks |
| F1 | `lib/stream_filter.hthr` (semantics, append laws, `counting`, `mapping`, `counts_bounded`), the new `Filter` bundle beside the old ones; driver threads `seen` | all programs written against it check, with the old bundles still present |
| F2 | `lib/elf64_read_filter.hthr`: `StepPiece`, `WriteKept`, the per-byte loop, chunk, process, tails, claim and stdout lemma | an elab test composes the process at an abstract file over a **hand-written** step piece |
| F3 | generator: `Filtered` reflection, emit-first lowering, `{p}_step_piece` | the piece for `tr -s`'s and `wc`'s steps certifies, plus a negative control (wrong emit) |
| F4 | producer `read_filter.rs`; `tr -s`, `tr -d` build and match host `tr` | CLI tests |
| F5 | `tr`, `wc -l`, `wc` move to `Filter`; the old bundles, processes, producer paths and tests are deleted | full suite; executables match host tools |

F2 (Heather) and F3 (Rust) meet only at `StepPiece`, so they can run in
parallel once F1 lands.

**Verification items, cheap and first.** If one refutes the design, stop
and amend it before working around it.

- **V1.** Does the reflector, given `step(s, b).next.f` spelled as a source
  function, already reflect it (helpers inlined, ι on constructor
  projections)? If yes, F3 is per-output source functions plus the Option
  ports, not a new result kind.
- **V2.** Is `MOV [RDI], DL` encoded by `byte_store_bytes`, and is
  `ADD RDI, RBX` a block instruction? **Holds.** The store always emits a
  REX prefix, so source DL is DL and not DH. Its base check already refuses
  RSP, RBP, R12 and R13 (`x86_64_store.hthr:23`). `AddRR` is the step
  block's own instruction.
- **V3.** Can a hand-written step piece for `tr -d` meet `StepPiece`, by way
  of `Computes`-style certificates for the flag and the byte? This sizes
  F2's test without waiting for F3.
- **V4.** Does the write loop touch R8 or R12–R15? **No.** It writes RSI,
  RDX, RDI and RAX (print block), R9 and R10 (advance) and RBX (retry), and
  Linux clobbers RCX and R11. It keeps R8, R12–R15 and RBP.
- **V5.** Is `write_events_then(Nil, Nil, Finished, after) = after`?
  **Refuted.** It is a zero-length `WriteEvent` followed by `after`, so an
  empty chunk output goes through `filter_writes` (§3.1).

## 9. Not this round

- **Expanding filters** (`unix2dos`, `dos2unix`) need more than one byte per
  input byte and a second writable region.
- **Arguments** (`tr -s` with argv sets) need an argv model.
- **Byte vocabulary** (`==` and literals) is
  `issues/byte-vocabulary-for-native-programs.md`; the programs still spell
  comparisons.
- **One program logic over interaction trees** is step 3, where this
  process's claim becomes a lemma.

## 10. As built (deviations, in the order they were found)

- **§2.2, the bundle's module.** `Filter` and `Finish` live in
  `lib/filter_program.hthr`, not `read_program`. Test harnesses load
  `read_program` from source, and a bundle whose finishes mean the
  formatters' lines would make every one of them check `field_line`. At F5
  `read_program` goes and `filter_program` is the read profile's bundle.
- **§2.4, F0 is two fixes.** `omega` unfolds a goal's head one δ-step at a
  time and stops at the first spelling it reads (a relation, `∧`, `False`),
  closing `True` outright. Weak head normal form went too far: it unfolds
  `Le` into its recursor. The unfolded goal is passed through `split_all`'s
  `simplify_goal`, so an applied count `λ s => s.lines` reads as the field.
  Then `split_all`'s simplifier reduces a projection whose receiver unfolds,
  within a bounded budget, to a constructor: `counting(g)(s, b).next` is
  `g(s, b)`. Without it, a counting step with nothing to split (`wc -c`'s
  `λ c b => Succ(c)`) left an atom `omega` spelled but could not
  re-elaborate. Such a step still needs `advances := …`, because `omega`
  does not unfold `g`. Its atoms are not read up to computation.
- **§3.1, the driver.** `seen` is the curried last parameter of `eof_run`
  and `EofSteps`, because a recursion that varies a parameter must curry it.
  A chunk that ends the run (`EofBodyEnds`) also gets `seen = input`, since
  the filter bounds its counts in that chunk too. The room premise's 4096 of
  slack covers it.
- **§4.1, the write loop.** Its reached states are named functions
  (`wl_moved`, `wl_going`, `wl_back`), because a theorem's `Exists` witness
  is opaque to conversion. `WlThen`, `WriteThen` and `FinishedThen` carry an
  `origin` register file and hand their continuation `WriteKept(state,
  origin)`.
- **§4, the state's vocabulary.** `state_init_block`, `StateKept`,
  `StateFramed`, `StateInitialised`, `EofTail` and `CountWord` moved from
  `elf64_read_state` into `elf64_read_pieces`, where both the old process
  and the filter use them.
- **§4, the library's split.** `lib/elf64_read_filter.hthr` is the
  process, its claim (`read_filter_runs`), its stdout lemma
  (`filter_sends`) and the quiet finish. `lib/elf64_filter_finish.hthr`
  holds the line finish and `filter_prints` (stdout is `spec(stdin)`), and
  reuses `fields_tail_runs` as it stands. That way a test of the process
  does not load the formatters. `WriteFailure` moved into the write loop.
- **§4.2, counts that fit.** `CountsAtMost` and `counts_grow` (each count
  after `n` bytes is at most `n`, from `advances` and a zero start) feed
  `ChunkFits`. `FilterRoom(Nil, _)` is `True`, so a filter without counts
  has a claim for any input. A count applied to a state is not an `omega`
  atom (`count(next)` for a local `count`), so those steps go through Nat
  lemmas.
- **Programs.** `tr -s '\n'` keeps a `Bool` (after a newline), and
  `tr -d '\r'` is `Stateless`. Their spec proofs restate the step's nested
  matches in their motives, each inner match annotated (`as λ _ => T`).
- **F3, the generator (§5.2).** V1 is refuted. The reflector does not see
  through `step(s, b).next.f`, because it inlines only helpers that return
  scalars and does not reduce projections of constructors. So `Filtered` is
  a result kind of its own in reflection, recognised by its resolved
  identity, whose ports are the state's, then the flag, then the byte.
  `counting(g)` reflects `g`, and `mapping(f)` reflects `f`. Their emits are
  library constants (`emits_never`, `emits_always`, `emitted_nothing`).
- **F3, the lowering order (§5.2).** It is not "emit first, into RBX and
  RDX". The lowering's byte registers for comparisons are only AL, CL, DL
  and BL, and RAX and RCX are taken. So an emit read from the state is held
  in R9/R10 while the fields are written in place, then copied into RBX/RDX
  (`emit_copy`). Fields that read each other in a cycle (`tr -s`) are held
  the same way. An emit that reads no state goes last, straight into place.
  The contract is unchanged. The proper fix is
  `issues/lowering-rex-byte-registers.md`.
- **F4, the producer (§6).** The context module restates the program's data
  as the profile needs them: the step (the written one, `counting<C>(g)` or
  `mapping(f)`), the zero state, the Nat fields as counts, and the finish
  over the first fields. Its `{p}_program` types the author's bundle at
  those, so a program whose data differ is refused there. The step piece is
  generated over the context's step, so the context imports
  `filter_step_piece`, whose constants the generator reads. The zero
  state's `CountsAtMost` is written as one `Nat::le_refl(0)` per count,
  since `omega` does not spell an applied count. A finish's own write loop
  is laid out under other names (`twrite` …), because one layout holds two
  write loops. The filter's cursor block is `cursors` (the write loop has an
  `advance`). `--print` is gone, since the finish says what is printed.
- **F5, what stayed.** The loop generator's `fold_body` path stays,
  because its record-state loops are generator coverage
  (`function_ir_loop_trace`'s `record_state_loop_certificate_checks`, now
  over a local copy of `wc`'s step) and search loops share the code. Only
  the program bundles' Rust (`ReadProgramKind`, `ReflectedReadProgram`,
  `reflect_step_record`) went. `fold_body_folds` and `fold_body_fold` stay
  beside it. The tails' libraries (`elf64_count_print`, `elf64_read_fields`)
  lost their process halves. Their mutation controls now run against the
  tails alone (`read_print_process`, `read_fields_process`), and the read
  pieces' controls against the filter (`read_loop_process`). The state
  layout's producer test is now the filter layout's
  (`read_filter::tests`).
- **Sizes**, in bytes: `wc` 5954, `wc -l` 1630, `tr` 682, `tr -s` 878,
  `tr -d` 755. `wc -l` used to exit with its count. It now always prints
  its line, through the same tail as before.
- **Filed:** `issues/hole-beside-a-splitting-field-default.md`,
  `issues/lowering-rex-byte-registers.md`,
  `issues/native-expanding-filters.md`.
