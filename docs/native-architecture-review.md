# The native program stack: an architecture review

Status: **review, 2026-09-30. R0 and R1 chosen and landed the same day (§8); R2 onward open.** Read-only
survey of what `wc -l`, `wc` and `tr` left behind, taken before a fourth
program (`tr -s`/`-d`, `issues/native-loop-emitting-stores.md`) adds another
process. The question is engineering, not speed: what is repeated, what is
awkward to use, what a program author has to know that nothing checks. No
timings were taken (§7 says where cost matters to the choices anyway).

## 1. The stack as it stands

From the bottom:

- **Machine and OS model.** `x86_64` (register instructions), five
  execution relations for the same code shapes (block, structured, access,
  fetched, Linux; §2.4), `IoMemory` (the file plus one RW page at
  0x410000), the Linux trace (`LinuxRuns` over read/write/exit events) and
  determinism (`linux_runs_every`).
- **Process libraries** (`lib/elf64_*`, about 5,000 lines). Each program
  added one: `elf64_read_state` (wc's fold across reads), `elf64_read_map`
  (tr's per-chunk map and write), `elf64_write_loop`, and the tails
  `elf64_count_print` and `elf64_read_fields`, over the shared blocks in
  `elf64_read_pieces` and `elf64_print_pieces`. Formatting is
  `decimal_line` (wc -l) and `field_line` (wc).
- **Generators.** The loop generator (`loop_native.rs`) composes typed
  pieces into a read-only loop through `AccessFragment`. The typed
  generators (`generate_elaborated_typed_x86`, `…_typed_fields_x86`) publish
  straight-line pieces as `StructuredArtifact`s.
- **CLI producers** (`crates/cli/src/native/`): one per profile
  (`read_loop.rs` for `--read-loop` with `--print`, `read_fields.rs` for
  `--fields`, `read_map.rs` for `--map`). Each lays out the program, emits
  image and jump facts, and instantiates the library's claim.

What works well and should survive any refactor: claims universal over
histories and runs; the determinism corollary on every build; `tr`'s author
experience (a 27-line file, one `BitVec(8) → BitVec(8)` function, no
theorems); `AccessFragment`'s layout machinery, which computes displacements
from children and proves them itself; the open-parts length discipline.

## 2. Findings

### 2.1 Layout is written four times, and a fifth in Rust

Every process states its layout as:

1. a right-nested `++` code function (`state_code`, `map_code`, …);
2. a length function and a `len_app` chain;
3. offset functions (`state_at_*`, `map_at_*`, `wl_at_*`, `ct_*`, `fc_*`:
   about 58 in all);
4. a `*Pieces` residency record, proved by a chain of `resident_split_at`
   (about 54 written steps; each step spells the whole remaining suffix);
5. skip and span functions, with an omega "sum" lemma and a target theorem
   per jump.

The producer then recomputes the same offsets and displacements from its own
Rust encoding of the fixed blocks (`read_map.rs` says so: "Offsets from the
entry, as elf64_read_map's `map_at_*`"), and the kernel ties the copies
together by `refl`. A library edit breaks the producer as an opaque `refl`
failure. Roughly two thirds of `read_state`, `read_map` and `write_loop` is
layout and stepping plumbing; the semantic core of each is a few hundred
lines.

Three styles of backward-jump fact coexist (span, absolute offset, and
`map_to_read_target`, which works only because the read sits at offset 0),
and tr's end-of-file JZ lands inside the write loop (`wl_at_exit`), so the
map process's skips list the write loop's internal lengths.

### 2.2 The same proofs, once per process

- **The failure path** (EINTR test, retry jump, exit 1) is proved three
  times: `state_failed`/`map_failed`/`wl_failed`, and likewise `*_retry`
  and `*_fail_exit`. The first two differ only in the layout's names, with
  three near-identical result types beside them (`StateFailedAt`,
  `MapFailedAt`, `WriteFailedAt`). About 300 lines.
- **The read request and end-of-file test.** `map_ask` factors the request;
  `state_from` inlines it four times; `wl_ask` is a third variant. The
  "JZ taken" step is written in `state_from` and again in `map_end`.
- **The chunk induction.** `state_from` and `map_from` share one skeleton
  (end, failure, chunk, interrupted), with the post-read memory and RIP
  boilerplate repeated in every arm.
- **Histories.** `ReadStep`/`ReadEnding`, `MapStep`/`MapEnding`,
  `WriteStep`/`WriteEnding`, each with its own validity predicates and
  event function. `MapStep` is `ReadStep` with a write history attached.
- **Stored bytes.** Three kits prove "memory holds these bytes at this
  offset": `line_in_word`/`print_sends` (wc -l), `StoredList` (wc),
  `store_byte_here`/`store_at_offset`/`map_page_mapped` (tr).
- **Register frames.** "Run a piece, then re-derive every live register by
  `trans(x.registers_preserved(R, keeps_R), …)`" is hand-threaded in
  `count_formats`, `field_prints` and `map_fetched`, with a per-client
  keeps record (`ReadPrintFormat` 10 facts, `FieldsFormat` 7, `MapKeeps`
  5).
- **Old and new APIs kept side by side** so earlier tails didn't change:
  `wl_from`/`wl_from_then`, `WriteTargets`/`WriteLoopTargets`,
  `write_events`/`write_events_then`.

### 2.3 Claims are long and conventions are unchecked

The claims take 24 (`read_map_runs`), 33 (`read_state_runs`) and 50–54
(`read_count_print_runs`, `read_fields_runs`, `read_fields_spec_runs`)
parameters: a loop-certificate bundle of about 16 values re-threaded through
every lemma, loose displacement premises (4–8), and residency.

For a program author (`examples/x86-native/`):

- `--read-loop` needs five names by flag (`--needle`, `--advance`,
  `--spec`, `--computes`, `--folds`), whose types are conventions checked
  only when the generated certificate is. A mistake surfaces as a kernel
  error deep in generated text.
- The author writes a `bounded_readonly` wrapper the CLI names instead of
  the step, and a `LoopFolds` theorem that is always "every branch is
  `refl`".
- A record state's advance theorem has no library type: its shape is fixed
  by a projection string in the generator.
- `--needle` restates what the `computes` theorem already fixes; a mismatch
  is caught only at the certificate.
- `--fields` takes exactly three `Nat` fields from R13–R15 and prints
  `%7d` (`issues/fields-profile-shape.md`).

### 2.4 The layers below: five ways to say "this code runs"

`ExecuteBlock`, `ExecuteStructured`, `ExecuteAccess`, fetched steps and
Linux steps describe overlapping code shapes. `AccessBranch` is weaker than
`CodeBranch` (TEST only, rel8 only). Nothing above single fetched steps can
hold a store or a syscall, so every loop that contains one is a hand
induction in a process library (`MapAt`, `EofChunks`, the write loop). Two
generations coexist (`ExecuteFetchedBlock`/`LinuxFetchedTrace` beside
`FetchedStep`; the `Linked*` block family), and some pieces are simply
written twice:

- `FetchedOrStore` (step_forms) and `LinuxStep` (linux_x86_64_io) are the
  same disjunction.
- `syscall_bytes` and `linux_syscall_bytes` are the same two bytes.
- The conditional's bytes are spelled in `branch_bytes`, `structured_bytes`
  and `access_bytes`.
- The `linux_runs_*` intro lemmas take `FetchedSteps` for read and exit and
  `LinuxSteps` for the rest.

Residency after a store has no lemma. `x86_64_fetched_code`'s header still
says "Execution never writes memory", and the process libraries work around
it by quantifying residency over every page. In `IoMemory`, code is fetched
only from the file, so a store can't change what is fetched, but that fact
is never stated.

### 2.5 Output

Two formatters with separate specs: `decimal_line` (per digit count, for
`n < 10000`) and `field_line` (per column, for `n < 10^7`). The restoring
kit is copied from one to the other with the shift changed from 40 to 32.
Each has its own tail, stores and offsets. The write loop's
`LinuxWritesFrom` seam is already the right boundary between "bytes in
memory" and "bytes on stdout".

### 2.6 Hardcoded values

- **Addresses and sizes.** The page base 0x410000 and the entry 0x4000e8
  appear as literals across the libraries and producers. `io_page_base()`
  and `read_capacity()` exist, but the literal dominates; 4096 appears
  dozens of times.
- **Registers.** Each process fixes its own. The state process has used 15
  of 15 since wc (native-wc-design §4), so registers can become
  parameters only in part.
- **Tail placement.** A tail is placed at `state_at_done(needle,
  loop_bytes)`, so the print tails can't follow the map process.
- **Store bytes.** Store encodings are hand-written byte vectors in the
  producers, not derived from `word_store_bytes`.
- **Stale text.** `issues/native-proven-formatting-api.md` and
  native-wc-design §5 still describe a one-word `field_word`, and
  native-first-program-design §10.2 still gives the old page address.

### 2.7 Producers and tests

- **Near-duplicates.** The producers repeat each other: `read_map.rs`
  re-encodes the read head and the write loop instead of reusing
  `state_head`/`write_loop`, because `WriteLoop` couldn't say where its JZ
  lands. `read_fields.rs` carries a copy of `claims`, and `Program`,
  `context` and `generate_loop` are repeated.
- **Four byte-literal spellings.** There are four ways to write a byte
  list.
- **Two typed generators.** They repeat each other line for line; the
  single-output one is the fields one with one un-narrowed piece per port.
- **Text assembly.** Generated text is mostly `format!` into `Module::raw`,
  and imports are de-duplicated by `contains`.
- **Tests.**
  - The three native CLI tests each copy the same helpers.
  - Each elab process test restates the producer's claim instantiation by
    hand, so a library signature change is made in three places.
  - No control mutates a producer's own layout.

## 3. What the findings point at

Most items above are one of four missing pieces:

1. **Relocatable, reusable code pieces with their proofs.** The read head,
   the failure tail and the write loop are each proved once per process,
   because no process can place and use someone else's proved piece at an
   offset. The write loop is halfway there: it takes `at`.
2. **A process driver.** Every process is "read until end of file, do
   something with each chunk, then a tail". The shape is proved per process
   because there is no statement of "what a chunk's body must do" that a
   driver could take as a parameter.
3. **A layout description shared by library and producer.** The four
   library spellings, the sums, and the Rust mirror are one description
   written five times.
4. **Uniform piece contracts.** Generated pieces enter through two
   interfaces (loop certificate, `StructuredArtifact`) and three
   client-specific wrappers with hand-threaded register frames.

Emitting stores (the next program's need), a formatting API and argv are
each easier after these, and each would otherwise add a sixth copy.

## 4. Candidate refactors

Ordered so each is useful alone and makes the next smaller. Line counts are
estimates from reading, not measurements.

### R0. Mechanical cleanup (small, low risk)

- **Merge the duplicates.** `FetchedOrStore` into `LinuxStep`, and
  `syscall_bytes` into `linux_syscall_bytes`. The `linux_runs_*` intros
  take `LinuxSteps` uniformly.
- **A frame law.** Add "a store keeps what is fetched" to the IO model, and
  correct `x86_64_fetched_code`'s header.
- **Name the constants.** Page base, entry and read size by their existing
  functions, and the entry once, not as `let entry = …` in every proof.
- **Remove small lemma copies.** `option_some_inj`, `nth_below` and the
  page lemmas move to `elf64_io`/`list`.
- **Retire the old paths.** `wl_from`/`write_events`/`write_targets` become
  the `_then` forms at their call sites. `ExecuteFetchedBlock`, the
  `Linked*` family and `LinuxFetchedTrace` are retired if nothing live uses
  them (to check).
- **Fix the stale text** (§2.6).

### R1. Relocatable read head and failure tail

Prove, once and at an offset `at`, with its own pieces record and a record
of its displacement facts:

- **The read head:** the read, TEST, JZ and JS. It provides `head_ask`,
  `head_at_end`, `head_chunk` (today's `eof_enter`) and `head_failed`.
- **The failure tail:** retry, JZ back, exit 1. It provides `fail_retry`
  and `fail_exit`, stated as "general registers agree except RAX and RBX",
  from which a client gets its own kept set.

The state process, the map process and the write loop use them instead of
their copies, and the write loop embeds the failure tail. This removes the
triplicated failure path and the inlined read steps (roughly 500 lines), and
it is the first use of the pattern R3 generalises.

### R2. Bundle the parameters

- A `LoopContract` record for the loop-certificate bundle.
- One displacement-facts record per piece (`MapTargets` exists; state has
  none).
- A uniform tail interface `EofTail(at, Inv)`, so the tails can follow any
  process.

Claims drop from 24–54 parameters to around 15. This also removes the
producers' long positional argument lists, which are fragile, repeated
string lists.

### R3. One read-until-EOF driver

`read_until_eof` over `ReadStep<X> { Chunk(bytes, x), Interrupted }`, with
an ending that allows a failure inside the body. It is parameterised by:

- an invariant `Inv(seen, gprs)`, framed against what the head clobbers;
- a **body contract**: from the head's fall-through with the chunk stored
  and `Inv(seen)`, reach the read with `Inv(seen ++ chunk)`, emitting
  `E(chunk, x)`;
- a tail contract at end of file.

`state_from`, `map_from` and `map_end` collapse into it. What stays per
process is the body:

- **wc:** the fold, `state_folds` and `state_chunk_close`;
- **tr:** the byte loop and the chunk's write;
- **next:** `tr -s`/`-d`'s step, store and write.

wc's input bound lives in `Inv`. Estimate: `read_state` about 950 → 400
lines, `read_map` about 1150 → 550, and the next process is a body, not a
1,000-line library.

### R4. One layout description

A labelled piece list in Heather (fixed block, near jump to a label, opaque
piece with its length lemma, sub-layout), with generic `offset(layout,
label)`, residency by label and "this jump lands on that label". It replaces
the `*_at_*` families, the split chains and the sum lemmas. The producer
emits the same description from one table (or evaluates the library's
outside the kernel check) instead of mirroring offsets. The producer's
layout also gets a mutation control.

The open-parts discipline must hold: lengths stay lemma-supplied atoms, and
closed offsets are only ever sums of those atoms.

### R5. Uniform piece contracts and one typed generator

- **One contract.** A generated straight-line piece enters through one
  contract: code, input placement, output placement, and a kept register
  set. A generic lemma replaces the hand-threaded `registers_preserved`
  chains and the per-client keeps records.
- **One generator.** The two typed generators merge; the single-output one
  becomes one narrowed piece per port.
- **In-place results.** `structured-lowering-in-place-results` then removes
  the copy-home glue the loop generator adds per field.

### R6. The author's surface

- **Programs as a checked bundle.** A program supplies a library record, e.g.
  `FoldProgram<S> { step, spec, advances, folds, computes }`, instantiated
  once and type-checked before generating. Any error then points at the
  author's source.
- **A library type for record advance,** replacing the positional
  conjunction.
- **Drop `--needle`** (taken from the bundle) and the `bounded_readonly`
  wrapper (the CLI takes the step).
- **The profile from the source's types.** `BitVec(8) → BitVec(8)` is a
  map, a fold bundle is a fold, and so on, rather than one flag per program.
- **One producer skeleton** (bundle, pieces, claim template); `image_facts`,
  `claims`, `_written` and the literal helpers are shared.
- **Shared test support.** The native CLI tests share their helpers, and
  each process test checks its instantiation against the producer's output
  rather than restating it.

### R7. Output

- **One stored-bytes kit.** `StoredList` generalised, with byte and word
  stores, replacing the three kits.
- **One emit-then-write tail.** Pieces store through a cursor, then the
  write loop sends `[base, cursor)`. The count tail and the fields tail
  become instances, and tr's per-chunk write is the same step.
- **One formatting spec.** `field(n) = pad_left(7, ' ', decimal(n))`,
  proved once. The restoring kit is shared over the shift.
- **Variable-width `%d` waits.** It needs byte-granular emitting stores, so
  it follows emitting stores and is not part of this refactor
  (`native-proven-formatting-api`).

### Not proposed now

A single effectful code tree (`ProcCode`: stores, syscalls, labelled edges,
Hoare rules over `LinuxSteps`) proved once would absorb R1, R3 and R4 in
one abstraction. It is the principled end state, but it would re-found every
process at once, against the kernel's depth and `let` limits. R1 → R3 → R4
reaches most of its value in steps that each land green, and leaves the door
open: the body contract of R3 is the Hoare triple such a tree would have.

## 5. How emitting stores fits

With R1–R3, `tr -s`/`-d` is a body for the driver: load, a generated step
that updates the state in place and sets an emit flag and byte, a store at an
output cursor advanced by the flag, then the chunk's write through R7's tail.
The generator keeps producing pure pieces (the per-byte step, composed as the
loop generator already composes fields and copies), and the store stays in
proved-once library code. That is the "library loop, generated step" route
put to the user on 2026-09-30, and it becomes much smaller after R3 than
before.

## 6. Proposed order and decisions to take

Proposed: **R0, R1, R2, R3**, then R4 before a new program's layout is
written, with R5–R7 interleaved as the next programs need them. The
existing wc, wc -l and tr builds migrate at each step, and the old copies
are deleted, not kept beside the new ones.

Decisions for the user:

1. The order above, or another. R6 (the author's surface) could come
   earlier, since it's the most visible roughness, but it is cheaper after
   R2.
2. Whether R4's layout description lives in Heather with the producer
   consuming it, or in one Rust table the library's facts are generated
   from.
3. Whether retiring the older execution paths (R0) is in scope, or waits
   for the `x86-64-machine-model` round.

## 7. Risks

- **Proof cost.** Generic lemmas over open code have cost more than
  specialised ones before (the `let` trap in `map_byte`, the
  `field-prints-gate-after-lowering-round` growth). R3's driver takes a
  body contract, so results must pass through records and `have`, as
  `map_fetched` does. R4's generic `offset` unfolding in every type is
  the least known; each of R3 and R4 should start with a probe on one
  process before migrating the others.
- **Tests near the CPU rail** (the map and fields process tests). A
  refactor that changes emitted terms runs them cold, so each step's
  suite should be watched against the rail, not assumed.
- **Register pressure.** Only the conventions that aren't forced by the
  15-register budget can become parameters.

## 8. As landed

### R0 (2026-09-30)

- **One SYSCALL encoding.** `syscall_bytes()` now lives in `x86_64_block`,
  beside the blocks it sits between. The copies in `x86_64_step_forms` and
  `linux_x86_64_entry` (`linux_syscall_bytes`) are gone, and every use was
  renamed.
- **`FetchedOrStore` and `LinuxStep` stay two definitions.** Neither module
  imports the other: `x86_64_step_forms` is below the Linux trace, and
  merging them would reorder the determinism test's fixtures. `LinuxStep`
  now says it is `FetchedOrStore` at the profile's accesses, which the
  determinism proof relies on by conversion.
- **Stale header corrected.** `x86_64_fetched_code`'s header now says a
  fetched step never writes, and that a profile keeps residency across its
  stores by stating it for every value of the data it never fetches from.
- **The write loop's duplicate targets are retired.** `WriteTargets`,
  `exit_targets` and `WlFrom` are gone. `write_targets` returns
  `WriteLoopTargets(at, wl_at_exit(at), pj)`, and `wl_from` (the instance
  that exits 0) takes it. `write_events` stays, since the claims state their
  traces with it.
- **Small lemmas.**
  - `option_some_inj` was a copy of `Option::some_inj` and is removed.
  - `nth_below` is not a copy: it is the converse of `nth_some_below`.
  - The page-store lemmas differ in shape and wait for R7.
- **Named constants.** `io_entry()` names the entry in every process module
  and in `io_initial`. The page base is `BitVec::ofNat(io_page_base())` in the
  read and map processes' instruction blocks and store addresses. The
  formatter tails (`elf64_count_print`, `elf64_read_fields`,
  `elf64_print_pieces`, `decimal_line`) keep the literal where `omega` or a
  closed evaluation reads it: omega takes a named constant as an opaque
  atom. R7 reworks those proofs anyway. `4096` beside `read_capacity()` is
  left as it is.
- **Older execution paths are not retired.** Both are live:
  - `ExecuteFetchedBlock`/`LinuxFetchedTrace` serve the exit-only arithmetic
    profile (`crates/cli/src/native/elf.rs`).
  - The `Linked*` block family serves the older FunctionIR lowering.

  That is the `x86-64-machine-model` round's question.
- **Stale text fixed.** `issues/native-proven-formatting-api.md`,
  native-wc-design §5 and native-first-program-design's status note.

### R1 (2026-09-30)

`elf64_read_pieces` holds two relocatable pieces, each with its code, its
length lemma, offsets from its start, a residency record proved once, and
one lemma per path through it:

- **The failure tail at `af`** (`fail_tail_code`, `FailTail`, `fail_tail`):
  - `fail_retry`, where EINTR goes back to a target given as a premise;
  - `fail_exit`, where any other errno exits 1.
- **The read head at `ar`** (`read_head_code`, `ReadHead`, `read_head`):
  - `head_read` and `head_read_failed` take the run from the head's start
    through the SYSCALL to a continuation, at the state Linux returns to;
  - `head_enter` handles a chunk, falling through past the JS;
  - `head_at_end` handles the empty read, where JZ goes to a target;
  - `head_failed` is the JS to a failure tail;
  - `read_retries` and `read_fails` compose the head with the tail.
- **One-step helpers.** `block_ran` and `near_ran` step a block or a near
  jump at an offset.

Every lemma names the state it reaches (`head_asked`, `head_going`,
`fail_back`, …) instead of hiding it behind an existential. A client's
register facts therefore still hold by conversion. For example, the state
process's `StateKept` across a retried read is `refl`, where it used to be
a conjunct threaded through a result type.

The processes use them:

- **State process (wc, wc -l).** `state_code` places `read_head_code` and
  `fail_tail_code`, and `StatePieces` holds a `ReadHead` and a `FailTail`.
  `state_failed`, `state_retry`, `state_fail_exit` and their result types
  are gone. `state_from`'s four arms are each a call to a head lemma
  around what is specific to the process.
- **Map process (tr).** The same: `map_ask`, `map_failed`, `map_retry`,
  `map_fail_exit` and `MapFailedAt` are gone, and `map_end` is `head_read`,
  `head_at_end` and `wl_exit`.
- **Write loop.** Its failure path is the failure tail
  (`WriteLoopResident.fail`). `wl_failed` is now TEST and JS only, and
  `wl_retry`, `wl_fail_exit`, `WriteFailedAt` and `WriteKept` are gone.

The names the producers and claims use stay: `map_at_retry`, `wl_at_wjz`,
the skip and span functions, `state_code_len` and `map_code_len`. Where an
offset is a head's or a tail's, it is now defined through theirs (for
example `state_at_setup() = rh_at_end(state_at_read())`). Each definition
unfolds to the same sum as before, so the jump-sum lemmas did not change.
Neither did the bytes or anything in `crates/cli`, apart from import lists
for `syscall_bytes`.

**Size.** The three processes lost 559 lines (state 949 → 693, map
1157 → 928, write loop 566 → 492) and the shared pieces gained 313, less
than §4's estimate. The gain is mostly that there is now one proof of the
failure path, the read request and the end-of-file test instead of two or
three. A fourth process that reads until end of file writes none of them.

**Tests.** Four library mutation controls followed the text they mutate:
`buffer_outside_page`, `setup_base`, `init_left_out` and `write_past_page`.
