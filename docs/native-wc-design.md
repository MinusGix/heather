# `wc`: a program the `wc -l` template can't express — design

Status: **decisions taken 2026-09-28 (§8); slice A landed 2026-09-28 (§3.1); slice B landed 2026-09-29 (§4.5–4.8); slice C landed 2026-09-29 (§5.1–5.2); slice D landed 2026-09-29 (§6.1); `wc -l` moved onto the state process 2026-09-29 (§9).** Owner: `issues/native-wc.md`.
Builds on `docs/native-read-until-eof-design.md` (the read loop and its
additive contract), `docs/native-syscall-failures-design.md` (failure paths),
`docs/fetched-step-determinism-design.md` (claims universal over runs) and
`docs/function-ir-readonly-loops.md` (the loop contract and its generator).

## 1. Why this program

`wc -l` is one process shape (`--read-loop`/`--print`) with a client loop body
and an additivity theorem (`--adds`). Plain `wc`, with no flags, prints lines,
words and bytes, and breaks that shape in three places at once:

1. **State crosses chunk boundaries.** A word can straddle two reads, so the
   word count doesn't add over concatenation: `words(a ++ b)` isn't
   `words(a) + words(b)`. `--adds` can't be stated, let alone proved.
2. **The state has several fields**: three counters and an in-word flag. The
   loop contract's carry is polymorphic, but its reflector and native
   generator take one `Nat` or `Bool` in one register.
3. **The output is a line of three fields**, not one decimal line.

The success test for the round: `wc -l` becomes an instance of what `wc`
needs, and `--adds` goes away. A second new flag would mean the round
generalised nothing.

## 2. The target

For any history of reads (as today: non-empty chunks with EINTRs, ending at
the empty read or a failed read) and writes, the built file's runs are
exactly (via `_runs_every`) the ones that read the chunks and write

```text
wc_line(lines(input), words(input), input.len())
```

to stdout, then exit 0, or exit 1 at a failure. `wc_line(l, w, c)` is GNU
`wc`'s output on a pipe: `"%7d %7d %7d\n"` (checked against coreutils 9.11:
fields are right-aligned in seven columns, one space between, widening past
seven digits). The claim covers counts below 10^7, so every field is exactly
seven characters. That makes the line 24 bytes, three 8-byte words: each
field's seven characters plus its separator (space, space, newline).

Words are POSIX's in the C locale: maximal runs of bytes other than
`\t \n \v \f \r` and space. GNU also treats byte 0xA0 as a separator unless
`POSIXLY_CORRECT` is set. The tests compare against
`LC_ALL=C POSIXLY_CORRECT=1 wc` on a pipe (on a redirected regular file, GNU
sizes the columns from the file instead).

The specifications are stated the way a reader would check them, not as
folds. `words` counts the non-empty pieces of the input split at whitespace.
Proving that the loop's fold computes them is the program's own proof work,
and dogfoods the tactics.

## 3. Slice A: the fold contract (no generator change)

Replace "the loop adds `spec(bytes)` to any count" plus additivity with
"the loop folds its step over the bytes", proved **once in the library**.

- `step_fold(body, needle, carry, bytes)`: the left fold of the body's
  `Continue` payload over the bytes. It is library-defined, not the
  program's.
- `loop_run_folds` (library, `lib/function_ir_loop.hthr`): for a body that
  never breaks and ignores the cursor, the loop over a buffer holding `bytes`
  from any carry ends at `End(|bytes|, 0, step_fold(…, carry, bytes))`.
  Today every program proves this itself; `wc_l`'s `count_lines_reads` is
  about 40 lines of buffer induction.
- **Cursor-freedom is required.** Each chunk's loop restarts at cursor 0, so
  a body that read its cursor would see chunk-relative positions, and the
  per-chunk folds would not compose. `CursorFree(body)` (the body agrees at
  every cursor) is a premise; for a body that never mentions the cursor it
  is `refl`.
- **Chunks compose for free**: `step_fold` over `a ++ b` is `step_fold` over
  `b` from `step_fold` over `a`, which is a list lemma. The process proof's
  chunk induction carries the state, and `eof_input(chunks)` falls out.
- **What a program proves** shrinks to `--folds`:
  `(bytes) → spec(bytes) = finish(step_fold(body, needle, init, bytes))`.
  That's a statement about its own functions, with no buffers and no loop
  semantics. `wc_l` proves it by induction on the list.
- The fits invariant keeps its shape: each `Nat` field advances by at most
  one per byte, so `total + 4096 < 2^64` bounds every intermediate state.

`wc -l` migrates in this slice: `--adds` and `--computes` go, `--folds`
comes in, and `count_lines_reads` disappears into the library lemma. This
slice stands alone and pays for itself whatever happens to the others.

### 3.1 As landed (2026-09-28)

Probes V1 and V2 held as written, with two amendments:

- **Two facts, two flags.** `--folds` names the step's `LoopFolds` theorem
  (always continues, and the same way at every cursor, as one equation:
  `body(needle, cursor, byte, carry) = Continue(loop_fold_step(…))`).
  `--computes` keeps its name but now names `ReadEofComputes(region, needle,
  spec)`: `spec(bytes) = step_fold(region, needle, bytes, 0)`. The existing
  `--advance` theorem is now also a premise of the process theorem, because
  it bounds the intermediate states.
- **The room premise is on the input, not the specification.** A general
  fold needn't grow with the input, so `count ≤ total` no longer bounds the
  running count. Instead the count stays within the bytes consumed
  (`step_fold_advances`), and both claims take
  `eof_input(chunks).len() + 4096 < 2^64`. The print profile gains this
  premise beside `small`. `EofFrom` carries `carry + |rest| ≤ limit`.

Library: `lib/function_ir_loop.hthr` (`loop_fold_step`, `LoopFolds`,
`step_fold`, `step_fold_append`, `step_fold_advances`, `loop_run_folds`) and
`lib/elf64_read_loop.hthr` (`eof_chunk_folds`, the fold invariant in
`eof_from`). `wc_l`'s loop facts went from about 70 lines of buffer
induction to about 25 lines about lists (`line_body_folds`,
`count_lines_fold`). The test `read_loop_needs_its_folds` refuses a build
without `--folds`, and one with another theorem in its place, where the fact
is used.

## 4. Slice B: a state of several fields

### 4.1 Reflector

The structured reflector admits scalar parameters (`Bool`, `BitVec(w ≤ 64)`,
`Nat` as a word) and scalar or two-constructor scalar-choice results
(`crates/elab/src/function_ir_source/structured.rs`). The backend already
places several results with one certificate each
(`lower_structured_results`). The additions:

- **Record parameters**: one port per field, in declaration order. A field
  projection is a port reference.
- **Record results**, and **choice results whose payload is a record**
  (`LoopStep<WcState>`): one output port per field plus the discriminator.
- Nested records and records in any other position stay out of scope.

**As landed (2026-09-28).** A record parameter's fields are ports in
declaration order (`ReflectedStructuredFunction::leaves` maps each port to
its parameter and field). `fst@(snd@ⁱ⁺¹(x))` over a record-bound variable
reads field `i`'s port, and a leaf may return the parameter itself (Σ-η
closes it against the constructor the expansion writes). A record result,
or a choice whose payload is a record, has one output port per field, then
the discriminator. Publication observes field `i` as `payload.fᵢ` in either
constructor. Record fields are `Nat` (always carried), `Bool` or
`BitVec(w)`, read from the declaration's field types. The test is
`record_state_step_publication_checks`: `wc`'s step with its certificate,
and two mutated sources that the same certificate refuses.

### 4.5 Near conditionals (found by B1's test, 2026-09-28)

`wc`'s step is past rel8's reach: 188 bytes of arms. A comparison costs 16
bytes and each constant 10, and a helper's test inside an arm counts
towards that arm. Short jumps would decline any realistic step, so
structured code gained `CodeBranchNear` (TEST, `JZ rel32` over the true arm,
`JMP rel32` over the false one). The lowering picks it when either distance
is past rel8. Library: its bytes, execution, layout and decoding
(`structured_block.hthr`), the near twins of the branch lemmas, the fetched
bridge (`fetched_code.hthr`) and memory purity (`access_memory.hthr`); the
certificate generator emits either form from one parameterised block. Tighter
instruction selection (a `mov` for a passthrough, `xor` for zero) would
shrink code, but it isn't needed for correctness and isn't done.

### 4.2 Loop library

`LoopHead`'s `carry_placed: rep(read_gpr(p.carry, …), carry)` becomes a
placement over the whole register file, `rep: Gprs → C → Type`. A one-register
carry is one instance of it. For a record carry, `rep` places each field in
its own register (`LoopWord` for `Nat` fields, `loop_bit` for `Bool` fields).
The fits invariant becomes per-`Nat`-field, with an advance premise per
field: the generalisation of `LoopAdvancesByAtMostOne`.

**As landed (2026-09-28).** `rep: Gprs → C → Type`, `carry_placed:
rep(state.gprs, carry)`. The transport lemma takes the placement at the
after state (`carry_kept: rep(after.gprs, carry)`) and the advance lemma the
next one. A one-register carry is `loop_in(register, loop_nat_rep)`, which
unfolds to the old statement, so existing proofs convert unchanged; only the
spelling of `rep` at each use changed. The loop refusal test's carry
mutation moved from the placement record to `loop_in`'s register.

### 4.3 Registers: the risk that needs a probe

Today's placement uses all 15 usable registers. The step body gets seven:
two outputs (payload, discriminator) and five temporaries. A four-field
state wants four carry registers and five outputs, about six more than
today. Candidate relief, in order of preference:

1. **Advance cursor and budget in place** (`next_cursor` and `next_budget`
   exist so a `Break` sees the pre-step values; they can be recomputed on
   that path instead). Frees 2.
2. **`flag` and `step` share a register.** The guard's flag is dead once its
   jump is taken. Frees 1.
3. **No needle register when the body ignores the needle.** The reflector
   already leaves unused `Nat` parameters without a port; extend that to the
   needle. Frees 1.
4. **Update the state in place**: the body writes the next state into the
   carry registers. This removes the payload registers entirely, but it is a
   parallel-copy problem (`issues/function-ir-x86-join-placement.md`) and
   the largest change here.

Probe V3 (§7) counts what `wc`'s body actually needs under 1–3. If 1–3 are
not enough, the choice between 4 and moving the byte counter out of the
state goes back to the user; see §8, question 2.

### 4.4 V3's answer (2026-09-28)

1–3 are not enough for four fields. The typed generator protects every
input: a result's register must be a temporary, and temporaries may not
overlap inputs (`lower_structured_results`: `InputOverlapsTemporary`,
`OutputRegisterUnavailable`). A comparison bit also needs a low-byte
register (RAX, RCX, RDX or RBX). During the step, base, length, needle,
cursor, budget, byte and four state fields are protected: that's 10 of 15.
The step's five outputs take the other five, leaving no scratch.

**Decision (Claude, delegated by the user): the process counts the bytes.**
The read loop already knows each chunk's length (the read's return in RAX),
so the profile keeps a byte total across reads, as real `wc`
implementations do, and gives it to the tail beside the state. The
specification is unchanged: the claim still states `input.len()`, now proved
from the running total instead of a per-byte field. The state drops to
`lines`, `words` and `inside`. Then 9 registers are protected and the step
has 6: 4 outputs and 2 scratch. That fits the current generator with relief
2 only.

Updating the state in place (relief 4) remains the general capability for a
state that doesn't fit. It is filed as
`issues/native-loop-state-in-place.md`, with V3's arithmetic, and not built
here.

**Correction (later the same day).** Counted exactly, three fields fill the
file too: 5 for loop control, 3 for the state, 1 shared by the byte and the
load address, the flag (it must survive the step, since the exit reads it to
tell a Break), the step's discriminator, 3 payload registers and 1 low-byte
scratch make 15 of 15, with the next cursor and budget already computed in
the freed payload registers. The process's byte total has no register. So
relief 4 is built after all (§4.6): the fields are updated one at a time, in
dependency order, each through a certificate for that field alone, into one
scratch register and then home. That frees two payload registers, and the
byte total goes back into the state (`bytes`) or to the process, whichever
is simpler once the loop fits.

### 4.6 Fields one at a time (relief 4, 2026-09-28)

`narrow_structured_region` (function_ir_cert) cuts a region down to some of
its outputs. Each dataflow keeps the cone of what is wanted, a producer or
branch nobody reads is dropped, and every interface narrows to what the kept
computation reads, plus what a continuation reads past it, in the original
order (validation wants a conditional's arms to list exactly its
arguments). Branches are kept, so a field reads what its branches test:
`wc`'s line count reads `inside`, because its non-space arm tests it.
`generate_elaborated_typed_fields_x86` publishes several outputs of one
source, each alone. The reflection, the source expansion and the
observation of the whole result are shared; each piece gets the narrowed
region, lowered and certified, and a typed artifact whose premises name only
the inputs it reads. The loop then orders the fields so that no field reads
a register an earlier field was written back to (a field reading itself is
harmless), computes each into one scratch register and copies it home, and
computes the discriminator last so the pieces can borrow its register.
`wc`'s step certifies this way with four temporaries: one result register
and three scratch.

### 4.7 The record loop (B3, 2026-09-28)

`generate_elaborated_record_loop_x86` (`crates/elab/src/function_ir_source/loop_record.rs`)
compiles a `bounded_readonly` over a record carry. (Since 2026-09-30 it is the
only loop generator, `generate_elaborated_loop_x86`, with a Nat or Bool carry
as a one-field state: docs/native-loop-generator-fold-design.md.) It keeps the Nat/Bool
loop's shape (the same guard, library induction and final theorem) with
the iteration as a list of typed pieces:

- the address into `byte`, then `movzx byte, [byte]` (the load reuses its
  address register);
- each field, alone, into scratch, then copied home, in write order;
- the discriminator;
- the next cursor and budget into freed scratch, then copied home.

(Since 2026-09-30, docs/native-architecture-review.md R5: each field, and
the cursor and the budget, are computed straight into their own registers,
whose old values are dead once read; the copies are gone.)

The state's placement (`{prefix}_rep`) is a conjunction per field: a Nat
field as its word, a Bool field as its placed bit. The invariant
(`{prefix}_fits`) says every Nat field fits a word with the budget still to
run. `--advance` is the right-nested conjunction "each Nat field grows by at
most one", in declaration order.

Three findings came out of building it:

- **Collapse.** Narrowing now collapses a branch whose narrowed arms compute
  alike (alpha-equal up to their own nodes' names). A folding step's
  discriminator then reads nothing (it's the constant `Continue`) and can go
  last, so the field pieces borrow its register. `lines` stops reading
  `inside`, and the loop shrank from 1,667 bytes to 890. The source side
  follows: the observation gives each port's collapsed spelling with a proof
  (one Bool case per collapsed branch, the other arm by conversion), and a
  piece's artifact goes through it. A discriminator that does read fields
  goes first instead.
- **Depth, not fuel.** A loop of a thousand bytes or more has a byte list the
  kernel cannot compare element by element against an appended tree: the
  comparison recurses once per byte, past the 1,024-frame depth budget,
  which reports as OutOfFuel. Access fragments now carry their bytes as
  their children's literals appended, with a proof (`lit`, `lit_proof`).
  `{prefix}_bytes()` is that tree, the encoding lemma is the composed
  proof, and both loop edges read the children's lengths through it. The CLI
  producer compares the loop's bytes with its own flat literal and will need
  the same treatment for `wc`.
- **Registers.** `wc`'s placement: base RDI, length RBP, needle RCX,
  cursor RSI, budget R12, flag R10, discriminator RBX (borrowed as scratch),
  byte R9, fields R13 R14 R15 R8, scratch R11 RAX RDX. Every register the
  loop keeps across reads (the fields) survives SYSCALL and the read's
  setup.

Test: `record_state_loop_certificate_checks` (function_ir_loop_trace).

### 4.8 The reading process (B4)

`lib/elf64_read_state.hthr`, beside `elf64_read_loop`, whose blocks, read
trace (`ReadStep`, `eof_events`, `eof_input`, `EofChunks`, `EofEnding`) and
jump record it reuses. It is polymorphic in the state type `C`, its placement
`rep: Gprs → C → Type` and its invariant `fits`, and differs from the Nat
process in three places:

- **No copy, no save.** The state registers are R13, R14, R15 and R8, which
  nothing between reads writes (the read's setup, SYSCALL's RCX and R11,
  the retry's RBX). The chunk's setup is the Nat setup without `R11 ← R13`,
  and the save block is gone: the loop is followed directly by the jump
  back. Init zeroes all four.
- **The state is a fold of what was read.** The outer induction is indexed
  by the bytes read so far, `seen`: at the read, `rep(gprs, step_fold(seen,
  init))`. After a chunk the placement moves along `step_fold_append`.
- **The program supplies three facts about its placement**, each small:
  `rep` reads only the four state registers (`StateFramed`); init's zeros
  place the initial state (`StateInitialised`); and folding any `seen` from
  `init` fits the next chunk's budget while `seen` and the chunk together
  stay below 2^64 (`StateRoom`). The record generator emits the first and
  the last (`{prefix}_rep_moves`, `{prefix}_room`, the latter from the
  advance theorem through a library lemma bounding one measure of the fold,
  `step_fold_measure`); the second is a conversion for zero initial fields.

The tail is a parameter as before (`StateTail` gets the final state in its
registers). The library's own profile is `exit(R13)` given a `status: C →
Nat` that the first register holds; the claim is stated over the final
state `step_fold(eof_input(chunks), init)`, with no specification — relating
it to `lines`/`words`/`len` is the program's work (slice D).

Test: `crates/elab/tests/read_state_process.rs` checks the library, refuses
mutations of the process shape, and instantiates the claim with the record
generator's certificate for `wc`'s loop at an abstract file.

**As landed (2026-09-29).** As above. The fits helper is
`loop_fits_from` (function_ir_loop_trace); a chunk's run is
`ReadStateFolded`. The failure path's theorems are restated over this
layout (`state_failed`, `state_retry`, `state_fail_exit`), since
elf64_read_loop's take its own pieces record; they differ only in offsets
and in keeping `StateKept` where the Nat ones keep R13. The refusals: a
setup writing a state register, a moved base, both jump spans, init left
out of the code, the exit reading another register than the status premise;
and, at `wc`, an init zeroing R9 for R8 (refused at `wc_initialised`).
`wc -l` could become a one-field instance of this process, retiring the
copy and save; nothing needs that yet.

## 5. Slice C: the three-field line

- `field_word(n, separator)` (as designed; §5.1 amends it to two words,
  `field_low` and `field_high`), for `n < 10^7`: the seven right-aligned
  characters of `n`, leading zeros as spaces, then the separator byte, as one
  word. It uses the same restoring-division scheme as `line_word`, over
  seven digits: 28 `place` steps against `line_word`'s 16, and nothing
  worse than linear. It is certified once per profile (since
  `issues/read-print-formatter-reproved-per-program.md` it is replayed after
  the first build).
- Three stores at page offsets 0, 8 and 16, then one write of 24 bytes
  through the existing write loop. The short-write, EINTR and failure paths
  are unchanged; only the buffer's contents and length differ.
- The meaning lemma: the 24 bytes are `wc_line(l, w, c)`. `decimal_line`'s
  lemmas are the model.

### 5.1 The formatter (C1, 2026-09-29)

**Amended: a field is two words.** Seven columns and a separator fill the
word, which leaves no room for the value the restoring chain works on, so
`lib/field_line.hthr` computes each field as two words with the value above
bit 32: `field_low(n)` (columns for 10^6 down to 10^3; the rest of the
count stays above them) and `field_high(n, tail)` (the top four digits taken
away at weight zero, then the columns for 100, 10 and 1, then `tail`'s byte,
the separator). Stored at +0 and +4, the second overwrites what is left of
the first, and each later field's low word overwrites the previous high
word's zero tail. A column left of the count's first digit is a space: a
`mark` step adds `'0' − ' '` to its byte when the count reaches its place
value. The spec is stated per column (`column(n, place)`: the digit there,
or a space left of the first digit; `field`, `three_fields_line`). The kit
is `decimal_line`'s at 2^32 (`field_*`). The generator now imports the
modules of the helpers a source calls (`owners`), which `decimal_line`'s own
formatter never needed.

**V4's answer: the words are too big to place.** Both certify (tests
`field_low_certifies`, `field_high_certifies`, `slow_acceptance_field_line_refusals`), but
`field_low` lowers to 1,911 bytes and `field_high` to 2,792; three inline
copies are 14 KB, and the program must fit one page (the call profile's RW
page is at 0x401000), with `wc`'s loop already 890 bytes. The size is the
lowering's, not the algorithm's: a mark is 68 bytes where about 20 would do
(a comparison's bit is materialised and tested instead of branching on the
flags, a copy is `movabs 0; or`, a zero is a 10-byte immediate), and
`raise32` is 288 bytes of `mov`/`add`/`mov`. Certification costs about
36 s and 65 s. Placement: §8, question 4.

### 5.2 The tail (C2, 2026-09-29)

`lib/elf64_read_fields.hthr` is the tail over `elf64_read_state` (§4.8): for
each count, in R13, R14 and R15, copy it to R11, run `field_low` into RAX,
set R9 to the page at `8k` and R10 to the separator's tail, store, run
`field_high`, set R9 four bytes on, store; then R9 and R10 to the 24-byte
line and the write loop. `read_fields_runs` states the claim over the final
state `step_fold(eof_input(chunks), init)` and three projections the program
names (`first`, `second`, `third`, with `counts`: its placement puts them in
R13–R15); relating them to `lines`/`words`/`len` is slice D's.

- **The write loop at an offset.** `lib/elf64_write_loop.hthr` is
  `elf64_read_print`'s loop restated at an offset `at` (`wl_from`,
  `WriteLoopResident`, `write_targets`), derived mechanically from its text;
  the blocks, trace and arithmetic are imported. `wc -l` could move to it
  later.
- **What the page holds.** `StoredList(page, offset, bytes)` (curried over the
  offset, which varies in the recursion) with four lemmas: a store's first
  four bytes land (`stored_four`), earlier runs survive stores that start past
  them (`stored_kept`, `field_kept`), runs join (`stored_join`), and a run
  from the page's start is what a write from there sends (`stored_sends`).
  Each field leaves `field(n) ++ [sep]` at `8k`; the three runs joined are
  `three_fields_line(a, b, c)` by computation (`line_stored`).
- **One field** (`field_prints`) is generic in its count register, offset and
  separator, and is used three times; it composes fetched runs and the two
  store steps as Linux steps and keeps R13–R15 (`CountsKept`).
- **The formatter's certificates** are parameters (`FieldsFormat`, over
  field_line's `FieldLowCert`/`FieldHighCert`: the generated artifacts at
  R11/R10 → RAX, each keeping R11 and R13–R15). `field_low_certifies` and
  `field_high_certifies` check the generated ones against them, each in a
  process of its own: together, with the libraries a `FieldsFormat` check
  would load, they passed the 300 CPU-s rail.

Tests: `read_fields_process` (library; `wc`'s loop composed into
`read_fields_runs` with the certificates abstract; refusals of a tail that
stores another register, formats one count twice, overlaps two fields, ends
the line with a space, writes 23 bytes or from the page's second byte,
stores the high word one byte early, or puts the tail in R12).

## 6. Slice D: the program

`examples/x86-native/wc.hthr`:

- `WcState { lines, words, bytes: Nat, inside: Bool }`, starting at zeros
  and `False`. The bytes stay a field (§4.8 keeps the whole state in
  place); the three counts come first, in the order printed.
- `wc_body`: on whitespace, `inside := False`, and `lines += 1` at a newline;
  otherwise `words += 1` when not `inside`, then `inside := True`; `bytes += 1`
  always. It is cursor-free and never breaks.
- The specs, as a reader checks them: `wc_lines` (the newlines, a `filter`),
  `wc_words` (the pieces of `wc_split`, the input cut at every whitespace
  byte, that aren't empty) and `wc_bytes` (the length). `count_wc_input`
  proves they are the first three fields of the fold from the zero state.

### 6.1 As landed (2026-09-29)

**V5.** The fold proof is structural over the input with the state general:
`wc_step_is` rewrites the loop's step to `wc_next(space, newline, s)`, a
function of the two classifications, so each case lemma matches on plain
`Bool`s. Lines need `newline_is_space` (by `bitvec_omega`'s bridges and
`omega`). Words carry the invariant
`fold.words + inside_words(s.inside, pieces) = s.words + words(pieces)`: a
word the state is already inside continues in the first piece and was
counted when it began. `omega` can't use a record field of a local as an
atom (`issues/omega-record-projection-atoms.md`), so the arithmetic goes through
five helper lemmas over plain numbers. The file checks in seconds.

**The build: `--read-loop --fields`**, with `--spec` given three times in
the order printed (`crates/cli/src/native/read_fields.rs`). The producer:

- reflects the loop's record (three `Nat` counts and at most one more field,
  in R13, R14, R15 and R8) and generates the record loop at the process's
  registers;
- generates `field_low` and `field_high` at the tail's registers as two
  fixed-name modules, checked before the program's, like `--print`'s;
- states what every record gives the process: `_framed` (from `_rep_moves`),
  `_init` and `_initialised`, `_counts` (the three words in R13–R15);
- lays out `read_fields_code`. The loop's bytes stay its published literal
  tree: the code is spelled around `_bytes()`, so no flat literal is
  compared against the tree (the depth trap) and the jump facts are `refl`;
- measures the code without evaluating it. The read profile read the file's
  size off the spelled code, which walks every byte; with three copies of the
  formatter that ran past the fuel, and a length chain generated over the
  closed pieces was no better (unification whnf'd the closed sums, which
  evaluates the formatter's encoding). The library proves the length once
  over open parts (`read_fields_code_len`, from `len_append`), and the
  certificate instantiates it with the formatter's `_byte_length` lemmas
  (`_code_len`); `image_facts` takes that proof. `_fits` was renamed
  `_code_fits`: the record loop's invariant already has the name.
  (Attributed afterwards: the spelled length needs more than the default
  fuel, and the twenty CPU-minutes were the elaborator's whnf oracle
  re-asking the substitution reducer after the value machine ran out; it
  now refuses in about a second. Closed in
  `issues/closed-length-facts-evaluate-encodings.md`.);
- concludes with `read_fields_spec_runs`, the library claim restated over the
  three specs through the program's `computes`.

Replaying the certificate's image decodes the loop's byte tree recursively;
in the test profile that overflowed the 8 MiB main thread, so `build-x86` now
runs on a thread with its own large stack
(`issues/module-image-decode-depth-vs-stack.md`).

A program may import the bundled proof library by its bundled names
(`bitvec_omega`), which the loader leaves to the builder when no file
answers them (`loader::load_providing`).

Test: `crates/cli/tests/native_wc.rs` (a build naming the specs in another
order is refused; the executable is compared with the counts and the host's
`LC_ALL=C POSIXLY_CORRECT=1 wc` on files, pipes and bursts that split
words; failed reads and writes exit 1).

## 7. Probes, before any design text is final

- **V1** (slice A): `loop_run_folds` checks over the real `loop_run`, and
  `wc_l`'s `--folds` proof is short. Refute if `CursorFree` can't be `refl`
  for a body that ignores its cursor.
- **V2** (slice A): `eof_from` restated with a carried state and no `adds`
  checks at the same cost as today (watch the `let` trap,
  `native-read-until-eof-design.md` §6).
- **V3** (slice B): hand-count and generator-count the registers `wc_body`
  needs with reliefs 1–3; also a two-field body (`words`, `inside`). Report
  before choosing relief 4.
- **V4** (slice C): `field_word`'s certificate size and cold cost against
  `line_word`'s (linear in nodes; about 44 declarations per node today).
- **V5** (slice D): the `words` spec and its fold proof, with bv_omega and
  tactics, before any generator work depends on it.

## 9. `wc -l` on the state process (2026-09-29)

The round's success test (§1) asked for `wc -l` to be an instance of what
`wc` needs. It is now: both run on `elf64_read_state`.

- **The loop is unchanged in kind.** `wc -l`'s Nat-carry loop certificate
  was already a `ReadStateCertificate`: the old `ReadLoopCertificate` is it
  at `rep = loop_in(p.carry, loop_nat_rep)`. The profile's placement swaps
  two registers, the count to R13 and the loop's flag to R11, so the count is
  the state and nothing is copied or saved around the loop.
- **A Nat state's facts** are library lemmas at the end of
  `elf64_read_state` (`count_rep`, `count_framed`, `count_initialised`,
  `count_room` from `LoopAdvancesByAtMostOne`, `count_word`), with the exit
  claim `read_count_runs` over the program's `ReadEofComputes`. (Since
  2026-09-30 the loop generator emits them, as for a record, and the claims
  take them as parameters: docs/native-loop-generator-fold-design.md §3.2.)
- **The printing tail** is `lib/elf64_count_print.hthr`: elf64_read_print's
  base block, formatter and store restated at the tail's offset
  (`count_tail`, `count_formats`, `count_writes`), then elf64_write_loop's
  write loop, the way the fields tail uses it. `read_count_print_runs` is
  the claim.
- **The producer** (`native/read_loop.rs`) lays out the state head and the
  write loop once (`state_head`, `write_loop`) for `--read-loop`, `--print`
  and `--fields`. The loop's bytes stay its published literal tree in all
  three, so the flat `_loop_written` comparison is gone.
- **What went away:** the old process in `elf64_read_loop` (`eof_code`, the
  save block, `eof_from`, `read_loop_runs`, about 850 lines) and the tail
  bound to its layout in `elf64_read_print` (`print_at_*`,
  `ReadPrintResident`, its own copy of the write loop, `read_print_runs`,
  about 800). What remains of both is the read and write profiles' pieces,
  renamed for it the same day: `elf64_read_pieces` and `elf64_print_pieces`.
  Their refusal tests now mutate those pieces and are refused by the library
  that uses them (the state process, the write loop, the count's tail).
- **Cost:** the `wc -l` builds bundle `elf64_read_state` now, and `--print`
  also bundles elf64_write_loop and elf64_count_print.

## 8. Decisions (2026-09-28, with the user)

1. **Output format: GNU's pipe format for now**, `"%7d %7d %7d\n"`, counts
   below 10^7. POSIX's minimal `"%d %d %d\n"` is wanted too, as a basic
   capability. The user's longer direction is a C-style API, proven in
   Heather, for easier conversion of existing programs. Both are filed as
   `issues/native-proven-formatting-api.md`, not in this round.
2. **The registers don't fit** (V3, §4.4). The user delegated the choice:
   the process counts the bytes; updating the state in place is filed for
   later.
3. **Order: slice A first**, landed on its own. Then B with its probe, then C
   and D.
4. **Where the formatter's code goes (2026-09-29, §5.1): lift the one-page
   limit.** The read profile's RW page moves up so a program image can fill
   the file's 64-KiB window, and the formatter goes inline three times. The
   alternatives, a tighter structured lowering and one copy shared by a call
   or a loop, are left for later; the lowering's size is filed with §5.1's
   measurements.
