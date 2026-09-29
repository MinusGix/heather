# `wc`: a program the `wc -l` template can't express — design

Status: **decisions taken 2026-09-28 (§8); slice A landed 2026-09-28 (§3.1); slice B next.** Owner: `issues/native-wc.md`.
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

## 5. Slice C: the three-field line

- `field_word(n, separator)`, for `n < 10^7`: the seven right-aligned
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

## 6. Slice D: the program

`examples/x86-native/wc.hthr`:

- `WcState { lines: Nat, words: Nat, inside: Bool }`, starting at zeros and
  `False` (bytes are the process's total, §4.4).
- `wc_body`: on whitespace, `inside := False`, and `lines += 1` at a newline;
  otherwise `words += 1` when not `inside`, then `inside := True`. It is
  cursor-free and never breaks.
- The specs: `lines`, `words` (split at whitespace, count the non-empty
  pieces), and `len`; `--folds` proves they are the fold's fields.
- The build: `--read-loop --fields` (the name is open), from one source file,
  with no count-specific flags.

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
