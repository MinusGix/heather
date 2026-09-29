# `wc`: a program the `wc -l` template can't express — design

Status: **draft for discussion, 2026-09-28.** Owner: `issues/native-wc.md`.
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

### 4.2 Loop library

`LoopHead`'s `carry_placed: rep(read_gpr(p.carry, …), carry)` becomes a
placement over the whole register file, `rep: Gprs → C → Type`. A one-register
carry is one instance of it. For a record carry, `rep` places each field in
its own register (`LoopWord` for `Nat` fields, `loop_bit` for `Bool` fields).
The fits invariant becomes per-`Nat`-field, with an advance premise per
field: the generalisation of `LoopAdvancesByAtMostOne`.

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

- `WcState { lines: Nat, words: Nat, bytes: Nat, inside: Bool }`, starting
  at zeros and `False`.
- `wc_body`: on whitespace, `inside := False`, and `lines += 1` at a newline;
  otherwise `words += 1` when not `inside`, then `inside := True`; always
  `bytes += 1`. It is cursor-free and never breaks.
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

## 8. Decisions for the user

1. **Output format.** Recommended: GNU's pipe format `"%7d %7d %7d\n"`,
   counts below 10^7. It matches the system `wc` byte for byte on a pipe,
   and one word per field is a gift to the formatter. Alternative: POSIX's
   minimal `"%d %d %d\n"`. That is harder: variable-width fields make the
   stores unaligned.
2. **If the registers don't fit** (V3): update the state in place (relief
   4, a general generator capability, the bigger round), or let the process
   count the bytes itself (the sum of the reads' returns; a process-level
   accumulator every program gets, but a special case in the contract).
   Recommended: decide after V3; lean towards relief 4 if it is needed,
   since the library should rank features rather than route around them.
3. **Order.** Recommended: slice A first and landed on its own (it migrates
   `wc -l` and retires `--adds`), then B with its probe, then C and D.
   C doesn't depend on B and could go in parallel.
