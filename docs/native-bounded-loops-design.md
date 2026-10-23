# Native bounded-loop certificates — design

Status: **design agreed 2026-09-24; probes done (§8); slices A0, A, B and C landed (§9)**. Owner:
`issues/native-bounded-loop-certificates.md`, step 3 of
`issues/native-shared-lowering-milestone.md`. Implementation state is in §9.

## 1. What exists, and what this adds

The source/IR contract (`docs/function-ir-readonly-loops.md`,
`lib/native/function_ir/function_ir_loop.hthr`) fixes the meaning: one evaluator `loop_run`, a
five-parameter wrapper reflected with its step function, and
`LoopReadable` defined from the evaluator's own outcome. The 09-20 rounds
also built one *iteration's* physical pieces: typed certificates for pure
source functions at explicit placements (`generate_elaborated_typed_x86`), a
byte load followed by a reflected body (`generate_elaborated_read_x86`),
effectful composition (`AccessCode`: pure, read, sequence, forward branch),
and the word/Nat bridges in `lib/native/function_ir/function_ir_loop_x86.hthr` (bounds test
polarity, address word, cursor advance). The guarded-read test composes one
guard → read → body path, but its composition proof is a hand-written
fixture (`crates/elab/tests/fixtures/guarded_read_consumer.hthr.in`).

This round adds the missing pieces: a backward edge, a loop's exits, an
induction relating machine iterations to `loop_run`, and a generator that
emits the whole certificate, including what the fixture does by hand. The
first client is `first_match` (Bool carry; its body already reflects).
`count_occurrences` needs a Nat carry port and is slice C (§9).

## 2. Machine shape

One loop, one entry, one exit, no outcome tag materialised:

```text
L:  guard            pure: g := cursor <u length ∧ 0 <u budget
    test g, g
    jz   X           forward: guard false → exit
    body             address; movzx byte; step body → (payload, disc→d);
                     cursor + 1, budget − 1 into scratch; copy payload,
                     cursor, budget into their head registers
    test d, d
    jz   L           backward: disc False (Continue) → head
X:                   fallthrough: disc True (Break) → exit
```

The exit state is read by an **observation**, not by tag-writing code:

| path to X | `g` | outcome |
|---|---|---|
| guard false, `length ≤ cursor` | 0 | `End(cursor, budget, carry)` |
| guard false, `cursor < length` (so `budget = 0`) | 0 | `Exhausted(cursor, carry)` |
| Break fallthrough | 1 | `Early(cursor, budget, carry)` — already advanced |

`g` distinguishes Early from the others because the body protects it (it was
1 on entry to this iteration). End against Exhausted is decided by cursor and
length, the order `loop_run` itself uses (end is checked before budget).
`Denied` has no machine path: a denied read has no normal `ByteLoadStep`, and
the premise `LoopReadable` excludes it. That's the existing contract, not a
new assumption. This register convention is the **exit interface** (how a
host reads the result). It is stated in Heather as `LoopObserved`, not as an
OS calling convention.

## 3. Library: the loop in `AccessCode`

Add one constructor rather than a separate top-level loop form, so a loop
composes with `AccessSequence`/`AccessBranch` like everything else (a
prologue, or a loop inside an arm later):

```text
AccessLoop(guard: AccessCode, flag: Gpr, exit_displacement,
           body: AccessCode, continue_flag: Gpr, back_displacement)
```

- **bytes**: `guard ++ TEST flag ++ JZ rel32 exit ++ body ++ TEST cont ++ JZ rel32 back`.
- **layout** (like the existing `AccessLayout` clauses): the exit target is
  `next_rip(start, 6 + |body| + 9)` from the forward JZ, and the back target
  from the backward JZ's start is the loop's own start, stated as
  `(loop_start) → near_branch_target(next_rip(loop_start, |loop| − 6), 6, back) = loop_start`,
  plus both children's layouts. Both edges are near jumps (§8 V1), stated
  with `near_branch_forward` and `near_branch_returns`, and through
  `access_loop_layout(...)` over child codes, never a tuple against a literal tree (the
  `fast-lane-heaviest-declarations` lesson already in `access_code.hthr`).
- **execution**: iterations are counted existentially,
  `ExecuteAccess(AccessLoop(..)) = λ b a => Exists<Nat>(λ n => LoopRuns(ExecuteAccess(access, guard), ExecuteAccess(access, body), …, n, b, a))`.
  `LoopRuns` recurses on `n` over the two relations it is handed.
  `Succ(k)`: the guard runs, `zf = False`, the body runs, `zf(cont) = True`,
  jump back, then `LoopRuns(k)`. `Zero`: a stopping iteration, either the
  guard exits or the body runs and falls through. Passing the child relations
  as arguments keeps `ExecuteAccess` structurally recursive (V3).
- **`access_memory`** gains the loop case by induction on `n`, so memory
  preservation stays a consequence of execution.

As for the rest of `AccessCode`, execution is structural: the recursion, not
RIP, decides what runs next. RIP is honest because layout ties each
displacement to the child lengths; a wrong back displacement fails layout,
not execution. That's the precedent `StructuredLayout` set. The
fetch/decode connection stays an explicit external boundary.

## 4. Library: the induction schema

Parameters: a `LoopPlacement` (registers for base, length, needle, cursor,
budget, carry, `g`, `d`), a carry representation `rep: BitVec(64) → C → Type`
(Bool: `ofBool(·).zero_extend(63)`; Nat: `LoopWord` in slice C), and a
client invariant `Inv: Nat → Nat → C → Type` (`True` for search;
`count + budget < 2^64` for counting).

`LoopHead(p, rep, access, buffer, needle, state, cursor, budget, carry)` is
a record: base/length/cursor/budget registers are `LoopWord`s of their Nats,
the needle is placed, `rep(carry register, carry)`, the memory agrees with
`buffer.read` (the `memory_agrees` shape of `loop_read_address`), and
`cursor ≤ length`. It reads only registers and memory, so it holds
definitionally across the TEST/JZ edges (`loop_edge`), and
`loop_head_transport` moves it across any step that kept the six head
registers and memory. `LoopAddressBound` and the canonical bound are fixed
for the whole loop, so they are premises of the glue, not head fields.

Two **per-iteration obligations**, over open states and values:

- `LoopGuardStep`: from `LoopHead(s, c, b, k)` the guard code executes to
  `m`, with `g` holding `loop_bit(loop_continues(len, c, b))` (not ended,
  and `1 ≤ b`) and `LoopHead` at `m`.
- `LoopBodyStep`: from `LoopHead(s, c, Succ r, k)`, `Inv(c, Succ r, k)`,
  `len.leb(c) = False` and `ReadsByte(c, byte)`, the body executes to `s'`
  with `LoopStepped`: `g` kept, and by the step `body(needle, c, byte, k)`
  either `Continue(next)`: `d = loop_bit(False)`, `LoopHead(s', Succ c, r, next)`
  and `Inv(Succ c, r, next)`; or `Break(result)`: `d = loop_bit(True)` and
  `LoopHead(s', Succ c, r, result)`.

The library theorem `loop_trace`, by induction on the budget and generalising
the state, cursor and carry:

```text
LoopHead(s, c, b, k) → Inv(c, b, k) → LoopReadable(b, region, buffer, needle, c, k)
  → LoopGuardStep → LoopBodyStep
  → Exists(after, ExecuteAccess(access, AccessLoop(…), s, after)
                 ∧ LoopObserved(p, rep, after, loop_run(b, region, buffer, needle, c, k)))
```

Layout is not a premise: as for every `AccessCode`, execution is structural,
and the final artifact carries layout beside it. The outcome equations
(`loop_run_end`, `loop_run_exhausted`, `loop_run_step`, `loop_run_denied`)
unfold `loop_run` one decision at a time through `loop_after_guard`/`_read`/`_step`,
so each rewrites a single scrutinee.

`LoopReadable(Succ r, …)` with `c < len` unfolds to `match read {None =>
False, Some(byte) => …}`. That supplies the byte for `ReadsByte` and the
tail's readability, and is what the 09-20 contract was shaped for. The guard
arithmetic is library lemmas in `function_ir_loop_x86`: `loop_guard_word`
(the machine guard is `loop_continues`), `loop_cursor_increment`,
`loop_budget_decrement` (`word ~ Succ r → word − 1 ~ r`), and
`loop_address_canonical` (`base + length ≤ 2^47` gives the read adapter's
low-canonical premise, through `BitVec::drop_low_zero_of_lt`).

## 5. The guard and the updates are library *source* functions

The guard, address, `cursor + 1` and `budget − 1` are ordinary Heather
functions in `function_ir_loop_x86` (e.g. `loop_guard(cursor, length, budget: BitVec(64)) → Bool`),
reflected and selected through the same `generate_elaborated_typed_x86` as a
client's code. No loop instructions are templated in Rust, and their typed
certificates are generated at whatever placement the loop uses. That's
the review's rule: explicit placements, shared selection.

## 6. What is generated per compilation

1. Typed certificates for `loop_guard`, `loop_address`, the two updates (at
   the chosen placement), and the client step body behind its read (existing
   generators).
2. The published loop: code, bytes, encoding, layout (`AccessFragment`
   extended with `looped(...)` resolving both displacements).
3. **Two glue theorems** instantiating `GuardStep` and `BodyStep` from those
   certificates: straight-line `let` chains of `_after`/`_typed_correct`/
   `_preserves`/`_memory`, the shape the hand fixture's `read_path` already
   has. Generated with structured emission.
4. The final theorem: `loop_trace` applied, then transported through the
   reflector's `source_agreement` to the **named source function**:

```text
first_match_native<M>(access, before, buffer, needle, budget, cursor, found,
    <placement premises>, bounded, inside, memory_agrees, Inv, readable)
  : Exists(after, AccessArtifact(access, loop_code(), loop_bytes(), before, after)
        ∧ LoopObserved(p, rep, after, first_match(buffer, needle, budget, cursor, found))
        ∧ frame(before, after))
```

The generator is `generate_elaborated_loop_x86` in
`crates/elab/src/function_ir_source/loop_native.rs`, with a
`NativeLoopPlacement` naming the eight head registers and the iteration's
scratch (address, byte, payload, next cursor, next budget, plus `extra`
temporaries). (Since 2026-09-30 the placement is the record loop's, head
registers plus one register per state field and three scratch, and a Nat or
Bool carry is a one-field state: docs/native-loop-generator-fold-design.md.) Its emission has two parts: `pieces` (the eight typed
certificates and the reflector's source agreement, elaborated as
`{prefix}_pieces`) and `text` (code, bytes, layout, the two iteration proofs
and the final theorem). A change to the composition rechecks only the second.

Two constraints turned up building it:

- The glue must not reach a register or memory fact through a field of a
  theorem-built record (`X_read_artifact(...).memory_preserved`): theorems are
  opaque, so `.continuation.after` never reduces to the state the next piece
  starts from. The glue uses the body certificate's own `_preserves`/`_memory`
  lemmas with `byte_load_preserves`, and builds the `ByteLoadStep` directly.
  The elaborator accepted the other spelling and the kernel refused it
  unlocated (`issues/elab-accepts-projection-through-opaque-theorem.md`).
- The guard and the step body select SETcc into a byte-addressable register,
  so `Rax`/`Rbx`/`Rdx`-class registers must be among their temporaries. The
  first placement therefore keeps the length in `Rbp`, not `Rdx`.

The export premises are the explicit boundary: register placement,
`LoopAddressBound`, the 2^47 canonical bound, `cursor ≤ length`, memory
agreement, `Inv`, and `LoopReadable`. ABI entry, RET, fetch and host I/O stay
outside and are named in the doc and the theorem comment.

Why the glue is generated rather than a library lemma over artifact families:
the typed certificates' parameter lists vary with arity and placement, so a
family lemma would first need a uniform `TypedStep` record around them. The
induction and outcome case analysis, where the real reasoning lives, are
library code either way. The uniform record is a possible later refactor, not
a prerequisite.

## 7. Tests and controls

- Kernel: `first_match_native` checks over open memory, open buffer, needle,
  budget, cursor and carry.
- Refusals at local boundaries: a wrong back displacement (layout), a wrong
  exit displacement, an unprotected `g` (Early mis-observed), swapped
  cursor/budget updates, a body certificate for another step function (stale
  source), guard polarity flipped, a missing budget decrement, the Denied path
  unreachable without `LoopReadable`.
- Native, the precedent's driver shape: every needle × positions (first, last,
  absent, repeated), empty input, zero budget, budget exhausted exactly at
  end, nonzero start cursor, match on the last budget unit, and a guard page
  after the buffer with the loop stopping at `length`. A test-only asm
  trampoline stores the exit registers to a struct; it is untrusted harness,
  not ABI.

## 8. Verification items — results (2026-09-24)

Probed through the real generators (a throwaway test in the `function_ir`
family) before any library work:

- **V1 byte lengths — near branches required.** At the loop's placements:
  guard 62 bytes, address 6, load + `search_body` 130, each counter update 13,
  each copy 13. The backward edge spans roughly 270 bytes and the exit edge
  roughly 200, so both of the loop's jumps are near (`JZ rel32`, 6 bytes).
  `NearControl` joins `x86_64_block` beside `ShortControl`: bytes, a decoder
  with soundness and completeness, execution, `near_branch_forward`, and
  `near_branch_returns`, which closes the back edge by the 2^64 increment
  period (`BitVec::iterate_increment_period`). The loop always uses near
  forms, so no per-loop short/near choice is needed.
- **V2 in-place results — refused, and not needed.** A typed certificate
  whose result register is one of its own inputs is refused
  (`InputOverlapsTemporary`). A pure `copy(x) = x` from a scratch register into
  the head register is accepted today, because the head register isn't an
  input of the copy. So each update is "compute into scratch, then copy",
  with no lowering change. In-place results remain a lowering improvement
  (smaller code, fewer artifacts): `issues/structured-lowering-in-place-results.md`.
- **V3 recursion — holds.** A toy with the same shape (a code tree whose loop
  case hands `Exec(guard)`/`Exec(body)` to a Nat-recursive `Runs`) passes the
  structural check, and so does a monotonicity induction through it (the
  shape of `access_memory`'s loop case).
- **V4 body placements — hold** with a fresh payload register. The payload
  lands in scratch and is copied into the carry register (V2).
- **V5 canonical bound — missing, cheap.** No `toNat < 2^47 → drop_low(47, 17, w) = 0`
  lemma exists. It is a short induction on the width, added in slice A.

## 9. Slices

- **A0 — near branches** (V1): `NearControl` in `x86_64_block`, landed 28d84281.
- **A — library, landed.** `AccessLoop` in `x86_64_access_code` (bytes,
  layout, `LoopRuns`, the exit/break/continue intro lemmas) and its
  `access_memory` case; `lib/native/function_ir/function_ir_loop_trace.hthr` (`LoopHead`, the two
  obligations, `LoopObserved`, `loop_trace`); the word lemmas and the
  `loop_guard`, `loop_next_cursor`, `loop_next_budget` and `loop_copy` source
  functions in `function_ir_loop_x86`. `crates/elab/tests/function_ir_loop_trace.rs`
  selects those functions through the shared generator and checks their
  certificates, with refusal controls for the word lemmas. The first
  instantiation of `loop_trace` against real certificates is slice B.
- **B — generator + search, landed.** `AccessFragment::looped` (with
  `near_loop_edges`), `generate_elaborated_loop_x86`, and
  `crates/elab/tests/function_ir_loop_trace.rs`.
  `search_loop_certificate_checks` checks the whole `first_match` loop and
  runs the published bytes natively. The run covers every needle, buffers up
  to 48 bytes ending flush against a guard page, every start cursor, eight
  budgets and both carries, each exit compared with a C reference of
  `loop_run`. `slow_acceptance_search_loop_refusals` refuses a shifted back
  edge, a shifted exit edge, a flag, counter or carry placement that
  disagrees with the code, and a step function edited after compilation. The
  library side added `loop_address`, `loop_open_inside`, `loop_bool_rep`,
  `loop_head_advance` and `loop_stepped`.
- **C — Nat carry + counting, landed.** Design in §9a.
  - `StructuredSourceType::NatWord` and the reflector's retry.
  - Nat tracking in the expansion (`track_natural`, with a per-port proof).
  - `bitvec_nat::word_of_nat` and its three lemmas.
  - `loop_fits`, `loop_fits_step`, `loop_nat_placed` and `loop_nat_word`.
  - `LoopAdvancesByAtMostOne` in `function_ir_loop`.
  - The generator's `advance` argument.

  `count_occurrences` compiles through the same generator and placement as
  `first_match`. Its certificate checks, and its bytes run natively against a
  C counting reference. The client added its source and `count_body_advances`
  and nothing machine-specific. The slow lane also refuses the same fact
  proved of another step.

## 9a. Slice C design: a Nat the body consumes

**Representation.** A Nat parameter or result the step body consumes gets a
64-bit port holding `word_of_nat(64, n) = zero.iterate_increment(n)`, the
modular image of `n` (`bitvec_nat`). A Nat the body never reads stays erased,
as `cursor` does. The reflector finds out which by retry: it reflects with
every Nat unported, and when the body consumes one, that parameter gets a
port and reflection runs again.

**Why the modular image.** With it, every equality the typed certificates
already state stays unconditional:

- `Succ(e)` reflects to `Add(e, 1)`, and `word_of_nat(Succ n) = word_of_nat(n).add(1)`
  is one lemma (`word_of_nat_succ`, through `iter_add_eq_add`).
- A passthrough, `bor(0, x)`, is definitional at literal width 64.
- The typed premise is `word_of_nat(64, n) = read_gpr(r)`, and the result is
  `read_gpr(out) = word_of_nat(64, observe(source(…)))`.

So the source-expansion and observation pipeline keeps its shape. It tracks
the Nat expression of each Nat-carrying port beside its word, and a leaf's
proof is built from those lemmas in place of `refl`.

**Where the bound goes.** No Nat operation needs a bound until a word is read
back as a Nat, and that happens only in the loop (`LoopWord`). The counting
invariant is `loop_fits: carry + budget < 2^64`. Preserving it needs one fact
about the step: its payload is at most `Succ(carry)`
(`LoopAdvancesByAtMostOne(region)`). That is a property of the source, not of
the machine, and the client proves it beside its step function (the review's
"any nontrivial semantic invariant" row). The generator takes the theorem's
name for a Nat carry. `loop_fits_step` turns it into the next invariant and
the `< 2^64` bound that `toNat_word_of_nat` needs.

Supported Nat forms in a body: parameter, `Succ`, `Zero`, literals. Addition of
two Nats, and Nat helpers, are later work.

One constraint surfaced building it. The payload observer for a carried Nat
must apply `word_of_nat` *outside* its match on the step:
`word_of_nat(64, match r { Continue(p) => p, Break(p) => p })`. The loop layer
states `word_of_nat(64, loop_step_payload(step))`, and for a neutral step that
is not definitionally the per-arm spelling. As in slice B, the elaborator
accepted the per-arm spelling and the kernel refused it unlocated
(`issues/elab-accepts-projection-through-opaque-theorem.md`, second instance).

## 10. Decisions for discussion

1. The loop as an `AccessCode` constructor with an existential iteration count
   (composable), rather than a separate top-level loop artifact.
2. One exit, with the outcome **observed** from `g`, cursor and length, rather
   than tag-writing exit blocks per outcome.
3. Induction in the library, per-iteration glue generated (§6's reason).
4. Search before counting within this issue, since counting's Nat carry is a
   frontend capability of its own (slice C).
