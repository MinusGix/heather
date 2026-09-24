# Native bounded-loop certificates — design

Status: **design agreed 2026-09-24; probes done (§8); slice A0 in progress**. Owner:
`issues/native-bounded-loop-certificates.md`, step 3 of
`issues/native-shared-lowering-milestone.md`. Implementation state is in §9.

## 1. What exists, and what this adds

The source/IR contract (`docs/function-ir-readonly-loops.md`,
`lib/function_ir_loop.hthr`) fixes the meaning: one evaluator `loop_run`, a
five-parameter wrapper reflected with its step function, and
`LoopReadable` defined from the evaluator's own outcome. The 09-20 rounds
also built one *iteration's* physical pieces: typed certificates for pure
source functions at explicit placements (`generate_elaborated_typed_x86`), a
byte load followed by a reflected body (`generate_elaborated_read_x86`),
effectful composition (`AccessCode`: pure, read, sequence, forward branch),
and the word/Nat bridges in `lib/function_ir_loop_x86.hthr` (bounds test
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

`LoopHead(p, rep, access, buffer, needle, state, cursor, budget, carry)`
means: base/length/cursor/budget registers are `LoopWord`s of their Nats,
needle is placed, `rep(carry register, carry)`, the memory agrees with
`buffer.read` (the `memory_agrees` shape of `loop_read_address`),
`cursor ≤ length`, and `LoopAddressBound`.

Two **per-iteration obligations**, over open states and values:

- `GuardStep`: from `LoopHead(s, c, b, k)` the guard code executes to
  `m` with `g` holding `ofBool(c <u len ∧ 0 <u b)` and the head registers
  preserved.
- `BodyStep`: from the head registers at the branch entry, plus
  `Inv(c, Succ r, k)`, `c < len` and `ReadsByte(c, byte)`, the body executes
  to `s'` with `d = disc(body(needle, c, byte, k))`, `rep(carry', payload)`,
  cursor `~ Succ c`, budget `~ r`, `g`, base, length and needle preserved,
  and `Inv(Succ c, r, payload)` when the step is `Continue`.

The library theorem `loop_trace`, by induction on the budget and generalising
the state, cursor and carry:

```text
LoopHead(s, c, b, k) → Inv(c, b, k) → LoopReadable(b, region, buffer, needle, c, k)
  → GuardStep → BodyStep → LayoutOf(loop)
  → Exists(after, ExecuteAccess(access, AccessLoop(…), s, after)
                 ∧ LoopObserved(p, rep, after, loop_run(b, region, buffer, needle, c, k)))
```

`LoopReadable(Succ r, …)` with `c < len` unfolds to `match read {None =>
False, Some(byte) => …}`. That supplies the byte for `ReadsByte` and the
tail's readability, and is what the 09-20 contract was shaped for. The guard
arithmetic is library lemmas: `0 <u b` iff `b ≠ 0` under `LoopWord`,
`word ~ Succ r → word − 1 ~ r`, and `base + length ≤ 2^47 → canonical(base + cursor)`
for the read adapter's low-canonical premise (V5).

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

- **A0 — near branches** (V1): `NearControl` in `x86_64_block`.
- **A — library.** `AccessLoop` (bytes, layout, execution, memory) with near
  edges, `LoopHead`/`LoopObserved`, `loop_trace`, the word lemmas, and the
  guard, update and copy source functions. Check it with
  a hand-instantiated loop in a test.
- **B — generator + search.** `AccessFragment::looped`, glue emission,
  `generate_elaborated_loop_x86(elab, "clients::first_match", placement)`
  from the existing wrapper reflector, the controls, and the native test.
- **C — Nat carry + counting.** A Nat port with a `LoopWord` representation
  and a bound premise in typed certificates (`Succ(count)` → `add 1`), the
  counting `Inv`, and `count_occurrences` through the same generator. The
  milestone's rule applies: the second client adds source, spec and tests,
  and nothing machine-specific.

## 10. Decisions for discussion

1. The loop as an `AccessCode` constructor with an existential iteration count
   (composable), rather than a separate top-level loop artifact.
2. One exit, with the outcome **observed** from `g`, cursor and length, rather
   than tag-writing exit blocks per outcome.
3. Induction in the library, per-iteration glue generated (§6's reason).
4. Search before counting within this issue, since counting's Nat carry is a
   frontend capability of its own (slice C).
