# Straight label code, computed: `Straight` and `straight_runs`

Issue: `issues/native-symbolic-execution-step.md`. Library:
`lib/elf64_straight.hthr`; client: `lib/elf64_command.hthr` (`cmd_straight`
and the phases listed under "Moved" below).

## What it replaces

With `Runs` (`docs/native-runs-design.md`) a phase is a `runs_seq` chain:
one rule per block, store, load or jump, each with its residency
(`framed_resident` over `cmd_at`), its frame fact (`framed_moved`,
`Framed(…, set_var(…))`), its landing fact (`cmd_j_*`), and a middle
predicate written out between every two of them. The issue asked for a step
that emits those terms: one call per straight run, a JCC decided from the
flags where it can be, a goal where it cannot.

## Decision: compute the obligation, prove the runner once

The step is not a `meta fn` and not elaborator sugar. It is an ordinary
function from the program's items to a type, and one theorem:

```heather
fn Straight(file, page, origin, events, labels, l: Prog, n: Nat)
    → (Nat → BitVec(64)) → MachineState<IoMemory> → Type
theorem straight_runs(…, l, n, fits, rest, code, vars, state,
    rip: state.rip = next_rip(origin, straight_from(l, n)),
    framed: Framed(file, page, vars)(state),
    held: Straight(…, l, n)(vars, state)): LinuxRuns(io_linux(), events, state)
```

`Straight(…, l, n)` reads the `n` items ending at label `l` and is, by
evaluation, what running them from `state` with the frame holding `vars`
comes to:

| Item | What it asks of `vars`, `s`, then the rest `then` |
| --- | --- |
| `Block(is)` | `then(vars, execute_block_normal(is, s))` |
| `Load(ld)` | the slot `q` the base holds, then `then(vars, word_load_after(ld, vars(q), s))` |
| `Store(st)` | the slot `q` the base holds, then `then(set_var(vars, q, src), word_store_after(…, st, s))` |
| `Jcc(cc, t)` | `(condition_holds(cc, s.flags) = True → leaf at t) ∧ (… = False → then(…))` |
| `Jmp(t)` | the leaf at `t` |
| anything else | `False` |

A leaf (`StraightLeaf`) is where the stretch ends, after its last item or at
a jump's target: `s.rip = next_rip(origin, at) → Framed(file, page, vars)(s) →
LinuxRuns(io_linux(), events, s)`. The caller proves it with the next phase's
lemma, given the RIP and the frame.

The caller writes one term per stretch: a pair per JCC and a leaf proof per
end. No intermediate state is named, no item placed, no landing cited, no
frame fact threaded: the kernel computes the states as the items' own
results (`execute_block_normal` over `execute_block_normal`…), and
conversion reads a register through them to the value written or kept, as
`runs_block`'s postconditions already relied on.

Why this and not generated terms: a generator in the meta layer has no
`match` or recursion over code (`docs/meta-def-registration-design.md` §2),
and elaborator sugar would be a second, Rust-side reading of the items'
semantics. Here the items' semantics are read once, in `straight_item`, and
`straight_item_goes` proves that reading against the machine. Nothing is
trusted, and the obligation is a type the elaborator already knows how to
check a term against.

### What decides an item, by evaluation

Each choice the computation makes is a closed `match` that conversion
evaluates when the caller's term is checked:

- **A load's or store's slot**: `slot_find(read_gpr(base, s.gprs), 32)`
  compares the base's value with each slot's address by `eq_bit`. The base
  was set by the block before (`MovRI(R11, slot_at(q))`), so the value is a
  closed word; `slot_find_some` turns the hit into the address equation
  `run_frame_store` and `frame_var_at` take.
- **A store's base form**: `store_base_plain(st.base)`, which
  `run_frame_store` requires.
- **A jump's landing**: `asm_same(here + size + d, to)`, then the same
  around 2^64 for a jump back, as `asm_lands` and `asm_lands_back_to` do.
  The leaf's RIP names the target's offset as the program computes it
  (`labels(t)`); `cmd_target` restates it at the target's label, by the same
  evaluation.

A miss is `False`: a store through a base that holds no slot, a jump that
does not land, an item the runner does not read. No caller can prove it, so
a stretch that asks for one fails where it is used.

### What a JCC leaves

Both sides, as two implications. A side the precondition rules out is
`absurd` of the flag fact against the precondition (`loop_last`: RSI is
zero, so `E` holds and the not-taken side is `absurd`). A side both
preconditions allow is the caller's case analysis, the branch the issue says
to leave as a goal. When the flag is closed (a compare of two constants) the
equation reduces and the side is `λ never => absurd(never)`.

## Items: `Load` and `Store`

`Asm` had stores and loads as `Code(bytes)`, which a computation cannot
read. `x86_64_asm` now has `Load(WordLoad)` and `Store(WordStore)`, with
`Code`'s bytes (`word_load_bytes`, `word_store_bytes`) and lengths; the
command's `wstore`/`wload` and the spill table use them. The assembled bytes
do not change.

## Where a stretch's code is

`straight_runs` takes the code up to its last label followed by anything,
`asm_code(fills, labels, l) ++ rest`, placed in every frame's image. The
whole program's code is that for any of its labels (`asm_code_back`:
`asm_code(p) = asm_code(asm_back(p, k)) ++ asm_code_after(p, k)`), so
`cmd_straight` supplies it once from `CommandPlaced` for any label. The
runner splits off each item's bytes as it walks back along the chain, as
`asm_resident_from` does.

## Cost

Not measured as a round goal (CLAUDE.md). The shape: each use evaluates its
stretch's items once (`asm_find` from the program's end to `l`, then the `n`
items), each store's `slot_find` (up to 32 word comparisons), and each
jump's landing.

## Not yet

- Byte loads and stores (`Code(byte_load_bytes(…))`) and the page: the
  argument scan's and the row's. A `LoadByte` item would ask for the byte
  and its read under every frame.
- A `Runs` form. The runner's leaves are `LinuxRuns` continuations, which is
  how the command's phases end; a stretch inside a `Runs` chain still uses
  the rules.
