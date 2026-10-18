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
fn Straight(file, origin, goal: MachineState<IoMemory> → Type, labels, l: Prog, n: Nat)
    → (Nat → BitVec(8)) → (Nat → BitVec(64)) → MachineState<IoMemory> → Type
theorem straight_runs(file, page, origin, goal, back: StepsBack(goal), fills, labels, l, n,
    fits, rest, code, vars, state,
    rip: state.rip = next_rip(origin, straight_from(l, n)),
    framed: Framed(file, page, vars)(state),
    held: Straight(…, l, n)(page, vars, state)): goal(state)
```

`Straight(…, l, n)` reads the `n` items ending at label `l` and is, by
evaluation, what running them from `state` with the frame holding `vars`
and the page `page` comes to (the table drops the page, which every item
but `StoreByte` hands on as it is):

| Item | What it asks of `vars`, `s`, then the rest `then` |
| --- | --- |
| `Block(is)` | `then(vars, execute_block_normal(is, s))` |
| `Load(ld)` | `SlotThen(base, λ q => then(vars, word_load_after(ld, vars(q), s)))` |
| `Store(st)` | for a plain base, `SlotThen(base, λ q => then(set_var(vars, q, src), word_store_after(…, st, s)))`; else `False` |
| `LoadByte(ld)` | `ByteThen(file, page, base, λ b => then(vars, byte_load_after(ld, b, s)))` |
| `StoreByte(st)` | for a plain base, `PageThen(base, λ c => then(page_stored(…, page, c, low byte of src), vars, byte_store_after(…, st, s)))`; else `False` |
| `Jcc(cc, t)` | `(condition_holds(cc, s.flags) = True → leaf at the jump's target) ∧ (… = False → then(…))` |
| `Jmp(t)` | the leaf at the jump's target |
| anything else | `False` |

`SlotThen(base, then)` is `Exists q. q < frame_slots() ∧ base = frame_at(8q)
∧ then(q)`: the caller names the slot, and the address equation is `refl`
because the block before set the base (`MovRI(R11, slot_at(q))`). A closed
`q < 32` is `trivial`.

`ByteThen(file, page, base, then)` is `Exists b a. base = a ∧ (every
frame's image reads `b` at `a`) ∧ a < 2^47 ∧ then(b)`. A byte the command
loads is an argument's, which is not in the frame, so the read is stated
for every frame (`ArgStays` gives it). The caller names the address as it
names a slot: the base register's value where nothing computed it (`rsi`),
the block's own sum where one did (`refl`), so the reads are facts about a
term the caller wrote and no read is met against the stretch's spelling.

### The goal

`goal` is any predicate on the end state, with `back: StepsBack(goal)`:
`goal(after)` and Linux steps from `before` to `after` give `goal(before)`.
`runs_back(events)` gives it for `LinuxRuns(io_linux(), events, ·)`, which
is how the command's phases end; a phase's own record (`operand_at_back` for
`OperandAt`) is another. A `Runs` chain is not needed around a stretch.

### The leaf

A leaf (`StraightLeaf`) is where the stretch ends, after its last item or at
a jump's target:

```heather
λ page vars state => (after) → after.rip = at → Framed(file, page, vars)(after) → after = state → goal(after)
```

The end state is bound (`after`), so the leaf's proof names it rather than
the stretch's own spelling of it (an `execute_block_normal` over an
`execute_near_control` over …); `after = state` is there for a fact the
spelling gives by conversion (`operand_head` reads RSI through it). Binding
it is the rule `docs/native-runs-design.md` ("Consuming a run") states for
`Runs`. (`_` in argument position is a section, not a hole, so a leaf cannot
be written as `goal(_)` and inferred.)

A jump's leaf is at `near_branch_target(next_rip(origin, here), size, d)`,
the jump's own target, with `here` the offset of the label before the jump
(`prog_len(before)`) and `d` its displacement to the target's name
(`near_rel(here + size, labels(t))`). The caller turns it into the target
label's RIP with the landing fact the command already has, through
`cmd_lands` (`cmd_lands_back` for a jump back), which states the landing in
that spelling: `trans(at, cmd_lands(l_last(), 6, t_total(), ca(l_total()),
cmd_j_last_je()))`.

### The caller's term

`loop_last` is one call: the slots of its two stores, then the JCC's pair.

```heather
cmd_straight(…, placed, page, λ s => LinuxRuns(io_linux(), events, s), runs_back(events),
    l_last_je(), refl, 6, vars, state, rip_is, Exists(frame, ⟨memory_is, holds⟩),
    Exists(19, ⟨trivial, ⟨refl, Exists(20, ⟨trivial, ⟨refl,
        ⟨λ _ after at framed _ => total_runs(…, after, framed.proof.left,
             trans(at, cmd_lands(l_last(), 6, t_total(), ca(l_total()), cmd_j_last_je()))),
         λ no => absurd(trans(sym(no), zero))⟩⟩⟩)⟩⟩))
```

No intermediate state is named, no item placed, no landing cited inside the
stretch, no frame fact threaded: the kernel computes the states as the
items' own results, and conversion reads a register through them to the
value written or kept, as `runs_block`'s postconditions already relied on.
A side a precondition rules out is `absurd` of the flag fact (`loop_last`:
RSI is zero, so the not-taken side is absurd). A side both preconditions
allow is the caller's case analysis: the branch the issue leaves as a goal.

`cmd_straight` is `straight_runs` for the command's program: it takes
`at: asm_find(cmd_prog(), l) = l` (by `refl`) and supplies `fits` and
`code` once, from `CommandPlaced`, for any label.

Why not generated terms: a generator in the meta layer has no `match` or
recursion over code (`docs/meta-def-registration-design.md` §2), and
elaborator sugar would be a second, Rust-side reading of the items'
semantics. Here the items' semantics are read once, in `straight_item`, and
`straight_item_goes` proves that reading against the machine. Nothing is
trusted, and the obligation is a type the elaborator already knows how to
check a term against.

## Keep the computed type structural

The elaborator unfolds `Straight(…)` when it checks the caller's term
against it, and its weak-head evaluation is far dearer than the kernel's on
anything that computes with words or walks the program. Two first drafts
showed it:

- Finding a load's or store's slot inside the type (`slot_find`, a search
  over the slot addresses by `eq_bit`) ran out of the elaborator's fuel.
  The caller now names the slot and checks the address by `refl`, which the
  kernel evaluates.
- Finding the label inside the type (`asm_find(cmd_prog(), l)`, from the
  program's end back to `l`) dominated the whole check. The caller now
  passes the label itself and `asm_find(cmd_prog(), l) = l` by `refl`.

For the same reason a jump's leaf names the jump's own target and not the
target label's offset (which would compare `here + size + d` against the
label, as `asm_lands` does): the landing is the caller's `cmd_j_*` fact.
Even that fact's spelling matters. The `cmd_j_*` facts name the jump by its
own label (`ca(l)`, `cmd_d(l)`); met against the leaf's spelling inside a
`trans`, they cost the elaborator about as much as the rest of the stretch.
`cmd_lands` takes the fact once at the stretch's spelling, where meeting it
is cheap. Spelling the leaf by the jump's label instead (`asm_at(l)`,
`asm_jump(labels, l)`, with `l` rebuilt as `At(before, name, item)`) was
dearer in both the elaborator and the kernel.

So the type is computed from the items' structure only: which constructor,
which register, which label. Anything numeric is a `refl` or a fact the
caller cites, checked by the kernel.

## Items: `Load`, `Store`, `LoadByte` and `StoreByte`

`Asm` had stores and loads as `Code(bytes)`, which a computation cannot
read. `x86_64_asm` now has `Load(WordLoad)`, `Store(WordStore)` and
`LoadByte(ByteLoad)`, with `Code`'s bytes (`word_load_bytes`,
`word_store_bytes`, `byte_load_bytes`) and lengths; the command's
`wstore`/`wload`, its three byte loads (`l_dash_load`, `l_ahead_load`,
`l_len_load`) and the spill program (`lsp_*`) use them. The assembled bytes
do not change. The process libraries' byte loads (the argument scan's, the
stat pass's, the cursor's) are still `Code`.

`StoreByte(ByteStore)` is a byte store to the page, which the row's tail
writes before each write. The page is not fixed for a stretch: `Straight`
carries it as it carries `vars`, so every continuation and leaf takes the
page first (`then(page, vars, state)`), and a byte store hands on
`page_stored(file, page, c, x)`, `io_store_offset`'s page with `x` at `c`.
`PageThen(base, then)` is `Exists c. c < 4096 ∧ base.toNat() =
io_page_base() + c ∧ then(c)`: the caller names the offset, from the
cursor's fact (`rdi`), as it names a slot. The leaf's `Framed` is over the
carried page, so the write after the stretch reads its stored bytes from
`io_store_offset`'s lemmas (`stored_store`, `stored_kept`, in `row_sent`).
Carrying the page left the other phases' kernel steps as they were. The
total row's seven stores (`l_tn*`) are `StoreByte` items too, run by
`put_runs` ("A stretch written once over any label").

## Where a stretch forks on data, split it

A stretch whose leaves depend on a value the caller takes apart (the dash
test on the operand's name: no byte, a first byte not `-`, `-` alone, `-`
and more) can be one call per case, each the whole stretch. The dash test
written that way (four calls over its seven items) took more kernel steps
than the hand-threaded proof it replaced and several times its elaboration:
each call unfolds the whole stretch again, and each nests the next byte's
obligation inside the first JCC's side.

Written instead as one call per straight run (`dash_test`: the first byte,
three items; `dash_ahead`: the second, four), with the byte computed from
the name (`first_byte`) rather than cased on, it took well under half the
kernel steps of the hand-threaded proof. A JCC's sides are then small terms:
the flag converted to a fact about the byte (`byte_differs`, `byte_same`
over `cmp_bytes`), and a lemma that cases on the name to say what it names
(`stdin_of_first`, `stdin_of_second`, `stdin_of_nul`). The case analysis is
in ordinary lemmas, outside any term checked against `Straight`.

## A stretch written once over any label

Where the same items repeat at many labels, the stretch can be a lemma over
the label rather than a call per label. `init_runs` zeroes nine slots, each
a block setting R11 and a store from RAX; `zero_runs` is that pair ending at
`zero_label(before, q)`, for any `before` and slot `q`, taking the label's
`asm_find` fact (`refl` at the caller) and a continuation (`ZeroGoes`) that
takes the frame with the slot zero. `Straight` unfolds over an abstract
`before` as over a concrete one, since it reads only the items' structure;
the slot's address is `refl` for any `q`. So the elaborator checks the
stretch once, and `init_runs` is a stretch of three items (the width's
store, RAX zeroed) and nine calls. Cold, its kernel steps fell to about a
seventh of the hand-threaded chain's (the chain's own `zero_slot` included),
and its elaboration rose by about the one check of `zero_runs`, not by a
check per slot.

The row's tail is written the same way, for a different reason: its two
arms share their first stretch and the shape of their second. `tail_test`
is the count's test (`l_named` to the JE), with a continuation per side of
the JE (`TailGoes`), and `named_runs` and `unnamed_runs` each pass the side
their count rules out as absurd. `byte_sends` is a byte stored after the
row and R9 and R10 set, ending at `byte_label(before, name, w)`, then the
row written (`row_sent`); the gap (`w` = 32) and stdin's newline (`w` =
10) are two calls of it. A first draft with each arm's stretches written
out in its own phase took over half again the kernel steps and about four
times the elaboration of this one.

## Where a stretch's code is

`straight_runs` takes the code up to its last label followed by anything,
`asm_code(fills, labels, l) ++ rest`, placed in every frame's image. The
whole program's code is that for any of its labels (`asm_code_back`:
`asm_code(p) = asm_code(asm_back(p, k)) ++ asm_code_after(p, k)`, with
`fills_fit_back` for the fills), so `cmd_straight` supplies it once from
`CommandPlaced`. The runner splits off each item's bytes as it walks back
along the chain, as `asm_resident_from` does.

## Cost

Not measured as a round goal (CLAUDE.md); one cold comparison against the
hand-threaded `Runs` chains was taken to check the issue's acceptance. The
kernel checks each item's residency once inside `straight_item_goes`,
against an abstract frame, plus the caller's `refl`s. Over the five moved
phases the kernel's steps went down (the chains' helper lemmas are gone; the
runner and `asm_code_back` are paid once). `operand_head` alone went up: it
absorbed its stretch's helpers, and its leaf reads RSI through the
stretch's spelled state.

What went up is elaboration. Checking a caller's term against `Straight`
makes the elaborator unfold it at each anonymous constructor and λ, and its
weak-head reducer copies the growing continuation at every step; that is
now most of each moved phase's time, more than the gate. It grows with the
stretch's length and the number of nested proof constructors. The library
side has no cheaper spelling left that was found (an arm per function did
not move it); the elaborator side is a reducer that shares
(`issues/elab-whnf-copies-straight-continuations.md`).

## Moved

The loop's last-operand test (`loop_last`, replacing `cursor_store_runs`
and `last_tested_runs`), the operand's head (`operand_head`), stdin
(`stdin_path`, replacing `stdin_block`), the open's return (`open_back`, both
arms, replacing `opened_block`) and the failed path (`failed_runs`).

Then, with `LoadByte`: the dash test (`dash_test`, `dash_ahead`, replacing
`ByteTested`, `dash_tested`, `ahead_tested`, `jne_open` and `dash_second`)
and the open's request (`open_path`, a stretch of one block whose leaf makes
the system call). Their continuations (`StdinAt`, `OpenAt`) take a framed
state, so they no longer close over the starting frame.

Then the phases whose continuations closed over the starting frame, once
those continuations took a frame:

- The name's scan (`name_scan`, replacing `NameEnd`, `name_test_block`,
  `name_load` and `name_len_block`): recursive over the name, one five-item
  stretch per byte ending at its back jump. The byte read is `NameReads`
  (each byte up to the cursor is known and not NUL) and the end is
  `NameFound`; the stretch's leaf at the back jump recurses one byte on.
- The name's write (`name_send`, replacing `name_copy_block`): two
  stretches, the copy (three items) and the found label (one item, then the
  write's system call). Its continuation is a `FramedWrite`, a write stated
  for every frame the caller's vars hold in, rather than over one image;
  `named_runs` hands its close and newline writes on the same way.
- The read's failure (`read_failed`): one five-item stretch to its jump.
- The loop's cursor (`loop_cursor`): one four-item stretch, then the
  cursor's own phase. It is written in continuation-passing style, ending
  in a `CursorGoes` the caller supplies, so `operand_step` and the empty
  list's arm of `operand_loop` are its continuations rather than terms that
  rebuild its end state.

Then, with `StoreByte` and the page carried:

- The row's tail: `named_runs` and `unnamed_runs` are the count's test
  (`tail_test`, four items, the JE's ruled-out side absurd) and a byte sent
  after the row (`byte_sends`, three items, then the write), both written
  once ("A stretch written once over any label"). The newline
  (`newline_send`) is one three-item stretch. Cold, their kernel steps fell
  to about a third (`row_send`'s included); their elaboration rose from
  about half a second in all to about two.
- `init_runs`, as a stretch per slot ("A stretch written once over any
  label"). As one stretch of its twenty-one items it had taken more than
  twice the chain's kernel steps: one long stretch nests every later item's
  obligation inside the earlier ones, and the elaborator unfolds the whole
  of it at every constructor.

`inputs_runs` is composition of other phases, with no code of its own to
move.

Then the last of the command's `Runs` chains:

- After the last operand: `total_runs` is one stretch of four items to its
  JB; `total_rows` one of five for the row's setup, the row, then
  " total\n" as seven calls of `put_runs` (a byte stored at RDI and RDI on
  by one, written once over any label as `put_label(before, w)`), and a
  one-item stretch for R9 and R10 before the write.
- The prologue: `keep_runs` is two stretches (the two slot stores, then the
  count against two to the JAE), `keep_single` one of four items to its
  JMP, `begin_runs` one of four (RBX and R12 into their slots) and
  `begin_test` one of six (the count's test, stdin's fd and its JMP).
- The spill's row setup: `spill_row` hands the spill's end state on
  (`runs_elim`) to one five-item stretch, its goal the `RowReady` record
  (`row_ready_back` is its `StepsBack`).

Cold, over these phases the kernel's steps fell to between a third and a
half of the chains' (the total row's to under a third). Elaboration rose
for the prologue and the spill's setup and fell for the total row.

Two things decided the shape:

- **`omega` stays out of a phase's term.** It reads every hypothesis in
  scope (`docs/creal-multiplication-round.md` met the same with `Rat`
  facts), and inside a stretch's leaf that scope holds the stretch's spelled
  state. In `keep_runs` two `omega`s for the count's bounds were three
  quarters of its kernel steps; as small lemmas (`two_or_more`,
  `one_or_none`, `under_two`), the phase fell to a fifth of the chain's.
  The total row's and the spill's arithmetic is the same way (`put_room`,
  `total_fits`, `row_fits`, `spilled_vars`). The rule holds for the
  hand-threaded process libraries too, whose phases name each state with a
  `let`: a goal that shares an atom with a register fact
  (`read_gpr(Rsi, s2.gprs).toNat() = …`) brings that state into the
  certificate. One such `omega` was two thirds of `stat_operand`'s steps;
  moving the libraries' phase `omega`s into lemmas (`bound_low`,
  `page_succ_room`, `values_lt`, `field_fits`, `slot_more`, …) halved the
  stat pass, the cursor, the filter and the row writer cold.
- **A JCC's side on a negated flag** (`AE`, `NE`) is `!b = True` or
  `!b = False`; `not_true_is` and `not_false_is` give `b`, so one stretch
  states both sides and no case analysis runs before it.

## The libraries' stretches

The process libraries keep no frame: they run wherever a program places
them, over the page alone. `lib/elf64_stretch.hthr` is `Straight` without
`vars`: `Stretch(file, origin, goal, labels, l, n)(page, state)`, with
`StretchLeaf` (the end state handed over bound, as `StraightLeaf`),
`WordThen` and `ByteAt` for a load (the caller names the value and its
address, the read shown over the page), and `PageThen` for a byte store.
`stretch_runs` is `straight_runs`'s counterpart; a library states its own
wrapper over its placement (`stat_straight`, as `cmd_straight`). The pieces
both kinds share (`StepsBack`, `runs_back`, `PageThen`, `page_stored`,
`straight_from`, `not_true_is`, `not_false_is`) live there, and
`elf64_straight` imports them.

A stretch reads a load only from a `Load` or `LoadByte` item; a
`Code(word_load_bytes(…))` item has the same bytes but leaves `False`, so
the stat pass's loads are now `Load`/`LoadByte` items (wc's bytes are
unchanged).

The stat pass's two heaviest phases moved first:

- `acct_stated` is one ten-item stretch from `acct` to its JMP, the
  other kind's two items a second (`acct_other`); the answer's kind is
  decided in the leaves (`stated_regular`, `stated_other`), and the phase
  is continuation-passing (`StatNext`), no longer an end state handed back.
- `stat_operand` is the operand test to its JNE (two items), then
  `stat_each`: one seven-item stretch from `each` to the lone dash's JE,
  split by the operand's shape (empty, one byte, more) so each byte the
  stretch reads is named, as the command's dash test is.

Cold, the two phases' kernel steps fell to a fiftieth and a twentieth of
the chains', and the stat pass's to a fifth.

## Not yet

- A system call ends a stretch: `closes_runs` still runs its JCCs with the
  `Runs` rules before `linux_runs_close`.
- **The spill's slots stay on the `Runs` rules** (`spill_one_runs`,
  `spill_runs`). A slot's source register is the state's (`state_gpr(spill(i))`),
  not a constant, so in the computed type each read of it is stuck behind
  the writes before it; a stretch has to restate the stretch's spelled
  states to show those writes keep it (`state_kept`), and to carry
  `WriteKept` through them. Tried as a stretch written once over any slot
  and register (`spill_one`, with `spill_goes` in continuation-passing
  style), the slot and its recursion took over twice the chain's kernel
  steps, and more elaboration.
