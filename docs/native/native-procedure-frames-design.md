# Procedure frames: each activation its own layout

Status: **proposed 2026-11-17**, for `issues/statement-procedure-frames-by-use.md`,
with Minus's direction of 2026-11-16 to take the proper form, not a
partial step. This note does one step of
`docs/native/native-procedures-are-functions-design.md`. That note built one frame, one call
and one contract (U5). It left "a file of words per procedure, each
numbering its own from zero with its own homes" (§2.7, §4) for a later
round, and this is that round. What a procedure means does not change. The
change is how the machine and the theorem describe an activation.

## 0. Summary

Today the statement compiler has one `Layout` for the whole program. Every
word has one home, and every procedure's frame holds a slot for every word
of the file. Each entry pushes the callee-saved registers that *any* word
of the program lives in, and the stack bound charges every level
`8 * (words + 7)`. The meaning already has a different shape: a callee
starts from a file of its own, zero but its parameters
(`Procedure::enter`), and the caller gets its own words back
(`Procedure::leave`). So the machine claims more than the meaning needs.
The theorem therefore asks for more stack than a program uses, and the
stack bound can't tell one procedure from another.

After this round, an activation is described by what it is:

1. **Each body has its own file and its own homes.** `main` and each
   procedure number their words from zero and are allocated alone. Each
   has its own `Homes` and its own check (`Procedure::fits`, and
   `Source::allocation_ok` for `main`).
2. **A frame holds only the slotted words.** A word homed in a register
   has no slot. A slot is a slot index (`InSlot(k)`), not the word's id,
   so a frame is as many words as its body slots.
3. **An entry saves what its own body writes.** That is RBX, and of
   R12–R15 and RBP the ones its words live in or its leaves use as
   scratch. The body's register footprint becomes a proved fact, and the
   callee's contract becomes System V's: every callee-saved register as
   it was (§2.4). This is the part with new proof.
4. **The stack bound comes from the call graph, by depth.** A level is the
   frame of the procedure entered there: its slots, its saved registers
   and its return address. Below it is the largest need of what it calls,
   one level shallower. `deep` is that number for `main` at the source's
   depth, plus the functions' room under the deepest frame.

Calls already move words from the caller's homes to the callee's, through
the argument and result registers (`Prog::calls`, `words_to`,
`words_from`). Nothing about a call site has to learn that the homes now
differ.

## 1. What is there

Checked against master at `fee1d30`, 2026-11-17.

- `Layout { low, words, capacities, homes, pool, taken, procedures, functions }`
  (`native_compile.hthr`): one `homes`, one `words`.
- `Home { InSlot, InReg(k) }` (`native_alloc.hthr`). A slotted word `id`
  is the stack word at `RSP + 8·id`, so a frame is `layout.words` words.
- `Procedure::entry_code` counts the depth, pushes `layout.kept()`
  (`Homes::kept`: RBX and those of R12–R15 and RBP that some word lives
  in), and opens `frame_down(layout.words)`. `exit_code` undoes it.
- `Source::allocation_ok` checks `main` under the homes. Each procedure is
  checked under the same homes by `Procedure::fits` when it is emitted.
  The Rust allocator (`crates/cli/src/native/allocator.rs`) mirrors
  `Greedy` over the whole source.
- `Target` carries the one `homes` and `words`. `Target::activation`
  enters a callee with `room * (8 * (t.words + 7)) + program_calls_room(…)`
  as its stack premise. `native_compile_correct`'s `deep` premise is
  `src.depth * (8 * (src.words + 7)) + program_calls_room(src.functions) + 8 * (src.words + 1) <= stack.size`.
- `Target::Spares` already says that a body's code keeps every register
  that is neither a home of its words nor RBX.

## 2. The design

### 2.1 A body's file

A `Procedure` keeps its record: `params`, `results`, `body`. Its ids are
its own, and the size of its file is computed, not stored:
`Procedure::words()`, one past the largest id its parameters, results and
body name (`List::word_bound`, `Stmt` word ids). `main`'s is `Source.words`
as now. A body naming an id at or past its file is refused, as now. The
meaning is unchanged: `enter` and `leave` already treat the callee's words
as its own.

The generators need no change. `native_build` already numbers a
procedure's words from zero: parameters first, then results, then its
body's (`native_build.hthr`, procedure `index`). Today the frame is the
program's word count anyway. After this round, each frame is its own.

### 2.2 A body's homes and its slots

```heather
inductive Home { InSlot(k: Nat), InReg(k: Nat) }
// Every body's homes: main's, then procedure p's.
record Placement { main: Homes, procedures: List<Homes> }
```

- **Slots by index.** `InSlot(k)` is the stack word at `RSP + 8·k`. A
  body's frame is `Homes::slots()` words, one more than the largest `k`.
  The allocator numbers a body's slotted words from zero in the order it
  slots them. The check is that two words whose lives overlap never share
  a slot: the interference check that already holds registers apart,
  applied to slots too. So two words that are never live together may
  share one, which is the same rule registers follow.
- **Homes per body.** The allocator runs once for `main` and once per
  procedure, each over its own body with its live-out set (`[]` for
  `main`, the results for a procedure). `Source::allocation_ok` becomes
  `Placement::ok(src)`: each body's homes fit and its body checks. The
  slotted-at-entry condition (`homes.slotted(live)`) stays `main`'s alone.
- **The Rust mirror** allocates per body the same way. Today it walks
  `main` only, and a source with procedures is allocated on the fork
  (`allocator.rs`, `main_of`). Each procedure's body is a `Stmt` the
  mirror already reads, so per-body allocation lets it take procedures
  too.

### 2.3 The layout and the target

`Layout` splits into what the program shares and what an activation owns:

```heather
record Frame { words: Nat, homes: Homes, pool: List<Gpr>, taken: List<Gpr> }
record Layout { low: BitVec(64), capacities: List<Nat>, frame: Frame,
    procedures: List<Procedure>, functions: List<Function>, frames: List<Frame> }
```

`layout.frame` is the activation being emitted. `layout.frames` holds every
procedure's frame, so a call site can find its callee's label and arity,
and the stack bound can find each callee's size. Emitting procedure `p`
emits its body under `layout.at(p)`, the same layout with `frame` replaced
by p's. The code that reads `layout.homes`, `layout.words`,
`layout.pool` and `layout.taken` reads them through `frame`. That is a
rename at every use, with no change to what it computes.

`Target` gets the same split. Its `homes`, `words`, `homed` and the
`fits` clause's word part move into a `frame` field, and
`Target::activation` takes the callee's frame as well as the new index.
`Target::Held` is unchanged in shape: it already speaks of "this
activation's slot words on the stack at RSP", so it now reads them through
the activation's frame.

### 2.4 The convention, per activation

- **Entry and exit** push and pop the activation's `kept()` and open
  `frame_down(8 * frame.slots)`. The order is as now: the depth first,
  then RBX and the kept registers, then the frame.
- **What a body writes.** A body writes three kinds of register: the homes
  of its words, RBX, and its leaf pool. Today the leaf pool is every
  register of `register_pool()` that no word of the *program* lives in
  (`Homes::leaf_pool`), and that pool includes R12 to R15 and RBP. This is
  sound today only because homes are global: a callee-saved register that
  is in the leaf pool holds no word of any caller. With homes per body
  that stops being true. A callee whose own words do not use R13 would
  take R13 as leaf scratch while its caller has a word living there.
- **So a body's footprint is part of its frame.** `Frame.pool` is chosen
  per body: the caller-saved scratch registers, plus whichever
  callee-saved registers the body takes for leaves. `kept()` is RBX and
  every callee-saved register in `taken` or `pool`. The allocator decides
  how many callee-saved registers a body's leaves get. None is the
  cheapest entry, and a leaf that needs more registers than the scratch
  set is the reason to take one.
- **A new body-level theorem.** The proof needs a statement it does not
  have today: running a body changes no register outside its frame's
  `taken`, `pool` and RBX. `Target::Spares` says this of one write to a
  word's home, not of a body. Each `Stmt::emit_runs` case has to carry it:
  a leaf by the lowering's `leaves_all` check, a home write by `Spares`, a
  SYSCALL by the Linux model's clobber set, and a call by the callee's
  contract. The callee's contract then says what System V says: every
  callee-saved register and RSP are as they were at the call. Today's
  contract claims less. It says the caller's live words survive, and gets
  that from the homes being global.
- **R10** is still carried in RBX by the caller, since it is caller-saved
  and in the home pool.

### 2.5 The stack bound

One activation of procedure `p` takes
`level(p) = 8 * (slots(p) + kept(p).len()) + 8`: its frame, its saved
registers and its return address. `main` takes its frame alone, as the
start-up gives it. What may be below an activation of `p` with `d` levels
of room left:

```heather
fn Placement::need(self pl: Placement, src: Source, p: Callee, d: Nat) → Nat
// p's level, and below it the most of: for each procedure q that p's body
// performs, pl.need(src, q, d - 1) at d > 0, or 8 at d = 0 (a call there
// exits in the callee's entry, after its CALL); and program_calls_room
// where p's body calls a function.
```

`deep` becomes `pl.need(src, Main, src.depth) <= stack.size`.
`Target::activation`'s `roomy` premise becomes the callee's `need` at the
room left. The bound is exact for the tree a program can make. A procedure
that performs nothing needs its level and nothing below it. A program with
no procedures needs `main`'s frame and the functions' room.
`program_calls_room` stays the function lowering's table.
`room-table-loose-ends` §2 (functions under the planned table) is then a
change to that one term.

**How it is computed and checked.** Written as a recursive function,
`need` calls itself once per call site, which is exponential in the
depth. It is computed as a table instead: one row of needs per depth, each
row from the one before, so the cost is `depth × call sites`. Where a
source's depth is large that is still too much for one `refl`. The
alternative keeps the function lowering's pattern, a table that is
proposed and checked: numbers `a(p)` and one slope `c`, accepted when
`level(p) + a(q) <= a(p) + c` for every call of `q` in `p`, which bounds
`need(p, d)` by `a(p) + c * d` at any depth and is checked once per call
site. For a program whose procedures do not recurse, `c` is zero and the
bound does not depend on the depth at all. F4 states `deep` from `need`
and proves the proposed table bounds it, so a certificate may use either.

**The bound now depends on the homes.** `8 * (words + 7)` was a function
of the source alone. `slots(p)` and `kept(p)` are the placement's, so
`deep` is stated for the placement a program is compiled with, as
compile-x86 states a function's room. A premise free of the placement
stays available as a theorem: `need` is at most the old bound.

### 2.6 What stays as it is

- The meaning of a `Source`, `Procedure::enter` and `leave`, and the tree
  side.
- A call site (`Prog::calls`, `performs`, `call_lent`). Words still cross
  a call through the argument and result registers.
- The function lowering, its frames and `program_room`.
- `Stmt::emit` above the word lemmas. It reads homes through the layout,
  which now means the activation's.

## 3. The steps

Each step is a PR, changes no meaning, and ends with the native gates and
the tools' GNU gates passing on the new code.

- **F1. Frame out of Layout and Target.** The `Frame` record, `layout.at(p)`,
  `Target.frame`, and every use reading through it. The program is still
  given one `Homes`, used as every body's frame, so the code is
  byte-for-byte what it was and the linked assembly and the tools' ELFs do
  not change. This is the large mechanical step, and it carries most of
  the proof's line count. It is safe because nothing about the bytes
  moves.
- **F2. Homes per body.** `Placement`, the allocator per body in Heather
  and in Rust, each procedure checked under its own homes, and
  `Target::activation` switching frames at a call. A body's leaf pool is
  its frame's, the body-level footprint theorem is proved, and the
  callee's contract keeps every callee-saved register (§2.4). This is the
  step with new proof in it, and it may split in two: the footprint
  theorem first, under the global homes, then the homes per body.
  Frames are still `words` slots, each body's own file size.
- **F3. Slots by index.** `InSlot(k)`, the slot interference check, frames
  of `slots` words. `Target::Held` and the slot lemmas read `RSP + 8·k`.
- **F4. The bound by call graph.** `Placement::need`, the `deep` premise
  and `roomy` stated from it, the certificates' literal. Close
  `statement-procedure-frames-by-use`.
- **F5. Functions under the planned table** (`room-table-loose-ends` §2):
  `Prog::links` under `program_room_planned`, and `program_calls_room`
  from it.

F2 and F3 each change code and the linked tools' bytes, and each ends by
regenerating what is checked in.

## 4. Decisions

| question | proposal | why |
|---|---|---|
| a procedure's file size | computed from its body, not a field | the meaning already gives each its own file; no generator change |
| slots | by index, shared by words never live together | a register-homed word takes no slot; the rule registers follow |
| where the frame lives in the proof | a `Frame` in `Layout` and `Target`, swapped at a call | every word lemma is stated over one activation already |
| the bound | per callee by depth, from the call graph | exact for the trees a program makes; `max frame × depth` would over-count |
| kept registers | the callee-saved registers in the activation's homes and leaf pool | a body's leaves use callee-saved registers as scratch, so its footprint decides what it saves |
| leaf pool | per body: caller-saved scratch, plus callee-saved registers the allocator grants | a global pool is only sound with global homes |
| checking the bound | `need` by rows, or a proposed table `a(p) + c * d` checked per call site | recursion on depth per call site is exponential; a large depth is too much for one `refl` |

## 5. Issues this touches

| issue | role |
|---|---|
| `statement-procedure-frames-by-use` | the owner; closes at F4 |
| `room-table-loose-ends` | its §2 is F5 |
| `native-register-moves-and-convention` | per-procedure homes, which it kept open, are F2 |
| `native-procedures-write-elf-capacity` | the Rust mirror allocating per body (F2) may retire it; check there |
| `rt-effectful-callees` | a reflected `EFun` lowered to a `Procedure` gets its own file and homes for free |

## 6. As built

What the steps turned into, where it differs from the sections above.
Sections 2.3 and 2.4 describe the design as first written; this section is
the record.

### 6.1 F1: the reserved words

No `Frame` record inside `Layout`. `Layout` and `Target` gained one field,
`reserved`: the words' room the region keeps before its buffers, which is
the program's whichever activation runs. `words` stays the running
activation's frame. The data offsets (`buffer_offset`, `scratch_offset`)
read `reserved`, the frame code reads `words`. Byte for byte the same code.

### 6.2 F2: pins, not a footprint theorem

Section 2.4 asked for a body-level footprint theorem: a body's code writes
only the registers of its frame's pools. It was not needed. The invariant
between statements already says what a body leaves alone, keyed on
`Homes::uses`: every lemma about a leaf's scratch, a home's write or a
call asks `uses(register) = False` before a register is written. So the
homes carry the registers a body is to leave alone though no word of its
own lives there:

- `Homes.pins` names them, and `Homes::pinned(r)` holds of a pool register
  that is in `pins`, has no word and is not R10. `Homes::uses(r)` is
  `lives(r) || pinned(r)`, so a pinned register is out of the leaf pool
  and in `taken`, and every existing rule preserves it with no new case.
- `Target.pinned` is what the pinned registers held when the activation
  was entered, and `Target::Agreeing` has a third clause, `Target::Pins`:
  each pinned register reads as that value. `main`'s are the registers the
  process started with.
- A procedure saves RBX and every one of RBP and R12 to R15 it does not
  pin (`Homes::kept`). The registers of the callee-saved five therefore
  split three ways: a word lives there (saved), pinned (untouched, not
  saved), or neither (a leaf's scratch, saved).
- The contract of a callee (`Target::Ends`) is System V's: all of RBX, RBP
  and R12 to R15 come back as they were. The callee proves it from its
  pops for the registers it saved and from `Target::Pins` for the rest
  (`Target::kept_all`). A caller no longer reads the callee's homes to
  know what survives a call (`Homes::returned`), which is what lets the
  two have different homes.

### 6.3 F2: a placement per procedure

`Source::compile(low, homes, bodies)`: `homes` are `main`'s, and `bodies`
is a `Frame` per procedure (`of`, `loops`, `pins`, `words`). The two are
separate arguments and not one record: every theorem about the
allocation's check is stated over `Homes`, and stays as it was.

- `Layout.bodies` holds the placements, `Layout::body(i)` is the layout
  procedure `i`'s code is compiled with (`List::procedures_code`), and
  `Target::called(i, …)` is the activation that runs it:
  `t.called(i, …).layout() = t.layout().body(i)` by `refl`.
- `Procedure::fits` also asks that the frame's homes are in the pool and
  that `words <= reserved`: the data offsets read `reserved`, so a frame
  may not pass it.
- The allocator colours `main` alone (`Greedy::colouring`) and each body
  alone (`Greedy::frame`, under the source's loop sets), then pins as many
  spare callee-saved registers as the body's leaves leave free, found by
  the scan (`Frame::pinning`, `Source::bodies`). A body's colouring the
  check refuses gives way to its slots, as `main`'s does.
- `write-elf` reads the placements on the fork (`List::frames_spelled`),
  spells them and each procedure's layout as literals, and holds each
  layout to `Layout::body` once (`{p}_layout_b{i}_is`).

One thing to know when touching `Target::layout`: it is one constructor
application (`Layout::tabled`), not a chain of `with_…` calls. A `match`
on a call that takes `t.layout()` abstracts its scrutinee from the goal
after unfolding, and a third wrapper around the layout made the leaves'
proofs stop finding it.

### 6.4 F4: the bound by the call graph

`Source::need(homes, bodies)` is what a program needs of its stack under a
placement, and the `deep` premise of `native_compile_correct` and of the
ELF theorems is `src.need(homes, bodies) <= stack.size`. It is §2.5's
`need`, built as §2.5 says to compute it:

- `Frame::level(places)` is one activation: `8 * words`, 8 for each
  register of `Homes::kept` and the return address.
- `Stmt::performed()` lists the procedures a statement performs, and
  `List::performed_by(i)` those of procedure `i`'s body.
- `List::deep_row(bodies, places, d)` has, for each procedure, the most
  its calls take with `d` levels of room: a row from the row before
  (`List::deepest` over the body's callees), so the table costs the depth
  times the call sites. `List::reach(procedures, bodies, places, d)` is
  the same for a list of callees, and nothing at `d = 0`.
- `need` is `main`'s `reach` at the source's depth, the functions' room
  (`program_calls_room`, unchanged), and `8 * (words + 1)` for `main`.

**How the proof knows which procedures a body calls.** Nothing is
threaded through `Stmt::emit_runs`. `Layout.callees` (and
`Target.callees`) names the procedures the running body may call:
`main.performed()` in `Source::layout`, the procedure's own in
`Layout::body`. `Layout::call_fits` refuses a call of any other, and
`Target::Calls` already hands a call's `call_fits` to the proof, so a call
arrives with `callees.holds(index)` (`CallFits.allowed`). `Target.roomy`
is `callees.reach(procedures, bodies, places, room)` plus the floor it
always had, and `List::reach_call` is the one step: a listed callee's
level and its own `reach` at one level less are within the caller's.

**The depth counts in a word, said on its own.** The old bound charged
every level at least a byte, so `depth * … <= stack.size` kept the depth
below `2^64` for the counter. The new bound does not grow with the depth
where nothing recurses, so the theorems take `small: src.depth <
Nat::pow(2, 64)`; a certificate gives it by evaluation.

**What it is not yet.** The floor is still added, not maxed: the
functions' room and a word sit below the deepest call even where the
deepest procedure calls no function. That is at most one function's room
too much. A premise free of
the placement (`need` is at most the old bound) is not proved; nothing
uses one. `need` over frames that are not literals is costly to
evaluate (`src.bodies()` runs the allocator's scan at every use), so a
test states it over `SpillAll().frames(src)` or a literal.

### 6.5 F5: the functions' room table is the homes'

`Homes.rooms` is the room table the functions are emitted under, function
`f`'s room at entry `f`. `Prog::links(functions, places, rooms, names)`
takes it, and `Homes::calls_room(functions)`, the largest room and the
CALL's word, is the functions' term of `Target.roomy` and of
`Source::need`. The table is a choice, as `places` is: the function
compiler checks each function against it (`Function::roomy`), so the
proofs are stated over any table and nothing new is proved about one.

- With no table (`rooms = []`), `Homes::room_table` is `program_rooms`,
  the table no placement exceeds: every function saving six registers and
  calling with eight slots. That is what the bound was before, and what
  `Source::homes()` and a test's `Homes::slots(src).placed(…)` still get.
- `write-elf` reads `program_rooms_planned`, the table its places ask
  for, on the fork and spells it in the homes' literal. A leaf that saves
  nothing then asks for no stack below its return address.

The table cannot be computed from `places` inside `links` without planning
or emitting the functions first: where one function's places end in the
list is known only by emitting it. So it is stated beside the places, by
whoever chose them.

The issue's other loose end, the optimizer's `Function::lowers` and its
probe in `verified.rs` under `index_rooms()`, is left as it is. That call
asks whether a placement lowers, yes or no, and reads nothing of the room;
a smaller table would cost a table's evaluation at every probe and change
no answer.
