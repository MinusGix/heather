# Register allocation for the native compiler — design

Status: **landed 2026-10-28.** Owner: `issues/native-register-allocation.md`.
Code: `lib/native/native_alloc.hthr` (homes, liveness, the check, the
allocators), `lib/native/native_compile_homes.hthr` (the invariant and the
check's soundness), and the compiler and its proof
(`native_compile*.hthr`), which now take the homes as an input.

## 1. What changes

The S3.2 compiler (`docs/native-effect-source-design.md` §7.4) kept the
whole environment in memory. Every statement loaded each word it read from
its slot and stored each word it wrote, with RBX holding the slot's address.
The proof was simple, and code size and time were what it cost
(`issues/native-compiled-code-shape.md`).

This round gives every word a **home**. A home is either the word's slot or
one register of a small pool, and it holds the word between statements. An
**allocator** proposes the homes. It is untrusted: the compiler **checks**
whatever homes it is given, by evaluation, and `native_compile_correct` holds
for every assignment the check passes. The proof covers all assignments at
once, so no program needs a proof of its own. If every word stays in its
slot, the compiler emits what the memory-resident compiler emitted, minus
the stores of words that nothing reads afterwards. A spill is therefore not
a separate path: it is the same path with that word's home set to its slot.

What this round does not do: moves between homes, a calling convention,
homes that change from one program point to another, and per-statement
clobber sets. §8 lists them.

## 2. Homes

```text
inductive Home { InSlot, InReg(k: Nat) }
fn home_pool() → List<Gpr> { [R12, R13, R14, R15, Rbp, R10] }
record Homes { of: List<Home>, loops: List<List<Nat>> }
```

`of` is indexed by word id. A word past the end of the list lives in its
slot. `loops` is each loop's live set, indexed by the word the loop tests
(§3).

The pool is every general register that no statement's code uses for
anything else:

- it excludes RBX, the address register;
- it excludes RAX, RCX, RDX, RSI, RDI, R8, R9 and R11, the call and leaf
  scratch, which includes the registers Linux's SYSCALL writes (RCX, R11,
  RAX);
- it excludes RSP.

So a home register changes only when its own word is written. That is why
the invariant needs no per-statement clobber sets (§8).

A leaf that goes through S4 whole takes its registers from those no word
lives in (`Layout::leaf_pool`, computed once per compile). Every home
register a program uses is one fewer register for its widest leaf. When a leaf does not fit, the compiler
takes it a node at a time, as before.

## 3. Liveness, and loop sets as part of the allocation

A word is **live** at a point when a later read may see the value it holds
there. `Stmt::live_in(homes, out)` computes this backwards over the
statement tree from what is live after the statement. A call reads its
arguments and writes its result. A leaf node reads its ports and writes its
own id. A `Branch` takes the union of its arms.

A `Repeat` needs a fixpoint, and that is where the cost was. Growing each
loop's set inside the check made the trusted evaluation iterate, and nested
loops multiplied the iterations. The check on cat alone ran past the
kernel's per-declaration fuel. So the sets are now **part of the
allocation**: `Homes.loops` holds them, and `Homes::loop_set(again)` reads
one (empty when absent). Liveness takes the set as given:

- `Repeat(body, again).live_in(homes, out)` is the set;
- what is live after the body is `loop_after(again, set, out)`, that is, the
  tested bit, the set again, and what is live after the loop
  (`Stmt::loop_out`).

The check asks only that the set is **closed**: what the body needs at its
head, given that, is within the set. That takes one pass over the body.

The untrusted side computes the least closed sets the usual way: it starts
from empty sets and runs a pass of the check's own liveness, joining each
loop's entry with what its body needs at its head (`Stmt::needs`), until a
pass adds nothing (`Homes::closed`). A wrong set cannot cause a wrong
compile:

- a set that is too small is not closed, and the check refuses it;
- a set that is too large is sound, and only keeps more words alive.

Two loops that test the same word share one entry, so its set must be
closed for both. Growing all the sets together under the check's liveness
gives exactly that. A first version grew each loop's least set on its own
and joined them afterwards. `yes STR` has two loops on one word, and the
join left a loop nested inside one of them with a set that was not closed:
its live-out had grown with the joined set. The check refused, as it
should. A shared entry is still imprecise, because each loop keeps the
other's words alive (`issues/native-loop-sets-by-loop.md`).

## 4. The check: the only trusted part

`Stmt::checks(homes, out)` is the specification:

- **Every write is apart from what is live after it.** When word `id` is
  written and `out` is live afterwards, no other live word shares `id`'s
  register (`Homes::apart`). A leaf is checked both ways the compiler may
  take it, whole and a node at a time.
- **Every loop's set is closed**:
  `body.live_in(homes, after).within(set)`, with `after =
  loop_after(again, set, out)`, and the body's own checks at `after`.

`Source::allocation_ok(homes)` adds two conditions:

- `homes.fits()`: every register home is in the pool;
- the words live where `main` starts are in their slots, which start at
  zero.

`Stmt::checks` asks the rest of a `Then` for its live set at every level. So
the compile evaluates `Stmt::checked`, which computes each set once and
returns it, or `None` when a check fails. `Stmt::checked_sound` and
`Homes::nodes_checked_sound` prove that the set it returns is `live_in` and
that `checks` holds. `Source::allocation_sound` gives the proof
`fits ∧ slotted(main.live_in(homes, [])) ∧ main.checks(homes, [])`.

`Source::compile(low, homes)` refuses homes that fail the check.
`Source::refusal` reports this as reason 12, which write-elf names as a bug
in the allocator.

## 5. The invariant

`Target::Placed` (the memory's half) is unchanged. It holds a file of words
in the region with the buffers and the command line. `Target::Held(live,
env, g, m)` adds the registers:

- some file `words` is placed;
- every live word reads as the environment's own from its home:
  `Homes::number(id, words, home_values(g))` is its slot's entry, or its
  register's value (`Homes::Agrees`);
- a dead word may hold anything.

Registers enter the invariant only through `home_values(g)`, the pool's
six registers read in order. So any write outside the pool keeps `Held` by
evaluation. Only three kinds of pool write need a lemma:

- a home's own write (`held_reg_set`);
- a write to a register no word lives in (`held_unused`);
- code that keeps every register a word lives in (`held_kept`, used by S4's
  leaves).

`Target::At(at, live, tree, env)` and `Target::Runs(s, call, out, p, q)`
take the live set. A statement run from `out` reaches the end of its code
with `Held` at `s.live_in(homes, out)` on entry and `out` on exit:

- `at_sub` widens a live set;
- `goes_repeat` is generic in the set, with the closure as a hypothesis;
- `emit_runs` takes `s.checks(t.homes, out)`.

A loop inside a statement's code, such as a read's copy into its buffer or
an open's path copy into scratch, writes memory and scratch registers. It
runs over the region as placed with the slots' words, and its invariant
carries the pool's values unchanged (`home_values(g) = vals` in `CopyAt`
and `PathAt`). So when the loop ends, the live words are rebuilt as held
from the same file and the same registers.

Emission (`native_compile.hthr`) reads and writes words through
`Prog::word_to` and `Prog::word_from`:

- **A read** loads from the slot, or copies from the home register through
  RBX. RBX is written either way, which keeps the leaf lemmas unchanged.
- **A write** stores to the slot or moves into the register, and only when
  the word is live afterwards. **A write to a dead word is dropped**, and
  that is where most of the gain comes from on a spilled program.

## 6. Allocators

```text
record Allocator { assign: Source → Homes }
fn Allocator::spill_all() → Allocator   // every word in its slot, least loop sets
fn Allocator::greedy() → Allocator      // weighted greedy colouring
fn Source::homes(self src) → Homes      // what write-elf uses: greedy
```

`greedy` first computes `Homes::slots(src)` (least loop sets, everything
in a slot). One more pass builds the interference graph (`Stmt::graph`): two
words interfere when one is written while the other is live after the
write. The graph is a row of flags per word, so adding a write never
searches a list of ids. The greedy allocator then weighs each word by its
reads and writes, with a loop body counting seven more per level than what
holds it. Taking the words heaviest first, it gives each one the first pool
register that no interfering word already has. A word live at the start
keeps its slot.

Every table here is built lazily, one `put` at a time. A row read after
thousands of writes would otherwise force thousands of `put`s nested inside
each other, and that runs past the evaluator's depth limit. The reader
reports it as running out of fuel, which is how the 8×-cat probe first
failed. So each `put` is settled as it is made: its spine and the entry it
changed are forced by a match.

**Why a record, not a class with proofs yet.** Minus suggested making the
allocator a type class whose instances prove properties, so that it can be
swapped or tuned. The check already makes soundness independent of the
allocator, so no instance has to prove that its homes are correct. What an
instance *could* still prove is **completeness**: its homes never fail the
check (`∀ src, src.allocation_ok(assign(src))`). Then reason 12 would be
unreachable for that allocator by proof, not only by testing. `spill_all`
is the natural first instance, but its proof needs `Homes::closed` to
reach a fixpoint within its fuel, which is a real lemma about the pass's
monotonicity. The record is the class's data half, and the move is filed as
`issues/native-allocator-class.md`.

**Per-function allocators.** The interface does not rule them out, and
nothing in the check assumes one allocator. A source has a single `main`
today, inlined helpers included, so "per function" has nothing to range
over yet. When procedures that call each other arrive (plan §7), each
procedure will carry its own `Homes`, checked against its own body. The
procedures then compose through a **boundary contract**: which pool
registers a callee may write (caller-saved) and which it keeps
(callee-saved), and where arguments and results go. With that contract in
place, two procedures can use different allocators, as long as each one's
homes pass its own check and the call site's `Held` is re-established
under the contract. The calling convention is filed with the moves
(`issues/native-register-moves-and-convention.md`), and per-function
allocators with the class.

**Where the allocator runs.** The greedy allocator, evaluated in the
kernel, costs more than one declaration's fuel on cat. So write-elf
evaluates it on its fork, where the read fuel is large. It spells the result
(`Homes::spelled`) as a literal `{p}_homes()` in the certificate. The
certificate proves `{p}_allocated(): allocation_ok(homes).IsTrue()` by
evaluation, so the kernel sees only the check. `native_cat_compiled` spells
cat's homes in the same way. Moving the heuristic into Rust would cost
nothing in trust (`issues/native-allocator-cost.md`).

## 7. Costs, as shapes

- **The check** is one pass over the statement tree. Each node does list-set
  work over the live set, and the kernel's unary `Nat` comparisons make
  that the constant factor. The check is linear in program size times live
  set size, with no fixpoint and no nesting factor.
- **Emission** reads the leaf pool and the registers words live in from
  `Layout`'s fields, which `Layout::of` computes from the homes once per
  compile (`Layout::of_pool`, `Layout::of_taken` say they are the filters).
  Recomputing them at every leaf and node had dominated emission's growth
  over the memory-resident compile and taken cat's single-`refl` compile in
  `native_cat_compiled` close to the kernel's per-declaration fuel
  (`issues/native-leaf-pool-per-leaf.md`).
- **The check in the certificate** is one `refl`
  (`{p}_allocated`). It grows linearly with the program and is the
  certificate's largest single item at eight times cat
  (`issues/native-allocator-cost.md`).
- **The greedy allocator** makes a few liveness passes (one per level of
  loop-set propagation) and one graph pass. Each is linear in the program,
  and a write costs its live set times the word count. It runs only on
  write-elf's fork, and the compile tests check with slot homes for the
  same reason.
- **write-elf** gains one `{p}_o_{id}` definition per part (that part's
  live-out). The joins take it, and its cost per part is the live-in of one
  statement.

## 8. Results

Code bytes and ELF file bytes, with the memory-resident compiler
("before") and with greedy homes ("after"). The before figures are from
master `a3cd402`.

| program | code before | code after | ELF before | ELF after |
|---|---|---|---|---|
| cat | 1192 | 758 | 1424 | 990 |
| tr | 1847 | 1170 | 2079 | 1402 |
| yes | 1011 | 733 | 1243 | 965 |
| echo | 2648 | 1822 | 2880 | 2054 |

That is roughly a third off each program. The four rebuilt binaries were run
and behave as before. Probe sizes for programs without a built binary:

| program | before | after |
|---|---|---|
| wc | 1108 | 784 |
| head | 1140 | 795 |
| yes with args | 2768 | 2132 |

## 9. Not done, each with an owner

- **Reading a home in place.** `word_to` copies a home register into the
  target through RBX, two moves. A direct move, or an S4 leaf that reads its
  inputs in their homes, would save both
  (`issues/native-homes-read-in-place.md`).
- **Moves and a calling convention.** A word keeps one home for the whole
  program. Splitting a word's live range, and moving it between homes at
  loop edges and around calls, comes with procedures
  (`issues/native-register-moves-and-convention.md`).
- **Per-statement clobber sets.** The pool excludes everything any
  statement may use. Knowing what each statement clobbers would let the
  pool grow to RSI, RDI, R8 and R9 across statements that don't use them
  (`issues/native-statement-clobbers.md`).
- **One loop set per loop**, not per tested word, so that loops which
  share a word stop keeping each other's words alive
  (`issues/native-loop-sets-by-loop.md`).
- **Completeness by proof**: the allocator class
  (`issues/native-allocator-class.md`).
- **Emission's constant factor**, the leaf pool recomputed per leaf
  (`issues/native-leaf-pool-per-leaf.md`).
- **The allocator's own cost** (`issues/native-allocator-cost.md`).
- **The narrow leaf's register cap.** A leaf over the 12 registers left
  beside two home registers goes node at a time, or is refused when it is
  narrow. That refusal existed before at 14 and is now at 12;
  `narrow_long_leaf` pins it. It is owned by the existing
  `issues/native-compile-wider-leaves.md`.
