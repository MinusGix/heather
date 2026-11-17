# Register allocation for the native compiler — design

Status: **landed 2026-10-28.** Owner: `issues/native-register-allocation.md`.
Code: `lib/native/native_alloc.hthr` (homes, liveness, the check, the
allocators), `lib/native/native_compile_homes.hthr` (the invariant and the
check's soundness), and the compiler and its proof
(`native_compile*.hthr`), which now take the homes as an input.

## 1. What changes

The S3.2 compiler (`docs/native/native-effect-source-design.md` §7.4) kept the
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
inductive Home { InSlot(k: Nat), InReg(k: Nat) }  // a slot by its index since native-procedure-frames-design.md §6.6
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
class Allocates<A> {
    assign: A → Source → Homes,
    never_refused: (a: A) → (src: Source) → src.allocation_ok(assign(a, src)).IsTrue(),
}
record SpillAll {}                      // every word in its slot, least loop sets
record Greedy { loop_weight: Nat }      // weighted greedy colouring, slots as fallback
fn Source::homes_by<A: Allocates>(self src, a: A) → Homes
fn Source::homes(self src) → Homes      // what write-elf uses: Greedy::standard() (weight 7)
```

An allocator is a type with an `Allocates` instance, and a tuning is a value
of that type (`Greedy(3)` weighs loops less than `Greedy::standard()`). The
class follows Minus's suggestion (2026-10-28) that the allocator be a type
class whose instances prove properties, so that it can be swapped or tuned.

**The law is completeness, not soundness.** The check already makes
soundness independent of the allocator, so no instance proves its homes
correct. What an instance proves is that the check never refuses them:
`∀ src, src.allocation_ok(assign(a, src))`. Reason 12 is then unreachable for
that allocator by proof, and since `Source::homes` is `Greedy`'s
(`Source::homes_ok`), it is unreachable for write-elf.

**`SpillAll`'s proof needs no fixpoint.** With every word in its slot, every
write is apart and every live word slotted by evaluation, so the check
fails only at a loop whose set is not closed. Proving that `Stmt::needs`'s
growth reaches a closed set within `closure_fuel` would need monotonicity
of liveness in the sets and a count of how far they can grow. Instead the
growth stays a heuristic, and what it stops at is checked once more
(`Source::closed_or_wide`). If the check refuses, or the fuel runs out, the
**widest sets** stand in: every word the program names
(`Stmt::words`) in every loop's set (`List::wide`). Those are closed for
every program (`Stmt::checked_wide`, one structural induction): everything
live is a word the program names, and every set holds all of them. On every
program so far the growth stops closed, so the result is the least sets as
before. The cost is one more check pass at the end, and the probes in
`lib/_tests/native/native_alloc_tests.hthr` pin both halves: the least set
leaves out a word written before it is read, and fuel 0 gives the widest.

**A heuristic made complete by a fallback.** `Greedy`'s colouring is not
proved to pass the check. Its `assign` checks its own homes and falls back
to the slots' when they fail (`Homes::or_else`, `Homes::or_else_ok`). That
is the general recipe for any heuristic that cannot be proved: an instance
in two lines, at the cost of one check pass. The price is that the proof
says nothing about the heuristic itself, and a colouring that failed would
fall back silently to a spilled program. So the probes check by evaluation
that greedy's colouring passes on its own and homes words in registers.

`Greedy`'s colouring first computes `Homes::slots(src)` (least loop sets,
everything in a slot). One more pass builds the interference graph
(`Stmt::graph`): two words interfere when one is written while the other is
live after the write. The graph is a row of flags per word, so adding a
write never searches a list of ids. The colouring then weighs each word by
its reads and writes, with a loop body counting `loop_weight` more per
level than what holds it. Taking the words heaviest first, it gives each
one the first pool register that no interfering word already has. A word
live at the start keeps its slot.

Every table here is built lazily, one `put` at a time. A row read after
thousands of writes would otherwise force thousands of `put`s nested inside
each other, and that runs past the evaluator's depth limit. The reader
reports it as running out of fuel, which is how the 8×-cat probe first
failed. So each `put` is settled as it is made: its spine and the entry it
changed are forced by a match.

**Per-function allocators.** Nothing in the class or the check assumes one
allocator for a program. A source has a single `main` today, inlined
helpers included, so "per function" has nothing to range over yet. When
procedures that call each other arrive (plan §7), each procedure carries
its own homes, checked against its own body, and so may carry its own
allocator: a procedure's allocator is any `A: Allocates`, chosen per
procedure (a hot loop's procedure tuned with a heavier loop weight, a cold
one spilled). The procedures then compose through a **boundary contract**:
which pool registers a callee may write (caller-saved) and which it keeps
(callee-saved), and where arguments and results go. Completeness composes
the same way soundness does: each procedure's homes pass its own check, and
the call site's `Held` is re-established from the contract, so a program
whose procedures each use a complete allocator is never refused for its
homes, whichever allocators they are. What the contract says is
`issues/native-register-moves-and-convention.md`'s. Whether two procedures
should share one allocator is then a tuning choice, not a soundness or
completeness question; early on every procedure can use `Source::homes`'s.

**Where the allocator runs.** The greedy allocator, evaluated in the
kernel, costs more than one declaration's fuel on cat. So write-elf first
evaluated it on its fork, where the read fuel is large; but a read keeps
every value it forces until it returns, and the allocator's memory grew
with the tool, past the 8 GiB rail on `wc` (round 9,
`issues/native-decimal-io.md`). write-elf now runs the same allocator in
Rust over the source it reads back (`crates/cli/src/native/allocator.rs`),
step for step and its lists in the same orders, so it proposes the same
colouring. It does not run the check, so `Greedy::assign`'s fallback is
write-elf's: the parts' check of the colouring is read before anything is
emitted, and if it refuses, the fork's homes stand in, which are then every
word in its slot (`Homes::or_else`). `HEATHER_ELF_ALLOCATOR=both` runs the fork's beside it and refuses
unless they agree, which `native_tools.rs` does for `tr`. This costs nothing
in trust: the homes are spelled (`Homes::spelled`) as a literal `{p}_homes()`
in the certificate, which proves `{p}_allocated():
allocation_ok(homes).IsTrue()` (by parts, §7), so the kernel sees only the
check. `native_alloc.hthr` stays the allocator's definition (`Greedy`,
the `Allocates` instance). `native_cat_compiled` spells cat's homes in the
same way.

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
- **The check in the certificate** is stated over the emission's parts
  (`{p}_ck_{id}`, joined by `Stmt::checked_then_of`/`branch_of`/`repeat_of`
  and `Source::allocation_of` in native_compile_correct): each part's
  `Stmt::checked` with its `out` and incoming live set as literals read on
  the fork (`Source::checked_spelled`), so no one `refl` grows with the
  program (`issues/native-tool-certificate-budget.md`).
- **The greedy allocator** makes a few liveness passes (one per level of
  loop-set propagation) and one graph pass. Each is linear in the program,
  and a write costs its live set times the word count. Evaluated, its
  memory grows with that work, so write-elf runs it in Rust, and the
  compile tests check with slot homes.
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
- **Per-procedure allocators**, once procedures exist (§6; with
  `issues/native-register-moves-and-convention.md`).
- **Emission's constant factor**, the leaf pool recomputed per leaf
  (`issues/native-leaf-pool-per-leaf.md`).
- **The allocator's own cost** (`issues/native-allocator-cost.md`).
- **The narrow leaf's register cap.** A leaf over the 12 registers left
  beside two home registers goes node at a time, or is refused when it is
  narrow. That refusal existed before at 14 and is now at 12;
  `narrow_long_leaf` pins it. It is owned by the existing
  `issues/native-compile-wider-leaves.md`.
