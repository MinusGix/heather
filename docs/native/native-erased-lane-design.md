# A native lane for answers that are checked afterwards

Status: **a design proposal, 2026-11-19**, for Minus's review; nothing is
built. It follows `docs/native/dogfooding-plan.md` §8 (question 3, answered
yes on 2026-11-19 under two conditions: done properly and not as a
fragment, and no bootstrapping chokehold). It extends
`docs/infrastructure/untrusted-evaluator-design.md`, whose machine it
replaces in time, and it changes no principle of
`docs/compilation-vision.md`.

One claim of the plan's discussion is corrected here, in §4: the lane
cannot go through FunctionIR and its proved lowering.

## 1. What the lane is

Some of what the tools evaluate is never trusted: an optimizer's search, the
bytes a lowering emits before a certificate states them, a tactic's or a
generator's run. Today `crates/run` interprets that work. The lane compiles
it to x86-64 instead, by a compiler written in Heather, and runs the
compiled code where the interpreter ran.

It has the trust the interpreter has and no more. Nothing it compiles
publishes a `Compile` instance, so no certificate can cite its code. Its
answers are checked by what checks the interpreter's now: the replayer, a
certificate's literals, the kernel's check of a tactic's term.

What it is for:

- **The compiler running on itself.** The optimizer, `Source::compile`, the
  `runtime fn` generator and the tactics written in Heather are the largest
  Heather programs there are. They become the lane's daily load.
- **The compile-time bar.** Reads are the largest part of a compile and run
  in a tree walker.
- **Learning the runtime before proving it.** What a constructor's cell, a
  closure and a count should be is found out under that load, and the
  proved setup's rungs 3 and 4 are then proofs of a design that has been
  used.

## 2. Its language is the erased core, all of it

The interpreter already defines the language: `Machine::erase` turns a core
term into a `Code` of eighteen forms (variables, functions and applications;
calls of definitions; numbers, successor and `elim_Nat`; pairs and their
projections; sums and `case`; tree nodes and their eliminators; `let`; unit
for every type, level and proof). Its meaning is what the machine computes,
call by need.

"Properly" is then a statement that can be checked: **the lane takes every
`Code` the eraser produces**, from its first version. That is affordable
because the language is small. The first version is complete and naive; the
later ones are faster. No form is left to a fallback by design. The
fallback of §7 is for budgets and for defects.

Two things the interpreter leaves stuck are in scope, because the compiler
needs them: a number past a machine word (numbers become unbounded, §3),
and a run that nests deeply (the lane's stack is the process's, with a
guard, and recursion over a number is a loop wherever §6 can make it one).
Codata and quoted code stay out until a customer runs them.

### Why the erased core and not something higher

A typed, first-order language with `match` and direct recursion, read from
the surface as `rt` is, would give better code with less work per function.
It would also be a second reflection of every feature, and a fragment by
construction: what the reflector does not read does not run. The erased
core is what every definition already becomes, so coverage is the
eraser's, which exists. The cost is that recursion arrives as eliminators
with an induction hypothesis, which §6 has to turn back into loops and
direct calls. That is the right trade for a lane whose point is to run
everything.

## 3. Values and memory

- **A value is a word.** A small number is in the word. Anything else is a
  pointer to a cell: a closure (code and captured values), a suspended
  computation, a pair, a sum's side, a tree node, a large number.
- **Call by need, as core is.** An argument, a field and a recursive answer
  are each computed when first read and once, so a suspended computation is
  a cell that is overwritten with its value. This is not optional: an
  eliminator is handed the hypothesis for every child, and only laziness
  keeps a step from running the ones it does not read.
- **Counts.** A cell carries a reference count, as the interpreter's values
  do, so a walk holds what is live and not what it has done. Counting is
  deterministic, which the fixpoint of §8 needs, and it is what later lets
  a constructor reuse a cell whose count is one, the lane's version of the
  `Unique` fact. A read may instead run in an arena that is dropped whole;
  that is a setting per run, measured, not a second design.
- **Numbers.** One word while they fit, limbs past it. The limb arithmetic
  is `crates/numeral`'s, which the plan ports as its second target, so the
  lane and the proved fragment meet there.
- **Named arithmetic stays.** The interpreter's `Prims` (a library
  definition over numbers run directly, compared with its own body on small
  numbers before it is believed) carries over unchanged. It is the first
  case of something larger (§6, representations).

## 4. Where it joins the existing compiler, and where it cannot

In the plan's discussion I said the lane would share FunctionIR and the
proved lowering, with only layout, closures and memory unproved. That was
wrong, and the note says so plainly because it was part of the argument.

FunctionIR is total, pure regions whose calls are to earlier functions by
number. The lane needs a call through a pointer, a cell that is
overwritten, and recursion that is not a loop. None of those is a node, and
adding them to FunctionIR would put unproved forms into the proved
compiler's language, which is the leak the lane must not have.

What the lane shares instead:

- **The assembler**: `Asm` items, labels and their landing, the instruction
  encodings, the ELF writer. The lane emits `Asm` directly.
- **Instructions as rows** (plan §5.3a). The lane needs encodings the model
  lacks: a call and a jump through a register, loads and stores at a
  displacement, multiply and divide. A row with a meaning serves both
  sides; the lane uses its encoding, the proved fragment its obligation.
- **The runtime system.** Allocation, counts, limbs and the copy loops are
  small functions over words and spans. They start in Rust (§9, stage 1),
  because the proved fragment cannot write them yet, and each is replaced
  by a proved `runtime fn` as rungs 1 and 2 reach it. Those replacements
  are ledger rows.

So the lane and the proved setup are two compilers above the assembler, on
purpose, and they converge from below (rows, the runtime) and from above:
a function leaves the lane when the proved setup can compile it, and the
proved setup's rungs 3 and 4 take their data layout from what the lane
settled. The guard against a permanent second compiler is therefore not a
shared pipeline. It is that the lane never gains a certificate, so
everything that is to be trusted has to come up the other side.

## 5. The compiler is Heather, and how its output runs

- **Its input is data.** `Code` becomes a Heather inductive, and a host
  request hands a generator the erased definitions reachable from a set of
  entries. The compiler is an ordinary Heather function from that program
  to `Asm`, in `lib/native/erased/`.
- **It runs first on the interpreter**, and then on itself (§8).
- **Its output is not checked in.** A compiled program is a
  position-independent blob in the native store, keyed by the hash of the
  definitions it was compiled from and of the compiler that compiled it. A
  miss compiles; a hit maps the blob and calls it. This is the difference
  from `crates/linked`, whose generated assembly is in the repository and
  is linked into the binary that would regenerate it
  (`issues/linked-assembly-bootstrap.md`).
- **It runs in the `heather` process**, on a thread of its own as the
  machine does, mapped read and execute only. A tactic's or generator's
  tree is read through the same `Values` trait, which gains a third
  implementation beside the kernel's and the machine's.
- **Budgets.** The machine counts steps and nesting. Compiled code counts
  at calls and at loop heads against a budget in a register, and has a
  guard page under its stack; past either it stops with `Stuck`, and the
  caller falls back.

## 6. From complete to fast

The first compiler is the machine's own rules, compiled: every application
through a pointer, every binding suspended. It is expected to be several
times the interpreter's speed and no more. Each step below is untrusted
like the rest, and is held to the naive compiler and to the interpreter by
the comparison of §7.

1. **Known calls and arity.** A call of a definition at its full arguments
   is a direct call with the arguments in registers.
2. **Strictness.** A value that is certainly read is computed at once and
   never suspended. Numbers first: most of the steps are arithmetic.
3. **Recursion as written.** An eliminator whose step applies the
   hypothesis to a child is a direct recursive call, and one that does so
   last is a loop. `elim_Nat` over a counter is a loop.
4. **Cells reused in place** where the count is one.
5. **Representations.** A library type may register a native
   implementation, as a number's arithmetic is named today: `NatMap` as an
   array, a `List<u8>` as a span. Each is compared with the definition as
   written before it is believed, as `Prims` are. This is where the largest
   factors are, since a map lookup through a trie is hundreds of steps, and
   it is `datarepr`'s idea without the proof, which follows.

## 7. Staying honest: the comparison

`HEATHER_READS` gains the lane: `native`, and `check`, which runs the
native code and the interpreter and refuses a read or a tactic step they
differ on. A whole-library sweep under `check` is the lane's acceptance
test at every stage of §6 and stays in the long lane. A difference is a
defect to fix, never a path to keep: a stuck or refused native run falls
back to the interpreter, reports itself under `HEATHER_READ_TRACE=1`, and
is counted, and a rising count fails the sweep.

## 8. No bootstrapping chokehold

The rules of the plan's §8.2, made concrete.

- **Stage 0 is the interpreter**, kept and tested for as long as the lane
  exists. `HEATHER_READS=interp` runs everything on it. `heather` builds
  with no native blob present and no generated file in the tree.
- **Stage 1** is the lane's compiler run on the interpreter, compiling
  itself. **Stage 2** is stage 1's code compiling the same source. The two
  blobs must be the same bytes. The nightly sentinel checks it, and a
  change to the compiler is merged with the fixpoint shown.
- **Determinism is a requirement of the compiler**, since the fixpoint
  needs it: no addresses, no iteration order of an unordered table, no
  clock in what it emits.
- **A bug cannot be inherited.** A blob is keyed by its compiler's hash, so
  a new compiler never runs on blobs an older one made of it without
  rebuilding from source on stage 0. What a miscompiling stage 1 emits
  differs from what the interpreter-run compiler emits, which is the
  comparison of §7 applied to the compiler itself.

## 9. Order of work

Each stage ends with something that runs and a measurement.

1. **The forms the assembler lacks** (a call and jump through a register,
   displaced loads and stores, multiply), as rows where the row mechanism
   exists and as encodings where it does not yet. **The runtime in Rust**:
   allocate, count, free, limbs through `crates/numeral`, the host calls.
   `Code` as a Heather type and the host request that hands it over.
2. **The naive compiler**, all eighteen forms. Acceptance: the
   whole-library sweep under `check` with no fallback.
3. **The fixpoint**, in the sentinel. From here the compiler compiles
   itself daily.
4. **Fast**, in the order of §6, each measured on the reads of one compile
   (`scripts/perf ab`) and held by `check`.
5. **The runtime moves into Heather**, a function at a time, as the proved
   fragment's rungs reach it; `crates/run` retires when the lane has run
   the suite for a settled time with no fallback.

Stages 1 and 2 need nothing from the proved fragment's rungs and can start
beside them.

## 10. Questions for Minus

1. **The runtime in Rust at first?** It is the fast way to stage 2, and it
   is a second stopgap after `crates/run`. The alternative waits on rungs 1
   and 2. Recommended: Rust first, each function a ledger row to replace.
2. **Counts or arenas as the default?** Recommended: counts, for
   determinism and for reuse in place; an arena per read as a measured
   setting.
3. **Compiled code in the `heather` process?** It is our compiler's output
   from our library, cached by hash, mapped without write. The alternative
   is a child process per run, which costs every tactic step a round trip.
   Recommended: in process.
4. **The erased core as the lane's only input** (§2), accepting that
   recursion has to be recovered from eliminators. Recommended: yes.
5. **What "fast enough" is.** Proposed: the reads of a SHA-256 compile in
   seconds, and a tactic's run no longer visible in a declaration's time.

## 11. What this does not do

- It proves nothing, and says so everywhere it prints.
- It does not compile users' programs: `compile-x86` and `write-elf` emit
  only what the proved compiler emits.
- It adds no form to FunctionIR or `rt`.
- It does not remove `crates/run` until stage 5.
