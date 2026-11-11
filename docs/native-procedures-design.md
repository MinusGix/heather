# Procedures in the native compiler — design

Status: **proposed 2026-10-31**, slice 1 landing with it; revised
2026-11-01 to caller-saves and a callee that starts from zero (§2, §3),
which is what the proof can carry. Slice 2 (the compile and its proof)
landed 2026-11-01. Owner:
`issues/native-compiled-procedures.md` (milestone `nh-procedures`, round R8
of `docs/compiler-milestones-proposal.md`). It draws in
`issues/native-procedure-contracts.md` and
`issues/native-register-moves-and-convention.md` where they are needed to
make a call compile, and leaves the rest of them open (§8).

`docs/native-procedures-are-functions-design.md` (proposed 2026-11-11,
round U5 of `docs/native-one-compiler-design.md`) keeps §1 and §2 of this
note, what a procedure is and what a call means, and proposes to replace
the convention, the compile and its proof (§3 to §5): words in a frame
of the activation, the callee saving, one contract with the function
compiler's. Until that round is built this note describes the code.

Today a native tool is a closed `Source` (`lib/native/native_source.hthr`)
whose procedures are Heather functions returning an `Act`, inlined where
they are called (`lib/native/native_build.hthr`). That has two walls: code
grows once per call site, not once per helper, and recursion that is not a
tail loop cannot be written at all. This note fixes what a procedure is in
the source, what a call means, how a call compiles, how the compile is
proved once, and the order the pieces land in.

## 0. Recommendation

- A **procedure** is a statement with parameters and results, kept in a
  table beside `main` (`Source.procedures`). A call is a new statement,
  `Perform(procedure, args, results)`.
- **A procedure's words are its own; buffers are shared.** A call starts
  the body with every word zero but its parameters, which get the
  arguments' words. When it returns the caller's words are as they were,
  but for the results, which get the body's result words. A procedure
  changes a buffer in place.
- **Calls nest at most `Source.depth` deep.** The call one deeper exits
  with a fixed status (`call_depth_status`, 139). This is the source's
  meaning, not a property of the machine, so the compiled code has nothing
  to approximate.
- The meaning is **by depth, not by fuel**: a call at depth `d` runs its
  body at `d - 1`, so the denotation is total by structural recursion on
  the depth and then on the statement. Fuel still bounds loops, as now.
- **Compiled, each procedure is emitted once**, after `main`, at a label of
  its own. A call is a CALL on the process stack (`X86Profile::process`,
  `StackPlaced`, PR #309). **The caller saves** the words it needs after
  the call (`out` less the results) by pushing them before the CALL, and
  pops them back into their homes after it. Words keep their one home each,
  as `docs/native-register-allocation-design.md` §2 fixed; the stack is
  where the caller's values wait.
- **A procedure reads only its parameters**: its body's entry set, with
  its results live after it, lies within its parameters. The compile checks
  it and refuses a procedure that does not.
- **The proof stays the one proof.** The words on the stack are a ghost
  list in the `Target`, read through an access above the current frame, as
  the command line is read above the stack's top. Every store a rule makes
  is below both, so no existing rule learns about the stack. A procedure's
  claim is `Stmt::emit_runs` at the callee's target: derived, never proved
  per procedure (the move `native-procedure-contracts` asks for).

## 1. The source

```heather
// A procedure: its parameters and results (word ids of its own) and its
// body.
record Procedure { params: List<Nat>, results: List<Nat>, body: Stmt }

inductive Stmt {
    …,
    // Procedure `procedure`, its parameters given the words `args`, its
    // results put in `results`.
    Perform(procedure: Nat, args: List<Nat>, results: List<Nat>),
}

record Source { functions, buffers, words, main,
    procedures: List<Procedure> := [], depth: Nat := 0 }
```

Ids are global: a procedure's words are ids of the one word file. Nothing
in the meaning needs them disjoint from the caller's, since the caller's
words come back whatever the callee wrote.

## 2. What a call means

```text
Perform(p, args, results) at depth d, env:
  d = 0:            Exited(call_depth_status)
  d = d' + 1:       let P = procedures[p]
                    let entry = (env, every word zero) with P.params := env's args
                    bind(P.body at depth d', entry, λ flow =>
                      Onward(e) => Onward(env with e's buffers,
                                            then results := e's P.results)
                      Exited(s) => Exited(s))
```

The parameters are set in order, each to its argument's word, all read
first, so a parameter named twice takes the later argument. The results
are set the same way, after the buffers.

`Stmt::denote` takes the meaning of a call as a parameter, a `Performs()`
handler, and is otherwise unchanged. `Source::performs(call, n, d)` is the
handler at depth `d`, by recursion on `d`. `Source::denote(args)`'s tree at
fuel `n` is `main` at depth `src.depth`. Fuel is shared by every loop at
every depth, as `Program::bind` shares it; `grows` is proved for any
handler that grows, and `performs` grows by induction on the depth.

**Why a depth and not fuel.** A tree cut at fuel `n` is a lower
approximation, and a machine meets the whole family only if it can do what
every fuel allows. No machine can recurse without bound in a finite stack,
so a fuel-cut call would make every compiled recursion unsound. A depth
that is part of the meaning is exact: the machine counts activations and
exits at the same call the source does. It is the same choice the heap
round makes for arena exhaustion (N4: "arena exhaustion as a defined
exit"). A program whose calls never nest past its depth never sees the
status, and the theorem's stack premise (§5) says how much stack that
needs.

**Why the callee starts from zero.** Seeing the caller's words would make
the callee's meaning depend on words its code cannot be shown to read
right: a word the caller holds dead has whatever its home last held, and no
claim can name that value as the environment's. Starting from zero, and
refusing a body that reads a word other than a parameter (§4.3), makes the
meaning and the code agree without a non-interference lemma.

*`mrec`*: the issue asked whether `mrec` over the fuelled `Program` spends
fuel per call. With a depth, the question disappears: the handler is
`mrec`'s unrolling at depth `d`, and no call spends fuel.

## 3. Words across a call: the convention

- **Arguments** go in RDI, RSI, RDX, RCX, R8, R9 (SysV's order), at most
  six; **results** come back in the same registers, at most six. None is in
  the home pool (`home_pool`, native_alloc), and the call's other code uses
  only RAX and RBX beside them.
- **Homes are global.** A word has one home for the whole program, in a
  register or its slot, as now.
- **Caller saves** (until U5's step 5b; see §4's note). At a call the caller pushes each word live after it but
  for the results (`out − results`, the set it needs back) from its home,
  and after the return pops each back into its home. The callee saves
  nothing, and its code may write any home.
- **Why not callee-saves.** The callee would have to keep every home its
  caller needs, and the only words a callee's claim speaks of are the ones
  live at its end: whether a body keeps a home it never names is not
  something any claim says, and saying it would take a frame property of
  every rule. Saving all of a procedure's own words (the first version of
  this note) leaves the same gap for the caller's words that the body
  passes through. The caller knows exactly which words it needs, and its
  claim says where each one is, so saving them there needs no new property.
  The price is a push and a pop per live word per call; a per-procedure
  clobber set that lets a caller skip words no callee touches is the
  refinement, `native-register-moves-and-convention`'s (§8).

## 4. The code

*Since 2026-11-11 (U5's steps 5a and 5b,
`docs/native-procedures-are-functions-design.md` §3) there is no `frame`
slot and the caller saves nothing: RSP is the frame, held in the claim
between statements; a word without a register lives in its activation's
frame there; and the callee saves the registers the program's homes use
and opens its own frame. §3's "why not callee-saves" was about static
slots, where a callee's code could write a caller's word; a frame above
the callee's RSP is out of its reach by the memory clause. What follows
describes the code before those steps; the `room` slot and the depth
test are as written.*

### 4.1 Layout

The data region gains two slots past the saved entry RSP: `frame`, where
the running activation's saved words begin, and `room`, how many calls deep
it may still go. The entry code stores the entry RSP into `frame` and
`src.depth` into `room`.

### 4.2 A call and a procedure

```text
caller:     RAX := [room]; TEST; JE deep      ; no room: exit(call_depth_status)
            [room] := RAX - 1
            RSP := [frame]
            each saved word: RAX := home; RSP -= 8; [RSP] := RAX
            each arg word into its argument register (word_to)
            CALL P                            ; return address pushed
            each saved word, last first: RAX := [RSP]; RSP += 8; home := RAX
            [frame] := RSP
            [room] := [room] + 1
            each result register into its result word's home (word_from)

P:          [frame] := RSP                    ; its frame: the return address
            each argument register into its parameter's home (word_from)
            body                              ; compiled with its results live
            each result into its result register (word_to)
            RSP := [frame]
            RET

deep:       exit(call_depth_status)
```

Body code may leave RSP anywhere (nothing proves it is kept, and nothing
needs it): `frame` is the truth, and every call and every return reload RSP
from it. A call's frame is `8 · (|out − results| + 1)` bytes, pushed and
popped one word at a time at `[rsp + 0]` (x86_64_stack's spill form), so
there is no limit on how many words it saves.

Procedure `i` is at label `i + 1`, the shared `deep` exit at label
`|procedures| + 1`, and `main` names its own labels from there, so a call's
target needs no table. Each procedure is emitted once, after `main`'s
closing exit; `deep` sits after the last one. `Prog::laid_out`'s one check
covers the CALLs as it covers the jumps.

### 4.3 What the check asks

- **The allocation** (`Source::allocation_ok`) is unchanged: it checks
  `main`. A call's liveness is its arguments and what is live after it but
  its results; its check is that the results are apart from what is live
  after it, as for any statement that writes words.
- **The compile** checks each procedure: its body's homes against its
  results live after it (`Stmt::checked`, with the source's homes), and the
  body's entry set within its parameters. A call is emitted only for a
  procedure there is, with as many arguments as parameters and as many
  results as it has, at most six of each, every word it names inside the
  word file, and each parameter apart from the parameters moved after it.
  Each refusal has a reason of its own in `Source::refusal`.
- Loops in a procedure's body use the source's loop sets as `main`'s do.
  The allocators compute them over `main` today, so a body whose loop has
  no set of its own is refused by the compile until the allocators cover
  procedure bodies (slice 4 needs it).

## 5. The proof

- **The stack in the `Target`.** `Target` gains the process's `Stack`
  (x86_64_stack), above the data region and below the canonical boundary,
  and the running activation: `frame` (an address in the stack), `frames`
  (the words from there to the stack's top: each call's return address and
  saved words, innermost first) and `room`. `Target::Stacking` reads the
  command line above the stack's top, and `Target::Framing` reads the
  `frame` and `room` slots and the frames above `frame`. Every store an
  existing rule makes is into the region, below both, so each rule keeps
  the two readings through `Target::stacking_store`; only `Stacking`'s
  projections are renumbered.
- **New rules**: CALL and RET (`native_compile_frames`), a push and a pop
  at `[rsp + 0]`, and the lemma that a store below an address keeps what is
  read above it (which a push needs for the frames above the frame, and
  every store for the command line above the stack's top).
- **The procedure's claim** is the body's `Target::Runs` at the callee's
  target, whose `frame` is the address of the return address the CALL
  pushed, whose `frames` are that address and the saved words on the
  caller's, and whose `room` is one less, with the result moves, the RSP
  reload and the RET as the continuation. It is proved for every procedure
  at once, by induction on the room: the `Perform` case of
  `Stmt::emit_runs` at room `d + 1` cites every procedure's claim at room
  `d`, and at room 0 the call exits through `deep`. That is the paper's
  linking theorem (Abate et al., `docs/wp-preserving-compilation-survey.md`
  §4, Theorem 3), by induction on the depth instead of Löb.
- **`native_compile_correct`** gains the stack: a `Stack` of the profile
  above the region, its top the entry RSP, the command line above it, and
  at least `8 · depth · (words + 1)` bytes deep. The ELF theorem's
  `StackPlaced` gives it, so a program whose depth needs more than 128 KiB
  of stack is refused by `write-elf`.

## 6. Why the stack holds the caller's words, not the callee's words

The issue's scope reads "a real frame per activation". The design keeps a
real frame per call on the process stack, but addresses a word at its home,
not at `[rsp + 8i]`. The alternative, a procedure's words living only in
its frame, would give every word load and store a stack-relative form, and
every rule of `native_compile_*` would have to prove RSP kept across its
code. Saving into the frame adds one push and one pop per saved word per
call and touches no existing rule. Words homed in the frame stay possible
later as a home kind (`InFrame(k)`) beside `InSlot` and `InReg(k)`, with
the frame's base in `frame`.

## 7. Slices

1. **The source** (this note's PR): `Procedure`, `Perform`, `Source.depth`,
   `Stmt::denote` over a `Performs()` handler, `Source::performs`, `grows`
   for both, the liveness of a call, and probes run by evaluation (a
   recursive sum that uses its parameter after the call, and the depth
   exit). The
   compile refuses `Perform` (`emit` is `None`), so the theorem is unchanged
   but for the handler it now quantifies over.
2. **The compile and its proof**: §4 and §5. Done when a source with a
   helper called from two sites and a non-tail recursion compiles and the
   compile is proved. Landed: the call site's code as claims of trees
   (`lib/native/native_compile_perform.hthr`), `Target::Hosts` (the
   program holds every procedure and the shared exit), `Source::calls_at`
   (every call at every depth, by induction on the depth, each callee's
   body by its own `Stmt::emit_runs`), and `native_compile_correct` for
   every source; probes in `lib/_tests/native/native_compile_tests.hthr`
   (one body, three call sites, and the refusals 14 and 15).
3. **`write-elf` and the builder**: a `proc` form in `native_build` whose
   words the builder numbers, `Source::spelled` and the Rust mirrors
   (`crates/cli/src/native`), and an ELF test that runs the recursion.
   Landed: `Source::spelled` spells `Perform` (tag 8) and a source with
   procedures (`[2]`, its depth after its words, its procedures after its
   buffers), and the Rust readback prints them. `write-elf` emits `main`
   from `Source::main_names`, reads the procedures' code
   (`List::procedures_reading`) and the shared exit after `main`'s exit,
   states the first by one `refl` and the second as `{p}_code()`, and
   proves the compile by `Source::compile_calls_of`. The builder has `proc`
   (a `Proc` gives the body its index and its parameters' and results'
   words, numbered from 0; the results are set to zero first, so a body
   reads no word but its parameters), `perform` and `depth`; a tool with
   procedures is lowered whole, as a literal, since the part-at-a-time
   lowering walks `main` only. The Rust allocator mirror walks `main` only,
   so a source with procedures is allocated on the fork. `procedures_run`
   (`crates/cli/tests/native_cat.rs`) runs the recursive sum, a call past
   the depth, and a builder tool summing its input by recursion.
4. **`grep -F`**, with the line-buffer helper a procedure, against GNU's
   tests under `LC_ALL=C`. Its helper loops, so the allocators' loop sets
   cover procedure bodies first (§4.3). Landed: the allocators pass every
   procedure's body after `main` (`List::bodies_needs` for the loop sets,
   `bodies_graph` and `bodies_weights` for the colouring), and the
   colouring falls back to the slots when a body fails the check
   (`Homes::or_else`). `write-elf` states each procedure's body a part at
   a time, as `main`'s (`Procedure::code_of`, `List::procedures_code_of`).
   `grep_f_tool` (`lib/native/native_tools.hthr`) tests and writes a line
   by one procedure called from two sites, and
   `compiled_grep_f_runs_as_gnu_grep` runs it beside GNU's. What is left
   for larger tools: `issues/native-procedures-write-elf-capacity.md`.

## 8. Left open, each with an owner

- Per-procedure clobber sets, so that a caller saves only the words whose
  homes its callee may write, and moves between homes:
  `issues/native-register-moves-and-convention.md`.
- A per-slot footprint and a relational frame for a `Proved` contract, the
  shared-counter control and the negative control:
  `issues/native-procedure-contracts.md`. This design derives the contract
  and needs no footprint, because the callee's words are its own by
  construction and buffers are shared.
- Words homed in the frame (§6): to be filed when a procedure needs them.
