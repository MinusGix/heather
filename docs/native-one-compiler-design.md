# One native compiler: joining `write-elf` and `compile-x86`

Status: **direction set by Minus 2026-11-11** ("unify first and then
export"); this note scopes it. U1, U2, the function compiler's half of
U3 and the placeless theorem a program's call needs are built (§3). Owner:
`issues/native-one-compiler.md`. It extends `docs/compilation-vision.md`
(§2.4's levels) and re-sequences `docs/native-library-exports-design.md`,
whose memory clause, lent spans and contract it keeps and whose rounds it
absorbs (§5).

## 0. Summary

There is one stack with two front doors. They share FunctionIR and the
verified lowering of a region to registers, and they have grown apart
above it. Three joints are missing, and the note closes them in order:

1. **A program cannot call a compiled function.** `Source` has functions
   in its meaning and its compiler refuses every `Call` region.
2. **Buffers exist on one side only**, and that side compiles byte nodes
   with its own code instead of the shared lowering.
3. **There are two kinds of call**: `compile-x86`'s System V functions and
   `Source`'s procedures, with their own convention and storage.

The end state is **one compiler of functions**. A function has a frame,
System V registers, buffers it is lent, and a body that may ask Linux for
things. A pure function is one whose body asks for nothing. A program is
`main` and a start-up. An export is a function called from outside. The
export then needs nothing built for it alone.

## 1. What each door has

Checked against the library on master, 2026-11-11.

| | `compile-x86` (functions) | `write-elf` (programs) |
|---|---|---|
| input | a `runtime fn`, reflected by `rt` to FunctionIR functions | a `Source`: statements over regions, Linux calls, loops, procedures |
| meaning | a word (`program_eval`) | an interaction tree over Linux's calls (`Source::denote`) |
| words live in | registers by a checked placement, a frame of spill slots | one global home each: a register of `home_pool` or a static slot |
| regions | the shared lowering, whole | the shared lowering for a pure leaf that qualifies, otherwise a node at a time |
| calls | System V: arguments in six registers, `callee_kept` kept, the callee's own frame; only to earlier functions, so depth is static | `Perform`: arguments in the same six registers, the caller pushes what it needs, the callee starts from zero, depth counted in the meaning (exit 139) |
| a FunctionIR `Call` | compiled (`function_ir_lower_calls`) | **refused**: "the builder inlines" (`StructuredRegion::code`) |
| buffers | none; byte nodes refused | static ranges of one data region; byte nodes by its own code, an index check and a load or store |
| claim | `Site::Returns`: a run to the return address with a post, over any memory `M` | `Site::Goes`: from here the machine runs as this tree, continuation-passing, over `X86Memory` |
| memory law | `Stack<M>`, and "the stack above the return address is unchanged" | the same `Stack` record, a `DataRegion`, and `Target::Placed` |
| theorem | `compiled_returns` | `native_compile_correct`: the process simulates the tree |

Two facts in the table decide the design.

**The doors already share the machine.** Both state their claims over
`Site`, `Prog` and the same `Stack` record. A `Returns` is a silent run, and
a tree claim absorbs silent runs; `write-elf` already makes CALLs and RETs
on that stack for its own procedures.

**Today's function theorem is too weak for a program to use.** Its post
keeps the stack words above the return address. A program calling a
function also needs its data region kept, the words' slots and every
buffer, and nothing says so. What is missing is exactly the memory clause
the exports note proposed: the stores a call may make. So the first step
of unifying and the first step of exporting are the same step.

## 2. The design

### 2.1 The memory clause is the stores a call may make

`Stack::Wrote(i, before, after)`: memory after is memory before under
stores into the callee's own room below its return address
(`docs/native-library-exports-design.md` §4, kernel-checked there). It
replaces `Unchanged` in the function compiler's post. From it follow the
caller's stack words, code residency, a lent span, and for a program its
data region, which lies below the stack.

### 2.2 A program's `Call` is a CALL

`Source.functions` are compiled into the program by the function compiler
and a `Call(callee, arguments, result)` region becomes: the arguments from
their homes into the argument registers, a CALL, RAX into the result's
home. The proof uses the function's `Returns` as a silent run.

- The home registers are R12 to R15, RBP and R10. A function keeps all but
  R10, so a word homed in R10 and live across a call is saved around it, or
  the allocator keeps such words out of R10.
- The room a callee needs is added to the stack premise the program's
  theorem already has.
- The meaning does not change: `Source::denote` already answers a `Call`
  by `program_eval(src.functions)`.

This is where the two doors first become one program: a tool whose helper
is a `runtime fn`, compiled once and called.

**How, settled against the code (2026-11-11).**

- *One `Prog`.* The program's code stays first, so its entry is offset
  zero; the functions follow (`emit_functions_after`). The function
  compiler's theorem is already about any site its code lies within
  (`MayCall`), so nothing is proved twice. Function `f` keeps the label
  `Succ(f)`; the program names its procedures, its deep exit and `main`'s
  labels past the functions' (`Layout.functions`), and the functions'
  inner labels start where the program's end.
- *The call.* RSP is loaded from the frame slot, as a procedure call
  does; the arguments go from their homes to the six registers
  (`Prog::words_to`); R10 goes to RBX, CALL, and back; RAX goes to the
  result's home. A function keeps RBX, RBP and R12 to R15, so with R10
  carried in RBX every home register is as it was, and no allocator
  learns anything.
- *The proof.* `Site::moves_call` against the function's `Returns` is a
  straight run, which a tree claim absorbs (`LinuxIo::goes_after`). What
  the program holds between statements (`Target::Held`) is kept by a
  word stored below its frame (`held_stack_store`), so it is kept by
  `Wrote` (`Star::invariant`): this is where U1 is used.
- *Room.* A function's own frame and its calls of other functions need
  stack below the activation that calls it, a fixed amount per function
  of the program. The theorem's stack premise grows by that: the depth of
  procedure calls times a frame, plus the functions' term
  (`Target.roomy`, and `deep` of `native_compile_correct`).
- *Checks.* The compile checks the functions evaluable
  (`program_evaluable`), each call's callee and arity, and that the
  result is apart from what is live after it; a region with a call is
  scoped like one with a node that reads the arguments and writes the
  result.
- *Placement.* Where a function's values go is the function compiler's
  proposal (`plan_program`), and it travels with the words' homes
  (`Homes.places`, `Homes::placed`): untrusted like them, checked by the
  functions' lowering (`Prog::links`). With none proposed the functions
  do not link, and the refusal says so.
- *`write-elf`.* The source's literal spells its functions; the
  heuristic runs once, on the fork, and the certificate states the
  linking of the functions onto the program as one equation, so today a
  function is as large as one declaration's fuel lowers
  (issues/native-function-emission-in-parts.md is the same limit on the
  other door, and its remedy serves both).

### 2.3 A buffer has one home, whoever lends it

As the exports note has it (§3 there): a value in every meaning, a home in
the lowering. The function compiler learns byte nodes, and a `Call` passes
buffers as well as words. Then:

- a program lends a function its static buffers, base a literal, the
  premise `Lends` discharged from the data region lying below the stack;
- Rust lends an export a slice, the same premise from Rust's rules;
- `write-elf`'s own byte-node code is retired in favour of the shared
  lowering once that reads and writes.

**How, settled against the code (2026-11-11): the function compiler.**

- *The meaning.* A program's buffers are numbered, and every function of
  it reads them by the same numbers. `BufferLoad(out, b, i)` means the
  byte of buffer `b` at `i`, zero past its end
  (`StructuredRegionHoldsOver`, `Function::Computes(…, buffers := …)`,
  `program_callees_over`; the evaluator is `program_eval_over`, tied to
  the relation by `program_eval_reads`). A function says how many buffers
  it takes (`Function.lent`), and buffer `k` arrives as its parameters
  `2k` and `2k + 1`, address then length, ordinary words. The meaning
  reads neither as an address.
- *A home is two values of the scope* (`Lent`, `function_ir_lower_reads`):
  the ids that hold a buffer's address and its length. A function's scope
  starts with its parameters' (`Function::homes`). A loop carries a home
  as state its passes hand on as it came: which state positions those are
  is an untrusted search (`carry_homes`) held to a check
  (`carried_sound`), and after the loop the home is the loop's outputs
  (`StructuredRegion::lends`), so a second loop over the same buffer
  finds it. A call hands the callee its count of buffers, their homes its
  first arguments (`args_lend`).
- *The bound is what the path knows.* The arm of a conditional taken where
  its bit is set knows the bit (`Known::Truth`). A load is accepted when
  some bit the path knows is the comparison `index < length` of a home of
  its buffer, folded at the branch (`File::bounded`), and refused
  otherwise. No check is emitted and no fact is asked of a front end: this
  is the exports note's default that always compiles (§5 there), and a
  proved bound (`InBounds`) is the later optimisation.
- *The code.* A load is a leaf of its own: the base moved to the
  placement's register, the index added, a zero-extending byte load over
  it (`File::load_at`). Leaves that read no buffer go through the lowering
  unchanged (`nodes_pure`), so that proof did not move.
- *The contract.* What a program lends is a `Lending`: how many buffers
  each function takes, where each lies, and its bytes. A function is
  entered with the homes of the buffers it takes as its first arguments
  and every buffer lent (`Stack::CalleeLent`: `Stack::Lends`, the bytes
  read at the address whatever the call stores below where it is entered).
  `Site::CallsLent` is every function meeting that. The contract without
  buffers is its instance at `Lending::none()` (`Site::calls_of_lent`), so
  every program that lends nothing is as it was, bytes included, and the
  old entry points are the new ones at an empty table.
- *The theorems.* `lower_program_lent_correct`, and what a caller cites,
  `compiled_returns_lent`: with the buffers lent the code returns what the
  program evaluates the function to over them.
- *Probes* (`lib/_tests/native/function_ir/function_ir_lower_reads_tests`):
  a byte under its bound with its code spelled, a loop summing a buffer,
  a call handing its buffer on, and eight refusals, each a theorem by
  evaluation.

Limits kept, each in `issues/function-ir-buffer-state-edges.md`: a loop
inside a loop that carries a home (the outer pass must hand on the
parameter itself, and after the inner loop the home is the inner loop's
outputs), and the comparison must be the one folded at the branch that
guards the load.

**What a program's call needs, and the question it raises.** A program's
buffers are static, so its call of a function that takes buffers supplies
the homes itself: the address a literal, the length the capacity, then the
words the region names. Two things follow.

- *A call reads the buffers as they are.* A program's region answers a
  `Call` by `call: Answers()`, a function of the callee and its words
  (`StructuredRegion::run`, `Source::denote` at
  `program_eval(src.functions)`). With buffers the answer depends on what
  they hold at the call, so `run` asks `program_eval_over` of its own
  buffers. This is also where U5 ends: a body with effects calls
  functions that read the state it has reached.
- *No meaning mentions an address* (vision §2.5), and the code passes one.
  The function's theorem is about the evaluation at the words it was
  entered with, the address among them, and a function that returned its
  buffer's address would compile. For an export this costs nothing: the
  certificate's last equation is the compiler's by `refl` over an open
  address word. A program's tree has no address to quantify, so it
  evaluates at address zero, and the compile needs the two evaluations
  equal. **Recommended:** a check and one theorem. A function is
  *placeless* when a base is read only as a home: by a load, as a call's
  home argument, as loop state carried unchanged. The check walks the same
  scopes the lowering does; the theorem says a placeless program's
  evaluation does not depend on the address words. The alternative, a
  premise each program discharges from its functions' agreement
  equations, puts a proof in every certificate that the generator can
  give once.

**Placeless, built** (`function_ir_placeless.hthr`). The check threads the
set of *hidden* ids, starting from a function's address parameters
(`Function::addresses`). `StructuredRegion::placeless(lent, hidden)`
holds when no node reads a hidden id, no branch tests one, a call passes
one only at a lent buffer's address place (`lent` gives each callee's
count), and a loop does not count by one, does not leave by one, and
carries one only at a place that came in hidden. `taints` says what is
hidden after a region: a node's output never is, and a loop's output is
where its input was. A function is placeless when its body is and its
result is not hidden. The theorem is `program_eval_placeless`: over any
buffers, a placeless program's function answers the same at word lists
that agree everywhere but the address places (`ListsApart` at
`base_mask`). It is proved once, by the evaluator's own recursion
(`Valuation::Apart`, `eval_nodes_apart`, `loop_eval_apart`,
`StructuredRegion::eval_apart`), and a program's compile cites it with one
`refl` of the check. The check is linear in the region except that a loop
nested in loops has its taints recomputed by each enclosing loop. It is
stricter than it must be in one way a lowered function never meets: a
value computed from an address and then discarded is refused. Probes:
`function_ir_placeless_tests` (the guarded load, the summing loop, the
call handing a home on; eight refusals, among them the function that
returns its address, with its two different answers).

### 2.4 A procedure is a function whose body has effects

The last joint, and the largest. `Stmt` becomes the body language of a
function; a region is the effect-free statement. A function's claim
becomes tree-valued, in the continuation form `Target::Runs` already has:
for every continuation, if the machine goes on as `k(result)` from each
state the function may return in, then from entry it goes as the function's
tree bound to `k`. A pure function's `Returns` is the case where the tree
is a value. `Perform` and the FunctionIR `Call` become one construct.

What changes on the program side is where words live: in the activation's
frame and registers, not in global homes. That removes the caller pushing
every live word, the callee starting from zero, and the two-convention
split. The recorded obstacle (callee-saves "unprovable: a claim speaks
only of words live at its end") is a property of global homes, where a
kept register is somebody's word; in the function compiler a kept register
is one the code never writes, which is already proved there.

Recursion keeps a depth in the meaning, for the reason
`docs/native-procedures-design.md` §2 gives: a finite stack can meet a
depth exactly and cannot meet fuel.

This joint gets its own design note when U1 to U4 are in, since it
re-bases `Target::Held` and the homes on frames. Its cost is the size of
the program compiler's storage proofs, not of anything new.

### 2.5 A program and an export

A program is a function `main`, a start-up that lends it the static
buffers and the command line, and an exit with its result;
`native_compile_correct` is `main`'s claim under the Linux model. An
export is a function with no effects and a generated Rust declaration.

## 3. The rounds

Each is a PR and ends with something that runs.

- **U1. `Wrote` in the function compiler.** *Built 2026-11-11.* The post
  states the stores (`Stack::Wrote`, `x86_64_stack.hthr`; `CalleePost` and
  `Framed` in `function_ir_lower_calls.hthr`); `Unchanged` and code
  residency are its corollaries (`wrote_unchanged`, `wrote_resident`), and
  the earlier theorem is `compiled_returns_keeps`. Nothing emitted moved:
  every linked export recertifies with its bytes unchanged.
- **U2. Programs call functions.** *Built 2026-11-11.* `Source`'s `Call`
  compiled as §2.2: `Prog::function_call` and `Prog::links`
  (`native_compile.hthr`), the call's run from the function's contract
  (`Target::functions_run`, `native_compile_function.hthr`), and
  `native_compile_correct` over a source with functions, with or without
  procedures. *Runs:* tr with each byte through a called function, beside
  GNU's; a tool calling a `runtime fn` that calls another; a procedure and
  a function in one file (`crates/cli/tests/native_tools.rs`).
- **U3. Buffers read through one home**, in three steps.
  - **U3a. The function compiler reads a lent span.** *Built 2026-11-11*
    (§2.3): homes, the path-known bound, the load, the contract with
    lending (`function_ir_lower_reads.hthr`, `function_ir_lower_calls.hthr`),
    `lower_program_lent_correct` and `compiled_returns_lent`. *Runs:* the
    probes' code by evaluation; no process yet, which is U3b's.
  - **U3b. A program's `Call` passes buffers.** Placeless functions
    (*built 2026-11-11*, §2.3); then `run` answers a call over its
    buffers, the call's code supplies the static homes, and `Lends` is
    discharged from the data region lying below the stack. *Runs:* a tool
    that reads its input into a buffer and calls a compiled loop over it.
  - **U3c. `rt` lowers `Get` and `Len`**, so the loop is a `runtime fn`;
    the scanner's loop is the customer.
- **U4. Buffers written.** Stores, `Wrote` over lent spans, `Unique`;
  `write-elf`'s byte nodes move to the shared lowering. *Runs:* `tr` with
  its byte map as a called function.
- **U5. Procedures are functions** (§2.4), after its own note. *Runs:* the
  tools with procedures (`grep -F`) rebuilt on it.
- **E. Export.** Generated declarations, the contract's controls, the
  scanner's loop linked into Rust
  (`docs/native-library-exports-design.md` §6, §10 R3).

E needs only U1, U3a and U3c. It is last because that is the order asked for;
it can move up without changing any other round.

## 4. What is not unified, on purpose

- **The three levels stay** (`Source` over FunctionIR over machine code,
  vision §2.4). A meaning with effects and a meaning without are different
  things; one compiler serves both.
- **The outer theorems stay two**: a process simulating a tree, and a
  function meeting a call contract. The first becomes an instance of the
  second at `main`.
- **`rt`'s two lowerings** (pure to FunctionIR, effectful to `Source`)
  merge only as far as U5 merges their targets.

## 5. What this does to the exports note and the issues

`docs/native-library-exports-design.md` keeps its §3 to §8 as the design of
memory and of the contract. Its rounds map here: R1 is U1 and U3's
lowering half, R2 is U3's `rt` half, R3 is E, R4 is U4. Its §2, the choice
of the function pipeline as the unit, is what this note generalises.

| issue | role |
|---|---|
| `native-one-compiler` | new; owns this note and the order |
| `x86-call-memory-footprints` | U1 states the clause; its authorized shared writes are U4, and it closes there |
| `function-ir-buffer-state-edges` | U3 and U4 in the function compiler |
| `source-buffers-as-views` | U3: the static instance; then views |
| `runtime-default-setup-soundness` | U3's `rt` half |
| `native-procedure-contracts` | U5 |
| `native-library-exports-design`, `self-lexer-linked` | E |
