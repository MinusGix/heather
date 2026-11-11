# One native compiler: joining `write-elf` and `compile-x86`

Status: **direction set by Minus 2026-11-11** ("unify first and then
export"); this note scopes it. U1 is built (§3). Owner:
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

### 2.3 A buffer has one home, whoever lends it

As the exports note has it (§3 there): a value in every meaning, a home in
the lowering. The function compiler learns byte nodes, and a `Call` passes
buffers as well as words. Then:

- a program lends a function its static buffers, base a literal, the
  premise `Lends` discharged from the data region lying below the stack;
- Rust lends an export a slice, the same premise from Rust's rules;
- `write-elf`'s own byte-node code is retired in favour of the shared
  lowering once that reads and writes.

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
- **U2. Programs call functions.** `Source`'s `Call` compiled as §2.2.
  *Runs:* a `write-elf` tool that calls a `runtime fn`, tested as the tools
  are.
- **U3. Buffers read through one home.** The function compiler reads a
  lent span under a path-known comparison; `Call` passes buffers; `rt`
  lowers `Get` and `Len`. *Runs:* a tool that reads its input into a buffer
  and calls a compiled loop over it; the scanner's loop is the customer.
- **U4. Buffers written.** Stores, `Wrote` over lent spans, `Unique`;
  `write-elf`'s byte nodes move to the shared lowering. *Runs:* `tr` with
  its byte map as a called function.
- **U5. Procedures are functions** (§2.4), after its own note. *Runs:* the
  tools with procedures (`grep -F`) rebuilt on it.
- **E. Export.** Generated declarations, the contract's controls, the
  scanner's loop linked into Rust
  (`docs/native-library-exports-design.md` §6, §10 R3).

E needs only U1 and U3. It is last because that is the order asked for;
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
