# One native compiler: joining `write-elf` and `compile-x86`

Status: **direction set by Minus 2026-11-11** ("unify first and then
export"); this note scopes it. U1 to U4 are built (§3), and U5 is designed
in `docs/native/native-procedures-are-functions-design.md`, its steps 5a to 5c
built (one frame, one call, one contract). E's read half is built: a
function that reads a span is exported, its declaration generated and its
contract's controls in place (`docs/native/native-library-exports-design.md`
§6.1), and the scanner's loop is one linked function proved to be the
specification's (§6.2 there); the write half's export is not. Owner:
`issues/native-one-compiler.md`. It extends `docs/compilation-vision.md`
(§2.4's levels) and re-sequences `docs/native/native-library-exports-design.md`,
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
(`docs/native/native-library-exports-design.md` §4, kernel-checked there). It
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
  (`MayCallOver`), so nothing is proved twice. Function `f` keeps the label
  `Succ(f)`; the program names its procedures, its deep exit and `main`'s
  labels past the functions' (`Layout.functions`), and the functions'
  inner labels start where the program's end.
- *The call.* RSP is the frame (since U5's step 5a; before it, loaded
  from a static slot); the arguments go from their homes to the six registers
  (`Prog::words_to`); R10 goes to RBX, CALL, and back; RAX goes to the
  result's home. A function keeps RBX, RBP and R12 to R15, so with R10
  carried in RBX every home register is as it was, and no allocator
  learns anything.
- *The proof.* `Site::moves_call` against the function's `Returns` is a
  straight run, which a tree claim absorbs (`LinuxIo::goes_after`). What
  the program holds between statements (`Target::Held`) is kept by a
  word stored below its frame, so it is kept by `Wrote`
  (`Star::invariant`): this is where U1 is used. Since U5's step 5c the
  call is `Target::goes_calls` from the one contract, and a function
  meets the contract by this proof (`Target::function_performs`).
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
  unchanged (`nodes_blind`), so that proof did not move.
- *The contract.* What a program lends is a `Lending`: how many buffers
  each function takes, where each lies, and its bytes. A function is
  entered with the homes of the buffers it takes as its first arguments
  and every buffer lent. As first built that was `Stack::Lends` (the
  bytes read at the address whatever the call stores below where it is
  entered); since U4's step 4a-3 it is the lending's laws and the bytes in
  memory when the call is entered (`Stack::LentOver`, §2.6), and
  `Site::CallsOver` is every function meeting that. The contract without
  buffers is its instance at `Lending::none()` (`lower_program_correct`,
  its statement unchanged), so every program that lends nothing is as it
  was, bytes included, and the old entry points are the new ones at an
  empty table.
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
returns its address, with its two different answers). A call over views
makes addresses of its own, its views' bases, which the check hides from
the lend on (`docs/native/native-library-exports-design.md` §3.1, V4d).

**A program's call, built.** Three pieces, each where the note said.

- *The meaning.* A region's calls are answered by `Readers()`, a function
  of the buffers as they are and then of the callee and its words
  (`function_ir_state.hthr`); `StructuredRegion::run` asks it of its own
  buffers. A source's are `program_readers(src.functions)`
  (`function_ir_placeless.hthr`): function `f`, lent `k` buffers, is
  answered by `program_eval_over` of the first `k` buffers the program
  holds (`lent_buffers`), at the homes `stated_homes` gives them (address
  zero, the length the buffer's own) before the words the call names. A
  call sees exactly what it is lent. For a function lent nothing this is
  `program_eval` by evaluation, so a certificate of a program without
  buffers states what it did.
- *The code* (`Prog::function_call`, `native_compile.hthr`). Buffer `b`
  of the file is the `b`th a function is lent. Its home is two
  immediates, the address the layout puts it at and its capacity, set in
  the block that carries R10 (`Layout::homes_block`); the words go to the
  registers after the homes'. A call fits (`Layout::function_fits`) when
  the function takes the words after its homes, six registers hold them
  all, and the file has the buffers. `Prog::links` checks the functions
  placeless, with rows of marks that hold (`program_linkable`; the rows
  matter once a function calls over views,
  `docs/native/native-library-exports-design.md` §3.1), and emits each under its
  count of lent buffers (`program_counts`). A function lent nothing is called by the code it
  was.
- *The proof* (`native_compile_function.hthr`). The function's contract
  (`Site::CallsOver`, at every address, over every buffers and under any
  lending whose laws hold) is cited at the placed homes over the buffers
  lent, and `program_eval_placeless` turns its answer into the stated one
  (`Target::answers_of`; the joints are `homes_apart`, `args_lent_placed`
  and `program_counts_lent`, `function_ir_lend.hthr`). The claim between
  statements places every buffer's bytes in the data region
  (`Target::buffer_readable`), so the buffers are in memory as they are
  when the call is entered (`Target::in_memory`), and the laws hold
  because the data region lies below the process stack, whose stores
  therefore miss it (`Target::loan`, with the whole stack as the caller's
  side). A buffer of a source is
  always as long as its capacity, which is why the capacity is the length.

What a function over a count needs: a read fills a prefix of the buffer,
so the count is a word the call passes, and the function tests its index
against the length home too. That test is the path-known bound; it costs
one comparison a pass that an optimizer could fold when the count is
known below the capacity (not built).

**A `runtime fn` reads a span: the design of U3c (2026-11-11; steps 1
and 2 built).** The joint so far ends at FunctionIR written by hand. What is
left is the front end: `rt`, its lowering and its loop theorems
(`rt.hthr`, `rt_lower.hthr`, `rt_loop.hthr`), the `Compile` class and the
generator (`runtime.hthr`). Read against them, five things are decided.
A first form of this design threaded the homes through the lowering
beside the term and carried an invariant about them; building it showed
that neither is needed, and what follows is the form that was built.

- *A lent buffer is the function's world, not one of its values.* `rt`
  has a byte buffer as a value already (`Bytes(cap)` with `Get` and
  `Set`), for the effectful layer, where a buffer is a static one named
  by its id. A lent span is different in the one way that matters to the
  proofs: no term makes one, moves one or chooses between two, so which
  buffer a read reads is static. So the spans join the type table and
  the callees in `World`, as the file of buffers the function is
  evaluated over (`World.spans`, the same list `Buffers()` is). The
  meaning of a function is a function of its words alone, in a world.

  The alternative, a span as a parameter of code `Bytes`, keeps the
  reflection's pin as it is and costs every statement that reads a
  signature as words: `Ty::Answers`, `Ty::apply`, a loop's `tail_sem` and
  its two equations each pass a call's arguments as a list of words,
  and a buffer among them would have to be cut out of each. With the
  spans in the world those statements do not change at all; they are
  read at a world that has spans.

  This is also FunctionIR's own shape. Its evaluator takes the file of
  buffers beside the valuation, and a callee is evaluated over the same
  file as its caller. So a call of a function that is lent spans needs
  no new term either: it is `Call(g, words)`, and `g`'s entry in the
  table of meanings is `g` at the same file.

- *A home is two words of the function.* A function lent `n` spans
  (`Fun.lent`) has `2n` parameters of type `Word(64)` before its own:
  span `k`'s address and its length, which is where FunctionIR looks
  for a home (`Function.lent`, parameters `2k` and `2k + 1`). They are
  variables like any other, so a term names a length by the variable
  that holds it, a call passes them as arguments, and nothing about
  homes is threaded through the lowering. The address is never read by
  the meaning: it is there for the machine.

- *One term reads, under the length it is given.* `Byte(k, i, length)`
  is the byte of span `k` at the word `i` when `i` is below the word
  `length`, and zero otherwise (`List::byte_within`). It lowers to the
  comparison and a branch on it: the load of buffer `k` at `i` where
  it holds, a zero where it does not (`Tm::lower_byte`). That is the
  check the function compiler asks for before a load (`File::bounded`),
  written by the language above it as this section said it would be.

  Since the term's meaning tests the same word its code tests, the
  lowering theorem has no premise about homes at all: it holds at every
  valuation, whatever `length` holds (`Tm::lower_byte_sound`, and
  `Tm::lower_sound` restated over the evaluation with buffers at the
  world's own file). There is no length term. Whether `length` *is*
  span `k`'s length home is not `rt`'s question: it is the function
  compiler's, which refuses a load whose bound is any other id
  (`peek_misread_refused` in the probes: `rt` lowers a read under the
  wrong word, soundly, and the code is not accepted).

  Truth about the length enters once, at the top. A source function
  over a span says `span.byte_at(i)`; it is the meaning at the world of
  that span and the length word `ofNat(span.len())`, where
  `byte_within` at the span's own length is `byte_at`
  (`List::byte_within_own`, for a span shorter than `2^64` bytes, the
  one fact asked of a file).

- *A loop carries the homes in place.* A pass sees only the loop's
  state, and the function compiler carries a home across a pass when
  the pass's `next` for its two places is the pass's own parameter
  (`carry_slot`). So a measured loop's words are two lists: the kept
  ones, which the pass hands on as its own parameters and never writes,
  and the moved ones, which it computes at fresh ids as before
  (`Fun::lower_measured(ks, w0, wrest, …)`; the loop's `next` is the
  kept parameters and then the fresh ids). The body is asked for one
  thing more than it was: a self-call passes each kept word as the
  variable it came in as (`Tm::split_kept`), and a body that does not
  is not lowered. What a pass leaves (`Tm::leave`) is then the
  recursion at the kept words as they stand and the moved ones as
  computed, the loop theorem is the one it was at the joined list
  (`Fun::measured_sound`, generic in which words are kept), and a
  function lent nothing keeps nothing and gets the code it had. A
  function with `lent > 0` that calls itself keeps its first `2·lent`
  words (`Fun::shape_params`). The loop's code is `lent` what the
  function is, and after it both the loop's outputs and the ids before
  it are homes (`StructuredRegion::lends`). Fuel loops keep nothing: a
  fuel recursion's count sits before its words, and none reads a span
  yet.

- *The class is about a function at a file.* `Compile<F>(f)` states that
  the code answers as `f` does, at every file (built in step 3a,
  `lib/native/runtime/runtime.hthr`). A function lent spans takes each as
  a pair of ordinary Heather parameters, the bytes and then the word it
  tests its index against, before its other words:
  `f(span, length, words…)`. Its code takes the home in the bytes'
  place, so the code's words are `place, length, words…` and the code
  never reads `place` except to load from it. `Ty::Lent(tys, lent, ps,
  r)` is that Heather type computed from the reflection's parameters,
  `Ty::lend` reads such a function at a file's spans as a function of
  the code's words (it drops each place and hands over span `k` of the
  file), and the class says, for every file `b` and every answering of
  calls that agrees with the table there, that the code evaluated over
  `b` answers as `Ty::lent_at(…, f, b)`. With no spans `Ty::Lent` is
  `Ty::Arrows` and `lent_at` is `f` by conversion, so a spanless
  instance states what it did, at every file instead of the empty one.

  Two things make one code serve every file. The table of callees is a
  function of the file (`callees: (b) → Sig::Sems(…)`), since a function
  that calls itself over a span is in its own table at that span; a
  spanless world's table is constant (`World::fixed`). And the lowering
  does not read the file: `Fun::lower_any_static` says the code at
  `w.over(cs, spans)` is the code at `w`, and a `Setup` carries that
  law for its own lowering (`static`), so `Setup::code(rt, w)` is the
  code whatever file the agreement is read at.

  The world at a file has one spelling, `World::at(w, callees, b)`, and
  the class reaches every part of it through that, its type table
  included. This is a rule about cost, not meaning: with the table
  spelled `w.tys` in one place and through the world at the file in
  another, a generated instance's check made the kernel compare the
  spelled-out reflection, at a cost that climbed steeply with a numeral
  inside it (issues/conversion-respelled-world-compares-reflection.md,
  `docs/proof-patterns.md` §2). The builders' proofs are opaque theorems
  (`Setup::agrees`, `fuel_agrees`, `measured_agrees`), so an
  instance is a constructor applied to them.

  A length word is a parameter of the Heather function and not the
  span's own length because that is what the code has: a word it is
  handed. The read is `span.byte_within(length, i)`, which is `byte_at`
  when the word is the span's length (`List::byte_within_own`), and the
  caller that lends the span is the one who knows it is. A `Span` type
  pairing the two, so the source reads `s.byte_at(i)` and `s.len()`, is
  a surface over this and is left for the export round, where the
  scanner's signature is written.

  Linking is stated over a file since step 3c (below).

  A loop needs more than the pin, and step 2 found where: a measured
  function is proved from its own `f::ext`, and `decreases` takes every
  parameter into its recursor, the span among them, so `ext` asks the
  two recursions it compares to agree at every span
  (issues/decreases-generalizes-fixed-parameters.md). The loop's
  `again` at one file knows nothing of another. So what such a function
  proves is `Guarded` at every world of a family at once: `again`
  answers at every key and agrees with the function below the measure at
  every key, which is exactly what `ext` can use. `Fun::guarded_by`
  brings it back to `Guarded` at one world, by answering with the
  function wherever the hypothesis speaks and with that world's `again`
  elsewhere; the body's meaning reads its recursion only at the calls it
  makes (`Tm::tail_sem_ext`). The loop theorem itself does not change,
  and `Fun::measured_sound_at` is it at each index. The family is the
  class at every file seen from one function, so the generator proves it
  as it proves `Guarded`, with the span a binder of each ih. If
  `decreases` comes to leave fixed parameters outside its recursor, the
  family is no longer needed and can go.

  The family has two indices, and they are not the same thing
  (`Fun::GuardedBy`): its worlds are indexed by the *file*, and its
  recursion is keyed by the *span*. The key is what `ext` quantifies
  over, and it cannot be the file: `again` at a file and `again` at the
  one-span file of its span are not convertible. The worlds are indexed
  by the file because that is where `Guarded` is wanted, at the world
  the function is compiled in. The family first built had one index, the
  span, its worlds the one-span files (`Fun::GuardedAt`, which is the
  keyed family with the key its index); that gave `Guarded` at
  `[b.span(0)]`, and bringing it to the world at `b` was left to
  conversion. That is a comparison of the body's meaning at two
  spellings of one file, which conversion can only settle node by node:
  the environment at every binder, the callee table at every call. Its
  cost is the body's size times what the body calls, and it passed the
  host's conversion budget at the scanner's loop, whose step is the
  whole automaton
  (issues/runtime-measured-instance-conversion-budget.md). With the
  worlds at the file there is one thing compared across the two
  spellings, the function at its head, and the cost is the body's alone.

  In the class this is `Setup::GuardedSpans`, the keyed family at
  `b ↦ w.at(callees, b)` whose key is the file's first `lent` spans
  (`Setup::spans_of`), and `Setup::guarded_spans` is `Guarded` at every
  file from it. It was first built keyed by `b.span(0)` for a loop lent
  one span; a loop over several is the same family keyed by the list of
  them, and nothing else changed
  (issues/runtime-loop-over-several-spans.md).

  The reflector decides what is a span (step 3b, built): in the
  generator's mode, each leading parameter of a pure `runtime fn` that
  is a `List<BitVec(8)>` followed by a 64-bit word is a span and its
  length word, numbered in order, and the function's code takes two
  words for the pair (`rt_lent`, `lib/native/runtime/rt_reflect.hthr`).
  `span.byte_within(length, i)` on such a span under its own length word
  is `Byte(k, i, length)`. A recursion passes each span and its length
  word on as they came in, which is what the loop's lowering needs to
  keep the home in place, and the reflector says so where a body does
  not. A call of another lent function passes the caller's span `j` as
  the callee's span `j`, with its own length word (step 3c): the callee
  reads the caller's file, and a `Call` that renames buffers is not in
  FunctionIR. Every other use of the span is refused with the reason:
  read under another word, read with `byte_at`, used as a value, or
  handed on in another place or under another word. A byte list anywhere
  else among the parameters is refused with what a span is.

  The generator then makes the instance the class states
  (`lib/native/runtime/runtime.hthr`). The table of a lent function is
  `Setup::lent_callees`: entry 0 the function at each file's spans, the
  spanless functions it calls after it, and its world is that table at
  the empty file. A function without a loop is pinned at every file
  (`Setup::alike_every` since loop-combinator-design §6.6, and `f::reflects` is stated over the file). A
  loop over its spans proves `Setup::GuardedSpans`, the keyed family of
  §2.3's step 2 (its worlds the files, its recursion keyed by a file's
  first spans), with the generator's usual proof from `f::ext` and
  `f::irrel`: the file is the statement's first binder, each ih binds a
  list of spans, and every recursive answer is asked at the places the
  loop was entered with. `Setup::guarded_spans` is `Guarded` at each
  file from it, at the world the function is compiled in. A loop over
  two spans keeps four home words in place, which leaves its body five
  of the nine registers a function's values have: `differ_sum`
  (`runtime_lent_tests.hthr`) compiles with its certificate, and the
  same loop with its parameters in the other order holds a tenth
  value, which the planner puts in a callee-saved register the function
  saves at its entry (issues/function-ir-values-in-kept-registers.md).

  Linking over a file (step 3c, built). The evaluator's two linking
  lemmas are stated over the buffers (`Function::eval_answers_over`,
  `Function::relabel_eval_over`; the old ones are these at no buffers),
  and a program is linked at every file at once:
  `program_linked_files(functions, arities, admits, sources)` asks each
  function to answer as `sources(b)` says over each file `b`, at the
  words its contract admits (since 2026-11-20, runtime-fn-setups-design
  §16.16 "Linking at admitted words"), and
  `program_linked_files_sources` gives `program_eval_over(b, functions)`
  as `sources(b)`. `Compile::part` is the class's agreement in that
  form, at the function's own table at `b`. Every generated program is
  linked this way, lent or not, so there is one linking and a spanless
  function's `f::agrees` is its reading at the empty file, as stated
  before; the cost over the old linking is a small constant per
  function. A lent function publishes `f::program`, `f::arities` and

      f::agrees_over(b, words…):
          program_eval_over(b, f::program, root, [words…]) = f(b.span(0), …)

  where the words are the code's (a place and a length for each span,
  then the function's own). A table is built an entry at a time
  (`Setup::lent_callees` over `Setup::callees_nil`), each callee's entry
  the callee at the file's spans, so a lent function calls lent and
  spanless functions alike.

  A tool's call states no address (`program_readers`: each home's place
  stated as zero and its length the buffer's), so what a call answers is
  the function at the tool's own buffer:
  `count_newlines_called` (`lib/native/native_tool_spans.hthr`) is
  `agrees_over` read at the buffers the tool holds. `compile-x86` still
  cites `f::agrees` and so does not take a lent function; a Rust caller
  that lends a buffer is the export round's.

  Step 3c also met the function compiler's placement heuristic. The
  reflector writes a call's arguments left to right, so a loop's next
  index is made before the byte is read and lives across the read; the
  heuristic then put the tally where the next index was wanted, the two
  arms of the pass's branch disagreed on where the outputs lie, and the
  code keeps only what the arms agree on (`File::meet`), so the loop was
  refused. A branch whose first plan loses an output that is read after
  it is now planned a second time with fresh places kept clear of every
  register something is wanted in (`StructuredRegion::plan_in`). The
  heuristic is untrusted, so nothing is proved of this, and a branch
  whose first plan loses nothing is planned as before: no compiled code
  changed. The emitter moving each arm's outputs to the branch's
  targets, so that no plan can lose one, is
  issues/function-ir-branch-arms-meet-by-placement.md.

What step 1 built (`lib/_tests/native/runtime/rt_spans_tests.hthr` is
its evidence): the term, its meaning, its lowering and the theorem, for
functions without a loop; every statement of `rt_lower` and `rt_loop`
over the world's file; a function `peek` that reads its span, lowered
by `rt`, proved to answer as its meaning over every file, run by
evaluation over a short buffer, and accepted by the function compiler
lent one buffer (`lower_program_lent`). A value region reads no bytes,
so the effectful layer cites the old statement through
`StructuredRegion::eval_byte_free`.

What step 2 built (`lib/_tests/native/runtime/rt_span_loops_tests.hthr`):
kept words in the measured loop and its theorem, the family form of
`Guarded`, and a function that counts a span's newlines from an index,
`count_from`, written in Heather with `decreases`. Its reflection is
lowered by evaluation to one code whatever the file, the code is
placeless and accepted by the function compiler lent one buffer, it
runs by evaluation, and at every span, place and length word it
computes `count_from` (`count_compiled`), `GuardedAt` proved from
`count_from::ext` and `count_from::irrel` as the generator will. A
self-call that moves a home is not lowered; a loop that keeps nothing,
or is lent nothing, is lowered and not accepted. The class admits such a loop's
instance since step 3a (built by hand in `runtime_spans_tests.hthr`), and
the generator makes it since step 3b.

One limit of the source language showed while writing it: a `decreases`
body that branches under its `match h:` arm with a self-call below the
branch has no `ext`, so a loop with two ways round has no Heather
function beside it today, though it lowers and runs (`count_split_body`;
issues/decreases-no-companions-nested-match-calls.md). The form with one
self-call and the branch in its arguments is the one proved.
*Since #579 (2026-11-12)* such a body has its companions, and the
generator takes it as it stands: `clear_line` (an exit inside the loop)
and `clear_text` (two calls of its own) in
`lib/_tests/native/runtime/runtime_span_tests.hthr`.

What it leaves open, on purpose: a span that is written. A write makes
the buffer a result as well as an input; §2.6 decides that the file
becomes state the meaning threads, and the world stays the place for a
span only while it is read.

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
`docs/native/native-procedures-design.md` §2 gives: a finite stack can meet a
depth exactly and cannot meet fuel.

This joint has its own design note,
`docs/native/native-procedures-are-functions-design.md`, written when U1 to U4
were in. It re-bases `Target::Held` and the homes on frames; its cost is
the size of the program compiler's storage proofs, not of anything new.
It refines one sentence above: `Perform` and `Call` become one construct
in the code (one call sequence, one contract) and stay two in the
meaning, since a region is a total function and what it calls must
answer with a value (that note's §2.1).

### 2.5 A program and an export

A program is a function `main`, a start-up that lends it the static
buffers and the command line, and an exit with its result;
`native_compile_correct` is `main`'s claim under the Linux model. An
export is a function with no effects and a generated Rust declaration.

### 2.6 A written buffer is state the meaning threads

U4's design. The question §2.3 left: when a function stores into a span
it was lent, is the file state that the meaning threads, or does the
function return the new bytes?

**Threaded, at FunctionIR and below.** The machine has one span and
changes it in place, and FunctionIR already has both halves of the
meaning at the region level: `StructuredRegion::run` carries the file
through `BufferStore` (`function_ir_state.hthr`), while `eval` and the
relation the function compiler is proved against
(`StructuredRegionHoldsOver`) read a file that never changes. U4 makes
the threaded one the meaning of a function: a call is answered with a
word and the file it leaves. "Returns the new bytes" is what the Heather
function does, and it is the class's to state (below); proving that the
one span updated in place is the list the function returned is the
reflector's question, about how the source uses the span, and not the
compiler's.

Three things stay as they are. A buffer is a number and a list of bytes,
and a store never changes a length, so a home's length word holds across
stores. A store outside the buffer is no store in the meaning
(`store_byte`), so the lowering asks what it asks of a load: the path
knows the index below the home's length. And which of its lent buffers
a function writes is read off the program, not declared: the buffers its
body stores into and the ones its callees write, which is computable
because a program's functions call only those after them. A function
that writes nothing has today's contract.

**What a caller lends is laws, not stability.** `Stack::Lends` says a
span reads its bytes after any store the callee makes in its own room.
That cannot say what a written span reads after a store into it, and
with stores into spans in play "stable under the callee's stores" is no
longer about the callee's room alone. So lending is restated in the
style of the `Stack` record, as laws at every memory, for the spans by
buffer number (`at`, `size`, `written`) and an offset `top` the callee's
words lie below:

- every span is canonical, and a word stored below `top` leaves every
  span's bytes;
- a written span's bytes are writable, a byte stored there reads back,
  and it leaves every other byte of every span, the stack's words below
  `top`, and the code.

A read span and a written span are apart because the last law says so,
and two read spans may overlap. These are what Rust's `&[u8]` and
`&mut [u8]` give a wrapper, and what a `DataRegion` gives a program's
static buffers (`DataRegion::apart`, `read_stored`, `store_outside`,
`store_keeps_code`). `top` is there because a program's buffers lie in
the same region as its stack, above the running frame: "a span store
keeps the stack" is true only of the words below them. `Lends` becomes a
consequence of the laws and stops being a premise.

**What a call may store** widens with it: `WroteIn(i, spans, before,
after)` is stores one after another, each a word of the callee's own
room below `i` (`Own`, as now) or one byte of a written span. `Wrote` is
the case with nothing written. From `WroteIn` and the laws follow what a
caller keeps: its words from `i` up to `top`, the code, and every span
nobody was lent to write.

**The contract.** Under the laws, a function called over the file
`before`, each lent span reading its bytes of `before`, returns with its
result, the kept registers, `WroteIn` over the spans it writes, and each
lent span reading its bytes of the file the meaning leaves. A callee is
handed the same spans under the same numbers (§2.3) and writes no span
its caller does not, by how the written set is computed, so a caller
lends on what it was lent (`Loan::narrow`).

**Inside the function compiler** the file is no longer a constant of the
proof. What emitting proves (`EmitsOver`) carries the file before and
after and, beside the frame, that every lent span reads the file as it
is now (`Stack::Trail`: `WroteIn` from the function's entry, and
`Stack::InMemory` of the file now).
Code that stores only in its own frame keeps that by the first law, so a
load reads through it at the memory it runs in, with no trip back to
entry. A store is a leaf of its own, like a load, under the comparison
that bounds its index: the address formed from the home in the register
its output is placed in, one `StoreByte` of the register that holds the
value, and the byte then there loaded back over the address, which is
what the store's output names (`File::store_at`, `store_emits`). The
reload is one instruction a planner that knows the output dead can drop
(`issues/native-store-reloads-its-byte.md`). The relation it is proved
against threads the file (`StructuredRegionRunsOver(effects, values,
region, before, after)`, a call's `effects` relating the file before to
the word and the file after), and the fixed-file relation embeds in it
for a region with no store, so everything proved through `eval` today
feeds the new theorem unchanged.

Which buffers a program stores into is computed (`program_stores`, from
`StructuredRegion::stores`), and the theorems take that each is one the
lending lets be written (`allowed`), weakened at each sub-region to the
buffers it stores into. A lending to read therefore still serves every
program that stores nothing, and a program that stores is not provable
under one. A store lowers only through a home, so the door without
buffers (`lower_program`) accepts no store and keeps its statement
(`lower_program_quiet`: lowered with no home, a program is quiet).

The relation is what the compiler is proved against, and it is computed
as well (`function_ir_run.hthr`): `program_run` answers a call with the
word and the file, a callee's run shared between whoever reads the one
or the other, and for an evaluable program that answer is one the
relation allows (`program_run_effects`). So a function that writes is
stated by evaluation, as one that reads is, and `compiled_returns_run`
is what its caller cites. There is one evaluator: `StructuredRegion::run`
(`function_ir_state`), which a program's statements are evaluated by,
answers a call with the callee's word and the file the callee leaves
(`Ending`, `Writers`), and `program_run` is it over a program's own
functions.

**A program's call** (`Source`) then answers with the file as well:
its callees are `Writers` (`program_writers`: `program_run` of the
source's functions over the buffers lent, the rest of the caller's file
put back), the statement after the call starts from the file the callee
left, and the claim between statements is rebuilt from the contract's
post, the buffers being the layout's cells (`Target::based_left`). A
program lends every buffer to write: its own statements store into them
already, so there is no span it must keep from a callee, and which ones
a callee does store into is the callee's program to say
(`program_stores`). `tr`'s byte map is the first customer.

**A `runtime fn` writes a span: the design of 4c (2026-11-11).** Read
against the runtime language as U3c left it and against its layer over
Linux (`rt_io.hthr`, `rt_io_lower.hthr`, `rt_io_loop.hthr`,
`rt_io_reflect.hthr`), six things are decided.

- *A function that writes is a computation, and computations are a layer
  over `rt`'s terms.* `rt`'s terms are values: total, pure, their meaning
  a function of their words in a world (`Tm::sem`), and U3c put the
  spans in that world for exactly that reason. A store changes the
  world. So it does not join `Tm`. It joins a layer over it, as a call
  to Linux did (`ETm`: `Pure`, `Let`, `Invoke`): `FTm`, computations
  over the file.

  - `Pure(t)`: a value, the file as it is.
  - `Let(e, body)`: a pure value bound once.
  - `If(c, yes, no)` and `IfEq`: a branch on a `Bool` variable.
  - `Put(i, length, v, body)`: the store, then the rest.
  - `Call(f, args, body)`: a computation of the program, its word bound
    for the rest, which goes on in the file the callee left.

  Its meaning threads the bytes of the one span it writes, span 0:
  `List<BitVec(8)> → Mutated<List<BitVec(8)>, value>`, over the rest of
  the file, which it only reads. Each pure term is read at the world of
  the file as it is then, `Cons(own, rest)` (`World::at`). Nothing in
  `rt.hthr`, `rt_lower.hthr` or `rt_loop.hthr` changes, and every
  theorem about a pure term is cited as it stands.

  The state is the written span's bytes and not the whole file for the
  reflection's sake. A source function is over its span, and its pin to
  the meaning is a conversion: a read after a store must compute, at a
  span that is a variable, to the source's read of the updated list.
  Span 0 of `Cons(own.put_within(…), rest)` is that list by computation;
  span 0 of a store into a file that is a variable is that list only by
  a theorem, which a pin cannot cite.

  The alternative is a `Put` among `Tm`'s terms, with a second meaning
  that returns the file. It saves a type and costs the property the
  pure language is built on: `Tm::sem` would be a value at a world some
  subterm changed, every statement about a term would need to say which
  file it is read at, and the pure lowering's theorem, which is over a
  fixed file, would be false of a term with a store in it.

- *The span is the computation's world, so it is used linearly by
  construction.* §2.6 asked that the old bytes be dead for a store in
  place to be sound. No `FTm` can name the file: a read is of the file
  as it is, and there is no term for the file as it was. So a body that
  reflects at all threads the span straight through, which is the
  argument that made `Io` linear in `ETm`. No separate uniqueness
  analysis is asked of the source.

- *One term writes, under the length it is given.* `Put(i, length, v)`
  leaves the span with the byte `v` at the word `i` when `i` is below
  the word `length`, and as it was otherwise (`List::put_within`, beside
  `byte_within`). It lowers to the comparison and a branch on it, the
  store of buffer 0 at `i` where it holds and nothing where it does not,
  which is the bound the function compiler asks of a store
  (`leaf_store`). As with `Byte`, the
  lowering's theorem has no premise about homes, and a `Put` under a
  word that is not the span's length home is lowered soundly and refused
  by the function compiler.

- *The source is a function from the span to `Mutated`.* The language
  has state-threading already: `fn T::m(mut self x: T, …) → R` has
  kernel type `T → … → Mutated<T, R>`, and a body's calls of such
  methods are threaded by the elaborator
  (docs/language/effects-capabilities-design.md §2). A function that writes a
  span is one of that kernel type over its bytes, however it is
  spelled: a `mut self` method on `List<BitVec(8)>` whose body says
  `span.put_within(length, i, v)`, or a function that returns
  `Mutated(span′, value)` itself. The written span is the first
  parameter and is span 0, its length word the next. One written span
  is what `mut self` gives, and it is enough for `tr`, the scanner and
  the hashes' output; a second is a language question (`mut` on a
  parameter that is not the receiver) and is left there.

  A loop is spelled the second way today. A loop is a function that
  `decreases`, and `decreases` does not yet cover a declaration with a
  `self` parameter (issues/decreases-self-parameter.md), so
  `raise_from` takes its span as a plain parameter and ends in its own
  call on the span as the pass left it. The reflector reads every
  spelling of that as the same thing, since it reads the kernel term.
  The generator asks more: a loop's instance is built from its
  recursor's `ext` and `irrel` companions, and a `decreases` arm with a
  `mut self` call statement before its self-call (`span.put_within(…);
  raise_from(span, …)`) has none today
  (issues/decreases-mut-call-statement-companions.md). So a loop that
  is a `runtime fn` makes its store in the self-call's argument
  (`raise_from(span.with_byte_within(…), …)`, or
  `List::put_within(span, …).after`), until the companions follow the
  statement. *They do since #579 (2026-11-12):* `raise_span` is written
  with its store as a statement, and `clear_from` is the probe.

  The reflector (`rt_file_reflect.hthr`, built in 4c-3a) reads the
  elaborated body the way the one over `Io` does. Each end of the body
  is a `Mutated` record, and its span is a chain of links back to the
  parameter: a link is a store (`with_byte_within`) or the `.after` of
  a call of a computation of the program. The chain is the order the
  stores and the calls happen in; each link's operands are reflected as
  pure `rt` in the file as that link finds it, and a call's word is
  bound for what follows. A branch that ends in a record in each arm is
  an `If`; the function's own call through its recursor's `ih`, last,
  is `Again`. What it refuses, each with its reason:
  - *The span as it was, read where the byte is not yet known.* No
    `FTm` names an old file. A byte read before a store and wanted after
    it is reflected all the same: the elaborator inlines the `let`, so
    the read's term is of the old span wherever it is used, and the walk,
    which has a path's links and what the path ends in in hand at its
    end, first finds the reads of a state that a later step makes
    (`rt_file_plan`), binds each before the link that ends its state
    (`rt_file_hoist`), and reads the later one as that variable, by its
    state and index (`rt_old_byte`). What is still refused is a read of
    an old state at an index that only a later step computes (a call's
    answer after the store): there is nothing to read it with before
    the store (issues/rt-file-read-before-store.md, closed).
  - *A span that branches and joins.* A statement `if` that stores,
    with code after it, makes the span a `match`; `FTm`'s branches each
    run to an end, and a join would duplicate the rest.
  - *A store under a word that is not the span's length parameter*,
    which the function compiler would refuse later with less to say.
  - *A call of a function that writes and is not in the table.*
  - *Another computation called last, directly.* The body's end would
    be the callee's record, not a record of its `.after` and `.value`.
    This was refused on the belief that the kernel has no η for records;
    it has (a record is a Σ spine, `lib/_tests/lang/record_eta_tests.hthr`),
    so `Mutated(c.after, c.value) ≡ c` and the pin can be a conversion
    (issues/reflect-tail-call-of-computation.md). Calling it and returning
    its word is the spelling that reflects today; only the self-call is
    direct, because the recursor's `ih` is what the continuation of
    `tail_sem` stands for.

- *A loop is the measured recursion, with the file carried.* A writing
  loop is a method that calls itself last (`raise_from` at `i + 1`); the
  reflection says so with `Again`. Its pass is the body lowered in tail
  position (`FTm::lower_tail`): a leaf that returns sets the exit flag,
  a self-call moves its words to the loop's next ports, and the stores
  and calls on the way are the ones the loop-free lowering makes. The
  function around the pass is `rt_loop`'s (`Fun::meas_code`: the kept
  words, the moved words, the bound and the exit flag), unchanged. The
  new proof is the pass over `loop_run` with the file threaded, by a
  measure that may read the span as well as the words.

- *The class states the run.* `Compile<F>(f)` says the code evaluated
  over a file answers as `f` at that file's spans. A function that
  writes has a class of its own, `CompileSpan<F>(f)`
  (`runtime_file.hthr`), whose statement is of the run: over any file
  `Cons(own, rest)`, with its calls answered by the program, the code
  ends with `f`'s word and leaves `f`'s span over `rest`. `f` is the
  function as written, of the span, its length word and its other
  words; the code takes the span's place first, which `f` does not
  read (`FTm::of_source`). A function may also read spans it does not
  write: they follow the written span's length word, each before its
  own, and `f` at a file is `f` at `rest`'s first spans
  (`FTm::Source(tys, lent, …)`, `FTm::read_at`). The meaning below it
  needed nothing for this, since a computation's pure terms are read
  at the whole file; what was of one span was the source's type, and
  with it the callees' table, which is now the writers' meanings at
  every `rest` so that a caller's theorem can be read at each file
  (`CompileSpan.writers`, `FTm::sems_cons`). A call passes its
  caller's read spans on as a pure call does (`rt_file_call`). The
  probes are `runtime_span_reads_tests.hthr`: a byte copied from one
  span into another, stated at every file, and a caller of it twice. A
  loop is the same function at each list of the spans it reads: its
  `ext` companion asks its recursions to agree at every such span, so
  the generator proves the keyed family (`FFun::GuardedBy`, as
  `Fun::GuardedBy` is for a loop that only reads) and
  `FFun::guarded_by` gives `FFun::Guarded` at each rest of the file;
  the measure is keyed with it, and may read the spans. An instance is
  the once-proved lowering read
  at a reflection: `FFun::lower_sound` pinned to `f` by conversion
  where the body has no recursion (`FFun::compile`), and
  `FFun::measured_sound` from `f`'s own recursor where it calls itself
  last (`FFun::compile_measured`).

  The table of such a function is the functions it calls that only
  read, by index, then the ones that write. A loop is not in its own
  table: its recursion is the loop's next pass and never a call.

- *Linking is over the run, a function at a time, over the files a
  writer is known at.* A function is put into a program with its calls
  renamed, and run it ends as it did with each call answered at its new
  name (`Function::relabel_run`, `function_ir_link.hthr`): an equation
  between states at every file, where the evaluation's theorem is
  pointwise.

  The linking theorem over evaluation states each function at the
  program's sources and carries the statement to the program by a
  theorem that functions answered alike evaluate alike. Over the run
  that second theorem would have to follow the file through every
  store, and the statement of a function that writes holds only at
  files with its span first and the rest as it was. So a program is
  proved over a family of files, `emb(s)` for every `s`
  (`program_spanned`): each function, its calls answered by anything
  that answers the functions before it as the sources say over the
  family, ends as the sources say. That is the shape an instance's
  statement already has (`FTm::CallsAgree` quantifies the calls), so
  nothing is carried, and the program's run is its sources over the
  family by induction along the program (`program_spanned_sources`).

  The family is every span with every rest of a file after it
  (`SpanFile`, `span_file`, `runtime_file.hthr`). It was the spans over
  one rest, the rest a parameter of each link, which is enough while a
  callee runs on its caller's file. A callee called over windows
  (§3.1 of the exports note) runs on a file of the windows, another
  rest, so the callees' meanings in a computation's world are at every
  rest (`FWorld.writers`), `FTm::CallsAgree` answers each computation
  at every rest, and a link's two lists are checked at every rest and
  span, still by conversion (`span_every`). Nothing a call on the
  caller's own file uses changed: it reads the meanings at the world's
  own rest.

  Two things are said of what answers the calls (`Writers::Sourced`):
  a call of as many words as the function takes ends as its source
  does, and a function marked still leaves the file whatever it is
  called on. The second is what a pure term's region beside functions
  that write asks of the pure functions it calls
  (`StructuredRegion::run_quiet_among`), at every call and not only
  the fitting ones.

  A function that only reads is linked from its `Compile` instance as
  it is and the fact that its code stores nothing: it runs as it
  evaluates with its calls answered by the words its callees return
  over the file, and leaves the file (`Function::run_still`,
  `Compile::spanned`). So linking sees one shape, a table of `Writers`,
  and a program of both kinds is proved at every file with a span
  first. What a link checks per function is what `Compile::part`
  checks: that each name is answered by the meaning the function's own
  table has for it, by conversion, and that it takes as many words,
  two short lists. A reading function's links are checked against the
  arities of the functions marked still alone (`still_arity`), which
  gives both facts in the one check. That a reading function's code
  stores nothing is read off the code once per link today; it belongs
  in the instance, or in a theorem of the pure lowering
  (issues/rt-pure-regions-are-quiet.md).

- *The generator is the one `runtime fn` has, told by the type.* A
  function whose type ends in `Mutated` writes; any other only reads
  (`runtime`, `runtime.hthr`). For one that writes the generator
  reflects it over the file, with every `runtime fn` it calls found by
  name and sorted into the ones that only read (their `Compile`
  instances) and the ones that write (their `CompileSpan` instances);
  builds its instance, by `FFun::compile` where the reflection's
  meaning converts to it and by `FFun::compile_measured` where it calls
  itself last; links it with everything it reaches, of either kind,
  each function one `spanned` step; and publishes, beside the function:

  | name | what it is |
  |---|---|
  | `f::rt`, `f::world`, `f::writes` | the reflection, the functions it calls that only read, the ones that write |
  | `f::code`, `f::compile` | the FunctionIR function and the `CompileSpan(f)` instance |
  | `f::program`, `f::arities`, `f::stills` | the linked program, how many words each function takes, which of them leave the file |
  | `f::runs_over` | `program_run(f::program, Cons(span, rest), root, [place, length, xs…]) = FTm::end_of(rest, f(span, length, xs…))`, at every span, rest, place and words |

  Nothing in the group is proved about `f` for `f`. A loop's equation
  (`FFun::Guarded`) is spelled by the generator from the recursor's
  companions, as the pure loop's is, and its measure is the function's
  own `decreases` term read at the words and the span, which has to be
  a word's `toNat` so that it is below 2^64 by that alone. What a
  tool's call does is then one step from `f::runs_over` with no
  evaluation of bytes: `program_writers` hands the function the home of
  the buffer it is lent, and takes the span back
  (`raise_span_called`, `native_tool_spans.hthr`).

  What the generator refuses in this round, each by name: a parameter
  or result beside the span that is not a 64-bit word (the pure
  generator's representations are not carried over yet); a loop with
  no `ext` companion; a callee that writes and is an ordinary `fn`; and
  whatever the reflector refuses. The names it publishes mention
  `runtime_file` and the linking modules, so a module that declares
  such a function imports them, and a module whose `runtime fn`s only
  read does not pay for them.

The layer over Linux lives in such a program without joining it yet.
What its theorems ask of the program's functions is that the ones a
pure term can call leave the file (`Writers::Still`), which a linked
program's marks decide (`program_writers_stills`); a function that
writes may sit beside them. A computation over `Io` that calls such a
function is one node the layer over Linux does not have yet.

The two computation layers nest and do not merge
(`docs/native/native-procedures-are-functions-design.md` §2.8, which corrects
what this section said before it). `ETm` lowers to a `Source`'s
statements and the layer over the file to a region, and a statement is
over regions, not beside them: one computation type with `Invoke`
beside `Put` would still need the region lowering for every function
without `Invoke`, the exports among them. So `ETm` gains the call of a
function, a writer included, as one node lowered to a `Compute` of a
region `Call`.

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
  - **U3b. A program's `Call` passes buffers.** *Built 2026-11-11*
    (§2.3): placeless functions, `run` answering a call over its buffers,
    the call's code supplying the static homes, and `Lends` from the claim
    between statements. *Runs:* `wc -l` with each read's newlines counted
    by `count_newlines` (`native_tool_spans.hthr`), a function lent the
    buffer, beside GNU's (`crates/cli/tests/native_tools.rs`). The
    function was written as FunctionIR until U3c step 3c.
  - **U3c. A `runtime fn` reads a span**, so the loop is Heather source;
    the scanner's loop is the customer. Designed in §2.3, in three steps
    that each leave the library whole.
    - *Step 1, built 2026-11-11:* `rt`'s read term and its lowering with
      its theorem, for a function without a loop, and every statement of
      the lowering over the world's file. *Runs:* probes by evaluation,
      and the lowered code accepted by the function compiler.
    - *Step 2, built 2026-11-11:* measured loops keep the home words in
      place, and `Guarded` is stated at every file at once
      (`Fun::GuardedAt`; keyed since 2026-11-12, `Fun::GuardedBy`).
      *Runs:* a newline count over a span, by
      evaluation, proved to compute its Heather function at every span.
    - *Step 3a, built 2026-11-11:* the class at every file, one code
      per function, and the generator's instances for spanless functions
      under it. *Runs:* a span read and a span loop as instances built by
      hand through the generator's own builders
      (`lib/_tests/native/runtime/runtime_spans_tests.hthr`).
    - *Step 3b, built 2026-11-11:* the reflector reads a span parameter
      and the generator makes the instance. *Runs:* the same read and
      loop as `runtime fn`s, a read of two spans, and a lent function
      calling a spanless one
      (`lib/_tests/native/runtime/runtime_lent_tests.hthr`).
    - *Step 3c, built 2026-11-11:* linking over a file, a lent function
      calling a lent one, and a tool's call proved to answer as the
      Heather function. *Runs:* `wc -l` with `count_newlines` a
      `runtime fn` (a loop and the function that starts it), beside
      GNU's.
- **U4. Buffers written** (§2.6), in steps that each leave the library
  whole.
  - *Step 4a-1, built 2026-11-11:* the stack's half
    (`lib/std/arch/x86_64/x86_64_lending.hthr`): `Spans`, the laws of a
    lending (`Loan`), `Stack::WroteIn`, what a span reads along the way
    (`own_reads`, `put_reads`, `put_keeps`) and what a caller keeps
    (`unchanged`, `resident`, `unwritten_reads`); `Stack::Lends` follows
    (`Loan::lends`). The instance is `DataRegion::loan`
    (`x86_64_byte_memory.hthr`): spans inside a region at or above `top`,
    a written one sharing no byte with another. *Runs:* nothing new; the
    probes lend two spans of any region, one to write, and show that no
    lending has a written span starting where another does
    (`lib/_tests/std/arch/x86_64/x86_64_lending_tests.hthr`).
  - *Step 4a-2, built 2026-11-11:* FunctionIR's half
    (`lib/native/function_ir/function_ir_writes.hthr`): the relation
    that threads the file (`StructuredRegionRunsOver`, `Function::Runs`,
    `program_effects`, a call's `Effects` relating the file before to
    the word and the file after), and the fixed-file relation embedded
    in it for a program with no store (`StructuredRegion::runs_quiet`,
    `program_effects_quiet`). *Runs:* nothing new; the probes show a
    store running to the file with its byte set and to no other, a load
    after a store reading the byte stored, and a caller's file being the
    one its callee leaves
    (`lib/_tests/native/function_ir/function_ir_writes_tests.hthr`).
  - *Step 4a-3, built 2026-11-11:* the function compiler's contract over
    the laws with the file threaded (`function_ir_lower_calls.hthr`): a
    `Lending` says which spans may be written, a call is entered over
    the file now (`Stack::CalledOver`) and answers with `WroteIn` and
    the file its meaning leaves in memory (`Stack::AnsweredOver`), and
    `lower_program_lent_correct` is `Site::CallsOver` against
    `program_effects` under any `Loan`. A leaf with a store was still
    refused at this step, so every lowered program was quiet and the
    fixed-file statements followed: `lower_program_correct` keeps its
    statement, at a loan of nothing (`Stack::loan_nothing`), and
    `compiled_returns_lent` now holds over any file as long as the one
    lent. `Source` supplies the laws (`Target::loan`). *Runs:*
    everything that runs today, its bytes unchanged; the probes add a
    function answering over a file other than the one its lending was
    made over (`function_ir_lower_reads_tests.hthr`).
  - *Step 4a-4, built 2026-11-11:* the store leaf
    (`function_ir_lower_reads.hthr`: `leaf_store`, `File::store_at`), its
    machine run (`store_emits`: the trail kept through a byte put into a
    written span, `Stack::trail_put`), and the theorems under `allowed`
    (`program_stores`); `compiled_returns_over` is what a caller cites
    for a program that stores, and `compiled_returns_lent` its case for a
    quiet one. `Prog::links` checks `program_quiet` until step 4b, so a
    program's calls are as they were. *Runs:* nothing new at the doors;
    the probes compile a byte stored under its bound, with its code
    spelled and its answer over a file proved through a meaning written
    by hand, and a loop that rewrites a buffer accepted with its
    contract, and refuse a store with no bound, no home, no register for
    its output or its value, or through the door without buffers
    (`function_ir_lower_reads_tests.hthr`).
  - *Step 4a-5, built 2026-11-11:* a storing program's meaning computed
    (`lib/native/function_ir/function_ir_run.hthr`): `program_run`
    answers a call with its word and the file it leaves (`Ending`), a
    region's calls answered by callees that may write (`Writers`), over
    `function_ir_state`'s nodes and loop. `program_run_effects` proves the answer one
    `program_effects` allows for an evaluable program, by the route
    `program_eval_reads` takes with the file threaded, and
    `compiled_returns_run` states the code's answer by it. *Runs:* a loop
    that rewrites a span ("abc" to "bcd", returning 3) and a byte stored
    under its bound, by evaluation, with the code's answer over the file
    in memory (`function_ir_lower_reads_tests.hthr`); a caller reading
    what its callee stored, which evaluation over a fixed file does not
    (`function_ir_run_tests.hthr`).
  - *Step 4b:* a program's call of a function that writes, in four steps.
    *Runs:* `tr` with its byte map as a called function over the buffer,
    beside GNU's.
    - *4b-1, built 2026-11-11:* the threaded run is placeless
      (`function_ir_placeless.hthr`, `program_run_placeless`): under the
      check a reading program already passes (`program_placeless`), two
      calls whose words differ only at the addresses of lent buffers end
      in the same word and the same file. A store's address is its
      buffer's home plus an index, which the check keeps out of every
      value, so the section is the reading one with the file carried
      (`State::Apart`: values alike off the hidden ones, files equal).
      *Runs:* a store under its bound answering the same at every
      address, a caller of it, and refused: an address stored as a byte,
      a store at an address, with the two files that differ shown
      (`function_ir_placeless_tests.hthr`).
    - *4b-2, built 2026-11-11:* one evaluator. `StructuredRegion::run`
      (`function_ir_state`) answers a call with the callee's word and
      file (`Ending`, `Writers`; `run_writing` is gone). A source's calls
      are `program_writers(src.functions)`: the function run over the
      buffers it is lent, on their stated homes and the call's words,
      and the caller's file with those buffers as the function left
      them (`relent`). A program that stores nothing answers with the
      word it did and the file as it was (`program_run_quiet`,
      `program_writers_quiet`), so the tools' statements are what they
      were, and the compile's proofs take that as a side condition
      (`Writers::Quiet`) until step 4b-3 proves the call without it.
      The run's ending is named `Ending` (`Answer` is the tactic
      library's). *Runs:* a program's call of a storing function stated
      with its words alone, its second buffer left as it was
      (`function_ir_placeless_tests.hthr`); `count_newlines` in a tool's
      meaning (`native_tool_spans_tests.hthr`).
    - *4b-3, built 2026-11-11:* the program compiler proves the call.
      A program lends its buffers to write (`Target::lending`, every
      span written) and proves the lending's laws for them from its
      data region's (`Target::loan`). What a call leaves is a file
      (`Target::Left`: the memory holds some `after` under the
      contract's post, and the caller's file is `relent` of it), the
      claim between statements is rebuilt over that file
      (`Target::held_left`, since U5 `Target::based_left`: the cells a
      callee stored into read the new bytes, the rest are kept by
      `WroteIn`), and `Target::answers_of`
      cites the function compiler's theorem under the program's own
      stores (`program_run_placeless`, `program_run_effects`).
      `Prog::links` no longer asks `program_quiet`, and the compile's
      proofs no longer take `Writers::Quiet`; the `rt` IO layer keeps it
      until 4c gives `rt` a write. *Runs:* a program whose statement
      reads the byte its callee stored, compiled, with a store
      elsewhere and one past the capacity beside it
      (`native_build_tests.hthr`).
    - *4b-4, built 2026-11-11:* `tr`'s loop as a called function.
      `raise_span` (`native_tool_spans.hthr`) is lent the buffer and
      makes one pass per byte: a load, a call of `raise_letter` (the
      word function the tool already called), and a store, the load and
      the store under the pass's one test of the index against the
      length. It is written as FunctionIR, since `rt` has no write until
      4c, so what it does is stated by evaluation and not yet at every
      file; 4c's `runtime fn` replaces it and brings that statement.
      Nothing in either compiler changed for it: a call between a load
      and a store in a loop over a lent buffer is what 4a built. *Runs:*
      `tr_upper_span_tool` beside GNU `tr`
      (`crates/cli/tests/native_tools.rs`); the function over "aZz{" at
      any address, a count short of the span and past it, and a
      program's statements reading the raised bytes after the call
      (`native_tool_spans_tests.hthr`, `native_build_tests.hthr`).
  - *Step 4c:* a `runtime fn` writes a span (§2.6), in four steps.
    *Runs:* `tr`'s loop as a `runtime fn`, stated at every file.
    - *4c-1 (built 2026-11-11):* the computation layer and its meaning
      (`FTm`, `FFun`, `FWorld`, `rt_file.hthr`), its loop-free lowering
      and that lowering's theorem over the run (`FTm::lower_sound`,
      `FFun::lower_sound`, `rt_file_lower.hthr`): the code a computation
      function lowers to, run on any words over any file
      `Cons(own, rest)` with its calls answered by the program
      (`FTm::CallsAgree`), answers the meaning's value and leaves the
      meaning's span over `rest`. What the build settled:
      - *One promise for every step.* A bound pure term, a call and a
        whole computation each promise the same thing of the region they
        lower to (`FTm::StepHolds`, over any meaning of the step), so the
        induction composes promises (`FTm::bind_sound`, `FTm::put_sound`,
        `FTm::if_sound`) and never reads a term.
      - *A pure term beside functions that write.* Its region is
        `Tm::lower`'s, unchanged, and its theorem is `Tm::lower_sound` at
        the world of the file as it is then; the bridge from that
        evaluation to the run is `StructuredRegion::run_quiet_among`
        (`function_ir_run.hthr`), which asks stillness only of the
        functions the region calls. That the region stores nothing and
        calls only pure functions is checked by evaluation where it is
        lowered (`FTm::value_checked`); both hold of every region
        `Tm::lower` builds, and a theorem saying so would retire the
        check (`issues/rt-pure-regions-are-quiet.md`).
      - *The program's order.* Pure functions sit below computations:
        computation `f` is FunctionIR function `base + f`, `base` the
        count of pure functions, so a pure function cannot call one that
        writes and the stillness the bridge asks is of indices below
        `base`.
      - *The store's shape.* The index against the length word is a leaf
        of its own, and the arm it guards widens the byte and stores it,
        the store a leaf of its own (`FTm::put_region`). The function
        compiler knows the comparison where the test ends its leaf: with
        the widening after the test in one leaf it refuses the store.
      - *Kept for the optimizer.* A store of a word's low byte narrows
        the word (`Trunc`) and `Put` widens it again: two `Resize` nodes
        the store does not need.

      *Runs:* `poke` (a store), `poke_low` (a store under a branch) and
      `poke_pair` (two calls of `poke`, then the first byte read back
      from the span they left), each pinned by conversion at any span,
      instantiated from the once-proof over any file, run on bytes and
      accepted by the function compiler; four refusals and a control
      (`lib/_tests/native/runtime/rt_file_tests.hthr`).
    - *4c-2 (built 2026-11-11):* the measured loop with the file carried
      (`rt_file_loop.hthr`). `FTm::Again(args)` is the function calling
      itself last; `FTm::tail_sem` is the body's meaning with that call
      answered by a parameter; `FTm::lower_tail` lowers the body as one
      pass and `FFun::lower_measured` puts `rt_loop`'s loop around it
      (`Fun::meas_code`, the pure loop's code and ids). The theorem is
      `FFun::measured_sound`: for a function `h` of the span and the
      words that the body computes when its self-call is answered by
      anything agreeing with `h` below a measure (`FFun::Guarded`), the
      measure below 2^64 (`FFun::Bounded`), the code run on any words
      over any file `Cons(own, rest)`, its calls answered by the
      program, answers `h`'s word and leaves `h`'s span over `rest`
      (`FFun::MeasuredHolds`). What the build settled:
      - *The recursion is a continuation, as in the pure layer.* The
        first sketch gave a pass a datatype of turns (left with a value,
        or went round with words); what was built is `rt_loop`'s shape
        instead. A pass's promise (`FTm::Turn`) is an equation at every
        continuation: leaving the pass, with the continuation resumed on
        the file the pass left, ends as the meaning does with its
        self-call answered by that continuation. So the cases compose as
        4c-1's do (`FTm::tail_bind_sound`, `FTm::tail_put_sound`,
        `FTm::tail_if_sound`), with two leaves (`FTm::tail_leaf_sound`,
        `FTm::tail_again_sound`).
      - *One conjunct the pure loop has no use for.* The promise also
        says the file the pass left has its other spans as they were
        (`FTm::Spanned`). The equation alone does not: where the pass
        goes round, it speaks through a continuation that reads only
        span 0, and the loop's induction needs the next pass to start
        over a file of the same shape.
      - *The measure reads the span.* It is `m(words, span)`, and the
        hypothesis `Guarded` gives about the self-call is at every span
        below the measure, since the pass hands on the span it wrote.
        That is the shape of the recursor's own `ext`, so a function's
        `Guarded` is its `ext` and `irrel` and nothing about the bytes.
      - *The loop theorem is over any state a file is made from.*
        `loop_run_agrees_measured<S>` (`function_ir_run.hthr`) runs a
        loop whose pass is known as an equation between endings against
        a recursion on `S` and the words, with the file `emb(s)` and an
        invariant on endings; the written span over a fixed rest is its
        first instance.
      - *The self-call is not a call.* The loop's code never emits a
        `Call` of its own index, so the hypothesis about the program's
        calls (`FTm::CallsAgree`) is about callees only and a loop with
        none takes the empty one. Outside a loop `Again` lowers as a
        call of computation 0; where a loop sits in its own table is
        linking's to say (4c-3).
      - *The function compiler takes the loop as generated.* The pass's
        test ends its leaf and the store is a leaf of its own, as 4c-1
        made them, so nothing in `function_ir_lower*` changed.

      *Runs:* `bump_from` (every byte from an index up by one) and
      `raise_from` (every byte through `raise`, a pure function of the
      program called between the load and the store, the program the
      loop above its callee). Each is lowered by evaluation, accepted by
      the function compiler lent one buffer, run on bytes, pinned to the
      recursor's step by conversion, and proved from the once-proof at
      every span, every rest of the file, every place and length word
      (`bump_called`, `raise_called`); the callee's side of
      `FTm::CallsAgree` is `program_run_quiet` and the pure once-proof
      (`raise_agrees`)
      (`lib/_tests/native/runtime/rt_file_loop_tests.hthr`).
    - *4c-3a (built 2026-11-11):* the reflector for a function over a
      span (`rt_file_reflect.hthr`; §2.6 has what it reads and what it
      refuses). `rt_file_reflect(computations, functions)` reads a table
      of writing functions over a table of pure ones and gives each
      `FFun`; a function with a recursor (`f::body`) is read as a loop,
      its body opened under the bound and `ih`. The pure reflector is
      the one the operands go through: its `Known` carries the file's
      state (`FileKnown`: which term is the span now, the calls so far
      and their words), so a read is of span 0 only when its list is the
      span as it is, and a writing call's `.value` is its variable.
      `List::put_within` is the `mut self` store beside
      `with_byte_within`. *Runs:* `reflects_file_as` holds four sources
      to the reflections 4c-1 and 4c-2 wrote by hand: `poke` (a `mut
      self` store), `poke_low` (a function returning `Mutated` under a
      branch), `poke_pair` (two calls of `poke` and a read of what they
      left) and `raise_from` (the loop, with `raise` its pure callee).
      Each reflection is pinned to its function by `refl`, the loop's
      to its recursor's step; four bodies are refused with their reasons
      (`lib/_tests/native/runtime/rt_file_reflect_tests.hthr`).
    - *4c-3b (built 2026-11-11):* linking over the run
      (`function_ir_link.hthr`) and the class (`runtime_file.hthr`);
      §2.6 has the design. `Function::relabel_run`;
      `program_spanned` and `program_spanned_sources` over a family of
      files; `Function::run_still`; `CompileSpan<F>(f)` with
      `FFun::compile` and `FFun::compile_measured`;
      `CompileSpan::spanned` and `Compile::spanned`, one conjunct of
      `program_spanned` each. *Runs:* the loop that raises every byte
      of its span, a `CompileSpan` instance from its reflection and its
      recursor, linked by hand with two `runtime fn`s, `raise` (which
      it calls, and which the program numbers otherwise than the loop's
      table does) and `twice` (which it does not). The program runs on
      bytes, is accepted by the function compiler, and its run is the
      loop at every file with a span first (`linked_raises`) and
      `raise` with the file left (`linked_raise`), from the instances
      alone; a link that names the wrong function is refused by the
      kernel (`lib/_tests/native/runtime/runtime_file_tests.hthr`).
    - *4c-3c (built 2026-11-11):* the generator (`runtime.hthr`; §2.6
      has what it publishes and what it refuses). `runtime fn` on a
      function whose type ends in `Mutated` reflects it over the file,
      builds its `CompileSpan` instance, links it with every
      `runtime fn` it reaches and publishes `f::program` and
      `f::runs_over`. *Runs:* a store, two calls of a function that
      writes with a read of what they left, a loop with a callee that
      reads, a loop with a callee that writes, and a function whose
      reading callee is lent the span it writes, each stated at every
      file from its generated theorem, run on bytes and accepted by the
      function compiler; three bodies refused with their reasons
      (`lib/_tests/native/runtime/runtime_span_tests.hthr`).
      `raise_span` is a `runtime fn` (`native_tool_spans.hthr`), the
      FunctionIR written by hand is gone, and `tr_upper_span_tool`
      calls the generated program: `write-elf` compiles it with its
      certificate and it runs as `tr a-z A-Z`. What a call of it does
      at every buffer is `raise_span_called`. *Found:* a `decreases`
      arm with a `mut self` call statement has no `ext` companion
      (issues/decreases-mut-call-statement-companions.md, fixed by
      #579); the compile
      of a tool over a generated program is not one kernel evaluation,
      so the build probe states that the function compiler takes the
      program and leaves the whole compile to `write-elf`.
    - *4c-4 (built 2026-11-11):* the layer over Linux drops
      `Writers::Quiet`. Its theorems (`ETm::lower_sound`,
      `ELoop::lower_sound`, the `lower_reads` of each) asked that every
      function of the program leave the file; they ask it now of the
      functions a pure term can call (`Writers::Still` among
      `functions_below(w.sigs.len())`, `function_ir_run.hthr`), which
      the lowering holds each pure region to by evaluation
      (`ETm::value_checked`), and the moves of a loop's rebinding ask
      nothing. So a computation over `Io` is its meaning in a program
      whose other functions write. Which functions of a linked program
      leave every file is one check of its marks (`program_stills`,
      `program_run_still`, `program_writers_stills`,
      `function_ir_link.hthr`), the marks the generator publishes as
      `f::stills`. *Runs:* the echo probes hold with the program's
      functions answering anything; a computation that reads and
      answers `raise_word` of the count is its surface method with its
      calls answered by `tr`'s program, where `raise_span` writes
      (`lib/_tests/native/runtime/rt_io_among_tests.hthr`).
      *Not here:* a computation over `Io` that itself calls a function
      that writes. That is a node of the computation language. This
      entry first said U5 would merge the two layers and the node would
      otherwise be built twice; the U5 note finds they nest instead
      (its §2.8), so the node is built once, in its own round
      (`issues/rt-io-calls-functions.md`), and does not wait on U5.
    - *4c-5 (built 2026-11-12):* that node. `ETm::Lend(f, cap, buf,
      args, body)` lends buffer variable `buf` and word variables `args`
      to function `f` of a table of lent functions (`Lent`: an arity and
      a run returning the bytes left and a word), and binds the bytes and
      the word. Its meaning is the table's run, the world unchanged; its
      lowering is `Compute` of a region `Call(base + f, ids, next)`, the
      functions lent numbered after the world's pure ones. Every earlier
      variable on the buffer is gone afterwards (`Loc::forget_all`), so a
      read of the bytes before the call is refused. The soundness theorems
      take one more hypothesis, `ETm::LentsAgree`: the program's function
      `base + f`, lent the file's first buffer, answers as the table's run
      and leaves the rest of the file. The lowering checks the buffer is
      the first (the prefix limit, `issues/source-buffers-as-views.md`).
      `Kept` at a buffer is now `env.buffers.nth(id) = Some(v)`, so a
      buffer's being there is part of the invariant. A loop's condition
      was moved to a fresh word at one bit, which the compiler refuses;
      a bit whose region's last node writes it at one bit now stays in
      that port (`ETm::placed`, `ETm::bit_kept_sound`). *Runs:* `tr` as
      one `ELoop` over `Io` (read, `Lend` to `raise_span`, write, while
      the count is nonzero) is proved to read as its meaning, compiles
      (`tr_lend_source`, since replaced by the `runtime fn tr_upper`,
      docs/native/io-programs-design.md §3), and matches GNU tr
      (`lib/_tests/native/runtime/rt_io_lend_tests.hthr`,
      `native_tools.rs`). *Not here:* the reflector does not read a call
      of a `runtime fn` on a buffer as `Lend`, and it reads no loops yet;
      a failed write cannot end the computation with status 1, since
      `ETm` has no exit.
  - *Step 4d, with U5:* `write-elf`'s own byte nodes move to the shared
    lowering. A program's own region reaches its buffers by the data
    region's addresses, as immediates; the shared lowering reads a home
    from two parameters and stores under the test against the length
    word. The two meet when a program's statements are a function's body
    and its static buffers are homes `main` is lent (§2.5), which is
    U5's frame change. Done before it, the step would re-prove the
    program compiler's byte nodes over global homes that U5 removes.
- **U5. Procedures are functions** (§2.4), designed in
  `docs/native/native-procedures-are-functions-design.md`: 5a RSP is the frame
  (built), 5b words in the frame and the callee saves (built), 5c one
  call and one contract (built: `Target::Callable`, a function and a
  procedure each an instance), 5d one byte lowering (step 4d above; moved
  by Minus on 2026-11-11 to go with buffer views,
  `issues/source-buffers-as-views.md`). *Runs:*
  the tools with procedures (`grep -F`) rebuilt on it.
- **E. Export.** Generated declarations, the contract's controls, the
  scanner's loop linked into Rust
  (`docs/native/native-library-exports-design.md` §6, §10 R3). Built: the
  declarations and the controls, on a first function that reads a span
  (§6.1 there), and the scanner's loop, `scan_token`, linked and called
  once a token (§6.2 there). The write half's export is its own round.

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
  stay two, as their targets do: U5 makes the targets one in the machine
  and leaves a region and a statement two kinds of meaning.

## 5. What this does to the exports note and the issues

`docs/native/native-library-exports-design.md` keeps its §3 to §8 as the design of
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
