# One native compiler: joining `write-elf` and `compile-x86`

Status: **direction set by Minus 2026-11-11** ("unify first and then
export"); this note scopes it. U1, U2 and a program's call of a function over a
buffer (U3a, U3b) are built (§3). Owner:
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
  placeless and emits each under its count of lent buffers
  (`program_counts`). A function lent nothing is called by the code it
  was.
- *The proof* (`native_compile_function.hthr`). The function's contract
  (`Site::CallsLent`, at every address and over every buffers) is cited at
  the placed homes over the buffers lent, and `program_eval_placeless`
  turns its answer into the stated one (`Target::answers_of`; the joints
  are `homes_apart`, `args_lent_placed` and `program_counts_lent`,
  `function_ir_lend.hthr`). `Lends` comes from the claim between
  statements, which places every buffer's bytes in the data region
  (`Target::buffer_readable`) and which stores below the running frame
  keep (`held_wrote`): so the buffers are lent to the call as they are
  when it is entered (`Target::lent_all`), with no fact about where the
  region lies beyond what `Target` already holds. A buffer of a source is
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
  (`Setup::plain_agrees`, `fuel_agrees`, `measured_agrees`), so an
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
  proves is `Guarded` at every world of a family at once
  (`Fun::GuardedAt`, the index being the span): `again` answers at every
  index and agrees with the function below the measure at every index,
  which is exactly what `ext` can use. `Fun::guarded_at` brings it back
  to `Guarded` at one world, by answering with the function wherever
  the hypothesis speaks and with that world's `again` elsewhere; the
  body's meaning reads its recursion only at the calls it makes
  (`Tm::tail_sem_ext`). The loop theorem itself does not change, and
  `Fun::measured_sound_at` is it at each index. The family is the class
  at every file seen from one function, so step 3's generator proves
  `GuardedAt` as it proves `Guarded` today, with the span a binder of
  each ih. If `decreases` comes to leave fixed parameters outside its
  recursor, the family is no longer needed and can go.

  In the class this is `Setup::Guarded`: `Guarded` at every file, each
  obtained from the family at that file's span 0
  (`Fun::guarded_at(…, b.span(0))`), which converts because the body
  and the function read a file only through that span. The family is
  indexed by the span and not by the file for that reason: `again` at a
  file and `again` at the one-span file of its span are not convertible.
  So a loop is lent one span for now; a loop over two is a family over
  pairs, built when something needs it.

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
  (`Setup::lent_every`, and `f::reflects` is stated over the file). A
  loop over one span proves `Setup::GuardedSpans`, the family of §2.3's
  step 2 at the one-span files, with the generator's usual proof from
  `f::ext` and `f::irrel`: the span is the statement's first binder and
  each ih's, and every recursive answer is asked at the place the loop
  was entered with. `Setup::guarded_span` brings the family to each
  file's span 0, and that is `Setup::Guarded` by conversion at the
  function's own body. A loop over two spans is refused (the family has
  one index).

  Linking over a file (step 3c, built). The evaluator's two linking
  lemmas are stated over the buffers (`Function::eval_answers_over`,
  `Function::relabel_eval_over`; the old ones are these at no buffers),
  and a program is linked at every file at once:
  `program_linked_files(functions, arities, sources)` asks each function
  to answer as `sources(b)` says over each file `b`, and
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

What it leaves open, on purpose: a span that is written. A write makes
the buffer a result as well as an input, so U4 decides whether the file
becomes state the meaning threads or the function returns the new
bytes; the world is the right place for a span only while it is read.

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
      (`Fun::GuardedAt`). *Runs:* a newline count over a span, by
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
