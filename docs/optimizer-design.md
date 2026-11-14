# A proved optimizer: plans replayed, rules as theorems, proofs requested

Status: design agreed by Minus 2026-11-14 ("Good design"); built parts are
named in §9. It extends `docs/compilation-vision.md` (principle 3, §2.3,
§2.4, §6.2) and does not re-derive it. What prompted it is the first
measurement of emitted code, [linked-sha256-speed](../issues/linked-sha256-speed.md).
The brief, in Minus's words: "elegant and extendible, rather than a big naive
list of passes", free to use research-level techniques, and with "the ability
to 'request' a proof from a function, wherein you know a high-value
optimization can be done. Sometimes the proof is immediately available (it is
already in that context), other times it can be found by a fuel-search (like
how a typical optimizer checks things, and may want to store information), or
just work abstractly."

## 1. The design in short

The optimizer is three small things proved once, and three open things that
grow without any new soundness proof.

**Proved once**

- **A replayer** for each code level. It takes a program and a *plan*, which
  is a list of moves, and returns the program with the moves made, or
  refuses. Its one theorem says that whatever it returns means what the input
  meant. Nothing else in the optimizer is trusted or proved.
- **A short list of moves** the replayer knows: rewrite by a rule at a place,
  share a value, drop a value nothing reads, put a callee's body where its
  call was, learn a branch's condition inside its arms, and run a loop over a
  different state.
- **The request**: how a move that needs a fact asks for it, and the kinds of
  answer the replayer accepts.

**Open**

- **Rules.** A rule is a theorem: two patterns over the IR's operators, side
  conditions, and a proof that the sides are equal where the conditions hold.
  An optimization of the rewriting kind is one more theorem in a table. A
  rotate written as two shifts, a word read as four bytes, a strength
  reduction and every constant fold are rules.
- **Fact producers.** Anything that can prove a side condition: what is
  already in scope, a verified analysis, a tactic under a budget, the
  programmer.
- **Searchers.** The code that chooses the moves. It is not trusted at all.
  It can be greedy at first and equality saturation, a superoptimizer or a
  learned cost model later, and none of that changes what is proved.

So a pass stops being a unit of proof. A pass is a searcher: a strategy that
writes moves. The list of passes a conventional compiler has still exists
here, but only as strategies, and a wrong one costs speed, never correctness.

The compiler already works this way in one place. The register planner
proposes a placement and the verified lowering either lowers with it or
refuses (`lib/native/function_ir/function_ir_lower*.hthr`). This design is
that arrangement at every level, with one vocabulary.

## 2. Why this shape

- **Search can be as aggressive as we like.** Soundness never rests on a
  heuristic, a cost model or the order strategies run in. This is principle 3
  of the vision (untrusted search over checked witnesses) taken as the whole
  architecture.
- **The kernel's work stays small.** The one pass that existed before this
  design (constant folding and dead values, `function_ir_pass.hthr`) is a
  Heather function the kernel runs whole. That is fine for a fold. It cannot
  be how a search runs. With plans, the search happens outside the kernel and
  the kernel replays the plan, at a cost that grows with the plan and not
  with the search.
- **An optimization's proof is small and ordinary.** A rule's proof is an
  equation about words or about a list of bytes. Those are the proofs that
  should need no tactic written: most new optimizations become a short
  theorem that `simp` or a bit-level decision closes.
- **The plan is data.** It can be printed, compared between two compiler
  versions, and cut down move by move until the instruction counter changes.
  When emitted code is bad, there is one thing to read.
- **It extends sideways.** A library can ship rules about its own operations
  beside its theorems. A DSL brings its own rule table. A new target brings
  its own. None of them touches the replayer.

## 3. Moves

The replayer's vocabulary is deliberately short. Each move has one law,
proved once. The level is FunctionIR, because every producer reaches it
(`rt`, a DSL, a hand-written instance), so one optimizer serves them all.

| Move | What it does | What its law rests on | Where SHA-256 needs it |
|---|---|---|---|
| Rewrite | Replaces an instance of a rule's left side by its right | The rule's theorem, and its conditions answered | Rotates, a word read as a word, folded constants, a repeated test |
| Share | Two equal values become one | Nothing; structural | The same word read twice |
| Drop | Removes a value nothing reads | A check that nothing reads it | What rewriting leaves behind |
| Inline | A callee's body where its call was | The callee is the program's function at that index | Most of a block's calls are four small accessors |
| Learn | Inside an arm, the branch's condition is a fact; a test of a known condition is its arm | The branch's own meaning | The length test on every byte |
| Restate a loop | Runs a loop over a different state | A simulation between the two states (§6) | The working variables in registers |

### 3.1 What a move's law is, over this IR's meaning

FunctionIR's meaning is declarative: a function's body is a set of
equations over one valuation for the activation (one more for each pass of a
loop), with the file of buffers threaded through the nodes in order
(`StructuredRegionRunsOver`, `Function::Runs`, `program_effects`;
`function_ir_writes.hthr`). The compiled code's contract takes that
relation as a premise: where the program's functions say a call may return
`result` and leave `after`, the code returns it (`Stack::CalledOver`). So
an optimizer from `fs` to `fs'` owes one statement, with the functions kept
at their indexes:

    program_effects(fs)(before, f, arguments, result, after)
      → program_effects(fs')(before, f, arguments, result, after)

Every valuation that satisfies the old body must give one that satisfies
the new. Read move by move, that says where the proof work is:

- **Dropping a node is free.** The new body asks less of the same
  valuation. Nothing about liveness is proved: if a later node reads the
  dropped id, the lowering refuses the program, which is the arrangement the
  planner already has.
- **Rewriting a node in place needs only the rule.** The valuation is
  unchanged, and every equation of the old body in the same scope holds of
  it, whichever side of the node it is written on. The replayer carries
  those equations as the definitions in scope, unfolds the old node and the
  new through them as far as the rule's two sides go, and compares.
- **A node with a new id needs the id to be new.** The valuation is
  extended at that id, so every other equation must not mention it. The
  replayer keeps a bound above every id of the function, takes new ids from
  above it, and the one lemma is that a region whose ids are below a bound
  holds alike of two valuations that agree below it.
- **Inline is that lemma once more.** A call's meaning is that some
  valuation satisfies the callee's body. The inlined body is the callee's
  with every id raised above the bound, and the new valuation is the
  caller's below the bound and the callee's above it. A loop's body has a
  valuation of its own, so nothing inside it is renamed.
- **Learn is the conditional's own meaning.** A conditional holds as its
  taken arm does, so an arm is transformed with the condition's bit among
  the equations in scope, and a conditional whose bit is known is its arm.

Requirements the lowering and the callers check of a program (which
buffers it stores to, that it lends nothing it should not) are computed
again on the new program, so no move owes their preservation.

An idiom that has no node (a rotate, a byte swap, a load of a word) can
arrive two ways, chosen per idiom. A new node costs a case in every match
on the node type, through the meaning and the lowering, and gives the
rules something to speak of: right where the idiom has algebra of its own,
as a rotate does. Or it is selection in the lowering, a place that covers
several nodes as `Folded` covers a constant (§7): right where the idiom is
only an encoding, as a 32-bit move for a narrowing is.

### 3.2 Facts and rules, as the probe built them

A probe of the replayer over the real node type checks, with its theorem
(2026-11-14; `function_ir_replay.hthr` when it lands). What it settled:

- **The proof state is a set of facts**: nodes known to hold of the
  activation's valuation. Every pure node of the old body is one as the
  sweep passes it, kept or dropped.
- **A rule is a clause over nodes with its proof**: premises and a
  conclusion, made from an instance's ids and literals, and one theorem
  that any valuation satisfying the premises satisfies the conclusion
  (`Clause::Sound`, `Rule`). `x + 0 = x` is the clause from a `Const` of
  zero and an `Add` to a `Move`, and its proof is one line about words.
  A rule is written in the IR's own vocabulary, so there is no pattern
  type, no expression type and nothing to unfold: applying a rule is
  finding its premises among the facts.
- **Four moves over a list of nodes**: keep the next node, drop it (never
  a store), derive a rule's conclusion into the facts, and emit a node
  that is among the facts. A rewrite is a drop, some derivations and an
  emit; sharing and copy propagation are rules like any other.
- **One theorem** (`replay_sound`): whatever the plan, the nodes returned
  run wherever the old ones ran, over the same valuation and files, and
  the facts returned hold there.

The fold pass's `Fact` (an id with its constant) and a range, a known bit
or a branch's condition are the same thing with a wider fact type, which
is where requests (§5) attach: an answer In scope is a fact, and an answer
Decided is a fact a rule derived.

What the kernel pays, as a shape: with the facts in a list a move costs a
scan of the function's facts, and a plan for a few hundred nodes runs a
query out of fuel. With the facts keyed by the id a node writes
(`NatMap`), a move costs a lookup, a rewritten node costs a few thousand
kernel steps whatever the function's size, and one query replays a few
hundred of them. A function's plan is therefore replayed a region at a
time with the facts threaded between, as the lowering is.

Memory needs no move of its own. A load after a store at the same index is
the stored value. A store after a store at the same index drops the first. A
load after a store at another index passes over it. These are rules, the
last one with the condition that the indexes differ, which is a request.

Share and Drop exist as parts of the folding pass, and the composition of
moves is the simulation diagrams already in the library
(`function_ir_pass_diagrams.hthr`, `lib/std/relation/transition.hthr`). The
first acceptance test of the replayer is to restate the folding pass as
rules and get the same theorem with less proof.

## 4. Rules: an optimization is a theorem

What an author should write, with the spelling only illustrative:

```heather
rule rotate_right({w: Nat}, a, b: Nat, x: BitVec(w), fits: a + b = w):
    (x >> a) | (x << b) = x.rotr(a)
{ … }
```

That is an ordinary theorem with an ordinary proof. The `rule` prefix does
one more thing: it reflects the two sides into patterns over the IR's
operators and adds the pair, with the proof, to a rule table. The author
never sees a pattern type.

Three kinds of condition, by who answers them:

- **On the instance's literals** (`a + b = w` where the shift counts are
  numbers in the code): decided by evaluation when the rule is applied.
  Nothing is asked of anyone.
- **On values** (this index is below that length): a request, §5.
- **On the program** (nothing between these two stores reads the buffer): a
  check the replayer runs over the nodes between.

What follows from rules being theorems, and is not available to a
conventional compiler:

- **A library's theorems can be its clients' optimizations.** If `Sha2`
  proves that its big sigma is three rotates and two exclusive ors, tagging
  that equation as a rule makes every caller's code use it. The person who
  knows the algebra of a type writes its optimizations, in the type's own
  file.
- **Rule tables are values.** A target has one (what its instructions do
  cheaply), a DSL has one, a constant-time dialect can have a smaller one
  that leaves out every rule whose timing depends on data.
- **Rules can be found by machine.** A candidate rule only needs a proof. So
  a tool can enumerate small terms, keep the pairs that agree on test inputs,
  prove them by a bit-level decision, and keep those that lower the cost.
  Not early work, but the design leaves the door open at no cost.

## 5. Requests: asking for a proof

A move may need a fact about the values at its place: this index is below
that length, these two indexes differ, this word is below 2^32. A
**request** is that proposition, stated over the values in scope at the
place.

The replayer never searches. The plan carries an answer with each request,
and there are five kinds:

| Answer | What it is | Cost | In the brief's words |
|---|---|---|---|
| **In scope** | The fact is already at the place: a branch condition above it, the equation that defines a value, a requirement of the function, an invariant of the loop around it | An index | "immediately available" |
| **Decided** | A verified analysis proves it by evaluation: a range, known bits, "this is that base plus a constant" | One evaluation step per value | "how a typical optimizer checks things" |
| **Proved** | A proof found outside by a tactic under a budget (`omega`, `bv_omega`, `simp`), checked by the kernel | A search, bounded by fuel | "found by a fuel-search" |
| **Required** | The fact becomes a requirement of the optimized function, and each caller owes it at its call | Nothing here; a request at each caller | "work abstractly" |
| **Tested** | Decidable at run time and unproved: test once, branch to the fast copy or the plain one | A test and a second copy | (versioning) |

If none applies, the move is not made, and the code is the plain code.

**Storing what was learned**, in two forms, both checked:

- *Abstract values in the plan.* The searcher attaches to each value what it
  found out about it (its range, its known bits). The replayer checks each
  one from the values it was computed from, one step, no fixed point. A
  loop's invariant is stated in the plan and checked to hold at entry and to
  be kept by a pass. So an analysis is run once, outside, and what the kernel
  sees is its result with enough written down to check it in one sweep.
- *Summaries of functions.* What a function's result is bounded by, which
  bytes it may store to, what it requires. Published beside its compiled
  code like any theorem, kept in the module's image, and recomputed only
  when the function changes. A caller's request about a callee's result is
  then answered In scope.

**Required is the modular answer.** The optimized code is proved to agree
with the function wherever the requirement holds. A caller that calls it
owes the requirement, which is a request of its own with the same five
answers, and so on outward. The record functions already work this way for
one fact: `Stored::Holds` (the span holds the record under its length word)
is a requirement the generator threads through every call. The length tests
in SHA-256 go because `Holds` puts "the length word is at least the record's
size" in scope, and the range of each offset is Decided.

**Requests the compiler could not answer are reported, largest first.**
Something like:

```
Sha256::run: 256 length tests would go
  wanted:  Sha256::stored().layout.size <= length
  give it: a requirement on `run`, or a theorem tagged as a fact about it
```

The programmer answers with a theorem, and the next build uses it. The
compiler asks, a person or a tactic answers, the kernel checks. An
optimization report in a conventional compiler says what it failed to do;
this one says what proof would let it.

### 5.1 How a fact reaches the lowering: it is an equation in the code

A test that goes leaves a load with no test above it, and the lowering
takes a load only where the path knows its index below the buffer's length
(`File::bounded`). So what the replayer proved has to arrive there, and it
does so without a new construct and without a second analysis in the
lowering.

A function's meaning is the valuations that satisfy its nodes' equations
(`Function::Runs`), and nothing in that meaning says an id has one
equation. So a fact is written as one more: after
`UnsignedLessThan(64, c, i, n)`, the node `Const(1, c, 1)` says the same
bit is one, and the two hold together exactly where `i` is below `n`.

- *Adding an equation the others imply keeps every run.* That is the law
  the replayer already has for `Derive` and `Emit`: the conclusion of a
  rule whose premises are facts is a fact, and a node among the facts may
  be written into the code.
- *Dropping one keeps every run too*, trivially, so a pass that does not
  understand an assumption may lose it and stays sound. What is lost is
  only speed: the lowering refuses the load and the function stays as it
  was.
- *The lowering reads it for free.* A comparison placed `Folded` emits
  nothing and is known as `Compared`; a one-bit constant placed `Folded`
  emits nothing and is known as `Truth` or `Falsity`, which is what an arm
  taken would have told it. `File::bounded` is unchanged.
- *A requirement is an assumption nothing in the function implies.* A
  function whose body assumes `K <= length` has no run where that fails, so
  a caller that has a run satisfied it, and the theorem about the compiled
  program is about the runs the source has. Required needs no mechanism
  beyond this one; what it needs is the producer stating the requirement
  and its own proof of the run using it.

The facts themselves are wider than nodes by one kind so far,
`Within(id, low, high)`: a word's value as a number lies between two
literals. Ranges are not an analysis built into the replayer. They are
rules like any other, a theorem each (a constant's range, a sum's where it
cannot wrap, a shift's, a narrow value's, the two a branch's condition
gives its arm), found among the facts by entailment: a premise
`Within(id, low, high)` is met by any known range inside it. The searcher
runs whatever analysis it likes and writes down only the derivations a
decision needs, so the kernel replays a few steps a test and never a fixed
point.

Learn is then three things. An arm starts from the facts before the
conditional and its condition as a constant. A comparison whose operands'
ranges decide it derives that constant (a rule). And a conditional on a
bit the facts say is constant is its arm (`Plan::Take`).

This builds on what exists: facts as propositions with several producers,
searched cheapest first, with a budget, is the facts-on-demand prototype
(`docs/facts-on-demand-design.md`), and the request from a generator is its
`Synth`. What is new is that requests are tied to places in a plan, that
Required and Tested exist, and the report.

## 6. Loops: one law, many optimizations

A conventional compiler has a pass each for keeping memory in registers,
strength reduction, moving invariant code out, hoisting checks, unrolling.
Here they are one law with different choices of a relation.

**The law.** A loop over state S with step s may be run as a loop over state
T with step t when there is a relation R between the two states such that R
holds at entry, a step of t from a state related to an S state lands in a
state related to s's step and exits when it does, and the result is read
back through R. That is a simulation, and the library has the diagrams for
it (`lib/std/relation/transition.hthr`).

**The instances**, each a choice of R:

| Optimization | T is S with | R says |
|---|---|---|
| Fields in registers | some of the buffer's fields also held as words | the buffer with those words stored back is S's buffer |
| Strength reduction | one more word `j` | `j = 4 * i` |
| Invariant code out of the loop | one more word `v` | `v` is the value computed from the loop's inputs |
| A check hoisted | nothing more | a fact, such as `i <= n`, which then answers requests inside the body |
| Unrolling | nothing more | one step of t is two steps of s |

The first row is the largest step for SHA-256. In this design it is not a
special pass. The plan says which fields to lift, the step t is the old body
after the memory rules have forwarded each load from the word that holds it,
and the stores happen once at exit. What is new to prove is the law, once.

The last column is also where invariants come from for requests: R's facts
are In scope for every move inside the body.

## 7. The machine level, and the search

**The machine level already has its plan**: the placement. Growing it means
letting the verified lowering accept more plans, each a case of its one
theorem:

- save round a call only the registers the plan names, a register left
  unsaved being empty afterwards so that a later read of it is a refusal;
- a frame sized by what the function saves, and none for a leaf;
- values that live across a call placed in kept registers;
- instruction forms: a 32-bit move to narrow a word in place of two shifts,
  constants loaded at their size, compare and branch fused.

Some forms need instructions the machine model does not have: a byte swap
for the word read, a rotate, the 32-bit moves. Each is a line of trusted
model (§10).

**The search**, in three stages, none of which changes a proof:

1. *Fixed strategies*, written as Heather functions: inline a small callee,
   apply rules bottom up until nothing changes or a budget ends, forward
   stores to loads, lift the fields a loop reads and writes.
2. *Equality saturation* over the pure values of a region, with the control
   structure kept as a skeleton (the acyclic e-graph Cranelift uses). The
   e-graph library (`lib/std/data/egraph.hthr`) already records why each
   pair of classes met, and that explanation is the list of Rewrite moves.
   The cost function is the instruction counter of the standard benchmark.
3. *Rule discovery and superoptimization* of short sequences, feeding the
   rule table.

Where the searcher runs is open. Written in Heather it is evaluated by the
generator, and compiled natively once the compiler compiles itself, at which
point the optimizer is one of its own customers.

## 8. SHA-256's list in this design

The steps the review of 2026-11-14 listed, and what each one is here:

| Step from the review | What it is in this design | New proof it needs |
|---|---|---|
| Save only what is live; no frame for a leaf | Machine plan | Two cases of the lowering theorem |
| Inline a small callee | The Inline move | Its law, once |
| Narrow by a 32-bit move; small constants | Machine plan (instruction forms) | One lemma each about the x86 model |
| Read a word as a word | A rule: four byte loads joined are a word load swapped | The rule (the equation is in `stored_words.hthr`), a load node and its lowering |
| Drop a length test `Holds` proves | Learn, with the request answered In scope and Decided | The range domain's soundness, once |
| Fields in registers across a loop | Restate a loop, with the memory rules | The loop law, once; three memory rules |
| Rotates and other idioms | Rules | A short theorem each |
| Vector and SHA instructions | A rule table for a target with those instructions, later | Model growth, Minus's call when it comes |

Six of the eight need a proof once and then nothing per optimization. The
list was written before the design, and it falls into the design's parts
without a special case.

## 9. Order of work, and what is built

1. **Live-only saves and leaf frames.** Machine plans; the largest single
   share of the counter; independent of everything else.
2. **The replayer at FunctionIR** with Rewrite, Share and Drop, and the rule
   table. Acceptance: the folding pass restated as rules, and the rotate
   rule added as the first new one. The probe before it is done (§3.2).
3. **Inline.**
4. **Requests** with the answers In scope, Decided and Required, and the
   range domain. Acceptance: SHA-256's length tests go, with no change to
   its source.
5. **Memory rules and the word load.**
6. **The loop law**, then fields in registers.
7. The report of unanswered requests, Proved and Tested answers, then the
   e-graph searcher.

Each step is its own pull request and states instructions per block before
and after, for SHA-256 and for the scanner (a pass lands with its counter).
The SHA-256 source may change where it can be improved, but it is not tuned
by hand for speed: it is the dogfood for these steps (Minus 2026-11-14).

| Step | State |
|---|---|
| 1, live-only saves | built: `Place::Spilling`, `File::plan_call`, `File::called` (`function_ir_lower_calls.hthr`) |
| 1, leaf frames | not built |
| 2, the replayer | built: `function_ir_replay.hthr`, rules in `function_ir_rules.hthr`; the folding pass is not yet restated as rules |
| 3, inline | built, and run by `compile-x86`: §9.1 |
| 4 to 7 | not built |

### 9.1 What is built, as built

**One law a function.** `function_ir_stage.hthr`: a `Stage<P>` rewrites a
function by a plan over its callees as the stage left them, and owes
`Rewrites(callees, old, new)`, that the new function may do whatever the
old may. `Stage::run_sound` lifts that to programs once, for every stage.
`Stage::then` makes two stages one (so a pass reads callees every pass has
been over, and a program's rewriting is stated once a function), and
`Stage::maybe` adds the plan that leaves a function as it is.
`ProgramRewrites(old, new, f)` is what a compiler lowering `new` owes for a
theorem about `old`.

**The passes.** Inline is a stage of its own (`function_ir_inline.hthr`):
the callee's body with its ids raised above the caller's bound, parameters
bound by moves from the arguments, the result by a move back. The replayer
is a stage (`replay_stage`), and tidying is the replayer twice
(`function_ir_tidy.hthr`): once reading every node through the moves
before it (`Step::Swap`, `Plan::Args`, `Plan::Inputs`), once dropping what
nothing reads. Tidying is not polish. The lowering names a buffer by its
home, the address and length the function was lent, and takes a load only
where an arm compared the index with that very length; an inlined body
reads moves of them, and is refused until it reads through.

**Emptying is a program's, not a function's.** A callee inlined everywhere
is called by nothing, and its code would be emitted all the same.
`function_ir_prune.hthr` makes every function the exported ones do not
reach one constant (`prune`, keeping each function's number, parameters and
count of lent spans, so the program lists and lowers as before), and
`prune_rewrites` is `ProgramRewrites` at a function that is reached, given
that the reached ones call only reached ones (`program_closed`). It is not
a stage: a stage's law is every function's, and an emptied function does
not do what the old one did. The walk that finds the list
(`program_reached`) is not trusted; the certificate states the list as a
literal and checks closedness by evaluation.

**The search is not trusted, and is evaluated.** `function_ir_optimize.hthr`:
`optimize_stage()` is inline, then tidy, or no plan;
`Function::optimized(callees, wanted)` finds a function's plans and the
function they make. `compile-x86` evaluates it a function at a time,
callees first, reads the answer back as source (`function_ir_spelled.hthr`),
and states both as literals; the certificate's statement is that the stage
makes the one from the other, checked by evaluation, a function a statement
(`Stage::run_next`). What the search made is kept only where the lowering
takes it with the planner's placement (`Function::lowers`); otherwise the
function stays as it is. Then the unreached functions are emptied, and the
two facts compose (`ProgramRewrites::then`) into the one the return
theorems take, at each exported function. Those theorems take the two
programs apart
(`compiled_returns_written_through` and its kin): the lowering and the
checks it needs are of the program made, the run is the published one's.
`HEATHER_OPTIMIZE=off` turns the passes off.

**Limits, each a next step.**

- A function is rewritten whole or not at all. One refused call site (the
  planner out of registers in a loop, issues/function-ir-planner-register-pressure.md)
  keeps the function as it was; a search a site at a time would keep the
  rest.
- What is inlined is every callee no larger than a constant, into a
  function no larger than another (`Wanted::usual()`). The second is there
  because a function's rewriting is one statement and the kernel's fuel is
  a statement's; stating a large function a region at a time removes it.
- Only a program that is lent spans is optimised. One of words alone is
  lowered by `lower_program`, whose theorem is over another relation
  (`program_callees`).
- An emptied function is still a function: a constant and a return. A
  program with them removed renumbers its calls, which is a rewrite of
  every caller and a theorem this one does not give.
- Tidying leaves empty regions where it dropped nodes; they cost nothing in
  the code and something to read.

**What it buys, as a shape** (`scripts/bench-native` counts instructions
exactly; its saved baseline has the numbers, and the pull requests record
them as they were measured). On SHA-256's compression, written as methods
that call one another, inlining removes about seven calls in ten and with
them about a sixth of the instructions executed; what remains is dominated
by loads and stores of words in the lent spans and by the register moves
around them, which is steps 4 and 5's ground. The scanner, which has few
small callees, gains a few percent. Code size grows with inlining and
comes part of the way back with emptying.

## 10. Machine instructions added for the optimizer

Minus, 2026-11-14: instructions may be added to the machine model as steps
need them, each checked to be formalized correctly, with a summary kept.
Vector and SHA instructions stay a separate decision. This table is that
summary; a row is added in the pull request that adds the instruction.

A row's check is: the manual's section for the instruction and each form,
the encoding compared byte for byte with an assembler's, and the model's
result compared with the real CPU's over edge operands and random ones
(flags included where the model states them, and left undefined where the
manual does).

| Instruction and forms | Used by | Model | Checked how |
|---|---|---|---|
| (none yet) | | | |

## 11. Where the ideas come from

Validated register allocation (Rideau and Leroy, for CompCert) is the
planner and checker the lowering already has. Translation validation
(Pnueli, Siegel and Singerman; Necula) is the replayer's stance, made
stronger because a plan is replayed by a proved function and not compared
after the fact. Equality saturation (Tate and others; egg, by Willsey and
others) and Cranelift's acyclic e-graphs are the search. Abstract values
checked and not computed is certified abstract interpretation (Besson,
Jensen and others). Rule discovery is Ruler and Souper. The loop law is data
refinement. The request, a compiler whose optimizations name the proposition
they lack and take the programmer's theorem as the answer, is this design's
own.
