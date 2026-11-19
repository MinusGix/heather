# Dogfooding plan: what stands between Heather and porting itself

Status: **a proposal, 2026-11-19**, written at Minus's request ("drastically
make compilation + proofs effective so we can start actually porting notable
parts of Heather and dogfooding the language"). It is a step-back review at
master `a776131c`, not a design of any one round. It decides nothing: §8 lists
what Minus decides, and every large step in §7 waits on that.

It reads `docs/compilation-vision.md` as settled and proposes nothing against
it. Where it names sizes, they are line counts at that commit, given so the
proportions can be seen; they are not targets.

## 1. The short answer

Three things were expected to be the wall: the size of the compiler's proofs,
the cost of a compile, and the proofs a program needs. They are real, and
none of them is the first wall. **The first wall is what compiles at all.**
Eighteen small programs, each a few lines modelled on Rust that Heather's own
crates contain, were written the way a newcomer to the fragment would write
them. All eighteen were refused (§2.1). What compiles today is the path the
demos walked: 64-bit words with add, subtract, the bitwise operations and
shifts by a literal; one byte span; tail recursion and the loops that lift to
it.

The reason the path is narrow is the second finding: **a feature is paid for
once per layer, and there are about six layers** (§2.2). So breadth grows
slowly however hard a round works, and each demo adds the one path it needs.

The third finding is about the destination: **Heather's own Heather code is
not the shape that compiles** (§2.3). The compiler, the optimizer, the
generators and the tactics are functions over lists, numbers, options,
inductive data and closures. The native fragment is words and byte spans.
Between the two is a ladder of data, and the plan is that ladder (§4), with
named ports of Heather's Rust on each rung (§6).

So the plan in one line: **drive rounds by a ledger of ports instead of by
demos, make a feature cost one place instead of six, and climb from words to
spans of records to inductive data to functional Heather, landing a real
component of Heather at each rung.**

## 2. What was measured

### 2.1 Eighteen small ports

Each probe is a `runtime fn` of a few lines, checked with the release binary
over the library at master. The sources are in the project folder
(`dogfooding-review/probes/`). "Refused" is the generator's or the
elaborator's own message, shortened.

| # | what it ports | written as | answer |
|---|---|---|---|
| 1 | FNV-1a over a span (the hashing shape of `crates/cache`) | `for` over `Bytes(n)`, read only | refused: a function over a span must return `Mutated<…>` |
| 2 | the same, the span `mut self` | | refused: the same |
| 3 | the same over `List<u8>` with `byte_within` | `for`, then tail recursion | refused: `mul` is an ordinary fn, the setup has no primitive for it |
| 4 | a decimal literal's value (`lexer.rs`) | `for` with `v := v * 10 + d` | refused as 1 |
| 5 | the same with an overflow flag, answer a record | two loop words, `→ Parsed` | refused as 1 |
| 6 | find a byte (`memchr`) | `for` with `return Some(i)` | refused: a `for` over words has no `break`, `continue` or `return` |
| 7 | the same as a `while` with `&&` | read only | refused as 1 |
| 8 | nesting depth (the shape of recursive descent) | a call of itself that is not last | refused: a recursion is lowered as a loop |
| 9 | a token kind as an enum | `→ Kind`, and `match k` | refused: `Kind` has no runtime layout |
| 10 | the same with the kind a word | parameter `b: u8` | refused: a parameter that is not a 64-bit word |
| 11 | `numeral::pred`'s borrow walk | `mut limbs: [u64; 4]` | refused: a type with no runtime layout |
| 12 | a count as a `Nat` | `→ Nat` | refused as 1 |
| 13 | positions as a list | `→ List<u64>` | refused as 1 |
| 14 | a generic helper | `twice(bump, x)` | refused: `twice` is an ordinary fn |
| 15 | copy between two spans (`memcpy`) | `dst: Bytes(n), src: Bytes(m)` | refused: `Bytes` has no runtime layout (as a second span) |
| 16 | two results | `→ Parsed` from one word | refused: `Parsed` has no runtime layout |
| 17 | Fibonacci | two loop words | refused: `fib#State` has no runtime layout |
| 18 | count and clear | an `if` that stores, with code after it | refused: the span through a branch that joins again is not reflected yet |

Four more stalled before the generator: a shift by a variable count (`rt`
wants a numeral), `x / 10` on a word (nothing designates `/` at `BitVec`), a
`while` whose measure halves (the default decrease search does not read the
shift), and a conjunction where a `Bool` result is expected. Each has an
honest message. Each is also a place a port stops in its first hour.

The refusals are not bugs. Every one is a line some issue already draws
(`function-ir-multi-word-calls`, `runtime-repr-narrow-words`,
`runtime-fn-recursion`, `rt-fixed-arrays-and-tables`,
`x86-wide-multiply-and-carry`, `runtime-nat-checked-arithmetic`,
`runtime-fn-arena-lists`, `span-caller-of-fact-taking-loop`). What the
probes add is the proportion: of the first things one writes, none compiles.

What does compile is good. `examples/readme/lines.hthr` reads as a program,
its theorem is two lines, and its certificate says what the bytes return.
The surface over `Bytes(n)` (`s[i]`, `for`, `while … invariant`) is close to
what a port wants to be written in. The fragment under it is the gap.

### 2.2 What a feature costs

`lib/native` and the machine models, by layer:

| layer | lines | what it is |
|---|---|---|
| x86-64 model | 12.6k | 22 register instructions beside the loads, stores, jumps and calls; their runs, memory, lending |
| Linux model | 6.6k | calls as trees, `Sim` |
| statement compiler (`native_compile*`) | 16.0k | `Source` to x86, proved once, a proof per emitter |
| the rest of `native_*` | 8.9k | `Source`, the builder, the allocator, the tools |
| FunctionIR | 37.1k | of it the lowering 15.2k, the optimizer 8.8k |
| `rt` and the generator | 27.3k | three reflected languages and `rt_held`: reflectors 6.0k, lowerings 6.1k, loops 4.8k, the generator 4.3k |
| probes (`lib/_tests/native`) | 18.5k | |

A binary operation such as `xor` is named in about nine library modules: the
instruction and its run, its kept-register lemma, the block form, the
FunctionIR node, its lowering and the lowering's proof, the `rt` operator,
its reflection, its lowering and that lowering's proof. A control feature is
worse, because `rt` is three languages (`Tm`, `FTm`, `ETm`,
`issues/runtime-language-layers-repeat-features.md`): a measured loop was
built three times, and a fourth for records held in memory. Reading a
big-endian word in one access took nine patches across four layers.

This is why the fragment is narrow. No single feature is hard. Each is long.

### 2.3 Heather's own code is not the shape that compiles

The code one would most like to run natively is already Heather:
`function_ir_optimize.hthr`, the replayer, `Source::compile`, the `runtime fn`
generator, the tactics. Minus's note on the untrusted evaluator
(2026-11-17) names the destination: `crates/run` is a Rust stopgap until
Heather compiles this code itself.

That code is `List<Nat>`, `Option<Found>`, records of functions, `map` with a
`λ`, `NatMap`, structural recursion. None of it is a word or a byte span.
The native fragment can express the leaves of Heather's Rust (a scanner, a
hash, limb arithmetic). It cannot yet express a node of a tree.

So "port notable parts of Heather" is three different jobs, by the data the
part is made of:

- **A. Kernels over bytes and words.** The scanner, UTF-8, SHA-256, numerals,
  hashing, byte codecs. Proved against a specification, linked into `heather`.
  The fragment almost reaches these; breadth and code quality block them.
- **B. Components over arrays of records.** A token array, a module image's
  decoder, the Merkle walk, a SAT checker, an interpreter's heap. This is how
  the Rust is written already (indices into vectors). It needs spans of
  words and of laid-out records, several at once, and a span that grows.
- **C. Functional Heather.** The optimizer, the compiler, the tactics and
  generators as they are written today. It needs inductive data, closures,
  general recursion, generics and `Nat`.

A reaches into B (a span of limbs is numerals), and B is the runtime C
stands on (a constructor is a cell in a span). That is the ladder of §4.

## 3. Diagnosis

1. **Rounds were driven by demos, and a demo asks for one path.** Sort,
   binary search, UTF-8, SHA-256 and the scanner each widened the fragment
   exactly where they stood. Nothing measured the fragment against what a
   port needs, so nothing showed that the base (multiply, a second loop
   word, a parameter narrower than a word, an early return) was missing
   while the top (found proofs in a lifted loop's tests, lending laws for
   windows) grew.
2. **The cost of a feature is the number of layers times the cost of a
   proof by hand at each.** Both factors can be cut. The layers repeat
   control (three `rt` languages, two compilers being joined). The proofs
   are written per case against the machine, though what each needs is
   computed from the code (`Fragment::before`), which is the form a tactic
   can fill.
3. **Everything waits for its proof-once before anyone can use it.**
   Principle 4 of the vision gives a lifecycle: a producer starts
   *certifying* (a checked proof per output) and moves into the verified
   theorem as it stabilises. In practice every feature enters at the
   verified end. For code whose answers are checked anyway (the optimizer's
   searches, a tactic's run) there is not even a certificate to want.

Proof size, compile time and program proofs are downstream of these. The
statement compiler is large because each emitter is proved by hand against
x86 (cause 2). A compile is slow because the compiler runs in an interpreter
(§2.3, job C). A program's proof is long where the bridge from a loop over a
span to the function it computes is written out each time, which the tactic
threads are already shortening.

## 4. The ladder

Each rung is a statement of what can be *written*, with the ports it unlocks.
A rung is done when its ledger rows (§5.1) compile and run.

- **Rung 0, today.** 64-bit words without multiply; one byte span; tail
  loops. Lands: the scanner, UTF-8, SHA-256 (slowly).
- **Rung 1, the scalar core.** Everything C can say about integers and
  control without memory: multiply, divide and remainder (a nonzero divisor
  is a found proof), shifts by a variable count, the widening multiply and
  add with carry; parameters, results and loop state at every word width,
  `Bool`, flat records and enums without payload by value; `return` and
  `break` in a `for`; a branch that stores and joins; read-only loops over
  `Bytes(n)`; a call of oneself that is not last (in flight in the stack
  threads); callers of loops that take facts (the route waiting on Minus).
  Lands: probes 1 to 10 and 16 to 18; the lexer's values; decimal reading
  and printing; a varint codec.
- **Rung 2, spans of anything.** `Words(n)` and spans of a `laid record`
  with `s[i]` under a found proof, as `Bytes(n)` has; several spans in one
  function, with the lending laws deciding what a store leaves; a span with
  a fill mark that grows to a capacity (a vector); constant tables.
  Lands: probes 11 and 15; `numeral` (limbs), the token array, byte codecs
  of the cache, a hash map, a SAT checker; the heap of rung 3.
- **Rung 3, inductive data.** An enum with fields as a tagged cell in a
  span, `match` as a read of the tag, lists and trees; who frees is one of
  two disciplines (an arena that is dropped whole, or counts), chosen per
  program. Lands: probe 13; a parser's tree; an interpreter; `sort` and
  `tac` as ordinary Heather (`nh-heap`).
- **Rung 4, functional Heather.** Closures, generics by specialisation,
  `Nat` as a word with a checked overflow or as rung 2's numerals.
  Lands: probes 12 and 14; the optimizer and `Source::compile` run natively
  (`self-compiler`), tactics and generators run natively, and `crates/run`
  retires.

Rungs 1 and 2 are the fragment growing under the vision as it stands.
Rungs 3 and 4 carry the one real decision of this plan (§8, question 3).

## 5. The moves, ranked

### 5.1 A ledger of ports drives the rounds

A directory of small ports, each named for the Rust it ports
(`lib/_tests/native/ports/`), under the project's own convention: a port that
does not compile yet stands under `// expect-error: <the refusal>`, so the
gate holds its reason; when a round lands, the expectation fails, and the
round flips the row to a positive probe run by `refl`. The eighteen probes
are the first rows. A round toward a rung says which rows it flips, and a
rung is its rows.

Three columns per port, filled as they become true: it compiles; it is
proved against its specification, with the proof's lines beside the
program's; its speed beside the Rust it ports. Those are the three things
"effective" means, and today none of them is tracked.

Cheap, and it changes what the other moves are measured by. First.

### 5.2 Rung 1 as one milestone

The scalar core is many small refusals, most with an issue. As separate
issues they have each lost to a demo's need. As one milestone with the
ledger's rows as its done-when, it is two or three rounds. It is the largest
unlock per line of work on this list, and nothing in it is a design question
except where a divisor's proof comes from, which Minus's rule already
answers (a partial operation takes a found proof).

### 5.3 A feature costs one place

Three parts, the first the most valuable.

**(a) Operations as rows.** An ALU-shaped operation is described once: its
meaning on words, the instruction template that computes it, the flags it
leaves, and one obligation, that running the template with the operands in
registers leaves the meaning in the result. `rt`, FunctionIR and the
lowering each have one generic case that reads a row, as the optimizer reads
a registered rule (`optimizer-rules-as-theorems`). Then multiply, a variable
shift, a rotate, `popcnt`, an `LEA` that adds and scales, or an immediate
form are each a row and a proof found by the tactic of §5.4, and a library
can register one, which is the vision's "a DSL that wants specific
instructions" made cheap. The code-quality list of
`issues/linked-sha256-speed.md` (addressing forms, small immediates, `LEA`)
is mostly rows.

**(b) One control language over the layers that have effects.** The open
design question's own lean: `FTm` and `ETm` share `let`, `if`, loop and call,
with pure terms as the leaves of both. Loops, calls and recursion are then
built once. `rt_held` joins it as a leaf over records, not a fourth copy.

**(c) One compiler, finished.** Step 5d of the join
(`statement-byte-nodes-on-shared-leaf`) moves byte work out of the statement
compiler into the shared leaf. This shrinks `native_compile*` by deletion,
which no proof style can.

### 5.4 The compiler's proofs: a tactic over the computed precondition

The open decision in "Make compiler correctness proofs elegant" is between
tactics that write the per-emitter bodies and one simulation argument in
place of them. The recommendation here is the tactic, for a reason the
claim calculus already contains: what a fragment needs before it is a
function of the fragment (`Fragment::before`), so the shape of an emitter's
proof is determined by its code. A tactic can walk that shape: a fetch, a
load, a store or a branch each asks for a record whose fields are a `refl`,
a hypothesis, a word fact for `bv_omega`, or a frame fact from a registry
(`cells_outside`, `store_holds`). `Fragment::clamp_before` is the pattern in
small: every line of its body is one of those four.

The same tactic discharges a row's obligation (§5.3a) and a hand-written
`Compile` instance's, so it is paid for three times over. A rewrite into one
simulation argument would restate sixteen thousand lines that are proved,
and hand proofs of the compiler wait on Minus's word.

Where "a quarter the size" then comes from: deletion through the join
(§5.3c), bodies written by the tactic, and operations that are rows instead
of emitters. Not known yet: how much of `perform` and `structured`, whose
bulk is environment reasoning between leaves, the tactic reaches. So the
first step is a prototype on three emitters of increasing difficulty
(`clamp`, one store, `loop_head`), priced before anything is converted.

### 5.5 Code quality has a named customer

The proved SHA-256 is two orders of magnitude slower than the cache's hash
and the issue's profile says why: addressing and immediate forms (rows),
registers saved around a call whether live or not, callees called once and
not inlined. The planner is untrusted already, so its half is search with
no proof. The target is `crypto-hash`'s own done-when, the compiled code
replacing the cache's scalar path, and the ledger's speed column keeps it
honest for every port after.

### 5.6 Program proofs are measured on the ports

The tactic threads (`induct` over a function, `simp_only` through branch
equations, `bv_decide`, `cases` on a call's result, facts given to loops)
are the right levers and are moving. What the ledger adds is the measure,
proof lines per program line on each port, and the pattern ports mostly
need: a loop over a span *is* a fold over the list it holds. Most ports of
Rust have a specification of exactly that form (the scanner is
`Accepted::longest`, a numeral operation is the number), so one tactic or
lemma family for "this loop is this fold" is worth more to dogfooding than
any other single proof lever.

### 5.7 The friction of a first hour

Smaller, and worth one round because a dogfooder meets them before anything
else: a `runtime fn` file imports some fifty modules
(`runtime-generator-imports`); `*` and `/` are not designated at words; the
default decrease search does not read a shift; a cold check after the
compiler is rebuilt is minutes, and a small compile is tens of seconds over
a warm store.

## 6. First porting targets

Ranked by how soon each can be on by default in the `heather` binary, which
is what dogfooding means.

| # | target | Rust it replaces | what blocks it | rung |
|---|---|---|---|---|
| 1 | **The lexer, on by default** | `crates/syntax/src/lexer.rs`'s scanning | The scanner and the token loop are compiled and linked today behind `HEATHER_LEXER=linked`. Left: its speed measured against the Rust lexer; tokens without a value made from the scanner's code instead of read twice; then the values (numerals, escapes) in Heather, which need multiply and the limbs. | 0, then 1 |
| 2 | **`numeral`** | `crates/numeral` (272 lines, in the trusted base, each operation one line of specification over `Nat`) | The widening multiply, divide and carries in the x86 model; spans of words; a write that changes the length. The best first proof showcase: the theorem is "this is the number". | 1 and 2 |
| 3 | **SHA-256 in the cache** | the scalar path of `crates/cache/src/sha256.rs` | Proved and linked; speed only (§5.5). | 0, with §5.3a |
| 4 | **Byte codecs of the cache** | the header and warning codecs of `module_image.rs`, the Merkle walk's hashing | Several spans, records by value, a growing span. To be scoped by a round; the candidate with round-trip theorems. | 2 |
| 5 | **The untrusted evaluator** | `crates/run` (923 lines) | Minus has named it. As Rust writes it (codes, environments and thunks in counted cells) it is rung 3; question 3 of §8 decides whether it is ported or made unnecessary. | 3 |
| 6 | **The optimizer and `Source::compile`, run natively** | the evaluator's work in every `compile-x86` and `write-elf` | Rung 4. This is `self-compiler`, and where the compile-time bar is met by an order of magnitude instead of by tuning. | 4 |
| 7 | **The parser** | `crates/syntax/src/parser.rs` (10k lines) | Rung 3 and a mature rung 1; large. After 5. | 3 |

Not targets yet: the elaborator and the kernel. They are rung 4 at a size
that should wait for 6 to show what compiled functional Heather costs.

## 7. Order of work

Steps 1 and 2 are small and are proposed to start on Minus's word. Each
later step opens with a design note or a prototype for Minus, as marked.

1. **The ledger** (§5.1): the directory, the eighteen rows and the
   convention, in `lib/_tests`. A probes-only change.
2. **The tactic's prototype** (§5.4) on three emitters, with what it costs
   to check and how many lines it removes. This answers the open decision
   with evidence. *Minus decides on its result.*
3. **Rung 1** (§5.2) as a milestone, the operations entering as rows
   (§5.3a) once step 2 has shown the tactic proves a row. Flips most of the
   ledger. Target 1's values and target 3's forms ride on it.
4. **Target 1 on by default**, in parallel with 3: measure, cut the double
   read, switch.
5. **The control language** (§5.3b). *A design note for Minus first*, with
   the loop as its worked example, as the issue asks.
6. **Rung 2** with `numeral` as its customer. *A design note first*: spans
   of words and laid records, several spans, the growing span.
7. **Rungs 3 and 4**, by question 3's answer.

Already moving and unchanged by this plan: the call-depth and stack-room
threads (rung 1's recursion), the route for callers of fact-taking loops
(route 1, a proof per call, is also this review's reading: it reuses the
proof the caller already passes and needs no new companion family in the
elaborator), the optimizer's search cost, and the tactic threads.

## 8. Decisions for Minus

1. **Is breadth the first priority?** That is, do the ledger and rung 1
   come before more depth on the paths the demos opened (lending laws for
   windows, further optimizer stages, the statement compiler's size)?
   Recommended: yes.
2. **Tactic or simulation for the compiler's proofs?** Recommended: the
   tactic over the computed precondition, decided on the prototype of step 2
   and not before.
3. **May functional Heather run natively before its backend is proved?**
   Rungs 3 and 4 can be built two ways.
   - *Proved first*: each form of data enters `rt` with its representation
     invariant and a case of the lowering's theorem, as `nh-heap` plans. The
     optimizer runs natively when the last form it uses is proved. Slow, and
     the result is a compiler with one theorem.
   - *Unproved lane first*: a second setup compiles the erased form the
     evaluator already defines (`Machine::erase`'s `Code`) through the same
     FunctionIR and lowering, with an unproved front (data layout, closures,
     counts) and no certificate. It may only be used where `crates/run` is
     used today, for answers that are checked afterwards: reads, tactics,
     generators. It has the trust `crates/run` has now, no more. The
     compiler compiles itself early, the compile-time bar is met there, and
     the proved setup grows beside it rung by rung until the lane is not
     needed. This is the lifecycle of principle 4 used on purpose.

   Recommended: the unproved lane, with the rule that nothing it compiles is
   ever cited by a certificate. It is the difference between dogfooding the
   compiler in weeks and after `nh-heap` and `nh-ownership`. It is also the
   choice most against the grain of how the native work has been done, which
   is why it is a question and not a step.
4. **Are the targets and their order right?** In particular, whether
   `numeral` (trusted base, slower than rustc at first) is wanted second, and
   whether the lexer should go on by default before its values are Heather's.

## 9. What this does not propose

- No change to the vision's principles, the certificate, or the kernel.
- No rewrite of the statement compiler's proofs by hand.
- No new intermediate language: rows and a shared control language reduce
  what exists.
- No milestone rows in `docs/roadmap.md` yet. If Minus accepts the ladder,
  rung 1 and rung 2 become submilestones of `hih-native-heather` and the
  ledger its measure, in the change that follows.
