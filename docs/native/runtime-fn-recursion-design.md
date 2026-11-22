# Recursion in a `runtime fn`: procedures, proved depth and the stack budget

Status: proposal (2026-11-20), revised 2026-11-21: the depth is a proved
bound inferred from the measure, the stack a budget in bytes checked once
(§3, §4). Revised 2026-11-22 on Minus's answers: every bound is one named
theorem `f::depth`, rewrites that take a recursion off the stack belong to
the optimizer (§5), and a caller enters a recursion with its room already
reserved instead of becoming a statement (§2.1). The short surface note that
`issues/runtime-fn-recursion.md` asks for before code. It replaces that issue's
"depth in the meaning": since #806 to #812 a program's stack room is asked
for in levels of checked calls, a call past them is a refusal of the
compiled program, and the room costs the same to check at any number of
levels (`docs/native/native-procedure-frames-design.md` §7.4).

## 1. What is there

- **The back end can recurse.** A `Source` procedure may `Perform` itself or
  a cycle of others. The compile checks a call only at the entry of a
  procedure that reaches itself, asks for `Source.levels` levels of such
  calls, and `Source::compiled_levels` proves, for every source it accepts,
  that every run whose checked calls nest at most `levels` deep is a run of
  the compiled program, never refused. Past them the program stops at the
  call, with the call-depth status, its output so far the source's.
- **The front end cannot.** A `runtime fn` reflects to `rt`
  (`lib/native/runtime/rt.hthr`). A pure one lowers to FunctionIR regions,
  whose functions call only functions before them; a self-call in tail
  position becomes one `Loop` (`rt_loop`, setups design §7.4) and any other
  is refused, "a recursive call that is not a loop needs procedures". A
  function over `Io` lowers to statements (`rt_io_lower`), but `ETm` has
  no call of another effectful function (`issues/rt-effectful-callees.md`).
- **The probes meet it first** (`docs/native/dogfooding-plan.md` §2.1, row 8,
  `port_depth`): nesting depth, the shape of recursive descent, is the first
  recursion anyone writes, and the parser Heather-in-Heather needs is that
  shape.

## 2. The route: a recursion is a call between statements

A region is a total function of its words, so what it calls must answer
with a value; a statement is a tree, so what it calls may ask Linux for
things, run out of levels or exit (procedures-are-functions §0 item 4).
A non-tail recursion can run out of levels, so it is a call between
statements. That fixes the route (built in the order of §8, pure recursion first):

1. **`ETm` calls an `EFun`** (`rt-effectful-callees`, not yet built): an
   `ETm` node calling another function of the program on variables, binding
   its answers and continuing. It lowers to a `Source` procedure and a
   `Perform`; its case of `ETm::lower_sound` is the callee's meaning
   (`Procedure::enter`, `leave`). Nothing recursive yet.
2. **The callee may be the caller, or a cycle.** With calls between
   statements built, a self-call is the same node naming entry 0; mutual
   recursion between `runtime fn`s is a cycle of entries. The compile's
   ranks and checks already find which entries reach themselves.
3. **A pure recursive function takes the statement lane with no effects.**
   Its body is an `ETm` with no `Io` node. Its meaning as a statement is a
   value or a stop at the levels, which is all §3 needs.

The first version drew a rule from this: **recursion lifts its callers to
statements.** A pure function that calls a recursive one cannot stay a
region, because its call can stop, so the caller is reflected as a
statement too, and its caller, up to `main`. A tail recursion still becomes
a loop, and a loop stays a region. The rule is sound but it is a cost paid
far from its cause: one recursion deep in a program would take everything
above it off the region lane, where the optimizer and the register planner
do their best work. §2.1 is the way out; the rule stays only as what
happens before it is built.

### 2.1 A call with its room reserved

The call can stop only because the stack can run out. Once the depth is a
theorem (§3), whether it can run out is decided before the recursion
starts: §4.2 checks `room(d(args))` once, where the program enters it. Below
that check the recursion cannot be refused, so a call into it is total, and
a total call is what a region can make.

So the caller does not lift. One place, the **entry**, makes the check and
is a statement (it is the one place that can stop); everything it calls
with the room reserved, recursion and callers of the recursion alike, stays
what it was. A region calling `f(y)` under a reservation carries the fact
that the room it needs is held, `fits(d(y), y)` and `d(y) ≤ k` for the `k`
levels reserved, the way a loop carries a fact in its state (`Loop::rule`),
and its call reads as `f`'s value by `Source::pure_reads`' argument, with
the levels taken from the fact rather than from `Source.levels`.

Where the entry goes is the searcher's choice, not the writer's: as high as
`main`, where a refused input has done nothing (guarantee 4), or as low as
the outermost call whose arguments bound the rest. And if the optimizer
turns the recursion into a loop (§5), there is no room to reserve and no
entry at all.

Not designed further yet: the region node for a reserved call, how the
fact reaches a callee that is several calls below the entry (a parameter of
the procedure, as a lent span is, is the likely form), and its case in the
FunctionIR meaning.

## 3. Depth: a proved bound, inferred by default

Revised 2026-11-21 on Minus's direction. The first version (§8.1, PR #836)
asked the program for `levels := n` wherever its call graph has a cycle.
That number is a fact about the run, not a choice the writer should have
to make, and a written number is a dead end: when it is too small, nothing
helps but a bigger one. The depth is now a **theorem about the function**,
in the manner of Quantitative CompCert (Carbonneaux et al., PLDI 2014):
the stack bound is proved at the source, as a function of the source's
inputs, in terms that do not mention frames, and the compiler supplies the
bytes a level costs and closes the comparison by evaluation. A bound is an
ordinary theorem, so tactics prove it and a better proof tightens it.

### 3.1 What "the depth fits" means

`PDef::fits(k, p, xs)` (`rt_ptm`, §8.1) says whether the call of
definition `p` at `xs` runs within `k` nested calls. It is total for any
recursion and evaluates at a closed argument. A **depth bound** for `f` is
a function `d` of its words with

```
theorem f::depth(x..): f::fits(d(x..), x..) = True
```

That statement is the whole interface between the function and the stack:
the compile reads `d` and nothing else about the recursion.

### 3.2 The default bound: the termination measure

A `decreases μ` function already proves, at every self-call, that
`μ(y) < μ(x)`. Every call the body makes therefore lands strictly lower,
and by strong induction on `μ(x)`, **`f::fits(μ(x), x)` holds for every
`x`**: a function whose measure is a `Nat` has its measure as a depth
bound, with nothing written.

The induction is one theorem in `rt_ptm`, generic over the body:

```
theorem PDef::fits_by_rank(defs, w, f, rank, descends: PDef::Descends(defs, w, f, rank)):
    (p: Nat) → (xs: List<BitVec(64)>) → PDef::fits(defs, w, f, rank(p, xs), p, xs).IsTrue()
```

where `PDef::Descends` says each body's calls, as `calls_ok` reads them
along the branch actually taken, are at arguments of lower rank. At rank 0
no call is allowed, so `calls_ok_mono` takes the body to `fits(0)`. Built
(2026-11-21), with `PDef::body_fits_mono`; what is left is the premise at
`f`, below.

**What it needs that the guard does not have.** `f::guarded` (§8.1) is
extensional: it says the body computes `f` whenever the calls are answered
by `f`. A call whose value the body discards could be at any argument and
the guard would still hold, so the bound cannot be read off it. The
decrease has to come from the place it is proved: the elaborator's lifted
obligations `f#obl_N`, one per call site, each under the hypotheses of the
path to it (docs/language/recursion/decreases-unfolding-design.md §4).
The elaborator names each lifted obligation `f::obl_N`, and the generator
walks `f::ptm` with one lemma per node (`PTm::calls_ok_bind`, `_recur`,
`_choose`), closing each call with the obligation whose reading (the
caller's words in order, the branch tests in scope) the call's lemma
accepts. The note first recommended a new companion, `f::descends`, from
the unfolding walk, to avoid matching the reflected branch tests against
the obligations' hypotheses; the join turned out not to be fragile, since a
reflected test's equation converts to the source's `match h:` equation, as
the guard's conversions already showed. Two things it did need: the rank is
the measure read at the first words of any list (`PTm::padded`), since
`Ty::on_words` matches on the list and is stuck at the statement's own
`xs`; and the environments are passed as handles read off each lemma's
premise, since spelled out every `Bind` copies the one before it twice. The
generator publishes `f::depth: (xs) → f::fits(μ(xs), xs) = True` wherever
the walk closes every call, and nothing otherwise (an obligation reading a
`let`'s or a call's result).

### 3.3 Tightening a bound

The measure is often loose: binary search's `hi - lo` is a correct depth
bound and an exponentially bad one. A tighter bound is any `ν` that also
drops at every call, since `PDef::fits_by_rank` takes any rank, not only
the termination measure. So a tighter bound is written the way a measure
is:

```
runtime fn find(xs: &[u64], lo: u64, hi: u64, k: u64) → u64
    decreases hi - lo
    depth log2(hi - lo) + 1
{ … }
```

The `depth` clause owes one obligation per call site, `ν(y) < ν(x)`,
lifted and defaulted (`omega`, `bv_omega`) exactly as `decreases`'s are,
and discharged by hand where the defaults fail (`on ?depth_N := …`, the
same as a measure's). The generator then publishes **the same theorem it
publishes without the clause**, `f::depth: (xs) → f::fits(ν(xs), xs) =
True`, by the same walk with ν in place of μ (the walk already takes any
rank). Every route ends in that one named statement, and the compile reads
nothing else (agreed 2026-11-22).

Built (2026-11-22). The parser takes `depth ν` after `decreases μ` and
refuses it alone. The elaborator lowers the body a second time with `ν` as
its measure, under the name `f#depth`, and keeps only the lifted
obligations, designated `f::depth_obl_N`; the writer's `on ?depthN := …`
are their discharges and every other `on` stays with the measure's
lowering. `ν` itself is published as `f::depth_rank`, a function of the
parameters, so the generator's rank is a global and needs no `Lam` spelled
per node. A `depth` obligation that does not hold is refused at its call,
"this recursive call must decrease the `depth` bound". A `depth` clause on
a declaration with loops or on a mutual recursion is refused as not built.
`runtime fn rstep2(n: u64) → u64 decreases n.toNat() depth n.toNat() / 2`
gets `rstep2::depth: rstep2::fits(n.toNat() / 2, [n])` with both
obligations found by the default closers, five levels at 10 where the
measure says ten.

Where no rank does (the depth depends on more than a drop per call, as a
flat `≤ 100` would), the writer proves `f::depth` themselves, in the
general form of §3.1 by `f`'s functional induction, and the generator
takes it as given rather than generating one. That route is left until a
program needs it: proving `fits` directly is the ugly case, and a rank
covers every recursion in the probes. A lexicographic measure gives no
depth by itself and needs a `depth` clause.

### 3.4 A closed program infers its depth

When `main` calls the recursion at closed arguments, `fits` evaluates.
The generator takes the least `k` with `main`'s calls fitting within `k`,
and that is the program's levels: no argument, no theorem. Built
(2026-11-21): `PDef::depth` evaluates a call's depth directly, in one pass
over its calls rather than a search over `k` (it is the least `k` with
`fits(k)`, below a fuel that for a measured function is never reached),
and `PTm::program_need` is main's. Nothing is proved of either: the
program is made at the levels they give and the verdict that `fits` holds
there is still what the theorem takes, so a wrong depth could only refuse.
`runtime fn sum_ten() → u64 { rsum(10) }` runs at eleven levels. `runtime(levels := n)` stays
as an optional check for a while (the program must fit within `n`), and
leaves once the byte budget of §4 is there to state the same thing in the
unit people mean.

## 4. The stack: a byte budget, checked once

### 4.1 Bytes, not levels

What a writer means by "this fits" is bytes: **this program runs in
1 MiB of stack.** It is a statement about the compiled program's
execution, so it belongs to the compiled theorem, not to the source's
meaning (which cannot mention bytes; recursion-stack-refusal, 2026-11-17).

```
runtime(stack := 1 MiB) fn main() → u64 { … }
```

The compiled theorem it publishes: run with that much stack, every run is
exactly the source's run, never refused. Its proof splits the way
Quantitative CompCert's does. The source half is the depth bound of §3, in
levels and free of frames. The compiler half is the room a number of
levels costs, which the compile already prices exactly by the call graph
(`Source::top`, `List::level_row`, procedure-frames design §7.4); the
comparison `room(d) ≤ 1 MiB` is closed by evaluation when `d` is closed.
When it fails, the refusal says what the deepest chain costs, which frame
dominates it, and what the bound was, so the writer knows whether to
tighten the bound, shrink a frame, rewrite (§5) or raise the budget.

Built (2026-11-22) for a closed program, as the generator's argument
beside `levels`: `runtime(stack := 65536) fn main() → u64 { … }`
publishes `main::stack`. The bytes a level costs are the placement's, so
the comparison is made where the placement is chosen: `write-elf`, compiling
`main::source`, reads `main::stack` beside it, refuses a program whose
`Source::need` is past it, and otherwise states the fit in the certificate
(`need(homes, frames) <= main::stack`, by evaluation). The refusal names
the need, the levels and what the last level costs: "`sum_ten_tight` needs
392 bytes of stack under this placement, past its budget `stack := 64`:
its calls nest 11 levels, the last costing 32 bytes". The contract's
`StackRoom` stays the exact need, which the program tests at startup; the
budget is the writer's ceiling on it. A budget on a program that calls no
recursion is refused for now. Naming the frame that dominates the deepest
chain, and the target, are left for when there is more than one frame in
it.

Without a `stack` clause the budget is the stack the system contract
presumes (Linux's default 8 MiB, `docs/native/system-contract-design.md`
§4.1). A budget past it needs the contract's mapped stack, and until that
lands it is refused at compile time with the room it would need.

### 4.2 An input-dependent bound: one check, before the recursion

When the bound depends on input (`μ(n) = n` for a recursion over a word
read at startup), its value is not known at compile time, but it is known
before the first recursive call. So the room is checked **once, at the
boundary**: where code outside the recursion calls into it, the call
computes `room(d(args))` from the cheap closed formula the periodic pricing
gives (#812), compares it with the stack left, and either enters the
recursion with no further checks or refuses there, before the callee runs.
When `main` makes that call first, the check is at startup and a refused
input has done nothing. This is guarantee 4 of the procedure-frames design
§7, with the bound in the function's own terms.

The back end needs one new charge for it: a call into a cycle that is
**budgeted** rather than checked, its premise `fits(d(args))` at the call,
and inside the cycle calls that are not checked at all.
`Source::compiled_levels`' proof already reads calls within the levels
as their values (`Source::pure_reads`); the budgeted call takes its levels
from the premise instead of from `Source.levels`.

With a `stack := …` clause and an input-dependent bound, the theorem's
set of refused runs is exactly the inputs whose bound does not fit, which
is stated, not discovered at a random depth.

## 5. Getting rid of the stack: the optimizer's job

A bound that does not fit is not the end: a rewrite turns the recursion
into something that needs less. The 2026-11-21 version did the rewrites in
the generator, which was the wrong layer (Minus, 2026-11-22). For a
function only the meaning matters, and a rewrite that keeps it is an
optimization; it belongs to the optimizer
(`docs/native/optimizer-design.md`), where it is one more rule, chosen by a
searcher against a cost, and where a target on which stack is cheap can
decline it while one on which it is dear takes it. The generator goes back
to only reflecting.

### 5.1 A level for procedures

The optimizer has a replayer per code level and its moves are FunctionIR's.
FunctionIR's functions cannot recurse, so a rewrite of a recursion needs a
level above it: **procedures**, the `PTm` definitions (later the `Source`
procedures they lower to). Its moves are the optimizer's, read there:

- **Rewrite** by a rule whose sides are procedure definitions and whose
  theorem says their meanings agree, `sem(lhs) = sem(rhs)` over
  `PDef::Unfolds`, where its conditions hold.
- **Inline** a non-recursive callee into its caller, and **restate** a
  recursion as a loop (a tail call already is one, `rt_loop`).

The level's one law adds depth to meaning: a move may replace a definition
only by one that means the same **and needs no more depth**, `fits(k, x)`
of the old implying it of the new. So `f::depth`, proved of the source,
stays a bound of whatever the optimizer makes, and the room check (§4) runs
on the optimized program, never looser than the source's. A move that does
take the recursion off the stack, as the accumulator does, publishes a
bound of 0 for what is now a loop.

**Stack is a cost.** The searcher already weighs instructions; at this
level it also weighs `room(depth)` in the target's bytes (`Source::top`).
Where the budget of §4.1 fails, the searcher is asked for a plan that
meets it before the compile refuses, and the refusal lists what it tried
and why each rule did not apply (the operation is not associative, the
continuation reads more than the result), so "too deep" always comes with
something to do.

### 5.2 The rules

1. **The accumulator.** A body `if c then b else e ⊕ f(y)` with `⊕`
   associative becomes `go(x, acc) = if c then acc ⊕ b else go(y, acc ⊕ e)`
   (entered as `f(x) = if c then b else go(y, e)`), a tail call, so a loop:
   no stack at all. On words, `+`, `*`, `^`, `&` and `|` are associative,
   which covers the sums, products and folds most recursions are. It is
   one rule with associativity as a condition, proved once by induction on
   the depth; the condition is answered by the registered learners as word
   rules' are. Generalising it (several base cases, the operand on either
   side, a let between) is Koka's tail recursion modulo context (Leijen and
   Lorenzen, POPL 2023), as more rules of the same shape.
2. **Later, and harder to find:** tail calls modulo constructors once
   `runtime fn`s build heap data (OCaml's `[@tail_mod_cons]`), frame
   shrinking (a frame holding only the words live across its call), and
   inlining one level of a recursion into itself to halve its depth.

### 5.3 The explicit stack on the heap, asked for

Any `PTm` recursion becomes a loop over a stack of continuation frames held
in a heap span: each `Recur`'s continuation is a frame tag and the words it
still reads (defunctionalisation of its CPS form). `PTm`'s four
constructors make this one generic theorem, not one per function. The depth
bound still applies and now sizes the heap span, checked once as §4.2
checks the stack; past it the run is refused the same way. It is a restate
move like the others, but it trades stack for heap, an allocation and a
copy per level, so the searcher never picks it unasked: it is **opt-in**
(`runtime(recursion := heap)`), the deliberate sidestep for a recursion
whose depth is truly large (agreed 2026-11-21), and the place to optimise
later (frames holding only live words, a span that grows by doubling).

## 6. Prior art

- **Stack analysis with a required annotation for cycles**: GNATstack
  reports cyclic call graphs as unbounded (`+?`) and asks the writer for
  their depth; MISRA C and SPARK's `No_Recursion` forbid recursion. The first
  version (§8.1) was this; §3 leaves it.
- **Verified source-level bounds**: Quantitative CompCert (PLDI 2014)
  proves stack bounds on the source with a frame-size metric the compiler
  supplies; CakeML's space cost semantics (OOPSLA 2020) proves programs run
  within a stated heap and stack. §3 and §4 follow the first.
- **Inferred bounds**: RaML's automatic amortised resource analysis infers
  polynomial bounds; the rank of §3.2 is the degree-one case Heather gets
  for free from `decreases`.
- **Making the problem go away at run time**: Go's and OCaml 5's growable
  stacks, Racket's continuation on the heap. §5.3 is the proved, opt-in
  version.
- **Rewrites**: Koka's TRMC (POPL 2023), OCaml's `[@tail_mod_cons]`; Zig's
  open proposal for safe recursion (ziglang/zig#1006) asks for exactly the
  check of §4.2 without a proof behind it.

## 7. What it shares with the depth-free tree

Programs over `Io` are read through the coinductive tree (`Source::tree_co`,
`rt_io_program`), which still nests calls by a depth; the depth-free
co tree is its own thread ("Remove the call-depth limit from the fuel-free
meaning"). The theorems of §3 and §4 need the levels in that meaning too: the co
tree's calls cut past `k` counted levels, as `Source::calls_within` cuts
the inductive one. Whichever lands second states its result with the
other's.

## 8. Steps

The first six steps of the 2026-11-20 order (statements read with their
calls answered, a pure recursion as a procedure, the levels in the charges,
the generator) are built, §8.1. From here, in order:

1. **The depth by measure** (built): `PDef::Descends` and
   `PDef::fits_by_rank` in `rt_ptm`; the generator publishes `f::depth:
   f::fits(μ(x), x)` from the lifted obligations (§3.2).
2. **Closed programs infer their levels** (§3.4, built): `runtime fn
   main()` with no argument; `levels := n` optional.
3. **The `depth ν` clause** (§3.3, built): parsed beside `decreases`, its
   obligations lifted and defaulted as a measure's, `f::depth` from ν.
4. **The byte budget** (§4.1, built for a closed program):
   `runtime(stack := n)`, checked at the compile and stated in its
   certificate; the refusal names the need, the levels and a level's cost.
5. **One check at the entry** (§4.2, §2.1): the budgeted call, unchecked
   calls inside a proved-bounded cycle, and the reserved call that keeps
   the recursion's callers regions.
6. **A procedure level for the optimizer** (§5.1) with the accumulator rule
   (§5.2), stack as a cost.
7. **The heap stack** (§5.3), opt-in.
8. Mutual recursion, a recursion calling other functions, lent spans
   (`port_depth`), and calls between `Io` functions with a buffer contract
   (`rt-effectful-callees`) and recursion over `Io` through them.

### 8.1 Built so far (2026-11-20, 2026-11-21)

- **Step 1** is `Stmt::thread_by` and `Stmt::reads_where`
  (`lib/native/native_source_io.hthr`): a statement with no loop, each
  call it makes `ok` and read as its answer, reads as its threading.
- **Step 2** took a narrower node than an `ETm` call: `PTm`
  (`lib/native/runtime/rt_proc.hthr`), a pure body over `rt`'s `Tm` with
  `Recur(p, args, rest)`, a call of procedure `p` on word variables. Its
  meaning reads calls through the procedures' meanings, `PTm::need` is its
  depth, and `PTm::lower_sound` proves its statements. A call of a
  recursive function cannot sit in a region (`Tm::CallsAgree` quantifies
  over every callee), which is why the node is on the statement lane and
  `Tm` is unchanged. `PDef::bodies` turns a list of `PTm` definitions into
  procedures meeting `Source::PureBodies`, given the one pin the generator
  will supply (`PDef::Unfolds`, the meaning's equations) and which entries
  fit within how many levels (`PDef::Fits`). `Source::pure_reads` (`lib/native/native_source_pure.hthr`)
  then reads every call within the levels as its value, by induction on
  the levels and, at one level, on the ranks of unchecked calls.
- **Step 3**, the part about charges: `Source::pure_program_reads`
  (`lib/native/native_compile_pure.hthr`) takes the charges and ranks of a
  compile that accepted the source, so a compiled source's `main`, its
  calls run as deep as they go, reads as `main` threaded with each call
  answered, for every run whose calls keep within `Source.levels`. Joining
  the co tree to the machine is the depth-free tree's thread (§7).
- **The depth became a predicate, `PDef::fits(k, p, xs)`**: whether the
  call runs within `k` levels, by recursion on `k` (each call it makes fits
  within `k - 1`). It needs no measure and no fuel, so it is total for any
  recursion, terminating or not, and at a closed argument it is `refl`;
  `PDef::fits_fit` proves it is what the bodies keep wherever every call
  is counted (a self-recursive function's are). The first version's `f::depth(x) <= levels`
  reads as `f::fits(levels, x) = True`, and a depth bound is the writer's
  theorem `f::fits(g(x), x) = True`. A cycle with unchecked calls in it
  would need the ranks in the recursion too; the generator refuses it for
  now.
- **Step 4, the guard and a whole program.** `Tm::to_ptm` reads a reflected
  body's calls of itself (`Call(0, …)`) as `Recur`s, under `if` and `if h:`
  too. `PTm::Guarded` is `Fun::Guarded`'s statement over a `PTm`, which the
  generator can prove as it proves a measured loop's; `PDef::bodies_one`
  takes it to every obligation. `PTm::program_reads`
  (`lib/native/runtime/rt_proc_program.hthr`) is a pure program's theorem:
  main a `PTm` over no parameters calling the recursive function's
  procedure, its value the exit status; for any compile that accepts it,
  where main's calls fit within `Source.levels`, the run exits with main's
  value and leaves the world as it was. `crates/cli/tests/native_recursion.rs`
  runs `sum(10)` compiled: 55 within 16 levels, the call-depth status 139
  within 9.
- **Step 4, the generator (2026-11-21).** A `runtime fn` whose call of
  itself is not its last act, over words with a word result and calling
  nothing else, is no longer refused: where the judgment refuses it and
  `Fun::recursive_ptm` reads its body, the generator publishes `f::rt`,
  `f::ptm`, `f::guarded` (`PTm::GuardedWords`, proved from `f::ext` and
  `f::irrel` as a measured loop's guard is), `f::unfolds` and `f::fits`
  (`f::fits(10, [10]) = True` by `refl`). The terms, their meaning and the
  pins moved to `rt_ptm` (`lib/native/runtime/rt_ptm.hthr`), which needs
  only `rt`, so `runtime` reads them without the native-source chain;
  `rt_proc` keeps the lowering.
- **A program, and its levels.** `runtime(levels := 16) fn main() → u64 {
  f(10) }`, a main over no words calling one recursion, publishes
  `main::ptm`, `main::source` (`PTm::program(…).get(trivial)`) and
  `main::reads: PTm::SourceReads(main::source, main)`: any compile of the
  source that is accepted, run against any world, exits with `main`'s
  value. It is `PTm::source_reads` (`rt_proc_program`), which reads the
  premises off the equation that made the source; the generator closes
  each by evaluation after checking `PTm::program_verdict` itself, so a
  main whose calls go deeper than its levels is refused saying so, as is
  one that states none (the first version's sentence). The levels are the generator's
  argument, the builder spelling the first version allowed, rather than a `levels n`
  clause in the header: a parser change bought nothing the argument does
  not. A caller with words of a recursion is refused naming it (§2's
  rule, not yet built). `write-elf` runs `main::source` to 55, and the
  same program at nine levels to the call-depth status
  (`crates/cli/tests/native_recursion.rs`).
- **Companions for non-tail calls.** The unfolding walk (`f_unfold`,
  `f::ext`, `f::irrel`; docs/language/recursion/decreases-unfolding-design.md
  §3) refused a recursive call under a method call (`n.add(f(n - 1))`) or
  bound by a `let`; both are walked now, which is what `f::guarded` is
  proved from.
- A closed probe (`lib/_tests/native/runtime/rt_proc_tests.hthr`): a
  non-tail recursive sum lowers, fits within 10 levels at 10 and not 9,
  its statements run to 55 at 10 with the world untouched, and a wrong-arity call and a bit-valued body are
  refused.

- **Depth, inferred (2026-11-21).** `PDef::fits_by_rank` (§3.2) and the
  evaluated depth (§3.4): a closed `main` states no levels, and a stated
  `levels := n` is a check. `write-elf` runs `sum_ten` at its inferred
  eleven levels to 55 and at ten to the call-depth status. Every
  recursion in the probes gets `f::depth` from its obligations: `rsum`,
  `doubled` (a `let`), `rpow2` (two calls, two obligations) and
  `rsum_from` (the measure on the second word).

## 9. Decisions for Minus

Agreed 2026-11-21: the depth is a proved bound, inferred by default from
the measure and tightened by the writer's theorems; the room is computed
once, not per call; an opt-in heap stack; a budget in bytes.

Agreed 2026-11-22:

1. The tighter bound is a `depth ν` clause beside `decreases`, and every
   route, the clause, the measure or a hand proof, ends in one named
   theorem `f::depth` (§3.3).
2. A budget in bytes is a claim about the compiled program for one target,
   and may hold on one target and fail on another: the runtime is platform
   specific to that degree, and the refusal names the target and the frame.
3. Rewrites that take a recursion off the stack are the optimizer's, at a
   level for procedures, with stack as a cost (§5).

Open:

4. Lifting callers to statements (§2) is a cost Minus is unsure of. §2.1's
   reserved call is the proposed way out; whether to design it before the
   byte budget (step 4) or after.
5. `levels` leaves the surface once `stack := …` lands (recommended),
   staying the compiler's internal unit.
