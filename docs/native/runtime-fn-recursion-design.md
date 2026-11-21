# Recursion in a `runtime fn`: procedures, proved depth and the stack budget

Status: proposal (2026-11-20), revised 2026-11-21: the depth is a proved
bound inferred from the measure, the stack a budget in bytes checked once,
and rewrites take a recursion off the stack (§3 to §5). The short surface note that
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

One consequence is a rule rather than a choice: **recursion lifts its
callers to statements.** A pure function that calls a recursive one cannot
stay a region, because its call can stop. The refusal says so and names the
recursive callee; the generator then reflects the caller as a statement
too. A tail recursion still becomes a loop, and a loop stays a region.

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
Two routes to `PDef::Descends` at `f`:

Built (2026-11-21) by the second route, which needed no new companion
after all: the elaborator names each lifted obligation `f::obl_N`, and
the generator walks `f::ptm` with one lemma per node (`PTm::calls_ok_bind`,
`_recur`, `_choose`), closing each call with the obligation whose reading
(the caller's words in order, the branch tests in scope) the call's
lemma accepts. The join the companion was to avoid turned out not to be
fragile: a reflected test's equation converts to the source's `match h:`
equation, as the guard's conversions already showed. Two things it did
need: the rank is the measure read at the first words of any list
(`PTm::padded`), since `Ty::on_words` matches on the list and is stuck at
the statement's own `xs`; and the environments are passed as handles read
off each lemma's premise, since spelled out every `Bind` copies the one
before it twice. The generator publishes `f::depth: (xs) → f::fits(μ(xs),
xs) = True` wherever the walk closes every call, and nothing otherwise (an
obligation reading a `let`'s or a call's result). The two routes as first
weighed:

- **Recommended: a companion, `f::descends`.** The unfolding walk that
  emits `f::ext` and `f::irrel` (`crates/elab/src/measure.rs`) already holds
  each call site's path hypotheses in source terms; one more instantiation
  of it, whose leaf at a self-call is that site's obligation rather than a
  congruence step, states that every call the step functional makes is
  below `μ(x)`. The generator then carries it to `f::ptm`'s `calls_ok` as
  it carries `f::ext` to the guard.
- The alternative: the generator walks `f::ptm` and closes each `Recur`
  with the matching `f#obl_N`. It needs no elaborator change but has to
  match the reflected branch conditions against the obligations'
  hypotheses, which is the fragile join the companion avoids.

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
and discharged by hand where the defaults fail. Where no rank does (the
depth depends on more than a drop per call), the bound is a theorem in its
general form, `f::depth` of §3.1 proved by `f`'s functional induction, and
the runtime fn names it (`runtime(depth := find::depth_log)`). In every
case it is an ordinary theorem; nothing about it is special to the
compiler. A lexicographic measure gives no depth by itself and needs one
of these.

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

## 5. Getting rid of the stack: rewrites and the heap stack

A bound that does not fit is not the end. A rewrite turns the recursion
into something that needs less, and each is **a function on `PTm` with one
meaning theorem**, `rewritten.sem = original.sem`, proved once in `rt`.
That makes them not quite compiler passes: the compiler is unchanged and
sees an ordinary program; the rewrite runs in the generator, its result is
published (`f::rewritten`, and the equation to `f`), and it is offered,
applied or declined by name, as the optimizer's rules are
(rules-as-theorems). Their cost is the generator's, and a wrong one is
impossible rather than unlikely.

1. **The accumulator.** A body `if c then b else e ⊕ f(y)` with `⊕`
   associative becomes `go(x, acc) = if c then acc ⊕ b else go(y, acc ⊕ e)`
   (entered as `f(x) = if c then b else go(y, e)`), a tail call, so a loop (`rt_loop`): no stack at all. On words, `+`, `*`,
   `^`, `&` and `|` are associative, which covers the sums, products and
   folds most recursions are. The meaning theorem takes associativity as a
   premise and is proved by induction on the measure. Recognising the
   shape on `PTm` is syntactic: a `Recur` whose continuation is
   `Value(op(e, Var(0)))` with `e` not mentioning the result. This one is
   strictly better whenever it applies, so it is **applied by default**
   and reported in `--explain`. Generalising it (several base cases, the
   operand on either side, a let between) is Koka's tail recursion modulo
   context (Leijen and Lorenzen, POPL 2023), done as proved rewrites.
2. **The explicit stack on the heap.** Any `PTm` recursion becomes a loop
   over a stack of continuation frames held in a heap span: each `Recur`'s
   continuation is a frame tag and the words it still reads
   (defunctionalisation of its CPS form). `PTm`'s four constructors make
   this one generic theorem, not one per function. The depth bound still
   applies and now sizes the heap span, checked once as §4.2 checks the
   stack; past it the run is refused the same way. It costs heap, an
   allocation and a copy per level, so it is **opt-in**
   (`runtime(recursion := heap)`), the deliberate sidestep for a recursion
   whose depth is truly large, and the place to optimise later (frames
   holding only live words, a span that grows by doubling).
3. **Later, and harder to find:** tail calls modulo constructors once
   `runtime fn`s build heap data (OCaml's `[@tail_mod_cons]`), and the
   general TRMC of (1).

The refusal of §4.1 lists the rewrites that apply and why the others do
not (the operation is not associative, the continuation reads more than
the result), so "too deep" always comes with something to do.

## 6. Prior art

- **Stack analysis with a required annotation for cycles**: GNATstack
  reports cyclic call graphs as unbounded (`+?`) and asks the writer for
  their depth; MISRA C and SPARK's `No_Recursion` forbid recursion. §3 is
  what #836 did; this note leaves it.
- **Verified source-level bounds**: Quantitative CompCert (PLDI 2014)
  proves stack bounds on the source with a frame-size metric the compiler
  supplies; CakeML's space cost semantics (OOPSLA 2020) proves programs run
  within a stated heap and stack. §3 and §4 follow the first.
- **Inferred bounds**: RaML's automatic amortised resource analysis infers
  polynomial bounds; the rank of §3.2 is the degree-one case Heather gets
  for free from `decreases`.
- **Making the problem go away at run time**: Go's and OCaml 5's growable
  stacks, Racket's continuation on the heap. §5 item 2 is the proved, opt-in
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
3. **The byte budget** (§4.1): `runtime(stack := n)`, the compiled theorem
   in bytes, the refusal that names the deepest chain and its frames.
4. **One check at the boundary** (§4.2): the budgeted call, unchecked calls
   inside a proved-bounded cycle, callers with words (§2's rule, which this
   needs anyway), the `depth` clause and `runtime(depth := …)` (§3.3).
5. **The accumulator rewrite** (§5 item 1), on by default.
6. **The heap stack** (§5 item 2), opt-in.
7. Mutual recursion, a recursion calling other functions, lent spans
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
once, not per call; rewrites and an opt-in heap stack; a budget in bytes.
Open:

1. The tighter bound's surface: a `depth ν` clause beside `decreases`
   (recommended, §3.3), with the general theorem named by
   `runtime(depth := …)` for what no rank captures.
2. `levels` leaves the surface once `stack := …` lands (recommended),
   staying the compiler's internal unit.
3. The accumulator rewrite applied by default and reported (recommended),
   or only when asked.
4. Recursion lifts its callers to statements (§2): a consequence, listed
   so it is seen.
