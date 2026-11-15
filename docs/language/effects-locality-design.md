# Effects and locality: what Heather has, where it is coarse, what to build

Status: **an assessment, 2026-11-08**. No code changes; the probes it cites
(§5.2) are in the appendix, run on `a6d30ca`.
Minus asked for a thread on effects ("I've heard some complaints about
effects not being local enough"). Read `docs/compilation-vision.md` and
`docs/language/effects-capabilities-design.md` first; this note extends them and
does not reopen their decisions.

"Not local enough" is the usual complaint about a monolithic world or `IO`
effect, and it is really three complaints:

1. **Signatures.** A function's type does not say which effects it uses.
   Every effectful function takes the whole `Io`, so a function that writes
   one log line and one that opens and overwrites files have the same type.
2. **Handling.** An effect cannot be interpreted locally: a block cannot
   say "inside here, logging goes to a list" or "these writes are
   buffered", because the world is supplied from outside and threaded
   opaquely.
3. **Reasoning.** A proof about one part of a program does not stay
   local: there is no frame rule saying that a function which only writes
   stdout leaves everything else alone, so specs mention the whole world.

## 0. In one page

**Today.** Heather has five kinds of effect, and four of them are already
local: `let mut` state is SSA (pure, entirely local), failure is
`Option`/`Result` with `?`, divergence is `Partial` (the delay monad over
`CoTree`), and tactics are a request tree with library handlers (`focus`,
`attempt`). The fifth, the operating system, is one capability: `Io`, a
world (a function from the history of exchanges to the next answer) and that
history. Effectful code threads it through `mut self` methods, a loop over it
means `Io → Partial<Mutated<Io, R>>`, and a compiled program's tree reads as
that function at every world (`Io::Reads`), proved once per construct.

**Where it is coarse.** All three complaints above hold for `Io`, plus some
plainer composition limits (§3): no effectful callbacks, no effectful callees
in `rt`, one loop cannot call another, no branch over the world in `rt`.
Some of the coarseness is semantic truth, not a design flaw: Linux's answers
on one descriptor *can* depend on what was done on another (a terminal echoes,
a pipe's reader waits on its writer), so a model where stdout and stdin are
independent would be unsound for some environments. Locality at the bottom
has to be an *assumption about the world*, stated and discharged, not a
property of the type.

**Recommendation** (§5), in layers, none of which changes what the compiler
proves:

1. **Keep one primitive world at the bottom.** The machine has one
   signature (system calls), the compiler is proved against it once, and
   `Io` stays the only thing `rt` lowers to `Invoke`.
2. **User effects are interfaces over a carrier, handled by choosing the
   carrier.** A class whose members are `mut self` operations
   (`class Log<C>`); a function generic in its carrier (`fn greet<C>(…, d:
   Log<C> := infer)`) says in its type that it only logs; a handler is an
   instance (pure: collect into a list; backed by `Io`: write to stderr;
   wrapping: buffer over another carrier). This is Effekt's capability
   passing and Koka's tail-resumptive handlers, resolved statically. It
   works today for pure carriers and for `Io` itself (probes, §5.2).
   Compiled by specialisation: at a concrete carrier the reflector sees
   pure code or `Io` calls, which it already handles, once it learns to
   flatten a carrier record that holds the world.
3. **Footprints are facts, and the frame rule is a theorem over worlds.** A
   semantic footprint (`Io::Only(P, f)`: every exchange `f` adds satisfies
   `P`), produced by a verified analysis over `ETm` and closed under
   `reads_bind`/`iterate`; and world *protocols* (stdin is a pipe of these
   chunks, stdout is a sink) composed separately, with one frame theorem:
   under a world separable at a partition, a function whose footprint is
   one side has a meaning that the other side's protocol does not affect.
   The same footprint fact is what a reordering pass consumes
   (`docs/compilation-vision.md` §3.2's `Writes`).
4. **Lift the composition limits** (effectful callees, statement arms with
   binds, `EIf`, callbacks that take the carrier), each already a known
   residue of R6.
5. **Control effects stay libraries.** Generators, backtracking, async and
   multi-shot effects are trees (`CoTree` + handlers, as `Tac` already is),
   compiled, when they are, by their own `Compile` instances (vision §2.2's
   DSLs). No row-polymorphic effect system and no first-class continuations
   in the language or in `rt`.

The alternatives weighed (§4): algebraic effects and handlers in the
language (Koka, Eff), capability passing (Effekt, OCaml's Eio), interaction
tree signatures and `interp`, linear or unique sub-worlds (Clean's files
split from `*World`), and separation-logic framing. The recommendation takes
capability passing for signatures and handling, ITrees for the semantics of
handlers that are not tail-resumptive, and separation for reasoning, and
declines in-language handlers with captured continuations because proving a
compiler for them once is a new, large contract (stack switching) that no
customer needs yet.

---

## 1. What Heather's effects are today

| Effect | Surface | Meaning | Compiled by |
|---|---|---|---|
| Local state | `let mut`, `:=`, `mut self` on any type, `for`, `while` | SSA lets; loops as a named step over `foldl`, `decreases` recursion, or `CoTree::iter` (sequencing design §5, §18) | pure `rt` (`Tm`, loops) |
| Failure | `Option`, `Result`, `?`, early `return` | values; `Bind`/`Pointed` instances (sequencing design §3.5, §15) | pure `rt` |
| Divergence | `partial fn`, `while` with no measure | `Partial<B> = CoTree<B>(Events::none())`; `CoTree::rec`/`iter` (`docs/language/partial-functions-design.md`) | `Repeat` (tail case) |
| Linux | `mut io: Io`, `io.read(…)`, `io.write(…)` | world threading: `Io → Mutated<Io, R>`, in `Partial` when it loops (`docs/language/effects-capabilities-design.md`) | `ETm`/`ELoop` → `Source` `Invoke`/`Repeat` → x86 |
| Tactic requests | `Tac` values built by `pure`/`ask`/`ask_then` | a request tree; `focus` and `attempt` are Heather handlers (`docs/metaprogramming/host-elaboration-interface-design.md` §3.3, §13) | not compiled; run by the host |

Beneath them sits the tree library: `Events` as containers
(`record Events { Cmd, Resp }`), `Events::sum`, finite `ITree` and
coinductive `CoTree`, `bind`/`iter`/`rec`, `Eutt`, and one handler,
`ITree::run_state` over `Events::sum(Events::state<S>(), E)`, whose
`run_state_bind` is what showed world threading and trees compose
(`issues/effects-direction.md`, 2026-10-21).

The native path for effects (R6, slices 1–5, PRs up to #482):

```
surface mut-self body ──reflect (rt_io_reflect)──▶ ETm / ELoop ──lower──▶ Source (Invoke, Repeat) ──▶ x86
        ▲                                             │ sem                         │ tree_co
        └────────────── Io::Reads (Eutt at every world), proved once per construct ─┘
```

`ETm` never names the world, so a reflected program cannot copy or drop
it: linearity holds by construction, and the reflector's refusals at the
call are the whole linearity check (capabilities design §8.1, §8.3). A
read lands in place and the buffer it overwrote is `Gone` (§8.5), so the
one uniqueness fact the lowering needs is decided there.

## 2. What is already local

The complaint is easy to over-apply, so first what does *not* need fixing:

- **State is local.** A `let mut` local is SSA; a `mut self` method on a
  record of your own is a pure function returning `Mutated<S, R>`. There
  is no global heap and no ambient state: two functions can only interfere
  through what they are passed and return. That is stronger locality than
  a separation logic gives an imperative language, because it holds by
  typing rather than by proof.
- **The meaning is compositional.** World threading composes by function
  composition; `Io::reads_bind` and `Io::reads_iter` make the compiled
  tree's agreement compositional too. Nothing about the *meaning* of
  `f; g` requires knowing `f`'s body beyond its function.
- **Failure and divergence are in the type.** `Partial<…>` and
  `Result<…>` say what a function may do, and the elaborator refuses a
  partial call used as a value.
- **Uniqueness is per buffer and decided at lowering.** The compiler does
  not need a global aliasing analysis.

So the coarseness is concentrated in one place: the operating system
capability, and the ways code over it composes.

## 3. Where it is not local

Each item names where it lives and whether the coarseness is essential.

**N1. One type for every effectful function** (signatures). `Io::cat`,
`Io::write_all` and `Io::echo_once` all take an `Io`. The type cannot say
"writes stdout only", "never opens a file", or "only reads". *Not
essential:* nothing in the meaning needs it; the information exists in the
reflected `ETm` (which `Invoke`s it makes) but is not stated anywhere a
caller or a spec can use.

**N2. One signature of effects, hard-wired** (signatures, handling). `Io` is
`record Io { world: World(), past: List<Exchange> }` with
`World() = List<Exchange> → (c: LinuxCmd<Nat>) → c.Resp()`. A user cannot
declare an effect of their own (a logger, a random source, a clock, a
key-value store) with the same surface; they write a record with `mut self`
methods, which works for pure state (§2) but cannot be backed by `Io`
without holding the world inside a record, which the reflector refuses
(capabilities design §5: "never stored in a record").
*Not essential.*

**N3. No local handling** (handling). A program cannot reinterpret part of
its own effects: buffer its writes, redirect stderr to a list, run a
sub-computation against a mock file. Worlds *are* deterministic handlers
(`World::piped` is a mock pipe and terminal), but a world is chosen by
whoever calls the function, for the whole run, and only specs do it. Tree
handlers exist (`run_state`, `Tac`'s `focus`), but effectful surface code
does not produce a tree; it produces a world-threading function. *Not
essential* for tail-resumptive effects (§5.2); essential to the surface's
shape for the others (§5.5).

**N4. No frame rule** (reasoning). A world is *any* function of the
history, so after a write to fd 1 a read on fd 0 may answer differently.
That is the point of one world (capabilities design §1: "a terminal echoes
what is written to it into what is read back"). The consequence is that
"`f` only writes stdout, so what `g` reads from stdin is unaffected" is not
a theorem: it is false at some worlds. Specs about the environment
(stdin holds these bytes; the file at this path holds those) are
predicates on a whole `World()`, with no vocabulary for combining one about
stdin with one about a file. *Essential at the bottom* (it is Linux's
truth); fixable by stating separability as a hypothesis (§5.3).

**N5. No effectful callbacks** (composition). A `mut self` call on an
outer `let mut` reached through a λ is refused (capabilities design §2.2),
so `xs.for_each(λ x => io.write(x))` cannot be written; the callback has to
take and return the world, and then `for_each` is world-specific. Effekt
calls this the second-class-capability restriction and lifts it with boxes;
here it is the price of linearity by construction. *Partly essential*: a
λ that captures the world and escapes would copy it; a λ that takes the
carrier as an argument is fine (§5.4).

**N6. No effectful callees in `rt`** (composition, compilation). `ETm` has
no call of another effectful function (capabilities design §8.4: "an
effectful callee (`EFun` calling `EFun`) is not modelled"). So effectful
code compiles only as one function, and an effectful helper is inlined by
hand or not at all. *Not essential*: `Source` has procedures
(`docs/native/native-procedures-design.md`, PR #326), and `reads_bind` is exactly the
call's case.

**N7. Shape limits of the surface over the world** (composition). A
measureless `while` has no `break`, and a bind inside a statement arm of its
body is not lowered, so one loop cannot call another (sequencing design
§18, item 6); `rt` has no branch over the world (`EIf`, capabilities design
§8.4). These are slices not yet built, not design.

## 4. The alternatives

For each: what it gives on the three axes, how it meets world threading,
and what it costs the compiler that is proved once.

### 4.1 Algebraic effects and handlers in the language (Koka, Eff)

Effects are declared operations; a function's type carries a *row* of the
effects it may perform (`⟨log, exn | e⟩` in Koka); a handler interprets
operations in a scope and may capture the continuation (resume zero, one or
many times). Rows give **signatures**, handlers give **local handling**,
and equational reasoning about handlers gives some **reasoning** locality.

- *Fit.* Two additions Heather does not have: row polymorphism in the type
  system (or an encoding through classes; §4.2 is that encoding), and a
  semantics for captured continuations. The semantics is the free monad /
  interaction tree, which Heather has; but then effectful code is *layer 1*
  over a tree carrier, the monadic surface `effects-direction` ruled out,
  and the surface stops being pure world threading.
- *Compilation.* Koka compiles handlers by evidence passing (Xie and
  Leijen, "Effect handlers, evidently", ICFP 2020; "Generalized evidence
  passing", ICFP 2021): tail-resumptive operations become calls through an
  evidence vector, and only general handlers need multi-prompt delimited
  control, implemented by yielding up the stack. OCaml 5 uses segmented
  stacks (fibers). Either way, a general handler needs the machine level to
  capture and reinstate a continuation, and proving *that* once is a new
  contract on `Source` and on the x86 calling convention (stack
  switching, or a CPS'd `Source`). No customer needs it today.
- *Verdict.* Take the tail-resumptive fragment (it is §4.2), leave the
  general one to libraries.

### 4.2 Capability passing (Effekt, OCaml Eio)

Effects are *values*: a capability object with the operations, passed
(explicitly or implicitly) to the code that uses them. A handler is a
scope that provides a capability (Brachthäuser, Schuster, Ostermann,
"Effects as capabilities", OOPSLA 2020; "Effects, capabilities, and boxes",
OOPSLA 2022). Eio does the object-capability version over OCaml 5's
effects: a function given only `stdout` cannot open files.

- *Fit.* This is what Heather's surface already is, for one capability:
  `io` is passed, its operations are `mut self` methods, and the
  linearity refusals are Effekt's second-class restriction. Generalised to
  user effects, an effect is a class over a carrier and a handler is an
  instance (§5.2). Signatures come from the class constraints; handling is
  choosing the carrier; and the meaning is still world threading of a
  carrier, because every operation resumes exactly once, in order.
- *What it cannot express:* operations that resume twice or not at all
  under the handler's control (backtracking, generators that suspend).
  Those are §4.3's.
- *Compilation.* Resolved statically, there is nothing to compile: at a
  concrete carrier the operations are ordinary functions (pure, or `Io`
  calls), and specialisation (the code is boxed and intensional, vision
  principle 8) hands the reflector code it already understands. The
  compiler theorem is untouched.
- *Reasoning.* An interface-generic function can be proved about at a pure
  carrier by `refl` and evaluation (§5.2's probes). Transferring a theorem
  from the pure carrier to `Io` needs either the instance-by-instance
  proof or a per-function parametricity theorem
  (`issues/certified-parametricity.md`), §7 question 3.

### 4.3 Interaction-tree signatures and `interp`

An effect is an `Events` signature; a program is a tree over a sum of
signatures; a handler is `interp`, mapping each event of one signature to a
tree over another, and `interp` is a monad morphism, so handler reasoning
is local (Xia et al., "Interaction Trees", POPL 2020, `docs/papers/3371119.pdf`).
Heather has the pieces: `Events::sum`, `run_state` and `run_state_bind`, a
coinductive `CoTree` with `Eutt`.

- *Fit.* The right *semantics* for handlers in general, including the ones
  §4.2 cannot express, and already the semantics underneath `Source`. As
  a *surface* it is layer 1 over a tree carrier, which is fine for library
  code that is about control (a parser, a generator, `Tac`) and wrong for
  ordinary effectful programs (`effects-direction`'s "avoid").
- *Generalising `Io`.* `Io` is the capability of one signature. A
  `Cap<E: Events>` with `world: List<Exchange<E>> → (c: E.Cmd) → E.Resp(c)`
  would make `Io = Cap<Events::linux()>` and give every signature the
  `against`/`Reads`/`reads_bind` kit. Worth doing only when a second
  primitive signature exists (a bare-metal device, WASI); §7 question 5.
- *Compilation.* A tree program compiles when it is a tree over Linux's
  events after handling. Handlers into Linux are fine; handlers that are
  not tail-resumptive need continuations at run time (§4.1's problem).

### 4.4 Linear or unique sub-worlds (Clean, Mercury, Rust)

Clean threads a unique `*World` and lets a program split unique handles out
of it (`fopen` returns a unique `*File` taken from the world, `fclose`
puts it back), so two files are independent values. Mercury threads an
`io` state. Rust's `&mut` gives every mutable place a unique owner.

- *Fit.* Heather is already this at the root (one linear `Io`, uniqueness
  by construction in `ETm`). Splitting the world into per-descriptor
  capabilities was considered and rejected (capabilities design §1, §7.1)
  because it asserts independence that Linux does not guarantee. Clean's
  split is sound for its own model of files as independent values, which
  does not include a terminal echoing one descriptor into another.
- *What survives.* Splitting *authority* without splitting *state*: a
  capability that can only write stdout is an interface (§4.2) whose
  instance at `Io` threads the one world. Uniqueness of *buffers* is a
  fact (`issues/unique-fact.md`), already decided at lowering.

### 4.5 Separation-logic framing

A frame rule: if `{P} c {Q}` and `c` touches nothing `R` mentions, then
`{P ∗ R} c {Q ∗ R}`. For memory, Heather is building this at the machine
level (`issues/wp-view-separating-product.md`, views local to a footprint).
For effects over a history, the analogue is protocols on parts of the
world composed by a separating conjunction, and footprints of functions as
sets of resources (this is the shape of modular ITree reasoning in, e.g.,
Song et al., "Conditional Contextual Refinement", POPL 2023, and of
multi-language linking over events in Sammler et al., "DimSum", POPL 2023).

- *Fit.* The right tool for **reasoning** locality, and only for it: it
  gives no signatures and no handlers. It lives entirely in specs and
  library theorems; the compiler never sees it.
- *Cost.* A footprint predicate, its closure under bind and iteration, a
  separability predicate on worlds, one frame theorem. All library; none
  touches `Source`. The real cost is choosing what a "resource" is when
  descriptors are allocated at run time by `open` (§7 question 4).

### 4.6 Summary

| | Signatures | Local handling | Local reasoning | Compiler proved once |
|---|---|---|---|---|
| Status quo (one `Io`) | no | specs only (worlds) | no frame rule | done |
| Algebraic effects in the language | rows | yes, all handlers | handler laws | new contract (continuations) |
| Capability passing over carriers | class constraints | tail-resumptive | at a pure carrier; transfer open | unchanged (specialise first) |
| ITree signatures + `interp` | `Events` index | all handlers, as trees | `interp` laws | only after handling into Linux |
| Unique sub-worlds | per handle | no | by independence (unsound for Linux) | unchanged |
| Separation framing | no | no | frame theorem | unchanged |

## 5. Recommendation

### 5.1 One world at the bottom

The bottom signature stays Linux's calls, `Io` stays the only capability
`rt` lowers to `Invoke`, and `Io::Reads` stays the one agreement. Every
other effect is either handled into it (§5.2) or stays out of compiled
code (§5.5). This is what keeps "the compiler is proved once" true: the
set of things `Source` and x86 must mean does not grow with the set of
effects users declare.

### 5.2 Effect interfaces over a carrier

An effect a user declares is a class whose members update a carrier, and
an operation is a `mut self` method generic in the carrier:

```heather
class Log<C> { log: C → List<BitVec(8)> → Mutated<C, True> }

fn Log::say<C>(mut self c: C, m: List<BitVec(8)>, d: Log<C> := infer) → True {
    c := d.log(c, m).after;
    trivial
}

// A program that may only log: its type says so.
fn greet<C>(c0: C, d: Log<C> := infer) → C {
    let mut c = c0;
    c := Log::say(c, [b(104), b(105)]).after;
    c := Log::say(c, [b(33)]).after;
    c
}
```

A **handler is an instance**, and handling is choosing the carrier:

```heather
record Collect { lines: List<List<BitVec(8)>> }                    // pure: collect
instance Log<Collect> { log := λ c m => Mutated(Collect(Cons(m, c.lines)), trivial) }

instance Log<Io> { log := λ io m => Mutated(Io::write(io, Io::stderr(), m).after, trivial) }

record Buffered<C> { inner: C, pending: List<BitVec(8)> }          // a wrapper
instance<C> Log<Buffered<C>> { log := λ c m => Mutated(Buffered(c.inner, c.pending ++ m), trivial) }
fn Buffered::flush(self c: Buffered<Io>) → Io { Io::write(c.inner, Io::stderr(), c.pending).after }
```

What the probes (appendix) show, all by `refl`:

- **Pure handling.** `greet(Collect([])).lines` is the two messages; a `for`
  loop generic in the carrier (`greet_n`) runs at `Collect` too. A
  program's logging is tested without a world.
- **The world as a handler.** At `Io`, the calls `greet` makes are exactly
  two writes to stderr, in order, *at a neutral world* (`greet_io_calls`).
  That is a footprint (§5.3) read off the meaning, and it holds because
  the carrier's type admits nothing else.
- **Local handling.** `greet(Buffered(io, [])).flush()` makes one write of
  the three bytes, at any world (`greet_one_write`): a block reinterprets
  its own logging as buffered over the world it was given, which is N3's
  "buffer these writes" with no new language feature.

What it needs:

1. **Dot calls on a carrier variable.** `c.say(m)` on `c: C` is "unbound
   name `say`": member lookup goes by the receiver type's head, and a type
   variable has none. So today the call is written
   `c := Log::say(c, m).after`, and the `mut self` threading that makes the
   `Io` surface pleasant is lost. The fix is a lookup rule: a dot call on a
   receiver whose type is a variable with class constraints in scope finds
   the members owned by those classes (Rust's trait methods on a generic,
   Haskell's class methods). Issue `method-call-on-constrained-carrier`,
   built 2026-11-08: `c.say(m);` now threads `c` through `Log::say`
   (`lib/_tests/lang/constrained_receiver_tests.hthr`).
2. **Several effects.** A function using two interfaces takes *one*
   carrier with both constraints (`d1: Log<C> := infer, d2: Rand<C> :=
   infer`), not two carriers, because two carriers both backed by `Io`
   would hold the world twice, and the reflector rightly refuses a copied
   world. Constraint sets are the effect rows. A carrier providing several
   interfaces is a record of handler states around the world
   (`Buffered<Seeded<Io>>`), each wrapper's instance delegating what it
   does not handle to `inner`. That delegation is boilerplate a deriving
   generator can write (`delegate Log to inner`), not a language feature.
3. **Compilation.** A `runtime fn` that calls `greet` at a concrete
   carrier reflects `greet` specialised (code is boxed and intensional:
   `greet` at `Buffered<Io>` is a term the reflector can unfold). What it
   meets is the world inside a record (`Buffered(io, [])`), which the
   reflector refuses today (capabilities design §5: never stored in a
   record other than `Mutated` and loop state). The fix is to read a
   carrier record as its fields, as pure `rt` already lays records out as
   their fields (setups design §16.7): the world field joins the chain,
   the others are ordinary variables. Linearity is unchanged, because the
   record is not copied either. Issue `reflect-world-in-carrier-record`.
4. **What stays out.** An operation that resumes twice, or that suspends
   and is resumed later, cannot be a `mut self` method. §5.5.

Why not make `Io` itself generic, as `fn cat<W: World>(mut io: W)`? The
capabilities design rejected that (§1: a type parameter on every effectful
signature), and the reason stands for the *primitive* capability: every
program would carry the parameter and gain nothing, since there is one
operating system. For user effects the parameter is the point, so the
recommendation keeps `Io` concrete and makes the interfaces generic. An
interface whose instance at `Io` is a restriction (`class Stdout<C>` with
only `write_out`) gives authority locality over the one world: a function
generic in `Stdout<C>` cannot open a file, though it runs against the
whole `Io`. That is Eio's object-capability discipline, without
splitting the state (§4.4).

### 5.3 Footprints and frames

Two pieces, both library, both in the `linux_world_co` family.

- **Footprint.** `Io::Only(P, f)`: for every world `io` and every
  `Returns(f(io), m)`, `m.past` is some list of new exchanges, each
  satisfying `P`, prepended to `io.past`. Closed under `reads_bind` and
  `Io::iterate` (a footprint of a body is a footprint of its loop). Produced
  three ways, cheapest first (vision §2.3): a verified analysis over `ETm`
  (every `Invoke`'s effect kind and, where its descriptor operand is a
  literal, its descriptor), so a compiled function's footprint costs one
  evaluation; a setup's judgment publishing it as a fact; a user lemma.
  Consumers: specs, and a pass that reorders or merges calls.
- **Separable worlds and the frame theorem.** A partition of commands into
  resources (`key: LinuxCmd → K`); a world is separable at `key` when its
  answer to a command depends only on the history restricted to that
  command's resource. A protocol is a predicate on the world restricted to
  one resource (`Pipe(0, chunks)`, `Sink(1)`), and protocols on disjoint
  resources conjoin. The frame theorem: at a separable world, if
  `Io::Only(key ∈ S, f)`, then `f`'s meaning, restricted to `S`, depends
  only on the world's protocol at `S`. A spec of `cat` then says "given a
  pipe on 0 and a sink on 1, `sent(1) = received(0)`", and composes with a
  spec of a function that writes only fd 2.

Separability is a *hypothesis*: at a terminal world it is false, and the
theorem says nothing there, which is correct.

### 5.4 Lift the composition limits

In order of how much they unblock:

1. **Effectful callees in `rt`** (N6): an `ETm` node calling another
   effectful function, lowered to a `Source` procedure call, sound by
   `reads_bind` and the procedure contract. Without it every effectful
   program is one function, which is the coarsest locality of all.
2. **`EIf` over the world** and **binds in statement arms** (N7), already
   the next R6 slices.
3. **Callbacks that take the carrier** (N5): a higher-order function whose
   callback is `C → A → Mutated<C, B>` (the world passed in and out, never
   captured). The surface refusal stays for a λ that captures the outer
   world; the generic `for_each<C>` over a carrier is the replacement, and
   it is §5.2's interface style applied to iteration.

### 5.5 Control effects are libraries

Generators, coroutines, backtracking search, async I/O and anything that
resumes zero or many times are trees with handlers, written in layer 1 over
a tree carrier, exactly as `Tac` is. They are compiled, when someone needs
them at run time, by their own `Compile` instances: a generator as a state
machine, a backtracking search as a loop over an explicit stack, async as
an event loop over `epoll`. Each such compiler is a DSL in vision §2.2's
sense, proved once for its own terms, and none of them asks `Source` for
continuations.

### 5.6 Restricted APIs are the default (Minus, 2026-11-08)

Minus, on this note: *"I agree that we need some notion of `Io`, in a sense
we're always running on a global system. But ideally everything should go
through smaller restricted APIs, this is better for understanding and for
optimization and so on. This probably still needs `Io` in some sense though
it'd be neat if it could be guaranteed that you aren't touching it."*

So the direction is §5.2 as the *default style*, not an option: `Io` is
named only at the top (`main`) and inside the instances that implement the
small interfaces over it; everything else is written against interfaces.
"Guaranteed you aren't touching it" then comes in three strengths, each
already within reach:

1. **By typing, for free.** A function with no carrier parameter is pure: it
   cannot reach `Io` at all. A function generic in `C` with only
   `Stdout<C>` cannot call `open` on its carrier, because `C` is abstract
   and no member of `Io` applies to it. The checker enforces this today
   (the generic `greet` cannot be written to read). What it does not stop
   is a *concrete* restricted wrapper (`record StdoutCap { io: Io }`) whose
   field a caller projects out: Heather has no private fields, so a
   restricted API must be a class over an abstract carrier, not a record
   around `Io`. (An `interface fn` opaque constructor is the other route,
   if a concrete type is ever wanted.)
2. **By the meaning, per instance.** At the `Io` instance, `Io::Only(P, f)`
   (§5.3) states the semantic guarantee: every exchange the run adds is a
   write to stdout. For a compiled function it is one evaluation of the
   footprint analysis over `ETm`.
3. **For every instance at once.** That `f` generic in `Stdout<C>` has
   footprint "stdout writes" at *every* carrier is a free theorem; per
   function it comes from certified parametricity
   (`issues/certified-parametricity.md`), §7 question 3.

For optimization, the interface is the footprint: a pass that wants to
reorder or merge two calls asks for their `Io::Only` facts, and a function
written against `Stdout<C>` publishes the narrowest one by construction.
The issue owning the library of interfaces
(`effect-interfaces-over-carriers`) should therefore aim at the standard
set an ordinary program uses (byte sinks and sources per descriptor, a
file-system interface, arguments, exit status), with `Io` itself reserved
for `main` and for the instances.

## 6. Fit with proving the compiler once

| Piece | Below `rt` | In `rt`/reflector | Library only |
|---|---|---|---|
| One world at the bottom | unchanged | unchanged | — |
| Effect interfaces | unchanged | specialise at the carrier; flatten carrier records holding the world | classes, instances |
| Footprints and frames | unchanged | an analysis over `ETm` (optional producer) | `Io::Only`, separability, frame theorem |
| Effectful callees | `Source` procedures (exist) | an `ETm` call node + its case in `lower_sound` | — |
| Control effects | unchanged | unchanged | trees, handlers, DSL compilers |

Nothing in the recommendation adds a construct to `Source` or the x86
level. The compiler-side work is in the reflector and in one `ETm` node,
each with its case of a soundness proof that is already by induction over
`ETm`.

## 7. Open questions for Minus

1. **Which complaint is it?** Signatures, handling, or reasoning (the
   introduction's three). The note addresses all three; the order of the
   issues in §8 assumes signatures and composition first, frames second.
2. **Class-generic carriers for user effects.** *Answered (Minus,
   2026-11-08, §5.6):* restricted APIs are the default, with `Io` at the
   top and in the instances. Capabilities design §1's rejection of a
   class-generic world stands for `Io` itself.
3. **Moving theorems between carriers.** `greet` proved at the pure
   carrier says nothing about `greet` at `Io` without either a second proof
   or a free theorem. Per-function parametricity
   (`issues/certified-parametricity.md`) would generate it from the body;
   is that the route, or is instance-by-instance proof acceptable?
   *Answered (Minus, 2026-11-08):* parametricity, proved within the
   language. Not a metatheorem for every definition, since code at layer m
   can observe code; a per-function certificate for the carrier-shaped
   fragment (`issues/carrier-parametricity.md`).
4. **What is a resource?** Descriptors 0/1/2 are static; descriptors from
   `open` are run-time values, and paths alias (two opens of one file).
   Start with the standard descriptors and paths as resources, descriptors
   bound to paths through the history?
5. **`Cap<E>` over any signature.** Generalise `Io` now, or when a second
   primitive signature exists?
6. **Run-time continuations, ever?** Async I/O over one thread and
   coroutines are the customers that would ask for them. If they are wanted
   on the native path, it is a `Source`/x86 contract (stack switching)
   proved once, and it should be a design round of its own.

## 8. Issues

Filed with this note:

- `effect-interfaces-over-carriers`: user effects as classes over a
  `mut self` carrier, pure and `Io` handlers, the surface for them (§5.2).
- `reflect-world-in-carrier-record`: the reflector and lowering accept a
  carrier record holding the world, flattened, so a specialised
  interface-generic `runtime fn` compiles (§5.2, §6).
- `io-footprint-facts`: `Io::Only`, its closure lemmas, and the analysis
  over `ETm` that produces it (§5.3).
- `world-separable-frame`: resources, separable worlds, protocols, and the
  frame theorem (§5.3).
- `rt-effectful-callees`: an `ETm` call of an effectful function, lowered to
  a `Source` procedure (§5.4, N6).
- `carrier-parametricity` (added after Minus's answer to §7 question 3):
  the free theorem of a function generic in an effect carrier, generated
  and checked in the language.
- `method-call-on-constrained-carrier`: dot calls on a receiver whose type
  is a constrained type variable find the constraining classes' members
  (§5.2 item 1).

## Appendix: the probe

Run on `a6d30ca` with `heather check -L lib`: every declaration checks.
The same file with `c.say(m)` in place of `c := Log::say(c, m).after` is
refused with "unbound name `say`" (§5.2 item 1). The imports are `logic`,
`nat`, `list`, `option`, `bool`, `bitvec`, `itree`, `linux_calls`,
`linux_trees` and `linux_world`.

```heather
fn b(n: Nat) → BitVec(8) { BitVec::ofNat(n) }

class Log<C> { log: C → List<BitVec(8)> → Mutated<C, True> }

record Collect { lines: List<List<BitVec(8)>> }
instance Log<Collect> { log := λ c m => Mutated(Collect(Cons(m, c.lines)), trivial) }
instance Log<Io> { log := λ io m => Mutated(Io::write(io, Io::stderr(), m).after, trivial) }
record Buffered<C> { inner: C, pending: List<BitVec(8)> }
instance<C> Log<Buffered<C>> { log := λ c m => Mutated(Buffered(c.inner, c.pending ++ m), trivial) }

fn Log::say<C>(mut self c: C, m: List<BitVec(8)>, d: Log<C> := infer) → True {
    c := d.log(c, m).after;
    trivial
}

fn greet<C>(c0: C, d: Log<C> := infer) → C {
    let mut c = c0;
    c := Log::say(c, [b(104), b(105)]).after;
    c := Log::say(c, [b(33)]).after;
    c
}

theorem greet_collect(): greet(Collect([])).lines = [[b(33)], [b(104), b(105)]] { refl }
theorem greet_io(): Io::sent(greet(Io::of(World::piped([]))), Io::stderr()) = [b(104), b(105), b(33)] { refl }
theorem greet_buffered(): greet(Buffered(Collect([]), [])).pending = [b(104), b(105), b(33)] { refl }

fn greet_n<C>(c0: C, n: Nat, d: Log<C> := infer) → C {
    let mut c = c0;
    for i in 0..n { c := Log::say(c, [b(46)]).after; }
    c
}
theorem greet_n_collect(): greet_n(Collect([]), 3).lines.len() = 3 { refl }

fn cmds(io: Io) → List<LinuxCmd<Nat>> { io.past.map(λ (e: Exchange) => e.cmd) }
theorem greet_io_calls(w: World()):
    cmds(greet(Io::of(w))) = [WriteCmd(Io::stderr(), [b(33)]), WriteCmd(Io::stderr(), [b(104), b(105)])] { refl }

fn Buffered::flush(self c: Buffered<Io>) → Io { Io::write(c.inner, Io::stderr(), c.pending).after }
fn greet_buffered_io(io: Io) → Io { greet(Buffered(io, [])).flush() }
theorem greet_one_write(w: World()):
    cmds(greet_buffered_io(Io::of(w))) = [WriteCmd(Io::stderr(), [b(104), b(105), b(33)])] { refl }
```

`greet_io` is at a piped world rather than a neutral one: `Io::sent` reads
the bytes a write's *answer* says were taken, and a neutral world may take
part of a write. The call list (`greet_io_calls`) holds at every world.
