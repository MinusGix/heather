# Effects as capabilities: `Io`, `mut self`, and the tree reading

Status: **built, first slice (2026-11-02)**, the first round of
`effects-uniqueness-surface` (R6 of `docs/native/compiler-milestones-proposal.md`,
milestone `nh-effects`). It extends `docs/language/sequencing-surface-design.md` §8
(effects are layer 2 with `mut self`) and `docs/native/runtime-fn-setups-design.md`
§6.1 and §8 (the setup's `sound` proves the effectful agreement once). Read
`docs/compilation-vision.md` first. Where this design is coarse (one
capability for every effect, no local handlers, no frame rule) and what to
build on it is assessed in `docs/language/effects-locality-design.md` (2026-11-08).

## 0. In one page

```heather
fn Io::cat(io: Io, capacity: Nat) → Partial(Mutated<Io, BitVec(64)>) {
    let mut io = io;
    let mut status: BitVec(64) = BitVec::ofNat(0);
    let mut left: List<BitVec(8)> = [];
    let mut going = True;
    while going {
        if left.len() = 0 {
            let r = io.read(Io::stdin(), capacity);
            match r {
                ReadFailed(_) => { status := BitVec::ofNat(1); going := False },
                ReadBytes(bytes) => { if bytes.len() = 0 { going := False } else { left := bytes } },
            }
        } else {
            let w = io.write(Io::stdout(), left);
            match w {
                Wrote(n) => { left := left.drop(n) },
                WriteFailed(_) => { status := BitVec::ofNat(1); going := False },
            }
        }
    }
    Pointed::ret(Mutated(io, status))
}
```

That is GNU `cat` with no arguments, in ordinary Heather. It is pure:

- `io` is a capability, a value of the record `Io`;
- `io.read(fd, n)` is a call of a `mut self` method, whose kernel type is
  `Io → BitVec(64) → Nat → Mutated<Io, ReadResult>`;
- on a `let mut` local or `mut` parameter, the call binds the answer and
  rebinds `io` to the world after it (SSA, §5.1 of the sequencing design).

Nobody writes a monad, and the meaning is world threading. The loop goes
round until the input ends, so it has no bound: it is a `while` with no
measure, and the function means `Io → Partial(Mutated<Io, R>)`, the world
threaded over the delay monad (§4). Until 2026-11-04 it took a `passes`
list that bounded the loop; that is gone.

Three pieces make that work, all built in this round:

1. **The capability** (`lib/std/os/linux/linux_world.hthr`, §1). An `Io` is
   a *world* and the *exchanges so far*. The world is a function from the
   history to the answer to the next call.
2. **`mut self` methods** (§2). A general language feature, not an effects
   one: the parser and the elaborator lower it, and the kernel learns
   nothing.
3. **The tree reading** (§3). `Io::against(t, io)` reads a tree over
   Linux's calls against a world. `Io::Reads(t, f)` says the coinductive
   reading (`Io::against_co`) is `f` up to taus at every world (§4), and
   `Io::reads_bind` and `Io::reads_iter` are sequencing's and the loop's
   cases, proved once.
   It is the statement a `runtime fn` setup's `sound` will prove for every
   program.

The probe that ties them together:

```heather
theorem cat_agrees_piped():
    Eutt<Mutated<Io, BitVec(64)>>(Events::none(), Io::against_co(cat(256).tree_co([]), piped()), Io::cat(piped(), 256))
{
    ERet(30, 20, cat_piped_end(), refl, refl)
}
```

Here `native_cat`'s `cat` is the hand-built `Source` that `write-elf`
compiles, read with no fuel (`Source::tree_co`, §4). Read against the same
world, it makes the same calls as the surface program, gets the same
answers, in the same order, and exits with the same status: the two
readings return the same `Mutated` value, history and all, so they are
equivalent up to silent steps. That is `Io::Reads` at one world.

## 1. The capability

```heather
record Exchange { cmd: LinuxCmd<Nat>, answer: cmd.Resp() }
fn World() → Type { List<Exchange> → (c: LinuxCmd<Nat>) → c.Resp() }
record Io { world: World(), past: List<Exchange> }

fn Io::call(mut self io: Io, c: LinuxCmd<Nat>) → c.Resp() {
    let a = io.world(io.past, c);
    io := Io(io.world, Cons(Exchange(c, a), io.past));
    a
}
```

`read`, `write`, `open`, `close` and `stat` are one `call` each, and
`write_all` (`linux_world_co`) loops over `write` until every byte is sent,
a computation in `Partial` (§4.1).

**Why one world, not `uniq Fd` per descriptor.** Linux's answers on
different descriptors are not independent. A terminal echoes what is
written to it into what is read back, and a pipe's reader waits on its
writer. If each descriptor carried its own state, the pure meaning could not
see that writes and reads interleave, and agreement with every environment
would fail. So the capability is the one world (Clean's `*World`), and a
descriptor is a word. Buffers are byte lists, which are values. That a
buffer is not aliased, so a read may land in place, is a fact for the
compiler (the `Unique` fact, `docs/native/facts-on-demand-design.md` §7), not a
type.

**Why a function of the history.** A world answers each call from every
exchange before it, so it is every deterministic environment there is: a
file that grows, a disk that fails on the third write, a terminal. Linux's
nondeterminism (which chunk a read returns, how much of a write goes) is
quantification over worlds: a statement "for every `io`" covers every
answer Linux may give. Two alternatives were tried and rejected:

- **A codata world** (`codata World { Answers(answer, next) }`) is equally
  general. But a program's history is then hidden inside the world, so a
  theorem cannot say what the program wrote.
- **A class-generic world** (`fn cat<W: World>(mut io: W)`) puts a type
  parameter and a constraint on every effectful signature.

The history is a list newest first, so `Io::sent(io, fd)`, the bytes written
to `fd` in order, is how a spec states output. At run time the capability is
nothing: the compiled program performs the calls, and the history is only
the meaning. A setup lays `Io` out as no words (§5).

**Scripted worlds.** `World::piped(chunks)` answers the k-th read with the
k-th chunk, cut to the size asked for, and takes every write whole. That is
a test's pipe and terminal. Every probe in
`lib/_tests/std/os/linux/linux_world_tests.hthr` runs by `refl` at such a
world, and some run at a neutral one.

## 2. `mut self` methods

### 2.1 Declaring

`fn T::m(mut self x: T, …) → R { body }` is lowered as follows:

- by the parser, to a function with result `Mutated<T, R>`, a prelude
  record `{ after: T, value: R }`;
- its body becomes `{ let mut x = x; body′; Mutated(x, value) }`;
- a body ending in a statement has value `trivial`, for a method returning
  `True`.

A plain `mut x: T` parameter is only the leading `let mut x = x;`: a local
copy, with the result unchanged. That is what `main(mut io: Io)` will want.

The refusals are named at parse time:

- a `mut` parameter of a theorem;
- an implicit `mut` parameter.

`return e` in a `mut self` body (built 2026-11-02,
`issues/mut-self-early-return.md`) returns `Mutated(x, e)` over the
receiver as the body has threaded it to the `return`: the parser wraps each
loop `Return` leaf after lowering the body (sequencing design §15.7). It is
allowed exactly where pure code allows `return`.

### 2.2 Calling

The parser cannot tell whether `x.m(a)` updates `x`: that needs `m`'s type.
So the lowering is split the way loops are:

- **The parser marks candidates.** It tracks the `let mut` locals and `mut`
  parameters in lexical scope. A method call on one of them, written as
  `let p = x.m(a);`, as the statement `x.m(a);`, or as a block's result
  `{ …; x.m(a) }`, becomes `\0mutcall(x.m(a))`.
- **The declaring block claims them** (`crates/syntax/src/imperative.rs`).
  A block that declared `x` turns the marker into `\0mutated(…)`. Joins and
  loops count `x` as assigned there, so a statement `if` joins it and a
  `for` makes it loop state.
- **The elaborator decides by type** (`crates/elab/src/statements.rs`,
  `elaborate_mut_call`). If the call's type is the `Mutated` record, `p`
  becomes an alias of `.value` and `x` an alias of `.after`, both
  projections of the one call. If it is not, the call is an ordinary `let`.

`let` is an elaborator alias, not a kernel binder, so either way the kernel
term is what a hand-written `let m = T::m(x, a); …m.after…m.value` would
give.

**The cost of deciding late.** A method call on a mutable local threads the
local whether or not the method updates it. A `for` body that only reads
`xs.len()` on a `let mut xs` makes `xs` loop state, and a statement `if`
joins it. The meaning is the same, and the step function carries one more
field. `let mut` appears only in tests today, so nothing in the library
moved.

**Refused, with reasons** (probes in the `linux_world` and
`imperative_statements` test modules):

- the statement `x.m(a);` where `m` does not update `x`: "this statement
  discards its value";
- a `mut self` call on an outer `let mut` reached through a λ: the λ cannot
  update it;
- a dot call of a `mut self` method anywhere the statements above do not
  thread it: on a local that is not mutable (`let p = y.m(a);` with a plain
  `let y`), or on a `let mut` local inside a larger expression
  (`f(x.m(a))`). It would give the `Mutated` record where the answer was
  meant and leave the receiver unchanged, so it is refused at the call:
  "nothing here keeps the update". The test is on the dot-call path
  (`refuse_unthreaded_mut_call`, `crates/elab/src/dispatch/member.rs`),
  which is hot, so it reads the callee's *written* result head, one surface
  lookup and no reduction; the candidate `elaborate_mut_call` is inferring
  is let through by its span (`DynamicScope::mut_call_site`). A method whose
  written result is `Mutated<…>` by hand is refused the same way: that is
  the same convention, decided by the same type. The qualified call
  `T::m(y, a)` is the record, as before.

An annotated `let p: T = x.m(a);` is a candidate like the unannotated one.
The declaring block binds the call to a private `#mutcallN` and the
annotated `let` reads it, so the annotation is held to the answer, not the
record.

## 3. The tree reading, and agreement once

```heather
fn Io::against<R>(t: ITree<R>(Events::linux()), io: Io) → Option<Mutated<Io, R>>
fn Io::Reads<R>(t, f: Io → Mutated<Io, R>) → Type { (io: Io) → Io::against(t, io) = Some(f(io)) }
theorem Io::reads_bind(…, rt: Io::Reads(t, f), rh: (a) → Io::Reads(h(a), g(a))):
    Io::Reads(ITree::bind(Events::linux(), t, h), λ io => g(f(io).value, f(io).after))
```

`against` is this handler's `run_state`. Each `Vis` is answered by the
world, and the history grows. `against_bind` is `run_state_bind`'s statement
at this handler, and it holds as an *equation*, not a bisimilarity, because
`against` erases `Tau`. `reads_bind`, with `reads_trigger` and `reads_ret`,
is the construct-by-construct agreement the issue asks for: "the pure
reading users reason with agrees with `denote` construct by construct,
proved once".

*Since 2026-11-03 (§4)* this finite `Reads` is restated: `Io::Reads(t, f)`
takes a `CoTree` and `f: Io → Partial<Mutated<Io, R>>`, and is `Eutt` of
`Io::against_co(t, io)` and `f(io)` at every world. `Io::against` and
`against_bind` stay as above for fuelled probes, and `Io::against_returns`
turns a fuelled `Some(m)` into a `Returns` of the embedded tree.

**Where it goes.** For effectful code, the setup design's `sound`
(`docs/native/runtime-fn-setups-design.md` §6.1) states
`Implements(c.denote(args), p.tree(args))`. With capabilities it is
`Io::Reads(c.denote(args), λ io => f(io, args))`. Every `Invoke` lowers to
a `Vis` and reads as `Io::call`. Every pure run reads as `Ret` of its
meaning. Sequencing is `reads_bind`, and loops are the next lemma (§4).

## 4. Loops and fuel

**Until 2026-11-04.** A source's `Repeat` was `ITree::iter` at fuel `n`,
which is cut after `n` passes, and a surface loop over a world was a `for`
over a list of `passes`, which runs at most `passes.len()` times. They
agreed whenever the tree was not cut: `cat_agrees_piped` was at fuel 4
against a world of three reads. §4.1 is what replaced it.

**Why that has to go** (`issues/effectful-loops-without-passes.md`). The
bound is real: a world is any function of the history, so "read until the
input ends" diverges for some worlds (`yes | tac`), and a total `fn` cannot
mean it. But `passes` puts that partiality in the worst place:

- running out reads as an outcome the binary never has: `Io::cat` returns
  status 0 when its outer `passes` run out, `tac` and `sort` write a
  truncated read as the whole input, and `write_bytes` reports a failure,
  where the tree is `Cut` and claims nothing;
- it is a ghost value posing as an argument: the compiled loop has no
  counter, so `runtime fn main` could only supply it by counting (not GNU's
  behaviour) or ignoring it (a signature that lies). `while … fuel` compiles
  to a counting loop for the same reason, so it is not the answer for loops
  over a world;
- `Io::Reads` is an equality at every world, and a loop tree at a fixed
  fuel is `Cut` (read as `None`) at some of them, so no loop lemma of that
  shape exists.

**Decided (Minus, 2026-11-03): the meaning is coinductive, and agreement is
up to taus.** A function whose body has a loop over a world with no measure
means `Io → Partial<Mutated<Io, R>>`, the world threaded over the delay
monad (`Partial<B> = CoTree<B>(Events::none())`,
`docs/language/partial-functions-design.md` §4.1; its §4.4 is this case). The world
answers every call, so the only coinductive structure left is silent steps.
That is the `runtime fn` setup's one piece of magic: the return type is
wrapped, and the elaborator's `mut self` threading becomes a bind in the
`Partial` carrier. A loop with no measure is allowed in any carrier that has
an iteration operator.

- **Agreement.** `Io::against` gets a corecursive form that reads a
  `CoTree` over Linux's events into `Partial<Mutated<Io, R>>`, and
  `Io::Reads` becomes "`Eutt` at every world". `reads_bind` and the loop
  lemma are restated up to `Eutt` and proved once. A lowering with one `Tau`
  per pass on both sides (lockstep) is a fast path that a tactic proves by
  induction on depth; it is not required, because compiler passes that
  change how often a loop goes round preserve `Eutt` and not lockstep.
  **Built (2026-11-03)**, in `linux_world_co.hthr`: `Io::against_co`, `Io::Reads` as `Eutt` at every
  world (the finite `Reads` and its lemmas are gone; `Io::against` stays
  for fuelled probes, and `Io::against_returns` turns one into a `Returns`
  of the embedded tree), `reads_ret`/`reads_trigger`/`reads_bind`, and the
  loop lemma `Io::reads_iter`: a body that reads as `step` gives a loop that
  reads as `Io::iterate(step)`, `CoTree::iter` in `Partial` over the state
  `Mutated<Io, A>`. All by direct corecursion (`docs/itrees/coitree-design.md`
  §7.9); a fuel-free cat reads to a `Returns` at count 7 at the piped world
  by `refl` (`linux_world_tests.hthr`).
- **What specs see.** `Returns(f(io), m) → P(m)` (fixpoint induction), a
  `Returns` with a count at a scripted world by `refl` (today's probes keep
  their number as the count), and divergence over every count. All of these
  are invariant under `Eutt`, so it shows up only in "program ≈ program"
  statements.
- **Diverging runs.** `Partial` forgets what a run that never returns wrote.
  Reactive specs (`yes`, a server, `cat` on a terminal) are stated on the
  tree over Linux's events, where writes are visible and `Eutt::traces`
  carries them.
- **Rejected:** a budget in `Io` (CakeML's clock in the state: honest, and
  no codata, but `Io` changes shape for every customer and results are junk
  when exhausted; it survives as the observation of `Partial` at a count);
  `while … fuel` (above); a finite-input world (rules out terminals and the
  most-general `World()`); an interaction tree as the surface meaning (keeps
  traces, but drops world threading from user code).

The work, in `issues/`: `partial-fn-surface`, `eutt-iteration-and-io-reading`,
`codata-up-to-friends-round-2` (up-to proofs), `eutt-setoid-rewrite` and
`eutt-tactics`; then `effectful-loops-without-passes` moves the customers.

### 4.1 The customers moved (2026-11-04)

`issues/effectful-loops-without-passes.md`, milestone `it-world-loops`.

- **A `Source` with no fuel** (`lib/native/native_source_co.hthr`).
  `Stmt::denote_co` reads a `Repeat` as `CoTree::iter`; procedures still
  nest to the source's depth (one call past it exits 139), so depth is
  counted but no fuel is. `Source::tree_co(args)` is the program's tree.
  It is a function of the environment (`Env → CoTree<Flow>`) so that its
  recursion is on the statement: a function whose result is codata is read
  as corecursive.
- **The bridge** is `Program::Refines` both ways, so the fuelled program
  and the fuel-free tree are the same program. `Source::tree_co_refines`:
  every trace `src.denote(args)` produces at some fuel, `src.tree_co(args)`
  produces at some depth. That is the direction a compiled program's
  theorem travels: its ELF refines the fuelled program, so it refines the
  fuel-free one. `Source::tree_co_refined` is the converse, which moves a
  spec proved on the fuelled side over. Both go construct by construct
  (`coitree_bridge`), over `ITree::Into(t, c)` (a finite tree's traces are
  the coinductive one's) and `CoTree::Onto(c, p)` (the coinductive tree's
  are a growing family's). A bind's trace is split (`IsTrace::split_bind`,
  the converse of `IsTrace::bind`, in `itree_trace`) and each part found
  at its own depth or fuel, then raised to their sum. A loop is
  `CoTree::iter_refined`/`iter_refines` generalised to a body that is
  itself a denotation (`ITree::into_iter`, by induction on the fuel;
  `CoTree::onto_iter`, by induction on the depth), so a `Repeat` inside a
  `Repeat`, sharing the source's one fuel, is covered.
- **The programs.** `Io::write_all` (`linux_world_co`), `Io::tac`,
  `Io::sort`, `Io::read_lines` and `Io::write_lines` (`line_tools`), and
  the test module's `Io::cat` take no `passes` and mean
  `Io → Partial(Mutated<Io, R>)`, written with `while` and no measure. Two
  limits of that `while` shape them (sequencing design §18, item 6): it has
  no `break`, so a loop stops by a `going` flag; and a bind inside a
  statement arm of its body is not lowered, so one loop cannot call
  another. So `cat` is one loop that holds what is left to write of the last
  read (read when nothing is left, otherwise write), `tac` and `sort` read
  in one loop and write in another, sequenced by binds at the top of the
  block, and `sort` orders its lines first (`List::sorted_out`, a pure walk
  per line that conses the greatest first) and then writes them.
- **The probes** state the same things as before, as a `Returns` at a count
  of silent steps; a negative control at a count too small; and a world
  whose input never ends (`yes | tac`), where no count settles.
- **The agreements.** `cat_agrees_piped` and `cat_agrees_failing` state
  `Eutt` between the source's fuel-free reading and the surface cat at a
  world, by the two counts and the end both reach (`ERet`), which is
  `Io::Reads` at that world. At every world it is R6 item 2 (§6).


## 5. Uniqueness is the setup's judgment

The elaborator checks nothing about linearity (sequencing design §8.3). In
this surface, using a capability linearly is mostly guaranteed by
construction:

- a claimed call rebinds the local, so the old version has no name;
- a `mut self` method returns its receiver.

What the surface does not stop is a copy. With `let io2 = io;`, both
versions reach later calls, and the pure meaning then forks the world: two
histories from one point. That is a fine function, but no machine does it.
So the default setup's capability-linearity clause
(`docs/native/runtime-fn-setups-design.md` §5.1) refuses it over reflected `rt`:

- each version of an `Io` is used exactly once;
- it is never stored in a record (other than the `Mutated` a `mut self`
  method returns, and loop state), a closure or a buffer.

A function that is never compiled may copy a world, which is useful in
specs ("had the program read instead…").

## 6. What R6 still needs

In order:

1. **`rt` capability types and an `Invoke` node** (setups design §8, N3).
   *Built as a computation layer, not a `Ty` (§8):* `ETm` with `Invoke`
   over pure `Tm`, in `lib/native/runtime/rt_io.hthr`, and the reflector
   reading an `io`-threading body into `Invoke`s
   (`lib/native/runtime/rt_io_reflect.hthr`, §8.3, slice 3).
2. **`rt` to `Source`.** Runs of pure statements become `Compute` leaves
   through N1's lowering, `Invoke`s become `Invoke` statements, and loops
   holding `Invoke`s become `Repeat`. `sound` is `Io::Reads` of the
   source's tree against the reflected meaning, by `reads_bind` and the loop
   lemma. *Built for computations with no loop (§8.5, slice 4):*
   `ETm::lower` in `lib/native/runtime/rt_io_lower.hthr` and
   `ETm::lower_reads`, `Io::Reads` of the lowered tree against `ETm::sem`.
   *Loops built (§8.6, slice 5):* `ELoop` in
   `lib/native/runtime/rt_io_loop.hthr`, lowered to `Repeat`, with
   `ELoop::lower_reads`. Branches over the world remain (§8.4).
3. **Linearity** as a clause of the default judgment (§5). *Built with
   the reflector (§8.3):* no `ETm` names the world, so the clause is the
   reflector's refusals at the call.
4. **`runtime fn main(mut io: Io, args: Args) → BitVec(64)`** publishing a
   `Source` that `write-elf` compiles as it compiles a builder tool today.
   This needs byte and string literals in programs and implicit compiler
   imports for program files. *Designed (2026-11-15, proposed):*
   `docs/native/io-programs-design.md`, the reflector's loops, the bridge
   from the surface `while` to `ELoop::sem`, the generator's program group
   and `write-elf` by path.
5. **The customers.** `cat FILE…`, `wc` and `head -n` are rewritten as
   `runtime fn`s over `Io`, pass the same GNU tests, and their builder
   versions are deleted.

`Io::cat` above is item 5's first program, already checked against the
builder-era source at a world.

## 7. Decisions for Minus

These were taken in the round and are recorded here so they can be
reversed:

1. **One world capability, with a history** (§1), over `uniq Fd` per
   descriptor, a codata world, or a class-generic world. *Taken: one
   `Io`.*
2. **`mut self` returns a prelude record `Mutated<S, R>`** rather than
   `Pair`. The record keeps the call's mutability visible in its type, so
   the elaborator decides by type and no flag goes into the module image.
   *Taken.*
3. **A method call on a mutable local threads it even when the method turns
   out not to update** (§2.2). The alternative is a call-site marker
   (`io.read!(…)`), which the sequencing design ruled out for readability.
   *Taken: implicit, as designed.*
4. **The capability is the world a computation layer threads, not an `rt`
   type** (§8.1), against setups design §8's "rt gains capability types".
   *Taken: linearity by construction.*
5. **Loops over a world mean `Io → Partial<Mutated<Io, R>>`, agreement is up
   to taus** (§4), over a budget in `Io`, `while … fuel`, or a finite-input
   world. *Decided by Minus, 2026-11-03.*

## 8. Capabilities in `rt`: the computation layer

`lib/native/runtime/rt_io.hthr`, probes in
`lib/_tests/native/runtime/rt_io_tests.hthr`.

### 8.1 Why a layer and not a type

Setups design §8 had `rt` gain capability types: `Io` a `Ty`, laid out as
no words, with a linearity judgment refusing a term that copies or drops
one. That judgment is a second type system inside the reflector's output,
and every pure `Tm` former (`Let`, records, `If`) would need a rule for it.

The layer instead follows the source's own split
(`docs/native/native-effect-source-design.md` §11) and call-by-push-value: values
are pure `Tm`, unchanged; computations are `ETm`:

- `Pure(t)`: return a value, world unchanged;
- `Let(e, body)`: bind a pure value;
- `Invoke(e, args, body)`: one call to Linux on variables, its results
  bound in order for `body`.

`ETm::sem(w)(g)(env)` is `Io → Mutated<Io, R>`: the world is threaded by
the meaning, never named by a term. No `ETm` can copy, store or drop the
capability, so N3 (setups design §5.1) holds by construction and the
default judgment needs no linearity clause; item 3 of §6 becomes the
reflector refusing a body that does not thread `io` straight through.

### 8.2 Effects are word-level calls

`Effect` is `Reads(cap)`, `Writes(cap)`, `Opens(cap)`, `Closes`, each with
operand and result codes (`Effect::params`, `Effect::results`) in `rt`'s
`Ty`: words and `Bytes(cap)` buffers, as `Source`'s `CallShape`s are. A
read lands its bytes in a named buffer (`fill`) and returns a count or a
negated errno; a write names a span. `Effect::sem` is *defined by* the
word-level `mut self` methods effectful code calls (`Io::read_into`,
`Io::write_from`, `Io::open_path`, `Io::close_fd`), so a pin unfolds onto
the elaborated body node for node: `echo_reflects`, an `EFun` against the
surface `Io::echo_once`, holds by `refl`, and a stale-buffer variant is
refused by the kernel (the negative control).

### 8.3 The reflector

*Built (2026-11-04, slice 3):* `lib/native/runtime/rt_io_reflect.hthr`,
`reflects_io_as` in `lib/_tests/native/runtime/rt_io_tests.hthr`.

The surface body is a chain of `Mutated` lets: each `io.m(…)` elaborates to
`let p = m(io_k, …); io_{k+1} = p.after; … p.value …`. The reflector:

1. walks the `.after` chain from the result back to the `io` parameter,
   which gives the call order;
2. refuses a call whose world is not the chain's current one (a stale or
   copied `io`), and any use of an `io_k` other than as the next call's
   world — this is the linearity check, located at the call;
3. reads each call's operands as pure `Tm`s (the existing value-numbering
   reflector) and binds them with `Let`s before the `Invoke`;
4. maps `.value` projections (`p.value.buf`, `p.value.result`) to the
   `Invoke`-bound variables, keying repeated occurrences of one call by its
   reflected operand levels, as pure `rt` keys repeated subterms.

What the build found and decided:

- **The calls are shared.** `elaborate_mut_call` binds one call and
  projects both `.after` and `.value` from it, so `Body` hands out one
  handle per call wherever the body reads it (unlike pure lets,
  `issues/elaborated-let-sharing-lost.md`). The reflector keys answers on
  that handle. A copy that is not the same handle is placed by its world's
  position on the chain and confirmed by `Defeq` against the call recorded
  there, rather than by operand levels: literals are not value-numbered, so
  re-reflecting a copy's operands would bind them again.
- **Where it lives.** The walk is `rt_reflect`'s, with `Known` gaining an
  optional `IoKnown` (the world's local, the methods, the calls made so
  far). With it, a field read of a call's answer is the variable its
  `Invoke` bound (`rt_read`), and the world is never a value. Without it,
  pure reflection is unchanged. `rt_io_reflect` drives the order: operands,
  their `Let`s, the `Invoke`, and the answer recorded for what follows.
- **Named constants.** `Io::stdin()` is a global with no parameters whose
  body is a word literal; the reflector reads such a global as its literal
  (its δ-reduct), in pure code too. Any other global still has to be a
  function of the program.
- **Refusals** (step 2, each probed with `expect-error`): the world read as
  a value, whole or a field of it; the world after a call read as a value;
  an answer of a call the chain does not go through, whether from a copy
  of `io` (`let mut old = io; … old.m(…)`) or from a qualified call whose
  world after is dropped; a call on a method the reflector does not know
  (`Io::read`, whose answer has no word-level code); a world through a
  branch (§8.4). A copy whose call is the chain's call, same operands, is
  the same call and reflects as it: the meaning of reading it twice is
  reading it once.
- **Not refused:** a call whose world and answer are both dropped. It is
  not in the elaborated term at all, so it is not in the meaning either,
  and the reflection agrees with the meaning; the program just does not
  make the call the source wrote. A lint belongs at the elaborator
  (an unused `let mut` world), not here.

### 8.4 Known limits

- **Branching over the world.** A statement `if` that calls on `io` in a
  branch joins per variable (`imperative.rs`), so the elaborated body
  projects `io` and each other variable out of the branch's tuple. An
  `EIf(c, a, b)` whose meaning branches on the whole `Mutated` needs a
  commuting conversion to agree with that by `refl`; either the lowering
  joins the world with the values or the pin goes through an equation.
- **Loops.** *Built as `ELoop` (§8.6).* A `for` over a list is not yet a
  loop form; a `while` with no measure is.
- **Callees.** An effectful callee (`EFun` calling `EFun`) is not modelled;
  `ETm::plain_world()` is the world with no callees.

### 8.5 Lowering to a `Source` (slice 4)

`ETm::lower(w, g, locs, next)` (`lib/native/runtime/rt_io_lower.hthr`)
turns a computation into `Source` statements: each pure value (a `Pure`, a
`Let`'s bound term) is the pure lowering's region (`Tm::lower`) followed by
a move of its one result port to a fresh word, each `Invoke` an `Invoke`
statement whose `CallShape` names the words and buffers holding its
operands, and sequencing `Then`. It returns the statements, the word the
value lands in, and the next fresh word; `None` is a refusal.

**Where variables live.** A layout (`Loc`, one per variable) places each
word or bit in a word of the environment, held as the number it is the
`toNat` of, and each byte buffer in a buffer of the file. A read fills its
buffer in place, so after it every variable that named that buffer is
`Gone`, and the lowering refuses a gone variable: the call's uniqueness
fact is decided at the lowering, not assumed. A buffer bound by a pure
`Let` has no word to live in and is refused too.

**The meaning of loop-free statements.** `Stmt::thread`
(`lib/native/native_source_io.hthr`) runs straight statements against a
world: each `Invoke` put to the world (`Io::call`) and its answer landed as
`Env::invoke` lands it. `Stmt::reads_thread` proves once that a straight
statement's coinductive tree reads as `thread` at every world, by
`reads_bind` and `reads_ret`.

**Soundness, once.** `ETm::lower_sound`, by induction over `ETm`: from any
environment holding the variables at their locations and any world, the
lowered statements' threading leaves the world `ETm::sem` leaves and the
meaning's value in the result word. Composed with `reads_thread` it is
`ETm::lower_reads`: the lowered tree, mapped through the result word's
read-back, reads as `ETm::sem` at every world, up to silent steps. Each
pure step uses `Tm::lower_sound` at the environment's valuation plus three
checks the lowering decides and the proof uses once: the region has no
byte node or loop (`byte_free`, so it evaluates as it runs and keeps the
buffers), it writes no live variable's word, and the value is one word or
bit.

**A decision in `rt_lower`.** `Ty::Holds` and `Ty::FlatHolds` at `Bytes`
are `True` (they were `False`): a buffer lives in the buffer file, so the
pure valuation asks nothing of it. No pure theorem depended on the old
value; it only made every environment with a buffer variable unusable.

**Probes** (`lib/_tests/native/runtime/rt_io_lower_tests.hthr`): echo (read
into the caller's buffer, write what came back) lowers, runs "hi" through a
piped world to stdout, and `lower_reads` instantiated at it says its tree
reads as the surface method `Io::echo_lowered` at every world. A
three-call open/read/close lowers; a write naming the buffer as it was
before the read, and a buffer bound by a pure `Let`, are refused.

**Left.** Branches over the world (§8.4); the lowering is not yet what a
`runtime fn` setup publishes, which is item 4's `main`. Loops: §8.6.

### 8.6 Loops over the world (slice 5)

**The form.** `ELoop` (`lib/native/runtime/rt_io_loop.hthr`) is a chain of
loop-free computations (`Seq(t, rest)`: `rest` sees `t`'s end context) and
loops, ending in a computation's value (`Done`). A loop is
`While(cond, body, rebind, rest)`: its state is the **whole environment**,
and each pass runs `body` (an `ETm`) and rebinds variable `i` to the end
context's variable `rebind[i]`. That is the surface `while`'s threading
(sequencing design §18): a local the body assigns is rebound to its new
value, any other to itself. The condition is a `Tm` of code `Bit`.

**The meaning** is in `Partial`, since the loop may go round forever:
`if cond { do body while cond }`, `Io::iterate` of a total pass that runs
the body (`ETm::sem_end`, the end environment with the world after the
calls), gathers the next state and tests the condition again. It is the
surface `while` up to silent steps; that bridge is the reflector's to
prove, as the state shapes differ (the surface nests the threaded locals
in `Mutated` pairs).

**The source side.** `Stmt::run` (`native_source_io`) is every statement as
world threading in `Partial` (a `Repeat` is `Io::iterate` of its pass, a
procedure call its tree read against the world), and `Stmt::reads_run`
proves once, unconditionally, that a statement's tree reads as it
(`Io::reads_iter` at a `Repeat`). `Stmt::run_straight` says a loop-free
statement's `run` is its `thread`, returned.

**The lowering** keeps every variable where it lived before the loop. A
pass is the body's statements, then moves of each word variable from
where the body left its new value back to its word, then the condition
again into the flag word the `Repeat` tests. Before the loop the condition
is computed once and a `Branch` skips the loop when it fails. A buffer
variable must end the pass in its own buffer; one rebound to a buffer a
read wrote over (gone) is refused. The moves are checked so that none
writes a word a later one reads or an earlier one wrote.

**Soundness.** `ELoop::lower_sound`, by induction over `ELoop`. A loop is
`Io::iterate_rel` (`linux_world_co`): two loops of total passes, started at
related states, whose passes leave the same world and go on together
(both round again at related states, or both out at related results),
followed by rests that agree at related results, agree up to silent steps.
Proved once by direct corecursion. The relation is "the environment holds
the state at the loop's places"; a pass keeps it by the loop-free
lowering's theorem, which now also gives the end environment
(`ETm::EndHolds`, `ELowered.locs`), the sources' and moves' theorems, and
the condition's. `ELoop::lower_reads` is `Io::Reads` of the lowered tree
against the meaning.

**Probes** (`lib/_tests/native/runtime/rt_io_loop_tests.hthr`): a loop that
echoes stdin to stdout until a read returns nothing lowers; its statements,
its meaning and the surface `while` it models (`Io::echo_all`) each send
"hiyo" at a piped world and end with 0; `lower_reads` instantiated at it.
Refused: the buffer rebound to the one the read wrote over, a word
condition, a variable rebound to one of another code.

**Left.** Branches over the world (`EIf`), so that a pass can skip a
write; the reflector reading a surface `while` into `ELoop` and the bridge
from its nested state to `ELoop::sem`; `runtime fn main`.
