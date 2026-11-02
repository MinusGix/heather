# Effects as capabilities: `Io`, `mut self`, and the tree reading

Status: **built, first slice (2026-11-02)**, the first round of
`effects-uniqueness-surface` (R6 of `docs/compiler-milestones-proposal.md`,
milestone `nh-effects`). It extends `docs/sequencing-surface-design.md` §8
(effects are layer 2 with `mut self`) and `docs/runtime-fn-setups-design.md`
§6.1 and §8 (the setup's `sound` proves the effectful agreement once). Read
`docs/compilation-vision.md` first.

## 0. In one page

```heather
fn Io::cat(mut self io: Io, capacity: Nat, passes: List<Nat>) → BitVec(64) {
    let mut status: BitVec(64) = BitVec::ofNat(0);
    for _ in passes {
        let r = io.read(Io::stdin(), capacity);
        match r {
            ReadFailed(_) => { status := BitVec::ofNat(1); break },
            ReadBytes(bytes) => {
                if bytes.len() = 0 { break }
                let ok = io.write_all(Io::stdout(), bytes, passes);
                if ok = Bool::False { status := BitVec::ofNat(1); break }
            },
        }
    }
    status
}
```

That is GNU `cat` with no arguments, in ordinary Heather. It is pure:

- `io` is a capability, a value of the record `Io`;
- `io.read(fd, n)` is a call of a `mut self` method, whose kernel type is
  `Io → BitVec(64) → Nat → Mutated<Io, ReadResult>`;
- on a `let mut` local or `mut` parameter, the call binds the answer and
  rebinds `io` to the world after it (SSA, §5.1 of the sequencing design).

Nobody writes a monad, and the meaning is world threading.

Three pieces make that work, all built in this round:

1. **The capability** (`lib/std/os/linux/linux_world.hthr`, §1). An `Io` is
   a *world* and the *exchanges so far*. The world is a function from the
   history to the answer to the next call.
2. **`mut self` methods** (§2). A general language feature, not an effects
   one: the parser and the elaborator lower it, and the kernel learns
   nothing.
3. **The tree reading** (§3). `Io::against(t, io)` reads a tree over
   Linux's calls against a world. `Io::Reads(t, f)` says the reading is `f`
   at every world, and `Io::reads_bind` is sequencing's case, proved once.
   It is the statement a `runtime fn` setup's `sound` will prove for every
   program.

The probe that ties them together:

```heather
theorem cat_agrees_piped():
    Io::against(cat(256).tree([], 4), piped()) = Some(Io::cat(piped(), 256, List::range(4))) { refl }
```

Here `native_cat`'s `cat` is the hand-built `Source` that `write-elf`
compiles. Read against the same world, it makes the same calls as the
surface program, gets the same answers, in the same order, and exits with
the same status: the two `Mutated` values are equal, history and all.

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
`write_all` loops over `write`.

**Why one world, not `uniq Fd` per descriptor.** Linux's answers on
different descriptors are not independent. A terminal echoes what is
written to it into what is read back, and a pipe's reader waits on its
writer. If each descriptor carried its own state, the pure meaning could not
see that writes and reads interleave, and agreement with every environment
would fail. So the capability is the one world (Clean's `*World`), and a
descriptor is a word. Buffers are byte lists, which are values. That a
buffer is not aliased, so a read may land in place, is a fact for the
compiler (the `Unique` fact, `docs/facts-on-demand-design.md` §7), not a
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
  update it.

**Not refused yet.** A method-syntax call of a `mut self` method on a local
that is not mutable, `let p = y.m(a);` with a plain `let y`, gives the
`Mutated` record. It is not refused at the call: the error appears where `p`
is used as the answer. Refusing at the call needs the method's result type
read on the dot-call path, which is hot, so it waits for a cheap test
(`issues/mut-self-call-on-immutable-refusal.md`). A call with an annotated
`let p: T = x.m(a);` is not a candidate either, so annotate the answer
after it.

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

**Where it goes.** For effectful code, the setup design's `sound`
(`docs/runtime-fn-setups-design.md` §6.1) states
`Implements(c.denote(args), p.tree(args))`. With capabilities it is
`Io::Reads(c.denote(args), λ io => f(io, args))`. Every `Invoke` lowers to
a `Vis` and reads as `Io::call`. Every pure run reads as `Ret` of its
meaning. Sequencing is `reads_bind`, and loops are the next lemma (§4).

## 4. Loops and fuel

A source's `Repeat` is `ITree::iter` at fuel `n`, which is cut after `n`
passes. A surface loop over a world is a `for` over a list of `passes`,
which runs at most `passes.len()` times. They agree whenever the tree is not
cut. `cat_agrees_piped` is at fuel 4 against a world of three reads.

The loop lemma for `Reads` is the next proof, and two statements are
candidates:

- `Io::against(iter(n, body, a), io)` equals a `for` over `List::range(n)`
  of the step;
- or the same as an inequality that ignores `Cut`.

The surface's `while … fuel n exhausted e`, designed in
`docs/sequencing-surface-design.md` §5.3, is the spelling programs will
want. It is not built (`imperative-statements-built`: "fuelled while"
open). Until it is, a program takes its `passes` list as a parameter, and
`runtime fn main` will supply it.

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
(`docs/runtime-fn-setups-design.md` §5.1) refuses it over reflected `rt`:

- each version of an `Io` is used exactly once;
- it is never stored in a record (other than the `Mutated` a `mut self`
  method returns, and loop state), a closure or a buffer.

A function that is never compiled may copy a world, which is useful in
specs ("had the program read instead…").

## 6. What R6 still needs

In order:

1. **`rt` capability types and an `Invoke` node** (setups design §8, N3).
   *Built as a computation layer, not a `Ty` (§8):* `ETm` with `Invoke`
   over pure `Tm`, in `lib/native/runtime/rt_io.hthr`. What is left of the
   item is the reflector reading an `io`-threading body into `Invoke`s
   (§8.3).
2. **`rt` to `Source`.** Runs of pure statements become `Compute` leaves
   through N1's lowering, `Invoke`s become `Invoke` statements, and loops
   holding `Invoke`s become `Repeat`. `sound` is `Io::Reads` of the
   source's tree against the reflected meaning, by `reads_bind` and the loop
   lemma.
3. **Linearity** as a clause of the default judgment (§5).
4. **`runtime fn main(mut io: Io, args: Args) → BitVec(64)`** publishing a
   `Source` that `write-elf` compiles as it compiles a builder tool today.
   This needs byte and string literals in programs and implicit compiler
   imports for program files.
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

## 8. Capabilities in `rt`: the computation layer

`lib/native/runtime/rt_io.hthr`, probes in
`lib/_tests/native/runtime/rt_io_tests.hthr`.

### 8.1 Why a layer and not a type

Setups design §8 had `rt` gain capability types: `Io` a `Ty`, laid out as
no words, with a linearity judgment refusing a term that copies or drops
one. That judgment is a second type system inside the reflector's output,
and every pure `Tm` former (`Let`, records, `If`) would need a rule for it.

The layer instead follows the source's own split
(`docs/native-effect-source-design.md` §11) and call-by-push-value: values
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

### 8.3 The reflector (next slice)

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

### 8.4 Known limits

- **Branching over the world.** A statement `if` that calls on `io` in a
  branch joins per variable (`imperative.rs`), so the elaborated body
  projects `io` and each other variable out of the branch's tuple. An
  `EIf(c, a, b)` whose meaning branches on the whole `Mutated` needs a
  commuting conversion to agree with that by `refl`; either the lowering
  joins the world with the values or the pin goes through an equation.
- **Loops.** `for` over a body with `Invoke`s needs `ERepeat` and the loop
  lemma of §6 item 2.
- **Callees.** An effectful callee (`EFun` calling `EFun`) is not modelled;
  `ETm::plain_world()` is the world with no callees.

