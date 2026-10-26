# The effectful source: a control layer over total FunctionIR

Status: **design, decided by Minus 2026-10-22 (A and L3, §12); not implemented.**
Round S3 of `docs/native-program-logic-design.md` (§7, §9, §10 item 6),
issue `issues/native-effect-source-compiler.md`. It also answers
`issues/function-ir-lowering-loops.md` and says what S3 contributes to
`issues/function-ir-source-denotation-after-b2.md`.

S3's question is what native programs are written in: the source whose
programs denote Linux trees, which a Heather function compiles to `Prog`,
with one theorem saying the compiled image meets the tree. Minus's answers
already fix three things. The surface is uniqueness threading that denotes
trees. The compiler runs by kernel evaluation first. The ideal version is
built from the start, with nothing temporary in a core piece. What is open is
the source's shape and, with it, where loops live.

As §10 item 6 asked, this doc writes `tr` both ways before choosing (§3).
Doing that turned up four facts about what is already built, which do more to
decide the question than taste does (§2).

---

## 0. Recommendation

**Two levels, split by totality rather than by effect.**

- **FunctionIR is the total level.** It holds dataflow, conditionals, calls
  to total functions, **one bounded loop** (at most `n` passes, with an early
  exit), and, later, buffers as values on state edges. Everything in it
  terminates, and its meaning is a function: a valuation, with no `Option`
  and no tree.
- **The layer is the control level.** It holds what may not return or what
  talks to Linux: calls to Linux (`≈ Vis`), sequencing (`≈ bind`),
  branching, **the one general loop** (`≈ iter`) and exit (`≈ Ret`). Its
  leaves are FunctionIR regions. `denote` maps each construct to the tree
  construct of the same name, so the compiler's proof is one small lemma per
  construct.

So option **A** for the source (§4) and option **L3** for loops (§5). In
one line each, why:

- **A, not FunctionIR grown with effect nodes (B).** S4's three rounds prove
  "the code runs to the end and the region's equations hold", over runs that
  never reach a syscall. A syscall node inside FunctionIR changes that
  statement for every construct, so B restates S4. Under A, S4's theorem
  enters unchanged as a `Proved` contract (§2.2).
- **L3, not "one loop, in the layer" (L1).** Heather's pure functions are
  total, and the compiled code should say so. Under L1 a pure function with
  a loop gets the tree's partial meaning, and its callers see an `Option`.
  Under L3 the bounded loop keeps it total. The general loop stays in the
  layer, where the tree already makes divergence honest with `Tau`s, and
  where its proof needs no variant (§5.3). The bounded loop is also what the
  old loop path compiles today, so B2 loses nothing.
- **L3, not general loops inside FunctionIR (L2).** A general loop makes
  FunctionIR partial. Its evaluator would then need fuel, and the `Option`
  would leak into every pure client.

Internal effects (buffers, memory) stay as the §10 input put them: values on
FunctionIR state edges, never tree events. One addition makes uniqueness
checked rather than trusted. The lowering's abstract file already refuses
code that reads a value whose register was overwritten, and it treats a
buffer's memory range the same way. A store gives the range the new buffer
value, and a later use of the old value fails the lookup, so `lower` refuses
(§6).

---

## 1. What is fixed

- `denote` is compositional: sequencing is `bind` and a loop is `iter` (§7
  of the program-logic design).
- Pure parts are FunctionIR regions, lowered by S4 and entering effectful
  code as `Proved` items (S2's `Wp`).
- Calls to Linux are explicit nodes, whose arguments are values and whose
  answers are bound for what follows, as in `Vis(c, k)`.
- The theorem is proved once, by induction on the source, with each case a
  `Wp`/`loop_at` proof over abstract inputs. It ends at
  `SimProgram(io_linux(), denote(p))` of the image of `compile(p)`
  (`lib/std/os/linux/linux_x86_64_sim.hthr`).
- Specs are size-free trees over `Events::linux_spec()`. A source denotes a
  tree over `Events::linux()`, with the sizes it reads, and is related to
  its spec by `ITree::Implements`/`Program::Implements`
  (`lib/std/os/linux/linux_trees.hthr`).
- The surface is uniqueness threading, and the source is the target it
  elaborates to (`issues/effects-direction.md`).

## 2. Four facts that decide most of it

### 2.1 FunctionIR's meaning is a relation; a tree needs a function

`RegionHolds`, `StructuredRegionHoldsIn` and `Function::Computes`
(`lib/native/function_ir/function_ir.hthr`) are equations over a valuation: "some valuation
satisfies the region". That suits a DAG, because the schedule is not
observable. A tree, though, has to compute its next command: to build
`Vis(ReadCmd(fd, size), k)`, `fd` and `size` must be values, not unknowns of
a relation. Whatever shape S3 takes, it needs a **total evaluator**
`StructuredRegion::eval(callees, region, env) → env`, with one agreement
theorem `eval_holds`: the evaluated valuation satisfies the equations, so
S4's statements apply to it. This is new work under every option (filed as
`function-ir-total-evaluator`).

An evaluator exists only for a total language. That is the root of the loops
question in §5: as soon as FunctionIR has a loop that might not terminate,
`eval` needs fuel and returns an `Option`.

### 2.2 S4's theorem speaks of runs that reach no syscall

Rounds 1–3 prove, for every placement, that `lower`'s code runs from its
entry to its end and that the region's equations hold of the registers after
(`Site::Runs`, `Site::Moves`, `Site::Calls`;
`lib/native/function_ir/function_ir_lower_calls.hthr`'s `lower_program_correct`). The runs are
fetched steps, stack steps and calls into the program's own functions. None
passes a syscall, and the post is pure.

A syscall node inside a `StructuredRegion` breaks that shape at every
construct. A region containing one does not run to its end: Linux answers in
the middle, so its meaning is a tree, and its lemma has to be a `Wp`/`Sim`
statement with a continuation. B therefore means either restating S4's three
rounds in `Sim` form, or carving each region into maximal pure pieces and
using S4 on those. The carving is A's layer, recomputed by the compiler
instead of written in the syntax.

### 2.3 Heather's pure functions are total

Everything the current `compile-x86` path compiles is a Heather function,
total by construction: structural recursion, or `bounded_readonly`'s
budgeted loop (`lib/native/function_ir/function_ir_loop.hthr`). Partiality enters native code in
only two ways: a program that talks to Linux, and a general loop (read until
end of input, or a write loop that may be answered `Wrote(0)` forever). Both
belong to programs whose meaning is a tree. So the split that keeps every
level's meaning simple is **total vs. not**, and "pure vs. effectful" is the
special case of it.

### 2.4 A `Proved` contract speaks of registers only

`Contract` is `pre`/`post` over `Gprs`, and `Contract::Runs` requires
`e.memory = s.memory` (`lib/std/os/linux/linux_x86_64_wp.hthr`). A region whose code
spills to its frame, calls a function (round 3's frames), or stores into a
buffer (§6) cannot enter `Wp` as a `Proved` item as built. The contract needs
a footprint: memory unchanged outside a named range, and a post over the
range. This holds under every option (filed as `wp-proved-memory-contracts`;
`issues/wp-stack-items.md` is the neighbouring piece for `CallTo`/`Spill`).

---

## 3. `tr`, both ways

The program: read standard input in chunks of up to 4096 bytes. On an empty
read, exit 0. On a failed read or write, exit 1. Otherwise map each byte by
`f`, write the chunk, and keep writing the rest after a short write. Its spec
is `tr_spec(f)` (`lib/native/stream_filter_spec.hthr`), an `iter` over
`Events::linux_spec()`.

Values below are named by `Nat` ids, as FunctionIR's ports are. `buf` is a
buffer value of capacity 4096 (§6); `map_bytes(f)` is a FunctionIR function
whose body is a bounded loop over `n` bytes of a buffer.

### 3.1 Written in the layer (option A)

```
Seq
  Pure     fd_in := 0; fd_out := 1; cap := 4096
  Loop again := more                                   // ≈ iter over the environment
    Seq
      Call   Read(fd_in, buf, cap) → buf, r            // ≈ Vis(ReadCmd(0, 4096), …)
      Pure   failed := r <s 0; empty := r = 0; n := r
      If failed  Exit(one)
      If empty   Exit(zero)
      Pure   buf := map_bytes(f, buf, n); off := 0      // total: FunctionIR's bounded loop
      Loop again := owed                               // the short-write loop: general
        Seq
          Call   Write(fd_out, buf, off, n - off) → w
          Pure   bad := w <s 0; off := off + w; owed := off < n
          If bad  Exit(one)
      Pure   more := 1
```

(`If c Exit(…)` with nothing after it is `If(c, Exit(…), Skip)`, and the
rest of the `Seq` follows.)

**`denote`** is structural, an environment-passing interpreter into trees
(§7.3). For `Call(Read(…))` it is
`Vis(ReadCmd(env[fd], env[len].toNat()), λ a => Ret(Next(env.answer(Read(…), a))))`.
`answer` decodes the answer the way the machine sees it: `ReadBytes(bytes)`
sets `r := len(bytes)` and fills `buf`'s prefix with `bytes`, and
`ReadFailed(e)` sets `r := -e`. `Loop` is `iter`, `Seq` is `bind`, `Pure` is
`Ret(eval(…))`, `If` reads a bit, and `Exit` is `Ret(Exited(status))`.

**Construct lemmas** (§7.5). There are six, one per constructor, each over
an abstract environment and continuation. `Pure` follows from S4's theorem
as a `Proved` item. `Call` is a `Wp` `Syscall` arm with the decode, stated
once per call shape. `Loop` is `loop_at`, with the ghost variant taken from
the tree's fuel (§5.3). `Seq`, `If` and `Exit` are glue. None of them
mentions `tr`.

**What `tr` itself costs**: running `compile` (by evaluation), and one
tree-level proof that `denote(tr_src)` implements `tr_spec(f)`, which
involves no machine (§8).

### 3.2 Written as FunctionIR with effect nodes (option B)

`StructuredRegion` grows `Syscall(shape)` and `Loop(carried, body, again)`,
and `tr` is one region:

```
Compose
  Dataflow  consts
  Loop carried := [buf], again := more
    Compose
      Syscall   Read(fd_in, buf, cap) → buf, r
      Dataflow  classify
      Conditional failed   Syscall(Exit(one))
      Conditional empty    Syscall(Exit(zero))
      Call      map_bytes(buf, n) → buf
      Dataflow  off := 0
      Loop carried := [off], again := owed
        Compose
          Syscall   Write(fd_out, buf, off, n - off) → w
          Conditional bad  Syscall(Exit(one))
          Dataflow  advance
```

**`denote`** has to give *every* `StructuredRegion` a tree:
`StructuredRegion::denote : region → env → ITree<env>(E)`. `Dataflow` is
`Ret(eval)`. `Conditional` is a match. `Call` of a pure function is now a
tree too, because nothing stops a callee from containing a `Syscall`. Then
`Callees`, a relation, has to become trees, or a validity side condition has
to keep callees syscall-free, which reintroduces the two levels as a
predicate. `Loop` is `iter`, which makes `Function::Computes` partial for
every client.

**Construct lemmas.** The lowering's induction over `StructuredRegion`
(`emit_calls_emits`) changes statement for every arm. Today it is
`MayEmitIn` over `Site::Moves` with a pure post. It would have to be a `Wp`
post carrying the tree's continuation, because any arm may contain a syscall
below it. `Dataflow` and `Sequence` arms that contain no syscall could
borrow S4's lemmas through a "this subregion is pure" case split, and that
case split is the layer again. The abstract file has to learn the syscall
clobber set (RAX, RCX, R11) at `Syscall` arms. That part is good: values in
other registers survive a syscall. But §7.4 gives the layer the same file,
so A gets this too.

**What B buys.** One IR, so one allocator sees across a syscall, and a pass
that hoists pure work out of a read loop is one pass. A gets the first by
threading S4's file through the layer (§7.4). The second remains a pass over
two levels.

### 3.3 What writing it out showed

- The layer's constructs are the tree's constructs, one to one. Under B the
  same six constructs exist, plus a pure/effectful classification on every
  existing one.
- The inner `map_bytes` loop is the hot loop, and it is total (at most `n`
  passes). The outer read loop and the short-write loop are general. **`tr`
  has both kinds**, so a design with one kind of loop serves one of them
  badly (§5).
- Neither form touches memory except through the buffer. The read fills it
  (a call's answer), the map rewrites it (FunctionIR), and the write reads it
  (a call's argument). That is §6's state edge, and it is the same under A
  and B.

---

## 4. The source's shape

| | **A: control layer over FunctionIR** | **B: FunctionIR with effect nodes** | **C: trees written directly** |
| --- | --- | --- | --- |
| Syntax | `Stmt` (six constructs, §7.1) with `StructuredRegion` leaves | `StructuredRegion` + `Syscall` + `Loop` | Heather functions returning `ITree` |
| `denote` | structural, one tree construct per constructor | structural, but every pure construct gets a tree meaning too | the program *is* the tree |
| S4's theorem | used unchanged as `Proved` contracts | restated in `Wp`/`Sim` form for every arm, or carved into pure pieces | n/a |
| Pure passes | never see effects | step around `Syscall`/`Loop` arms | n/a |
| `Callees` | stays a relation over total functions | becomes trees, or gains a "no syscall" side condition | n/a |
| Placement across a call | the layer threads S4's abstract file (§7.4) | one allocator | n/a |
| Hoisting pure code across a call | a pass over two levels | a pass over one | n/a |
| Compilable by a Heather function | yes (syntax) | yes (syntax) | **no**: a continuation is a closure, which `compile` cannot inspect |

**C is not a source.** A tree's continuations are functions, so a compiler
written in Heather cannot look inside them. Reading a Heather function's
body is reflection (the host `View`, `tac-host-interface` R2), and that is
how the *surface* reaches the source, not a replacement for it. It is in the
table because it is the first thing "denotes trees" suggests.

**Recommendation: A.** Its one real cost relative to B is that
optimisations moving pure code across a call see two levels. That is a pass
to write when there is an optimiser, and it does not touch any statement
proved once.

## 5. Where loops live

### 5.1 The options

- **L1: one loop, in the layer.** FunctionIR stays loop-free, which is all
  S4 lowers today. A pure function with a loop becomes a layer program over
  `Events::none()`, read back through `ITree::returned` as an `Option`.
- **L2: FunctionIR keeps general loops.** `StructuredRegion` gains `Loop`,
  and S4 gains a fifth round proved with a pure instance of the loop rule.
- **L3: split by totality.** FunctionIR gains a **bounded loop** (at most
  `bound` passes, the body producing an early-exit bit), which is total. The
  layer has the one **general loop**. S4's fifth round lowers the bounded
  one.

### 5.2 Comparison

| | L1 | L2 | L3 |
| --- | --- | --- | --- |
| FunctionIR's meaning | total | partial: `eval` needs fuel → `Option` | total |
| A pure function with a loop | partial meaning (`Option`) though Heather proved it total | partial | total |
| `tr`'s hot inner loop | crosses the layer each pass; layer placement | inside the pure allocator | inside the pure allocator |
| The old loop path before B2 (`bounded_readonly`) | becomes a layer program | S4 round 5 | S4 round 5, the same shape as the existing contract |
| Proof of a pure loop's code | `loop_at`, fuel as variant | a pure loop rule plus agreement between relation and fuelled `eval` | induction on `bound`, no variant at all |
| Loop constructs | one | one (two semantics: relational and fuelled) | two, one per level |

### 5.3 Why the general loop costs nothing extra in the layer

`loop_at` (S2) asks each pass either to make a syscall or to lower a ghost
variant `w`. A general loop has no variant of its own, but its denotation
does. At fuel `n`, `iter` goes round at most `n` times, and a pass that
makes no call consumes one of them. The variant is therefore the tree's
remaining fuel. When it reaches zero the tree is `Cut`, and `Sim` at `Cut`
is `True` (`sim_cut`). The layer's `Loop` lemma takes `w :=` the fuel left
in `iter` and never asks the programmer for a variant. That is the honest
reading: the theorem claims every finite trace and says nothing about
termination. Liveness waits for the coinductive tree.

### 5.4 Recommendation: L3

Two constructs, but each one is the natural loop of its level, and neither
level's meaning gets more complicated. This is the same split as Heather's
own: structural recursion is total, and general recursion goes through
`iter`/`mrec`. When the surface elaborates (§9), a `for`/structural loop
becomes FunctionIR's bounded loop and a `loop`/`while` becomes the layer's.
A bounded loop with no early exit, run `bound` times, is a fold. With an
early exit, it is `bounded_readonly`'s shape.

**The bounded loop has an explicit `Exhausted` outcome**, as
`bounded_readonly` does. A loop that runs out of passes before its exit bit
is set yields `Exhausted`, not an `Option` and not a cut. Its meaning is then
total and a function. A function defined by well-founded recursion (gcd by
`Wf`, say) has no count to read off, but it does have a measure. It compiles
with `bound :=` the measure at entry, and the function's own proof that the
measure decreases shows `Exhausted` is unreachable. The IR never needs a
dependently typed "this decreases" field. A loop that is pure but may
diverge, with no measure at all, is not a FunctionIR loop: it is the layer's
`Loop` with no calls in its body, and the tree gives it `Tau`s.

*As built (S4 round 5):* the pass that sets the exit bit is a pass too, so
the bound that provably never runs out is the measure at entry plus one, or
the measure itself when it stays positive at every pass.
`loop_runs_unexhausted` (`lib/native/function_ir/function_ir.hthr`) takes the invariant and
the measure, and states it for any bound above the measure.

`issues/function-ir-lowering-loops.md` then resolves as: **S4 gains round 5,
the bounded loop**, and B2 waits for it as that issue already requires.

---

## 6. Internal effects: buffers as values

A buffer is a value in FunctionIR and in the layer's environment: a
`Bytes(capacity)`, which is what a uniqueness-threaded `uniq Buf` denotes.
A load is a node `Load(buf, index) → byte`. A store is a node
`Store(buf, index, byte) → buf'`, an RVSDG-style state edge. `Read`'s answer
writes into a buffer value, and `Write`'s argument reads from one. Nothing
about memory is a tree event, so an array access never splits a region.

**Uniqueness is checked by the compiler, not trusted.** The lowering already
tracks an abstract file: which value each register holds. A placement that
overwrites a value still needed makes a later lookup fail, and `lower`
refuses (`lib/native/function_ir/function_ir_lower.hthr`). Buffers get the same treatment. The
file also says which buffer value each memory range holds. A `Store` updates
the range in place to hold `buf'`, so `buf` is no longer held anywhere, and a
later use of `buf` fails the lookup. The surface's uniqueness discipline is
what makes such refusals rare. The theorem never depends on it: it is stated
over every program `lower` accepts, as S4's is over every placement.

**What this needs from `hih-memory-model`** (`issues/byte-memory-access-model.md`,
starting in parallel): byte reads and writes with explicit outcomes, and a
view (S2's `View`) over a buffer's range, so that a buffer's value in the
environment and its bytes in memory are related by `view.Holds`. With §2.4's
footprints, a region that stores into a buffer enters `Wp` as a `Proved`
item whose footprint is that range. Filed as `function-ir-buffer-state-edges`.

**Faults.** `lib/std/machine/memory.hthr` (the memory-model round, in parallel)
gives checked accesses as `Result<_, Fault>`, and a buffer is a
`Memory` over the index space `0..capacity`. A region with loads or stores
then evaluates to a `Result`, and the layer's `Pure` leaf turns `Err` into a
separate process-end outcome, `Faulted`, beside `Exited(status)`. It is not
mapped onto an exit status. Its machine side, a trap path whose meaning is a
signal, belongs to `issues/linux-syscall-trace-model.md`. Regions whose
indices are guarded below the capacity discharge the `Ok` case by the
model's span lemma, and a compiled program that cannot fault never reaches
that path.

The first S3 round does not need this. Its first program is `cat`, whose
buffer is touched only by calls (§10).

**As built** (`issues/native-source-bytes.md`, 2026-10-26). The first byte
nodes take a simpler road than the one above, which stays the target. A
region's buffers are a `List<List<BitVec(8)>>` threaded beside the
valuation by `StructuredRegion::run` (`lib/native/function_ir/function_ir_state.hthr`),
not port values; `eval` is unchanged and is `run` from no buffers
(`run_empty`). `BufferLoad(output, buffer, index)` reads a byte zero-extended,
and `BufferStore(output, buffer, index, value)` stores a word's low byte and
reads it back. An index past the buffer's end loads zero and stores nothing,
so no `Faulted` outcome exists yet. Every buffer already lives in the data
region under S3.2's `Target::Placed`, so the statement compiler compiles a
leaf of one byte node there, CMP-guarded against the capacity
(`lib/native/native_compile_bytes.hthr`), with no footprint and no change to
S4, which refuses the nodes. Initial bytes are stored at entry.

---

## 7. The layer

### 7.1 Syntax

```heather
// A call to Linux, its operands named by environment ids. The machine-side
// command (`LinuxCmd<Nat>`) is computed from the environment by `denote`.
inductive CallShape {
    Read(fd: Nat, buf: Nat, len: Nat, result: Nat),
    Write(fd: Nat, buf: Nat, from: Nat, len: Nat, result: Nat),
    Open(path: Nat, result: Nat),
    Close(fd: Nat, result: Nat),
    Stat(target: Nat, buf: Nat, result: Nat),
}

inductive Stmt {
    Pure(region: StructuredRegion),           // total: FunctionIR
    Call(call: CallShape),                     // ≈ Vis
    Seq(first: Stmt, then: Stmt),              // ≈ bind
    If(condition: Nat, yes: Stmt, no: Stmt),   // a one-bit value
    Loop(body: Stmt, again: Nat),              // ≈ iter: round again while `again` is set
    Exit(status: Nat),                         // ≈ Ret
}

record Source { functions: List<Function>, buffers: List<Nat>, main: Stmt }
```

`Skip` is `Pure` of the empty region. `functions` are the program's total
functions, called from `Pure` leaves by FunctionIR's `Call` node.
`buffers` are capacities, laid out by `compile` in the image's data area. A
`StmtValid` predicate is computed by evaluation, as `StructuredRegionValid`
is: ids defined before use, widths agree, and a call's operands are words or
buffers as its shape requires.

### 7.2 The environment

`Env` holds words and buffers. The update `env.answer(shape, a)`
decodes a Linux answer into the environment as the machine sees it: a count
or a negated errno in `result`, and a read's bytes in `buf`'s prefix. It is
defined once per call shape.

*As landed (S3.1, `lib/native/native_source.hthr`):* both files are data, not
functions: `words: List<Nat>` and `buffers: List<Bytes>`, indexed by id.

- A region sees them through `Env::valuation`, which reads each word at
  every width as its low bits.
- What a region writes is read back at each written port's width and stored
  zero-extended (`Env::settle`).

As functions (`Valuation()`, `Nat → Bytes`), each read re-ran the updates
that built the value, so evaluation cost compounded with every statement.
As constructor fields, each word is computed once. Once read, it stays read:
the kernel's value cache keeps what a query forced (until 2026-10-22 a FIFO
evicted the cells under each 64-bit operation's intermediates, and longer runs
recomputed them: `issues/kernel-value-cache-evaluation-thrash.md`).

### 7.3 `denote`

```heather
inductive Outcome { Next(env: Env), Exited(status: BitVec(64)) }

fn Stmt::denote(self s: Stmt, src: Source, n: Nat, env: Env) → ITree<Outcome>(Events::linux()) {
    match s {
        Pure(region) => Ret(Next(region.eval(program_callees(src.functions), env))),
        Call(shape) => Vis(shape.cmd(env), λ a => Ret(Next(env.answer(shape, a)))),
        Seq(first, then) => bind(first.denote(src, n, env), λ o => match o {
            Next(env2) => then.denote(src, n, env2), Exited(st) => Ret(Exited(st)) }),
        If(c, yes, no) => match env.bit(c) { True => yes.denote(src, n, env), False => no.denote(src, n, env) },
        Loop(body, again) => iter(n, λ e => map(body.denote(src, n, e), λ o => match o {
            Next(env2) => match env2.bit(again) { True => Continue(env2), False => Break(Next(env2)) },
            Exited(st) => Break(Exited(st)) }), env),
        Exit(status) => Ret(Exited(env.word(status))),
    }
}

fn Source::denote(self src: Source) → Program<BitVec(64)>(Events::linux())   // `at(n)` runs main at fuel n
```

Fuel is shared by every loop at depth `n`, as `Program::bind` shares it.
`Source::denote`'s `grows` comes from `below_bind` and `iter_family_grows`,
by induction on the statement. Because `denote` is an ordinary Heather
function over syntax, a source program can also be **run** by evaluation
against a scripted world (`run_state` with a world handler). That gives the
source a testable meaning before any machine is involved.

**Target, now and later.** `denote` targets the fuel family (`Program`) now.
When the coinductive tree lands (`docs/kernel-coinduction-design.md` §6),
`denote` gets a corecursive twin into it, `Program` is recovered by
`approx`, and the theorem keeps its statement. That migration adds a
definition and changes no statement, so no temporary piece is built into
the core.

### 7.4 `compile` and the invariant between constructs

`compile(src) : Option<Prog>` threads a **layout**: S4's abstract file
extended with frame slots and buffer ranges, saying where each live
environment value is. A `Pure` leaf is lowered by S4 with its input and
output registers taken from the layout. Its code enters as a `Proved` item
whose contract is S4's theorem, with the frame and buffer footprint of §2.4.
A `Call` moves operands into the syscall registers, emits `Syscall`, then
records in the layout that RAX holds `result` and that RCX and R11 hold
nothing. Values in other registers survive, so nothing is spilled around a
syscall unless the placement says so. Placement is an input, outside the
proof, exactly as in S4.

The invariant `Inv(layout, env, s)` says: each register and slot the layout
names holds the environment's word, each buffer's bytes are in its range
(`view.Holds`), the code is resident, and the stack laws hold. It is stated
once.

### 7.5 The construct lemmas and the theorem

Each lemma is in continuation form, because `Sim` has no "this code, then
that code" rule of its own. `Wp`'s post is the continuation:

```
Stmt::compiles(s, layout, …): compile_stmt(s, layout) = Some((code, layout')) →
    (env, state, K) → Inv(layout, env, state) → at the code's entry →
    ((o, state') → Inv(layout', o, state') → at the code's end → Sim(K(o))(state')) →
    Sim(bind(s.denote(src, n, env), K))(state)
```

The proof is by induction on `s`, one case per constructor:

- `Pure`: `Wp`'s `Proved` arm, with S4's theorem and `eval_holds` (§2.1).
- `Call`: `Wp`'s `Syscall` arm, `next` of a `Vis`, and the decode lemma for
  each call shape.
- `Seq`: the inductive hypotheses composed, with `bind` associativity up to
  `Same` (`sim_of_same`).
- `If`: the `Jcc` arm.
- `Loop`: `loop_at`, with `inv(w, t, v, s) := ∃ env. t = iter's remainder at
  fuel w ∧ Inv(…)` (§5.3).
- `Exit`: the exit request.

Every obligation is over abstract inputs, so none of them grows with the
program, which is the cost argument of the program-logic design (§6.3). The
theorem is the `main` case at `K := λ o => Ret(status(o))`, from the
loader's initial state, for every page, register file and flags.

*As landed (S3.2, `lib/native/native_compile*.hthr`):* the shape above with
three simplifications. The layout is fixed rather than threaded: every word
has an eight-byte slot in one data region, each buffer a range after the
words at its capacity, and a scratch range past them, so the invariant is
the memory alone (`Target::Placed`: the region holds cells that keep the
environment) and no register carries a value between statements. The
construct lemmas are proved over the code's claim `Target::Goes` (every
state at an offset, its code resident, meeting a condition, runs as a tree)
with one rule per instruction form, not through `Wp`; a statement's claim is
`Target::Runs`, the continuation form above with `Inv` as `Placed`. And a
`Pure` leaf is a register-only dataflow region, so it enters by S4's
`Region::lower_correct` with memory untouched and needed no footprint (§2.4
stays open as `wp-proved-memory-contracts`, for leaves that spill or call).
A read lands in the scratch range and is copied into its buffer only when it
succeeds, since Linux may leave the range written after a failure. `Loop` is
an induction on the loop's fuel, the body run with the test and a JMP back
as its continuation. The theorem is `native_compile_correct`; cat compiled
at the I/O image's page sends what it read (`cat_native_sends`,
`native_cat_compiled.hthr`). Other region shapes, other calls and the code's
shape are `native-compile-wider-leaves`, `native-compile-other-calls` and
`native-compiled-code-shape`.

## 8. Per-program cost, and one gap

A program is built by evaluating `compile`, and it inherits the theorem: it
meets `denote(src)`. Facts users care about are proved against the size-free
spec, so a program also needs `Program::Implements(src.denote(), spec)`.
That is a tree-to-tree proof with no machine in it, but it is per program,
and for `tr` it relates two `iter`s with different state shapes: the
source's buffer and offsets against the spec's `FilterAt`. The library has
no lemma for "two `iter`s related by a state relation that each body
preserves up to one call" (filed as `itree-iter-simulation`). With it, the
per-program proof is a pass-sized lemma.

## 9. What S3 says about its neighbours

- **The surface** (`effects-direction`). The uniqueness-threaded surface
  elaborates locally into this source. A `let` of pure expressions becomes
  a `Pure` leaf, `io.read(fd, buf)` becomes a `Call`, `loop`/`while`
  becomes `Loop`, and `for`/structural recursion becomes FunctionIR's
  bounded loop. The pure reading users reason with (world threading) agrees
  with `denote` construct by construct, which is `run_state_bind`'s
  statement, proved once. That is the surface round's work.
- **The source-to-IR question after B2**
  (`function-ir-source-denotation-after-b2`). For effectful programs, the
  answer is that issue's option 3: the program is this source, written
  directly or elaborated, and nothing has to be reflected. For pure
  functions L3 is what makes the question answerable, because reflected
  structural recursion lands on the bounded loop and stays total. That
  issue's "1 now, 2 when the host `View` exists" stands.
- **Procedures that make calls** (program-logic design §10 item 2) are a
  later `Stmt` constructor. They denote by `mrec`, and their code enters by
  a `Proved` contract whose post is a `Sim`. Nothing in §7 precludes them.

## 10. Rounds

| Round | Content | Done when |
| --- | --- | --- |
| S3.0 | `function-ir-total-evaluator`: `eval` over `StructuredRegion` and programs; `eval_holds` | `eval` agrees with every S4 example by `refl` |
| S3.1 | The layer: `Stmt`, `StmtValid`, `Env`, `denote` into `Program`, `grows`; `cat` and an exit-status example written in it, and run against a scripted world | `cat`'s source `Implements` a `cat` spec over `linux_spec` |
| S3.2 | `wp-proved-memory-contracts`, then `compile` and the construct lemmas, and the theorem | `compile_correct`, with `cat` built by evaluation and its claim instantiated |
| S4.5 | FunctionIR's bounded loop and its lowering (`function-ir-lowering-loops`) | the old loop path's examples go through `lower` |
| S3.3 | `function-ir-buffer-state-edges` (with `hih-memory-model`) | a region that maps a buffer in place lowers, its footprint in its contract |
| S5 | `tr` from its source through the compiler, `itree-iter-simulation` for its `Implements` | as the program-logic design's S5 |

S3.0, S3.1 and S4.5 can run in parallel. S3.2 needs S3.0 and the contract
footprints. `tr` needs everything above it.

## 11. Why this is the right shape, not only the cheap one

That S4 is reused unchanged under A is a consequence of the split, not its
justification. On principle alone:

- **A syscall's answer is control, not data.** A dataflow node's output is a
  function of its inputs. FunctionIR's meaning, CSE, reordering and every
  pure rewrite rest on that. Linux picks a syscall's answer, so it is not a
  function of the call's inputs. There are only two honest ways to put a
  syscall in dataflow.
  - Reify the world as a value: an IO token whose meaning is
    `World → (World, answer)`, which is `run_state`'s interpreted view. That
    builds a world model into the IR, which S1's abstract container
    deliberately avoided.
  - Make the IR's meaning a tree. The IR has then become the layer.

  A relational reading ("some valuation satisfies it") would not just be
  awkward. It would pick the answer *angelically*, which is wrong. An answer
  binds a continuation, and that is `Vis`.
- **Two levels are the minimum, not cruft.** This is Levy's split in
  call-by-push-value between values and computations, and Moggi's
  computational metalanguage. FunctionIR is the value level (total, a
  function), and the layer is the computation level (a tree). Whether the
  two are written as two inductives or as one inductive indexed by level is
  a matter of representation. FunctionIR exists, so two.
- **Termination is semantic, and an IR should keep it where it is known.**
  Heather's own type theory makes the same split: structural and
  well-founded recursion are total, and general recursion goes through
  `iter`, fuel or coinduction. L1 throws away totality the source already
  proved. L2 puts partiality into the one level whose whole value is being a
  function. L3 keeps each level's meaning as simple as it can be.
- **What B genuinely buys** (one allocator, passes that move code across a
  call) is tooling over A: passes that see both levels. It is not a reason to
  change either level's meaning.

## 12. Decision

*Decided by Minus, 2026-10-22* ("your recommendations make sense to me"),
after asking for the case on principle (§11):

1. **The source's shape: A**, a control layer over FunctionIR.
2. **Loops: L3**, split by totality. The bounded loop with `Exhausted` is in
   FunctionIR (S4 round 5), and the general loop is in the layer.

The rest follows from those two answers: the denotation target, buffers as
state edges, and how the layer places values. The rounds are §10's.
