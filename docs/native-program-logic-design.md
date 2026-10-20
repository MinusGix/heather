# One program logic for native code

Status: **design, 2026-10-20, for review.** Milestone `hih-program-logic`
(`docs/roadmap.md`). Issue: `issues/native-one-program-logic.md`, whose three
questions §1 answers. Nothing here is implemented; §9 splits the work into
submilestones, one round each, with an issue per round.

The milestone asks that native code be "stated and proved through one program
logic (one effectful code tree, rules proved once) instead of the five 'this
code runs' shapes, and the assembly layer redesigned on it", and that the
logic be stated so that "this code refines the interaction tree `t`" comes out
later as a lemma, not a re-founding (`it-native`).

## 0. The proposal in one page

The pieces that already work become the logic; the pieces that compete with
them are retired.

1. **One machine.** A process is `LinuxStep` (a fetched instruction or a
   store) between syscalls, over a `LinuxIo<M>` profile. That is the only
   step relation clients see. `ExecuteBlock`, `ExecuteStructured`,
   `ExecuteAccess` and the older fetched-block and linked families stop being
   judgments and become either the semantics of one code item or lemmas into
   steps (§3).
2. **One code tree.** The labelled program `Prog` of `Asm` items
   (`lib/std/arch/x86_64/x86_64_asm.hthr`) is the code tree. It gains two
   items: `Syscall`, and `Proved(bytes, contract)`, a piece of code that
   enters with its own triple (a generated step, a called procedure, a
   library piece). Labelled edges are the jumps it already has (§4).
3. **Specifications are coalgebras over Linux's events.** Linux's calls and
   answers become a container (`LinuxCmd`, `LinuxAns`). A program's
   specification is a state machine `Spec<Q>` whose step either exits, or
   issues a command and continues from the answer. It is writable today
   (its continuation field is not recursive), stays at one universe level,
   and an interaction tree is one such machine (its carrier is the tree,
   its step is `observe`). So the logic needs no interaction trees to be
   built first, and meets them without re-founding (§2, §7).
4. **The judgment is `Sim(spec, q)(s)`**: from machine state `s`, for every
   history of answers the spec allows from position `q`, the machine
   produces exactly the spec's calls and exit. Today's claims
   (`LinuxRuns(io, events(history), start)` for every history) are this
   judgment at a spec that computes those events, and a bridge lemma says so
   (§2.4). With determinism (`linux_runs_every`) it is trace equivalence
   with the spec, not only refinement.
5. **One weakest precondition, computed.** `Stretch` and `Straight` already
   compute what running a run of items requires, by evaluation, and prove it
   once. They become one function `Wp` over all items, syscalls included,
   with the spec position carried beside the state, parametric in a memory
   view (Straight's frame of slots and Stretch's bare page are two views).
   Proved once: `wp_sound` (§5).
6. **Loops by one rule, measured by the history.** A back edge to a label
   with an invariant is closed by `loop_at`, proved once by induction on the
   remaining history and a variant: a path through the body that passes a
   syscall consumes an answer, and one that passes none must decrease the
   variant. The wp tracks which by evaluation. This replaces the hand
   inductions (`eof_from`, `filter_loop`, the write loop, the operand loop)
   (§6).
7. **Observable facts are proved about the spec, not the machine.** `stdout
   = spec(stdin)` becomes a lemma about the spec's traces, proved once with
   no machine in it; the machine proof is only `Sim`.

What is not proposed: a separation logic (that is `hih-memory`'s), a Hoare
logic over FunctionIR (the logic is at machine code; IRs lower into it), and
kernel coinduction (not needed: §7).

## 1. The issue's three questions

**1. One step relation with derived rules, or a structured code tree with
Hoare rules?** Both, at different layers, and the split is the one the
library already found. The machine has one step relation (`LinuxStep`).
Above it is not a structured (nested `if`/`while`) tree but the *labelled*
program `Prog`, because native control flow is jumps to labels and the
structured shapes were what made `ExecuteStructured` and `AccessBranch`
weaker than the code they described. Rules are not stated per shape: one
`Wp` computes the obligation of any run of items, and the only rules proved
by hand are `wp_sound`, `loop_at` and the item contracts' composition. The
"R1 → R4 was incremental because of depth and `let` limits" warning still
holds and shapes §8: the wp is a computed type over item structure only, the
caller names every witness, and each loop's obligation is its own lemma.

**2. Do processes become FunctionIR regions with state edges?** Not as part
of this milestone. Processes stay `Prog` programs written in Heather
(`docs/native-straight-runs-design.md`; the layout moved out of Rust in PR
#71), and their proofs move onto the logic. FunctionIR keeps lowering pure
regions; its output enters a program as `Proved` items whose contract is
the lowering's certificate (§4.2). State edges in FunctionIR (a world token,
which is uniqueness threading as an IR construct, `effects-direction`'s
first leaning) are the natural *source* of `Syscall` items when a pass
lowers effectful code, and that is `hih-passes`' work, with this logic as
its target. Nothing here forecloses it.

**3. Is `ir_v1`/certgen retired onto FunctionIR?** Not decided here: the
logic does not touch `ir_v1`. The lean is to retire it when `hih-passes`
picks one source IR, and the decision is filed there
(`issues/ir-v1-retirement.md`).

## 2. Specifications

### 2.1 Linux's events as a container

`LinuxEvent` today is a call with its answer in one constructor. Split it:

```heather
inductive LinuxCmd {
    ReadCmd(fd: BitVec(64), max: Nat),
    WriteCmd(fd: BitVec(64), bytes: List<BitVec(8)>),
    OpenCmd(path: List<BitVec(8)>),
    CloseCmd(fd: BitVec(64)),
    StatCmd(target: StatTarget),
}
inductive LinuxAns { Read(r: ReadResult), Write(w: WriteResult), Open(o: OpenResult), Close(c: CloseResult), Stat(s: StatResult) }
fn Answers(c: LinuxCmd, a: LinuxAns) → Type   // the answer fits the call: a read's bytes are at most `max`, an errno is 1..4095, …
```

`Answers` is a predicate rather than a dependent `Resp(c)` so that one
answer type serves every call and a history is a plain `List<LinuxAns>`;
the container `(LinuxCmd, λ c => Σ a. Answers(c, a))` is the same object.
Exit is not a command: it ends a run, as `Ret` ends a tree (§2.2). The
`read` command names `max` (the request's RDX) because the answer's bound
depends on it; a spec that does not care about the buffer size is the
abstraction question of §10.

What Linux leaves that the program cannot observe through the trace (RCX,
R11, a failed read's junk bytes) is not an answer. The machine rule
quantifies over it, as `LinuxRuns` does today.

### 2.2 Specs as coalgebras

```heather
inductive Move<Q> {
    Exit(status: BitVec(64)),
    Call(c: LinuxCmd, k: LinuxAns → Q),
    Cut,                          // no obligation: a fuel-cut tree's leaf (§7)
}
record Spec<Q> { next: Q → Move<Q> }
```

A spec is a state type `Q` and a step. `k` is a function field, but not a
recursive one (`Q` is a parameter), so the surface writes it today; and `Q`
is a parameter, not a field, so `Spec<Q>` is at `Q`'s level. A hand-written
spec picks `Q` to be what the program remembers: the stream filter's is
the filter state and the output still to write; `wc`'s is the operands left,
the counts so far and the current descriptor.

`Cut` is there for one client, the interaction-tree bridge (§7). Hand
written specs never use it, and `Sim` at `Cut` is `True`, so a claim over a
spec with no `Cut` reachable says everything.

### 2.3 Histories, traces, and the judgment

```heather
// The answers a run gets, in order; a valid history is one the spec allows
// and that ends at the spec's exit.
fn Valid<Q>(spec: Spec<Q>, q: Q, h: List<LinuxAns>) → Type      // by recursion on h
fn trace<Q>(spec: Spec<Q>, q: Q, h: List<LinuxAns>) → List<LinuxEvent>   // calls zipped with answers, then the exit

// From `s`, the machine meets the spec along history `h`: Linux steps to a
// syscall whose request is the spec's call (or exit), and for every junk,
// RCX and R11 Linux leaves, the state after the answer meets `k(a)` along
// the rest. By recursion on `h`, as `LinuxRuns` is on its events.
fn RunsAs<M, Q>(io: LinuxIo<M>, spec: Spec<Q>, q: Q, h: List<LinuxAns>) → MachineState<M> → Type

// The judgment: every valid history.
fn Sim<M, Q>(io: LinuxIo<M>, spec: Spec<Q>, q: Q) → MachineState<M> → Type {
    λ s => (h: List<LinuxAns>) → Valid(spec, q, h) → RunsAs(io, spec, q, h, s)
}
```

The request a call makes is stated once per command (`Requests(io, s, c)`:
RAX the call's number, RDI the descriptor, RDX the length, the write's
bytes at RSI by `LinuxWritesFrom`, …), and the state after an answer once
(`answered(io, s, c, a, junk, rcx, r11)`, the existing
`linux_read_return`/`linux_write_return`/… by cases). These are
`LinuxRuns`' arms, factored so that the wp's syscall arm (§5) and
`RunsAs` read the same definitions.

`Sim(io, spec, q)` is closed backward under `LinuxSteps` (it is a
`StepsBack` goal), so everything `Stretch` does with its `goal` it does with
`Sim`.

A program's claim is `Sim(io_linux(), spec, q0)(io_initial(file, page, gprs,
flags))` for every page, registers and flags.

### 2.4 The bridge to today's claims

```heather
theorem runs_as_linux_runs<M, Q>(…): RunsAs(io, spec, q, h, s) → LinuxRuns(io, trace(spec, q, h), s)
theorem linux_runs_runs_as<M, Q>(…): LinuxRuns(io, trace(spec, q, h), s) → RunsAs(io, spec, q, h, s)
```

Both by recursion on `h`; the arms match because `RunsAs` is `LinuxRuns`'
arms factored. With them:

- every existing claim is an instance: `filter_events(shape, steps, ending,
  tail)` is `trace(filter_spec(shape), q0, h)` for the history that
  `steps`/`ending` encode (a lemma per process, by recursion on the steps),
  so migration can go one process at a time and old and new proofs can feed
  each other;
- `linux_runs_every` (determinism) applies to `Sim` claims unchanged: any
  run from the start that got answers `h` produced `trace(spec, q0, h)`.

### 2.5 Observable facts move to the spec

`filter_prints` today proves `stdout = spec(stdin)` from the claim's event
list. Under this design it is a lemma about `trace(filter_spec(step), q0,
h)` alone: what the spec writes to descriptor 1, given what it read from
descriptor 0. No machine state, no code, no layout appears in it, so it is
proved once per *spec*, reused by every compilation of it, and is exactly
the statement an interaction-tree program would make about its own traces.

## 3. One machine

| Today | Becomes |
| --- | --- |
| `FetchedStep`, `StoreStep`, `LinuxStep`, `LinuxSteps` | The machine. `LinuxStep` is the one step; `FetchedOrStore` (step_forms), its duplicate, goes. |
| `LinuxSyscallAt`, the `linux_runs_*` intro lemmas | The syscall boundary of `RunsAs`, stated once (`Requests`, `answered`); the intro lemmas take `LinuxSteps` uniformly. |
| `ExecuteBlock` / `execute_block_normal` | The semantics of the `Block` item; `block_fetched` is a lemma into steps. No client states `ExecuteBlock`. |
| `ExecuteStructured`, `StructuredCode`, `Computes` | A generator's certificate *inside* a `Proved` item's contract (§4.2). Not a judgment a program is stated in. |
| `ExecuteAccess`, `AccessFragment`, `AccessBranch` | Retired: the loop generator emits `Prog` items and `Proved` steps. |
| `ExecuteFetchedBlock`, `LinuxFetchedTrace`, the `Linked*` family | Deleted (the older generation the review named, §2.4). |
| `Runs` (elf64_runs) | A triple defined from `Wp`, kept as notation for the few places a chain is cheaper (the spill's slots). |
| `syscall_bytes` / `linux_syscall_bytes`, the conditional's three byte spellings | One each. |

The machine is parametric in the memory (`LinuxIo<M>`); `IoMemory` is the
profile every program uses today, and `hih-memory-model`'s byte memory is
another `M` (§5.4).

The canonical ISA model (`issues/x86-64-machine-model.md`) is below this
layer: today `FetchedStep` covers the emitted subset (`EmittedInstruction`).
When the canonical decoder and `Execute` replace that subset, `LinuxStep`'s
fetched half is restated over them and nothing above the machine changes.

## 4. One code tree

### 4.1 Items

`Asm` keeps its items: `Block`, `Load`, `Store`, `LoadByte`, `StoreByte`,
`Jcc`, `Jmp`, and the byte-level ones (`Code`, `Piece`, `Refer`, `Hole`). It
gains two:

- `Syscall`: two bytes, `0F 05`, with a semantics the wp can read (it is
  `Code(syscall_bytes())` today, which the wp cannot).
- `Proved(bytes, len, measured, contract)`: code with a contract, below.

`Code`, `Piece`, `Refer` and `Hole` keep their place in layout, and their wp
stays `False`: they are bytes without a meaning, and a program that wants to
run through one states it as a `Proved` item instead. Labels, `then`,
`asm_resident`, `asm_jump` and landing by evaluation are unchanged: they are
the "labelled edges" the milestone asks for, and they already live in
Heather.

### 4.2 Contracts: how proved code enters

```heather
// Code that runs from any placement: from a state at its start meeting `pre`,
// steps reach its end, where `post` relates the end state to the start.
record Contract<M>(io: LinuxIo<M>, bytes: List<BitVec(8)>) {
    pre: MachineState<M> → Type,
    post: MachineState<M> → MachineState<M> → Type,
    runs: (at: BitVec(64)) → (s: MachineState<M>) → s.rip = at → CodeResident(io.fetch, s.memory, bytes, at) → pre(s) →
        Exists(λ e => LinuxSteps(io, s, e) ∧ (e.rip = next_rip(at, bytes.len()) ∧ post(s, e))),
}
```

A contract is the triple the review's R3 named as "the body contract … the
Hoare triple such a tree would have". It covers the three ways proved code
enters a program today, through one interface:

- a generated pure step (`Computes`: output register equals `f(inputs)`,
  scratch clobbered, the rest kept, which is a relational `post`);
- a library piece placed anywhere (the read head, the failure tail's
  straight part, the formatter);
- a called procedure with its call summary (`docs/x86-64-call-summaries.md`),
  whose `post` is the summary.

The relational `post` binds the end state as a variable, which is the
"bind the end state" rule (`docs/native-runs-design.md`, "Consuming a run")
built in: the wp hands the caller `e` and `post(s, e)`, never a projection
out of a proof.

v1 contracts are syscall-free. Library code that makes calls (the write
loop, the read head with its retry) is either items in the program, or a
phase lemma ending in `Sim` and reached at a leaf, as today. A contract
whose post is itself a `Sim` (a procedure that does I/O) is the natural
next step, left until a client wants it.

## 5. One weakest precondition

### 5.1 What it computes

`Stretch` and `Straight` are already weakest preconditions: functions from
items and a continuation to a type, proved sound once, with the obligations
read by evaluation. They differ in the memory they carry (the page, or the
page and a frame of slots) and both stop at syscalls. `Wp` is them
generalised:

```heather
// What running the `n` items ending at label `l` requires, from spec
// position `q`, view `v` and state `s`, given what holds where they end.
fn Wp<M, V, Q>(io: LinuxIo<M>, view: View<M, V>, spec: Spec<Q>, origin: BitVec(64), labels: Nat → Nat,
    l: Prog, n: Nat, post: Bool → Q → V → MachineState<M> → Type) → Q → V → MachineState<M> → Type
```

Per item, with `then` the rest:

| Item | Obligation |
| --- | --- |
| `Block(is)` | `then(q, v, execute_block_normal(is, s))` |
| `Load`, `LoadByte` | the view's load arm: names the value and address, then `then` at the load's result |
| `Store`, `StoreByte` | the view's store arm: names the place, then `then` at the new view and the store's result |
| `Jcc(cc, t)` | `(flag = True → leaf at t) ∧ (flag = False → then(…))`, as now |
| `Jmp(t)` | the leaf at `t` |
| `Proved(…, c)` | `c.pre(s) ∧ ((e) → c.post(s, e) → then(q, v', e))` with `v'` the view's frame of `e` |
| `Syscall` | by `spec.next(q)`: `Exit(st)`: the exit request; `Call(cmd, k)`: `Requests(io, s, cmd) ∧ ((a) → Answers(cmd, a) → (junk, rcx, r11) → then(k(a), v', answered(…)))` with the passed flag set; `Cut`: `True` |
| `Code`, `Piece`, `Refer`, `Hole` | `False` |

Two things are new beside the syscall arm:

- **The spec position `q` rides beside the state.** Items that make no call
  pass it through untouched. A syscall arm computes `spec.next(q)`, which
  reduces whenever the spec's step does not case on data the invariant
  leaves abstract (a filter's next call is a read whatever it has seen; a
  write's bytes are a function of `q`). Where it is stuck, the caller cases
  on `q` in an ordinary lemma first, as `dash_test` does for the byte
  (`docs/native-straight-runs-design.md`, "Where a stretch forks on data").
- **A `passed` flag** says whether the path to this point went through a
  syscall. It is `False` at the start and set by the syscall arm, and the
  leaf receives it. The flag is a function of *which items the path
  crossed*, never of data, so it evaluates away; its only reader is
  `loop_at` (§6).

### 5.2 Memory views

A view is how a program sees its memory between items: `V` and a relation
`holds: V → M → Type`, with the load and store arms and their soundness
lemmas. The two that exist:

- **page** (`Stretch`): `V` is the page's bytes, `holds(page, m)` is `m =
  IoMemory(file, page)`, byte stores name an offset (`PageThen`);
- **frame** (`Straight`): `V` is the page and the slots, `holds` is
  `Framed(file, page, vars)`, word loads and stores name a slot (`SlotThen`).

`hih-memory-model` adds a third over its byte memory, with access outcomes
explicit in the arms (§5.4). The view is a record of transparent functions;
the risk that the elaborator now meets `view.store_arm(…)` instead of the
arm itself is the first thing the implementing round probes (§8).

### 5.3 Soundness, once

```heather
theorem wp_sound(…, back: wp leaves imply Sim, held: Wp(…)(q, v, s), rip, holds: view.holds(v, s.memory)): Sim(io, spec, q)(s)
```

stated per history underneath (`wp_runs`): from `Wp(…, post)(q, v, s)`
and a valid history `h`, `RunsAs(q, h, s)` follows from `post` at every
leaf, at the leaf's own position `q'` and remaining history `h'`, where
`h' = h` when the path passed no syscall and `h'` is shorter when it passed
one. That per-history form is what `loop_at`'s induction uses.

The existing `stretch_runs`, `straight_runs` and `runs_*` rules become
instances (or are deleted where a caller moves to `Wp`).

### 5.4 Memory

The logic adds no memory assumption of its own. A store arm carries the
access premise (`PageThen` is the page's `writable` today), and a view over
`hih-memory-model`'s memory will carry its explicit outcomes the same way;
a rejected access is a `False` arm, not a silent update. Footprints and
framing across calls are `issues/x86-call-memory-footprints.md`'s; a
separation-style assertion language over the byte memory is
`hih-memory`'s, and plugs in as a view.

## 6. Loops: one rule, measured by the history

Every loop in the native code today is a hand induction: `eof_from` over
the chunks, `filter_loop` over the bytes left, the write loop over short
writes, the operand loop over the operands. Each restates the same
argument: from an invariant at a label, one pass of the body comes back to
the label with the invariant, or leaves.

```heather
// An invariant at label `l`, with a ghost variant `w`.
theorem loop_at<M, V, Q>(…, l: Prog, inv: Nat → Q → V → MachineState<M> → Type,
    body: (w: Nat) → (q, v, s) → inv(w, q, v, s) →
        Wp(…, from l …, λ passed q' v' s' =>
            Either(Back(passed, w, inv, q', v', s'),     // at l again, with the invariant at some w', and passed ∨ w' < w
                   Sim(io, spec, q')(s')))               // or left the loop, the rest of the process
        (q, v, s)):
    (w, q, v, s) → inv(w, q, v, s) → Sim(io, spec, q)(s)
```

Proved once, by induction on the history and then the variant
(lexicographic on `(h.len(), w)`): a pass that went through a syscall
consumed an answer, so the history is shorter; a pass that went through
none must have lowered the variant. The two cases the library has are both
instances:

- **I/O loops** (read until end of file, the write loop over short writes)
  need no variant at all: every pass makes a call. The write loop's
  termination, which today rests on the `WriteStep` list being finite, is
  the history being finite. A zero-byte write (Linux may answer `Wrote(0)`)
  is not a special case.
- **Pure loops** (the filter's byte loop, a scan) take the bytes left as
  the variant, and their back edge never sets `passed`.

A loop nested in another's body is `loop_at` inside the outer body's
obligation, at a leaf; there is no global table of cut points. The
multi-label form (several invariants, one per cut point of an irreducible
graph) is not needed by any program and is left out.

This is where most of the process libraries' bulk goes: `EofProcess`,
`EofSteps`/`EofEnd`, the history encodings and their per-process event
functions (`eof_run`, `filter_events`) are replaced by the spec and one
`loop_at`. What stays per program is the invariant and the body's
obligation, which is the program's actual idea.

## 7. Meeting interaction trees (`it-native`)

The logic is built so the tree library adds a lemma and nothing else.
Assumed from `issues/interaction-trees-container-model.md`: only that a tree
is an inductive (fuel-cut, `W`-lowered) tree over container events with
`Ret`, `Tau`, `Vis` and a `Cut` leaf, and that its trace set is
`is_trace_of`.

- **A tree is a spec.** `tree_spec: Spec<Tree>` with `next(t)` stripping
  `Tau`s by structural recursion (a fuel-cut tree is well-founded, so this
  terminates) and mapping `Vis(c, k)` to `Call(c, k)`, `Ret(st)` to
  `Exit(st)`, `Cut` to `Cut`. Events are `LinuxCmd`/`LinuxAns` directly, or
  through a container morphism when the tree speaks a smaller signature.
- **Refinement is a lemma**: `Sim(io, tree_spec, approx(n, t))(start)` for
  every `n` gives that every machine run's trace is a trace of `t`, through
  `trace(tree_spec, …) = is_trace_of` (by recursion on the history) and
  determinism. At `Cut` the claim says nothing, which is the fit doc's
  §4: finite traces, every one reached at some fuel; liveness is what is
  lost, and no native claim states it today.
- **No re-founding**: hand-written coalgebra specs keep working, and a
  program whose spec is later given as a tree proves `Sim` at `tree_spec`
  the same way. The equation `tree_spec ≅ hand_spec` (bisimilar coalgebras
  have equal `Valid`/`trace`) is a lemma when someone wants it.

The fit doc's §6.1 sketched the trace as "the `is_trace_of` set of a
machine denotation"; this design states the same thing from the other
side (the spec is the tree, the machine simulates it), which keeps the
machine relational and puts no tree inside the kernel's evaluation of a
run.

The effectful author surface (`issues/effects-direction.md`) then has a
target: an effectful Heather program denotes a spec (a coalgebra or a
tree), and compiling it means proving `Sim` of the compiled code at that
spec.

## 8. Cost discipline

The straight-code rounds measured what makes computed obligations dear, and
the design keeps to it (`docs/native-straight-runs-design.md`, "Keep the
computed type structural"; `issues/elab-whnf-copies-straight-continuations.md`):

- **Structural only.** `Wp` reads which constructor, which register, which
  label. Addresses, offsets and landings are `refl` facts or citations by
  the caller; slots, page offsets and answers are named by the caller.
- **The end state is bound**, at every leaf and after every `Proved` item.
- **The elaborator's whnf is the cost**, not the kernel's. `Wp` adds two
  arguments to every continuation (`q`, `passed`) and a view record. The
  first round probes one moved phase (`loop_last`, the filter byte loop)
  against its `Stretch`/`Straight` version with `scripts/perf ab` before
  migrating anything, and specialises the view (two monomorphic wps sharing
  one soundness proof) if the record costs.
- **One lemma per loop body**, never a table of cut points checked as one
  term.
- **No `let`-bound runs**: `loop_at` and `wp_sound` take continuations.

## 9. Rounds

Each round is one PR and one issue, and each lands green with the old
proofs still standing until it moves them. Submilestones of
`hih-program-logic` in `docs/roadmap.md`.

| Round | Submilestone | Issue | Done when |
| --- | --- | --- | --- |
| P1 | `hih-pl-spec` | `native-linux-spec` | `LinuxCmd`/`LinuxAns`, `Spec`, `Valid`, `trace`, `RunsAs`, `Sim`, the bridge both ways, and the stream filter's spec with `filter_prints` restated over it. Library only; no program moves. |
| P2 | `hih-pl-wp` | `native-one-wp` | `Wp` with views, `Syscall` and `Proved` items, and `wp_sound`; `Stretch` and `Straight` are instances; one phase each moved and probed. |
| P3 | `hih-pl-loops` | `native-loop-rule` | `loop_at`, with the filter's byte loop and its read-until-EOF loop on it. |
| P4 | `hih-pl-first-program` | `native-filter-on-program-logic` | The stream filter's claim is `Sim(filter_spec)` end to end, the old claim derived through the bridge, and its process library's hand inductions and history encodings deleted. |
| P5 | `hih-pl-retire` | `native-retire-execution-shapes` | `wc`, `wc -l` and the command on the logic; the five shapes' client judgments and the duplicates of §3 gone; generated pieces enter as `Proved`. The milestone is done. |

P1 is safe to start now and touches only new library files. P2–P3 touch the
native lane (`lib/elf64_*`, `lib/std/arch/x86_64/x86_64_asm.hthr`) and nothing
in the elaborator. P4–P5 also touch the producers in `crates/cli/src/native`
and the native support lists, a shared hotspot, so they should not run
beside another native round.

A tactic is filed with the rounds (`issues/wp-obligation-tactic.md`): the
caller's term against a computed `Wp` is the same shape every time (an
`Exists` per slot, offset or value naming what conversion already knows, a
pair per `Jcc`, a λ per leaf), which is the third-time rule of
`docs/roadmap.md`'s "Tactics everywhere".

## 10. Open questions

1. **Abstract specs.** A spec states `ReadCmd(0, 4096)`: the buffer size is
   the program's choice, visible in its spec. A spec that says "reads stdin
   in chunks of any size" is a container morphism from an abstract
   signature to `LinuxCmd` with a refinement condition on `max`. Wanted
   before a spec is shared by two compilations with different buffers; not
   before.
2. **Contracts that make calls** (§4.2): a procedure whose post is a `Sim`.
   First client: a library write loop called from two places.
3. **Divergence and partial runs** (`issues/linux-syscall-trace-model.md`):
   `Sim` is total (the machine reaches each call). A spec for a server that
   never exits is a `Cut`-free infinite coalgebra, and `Sim` still means
   "every finite history is produced"; what is missing is a claim about a
   run cut off between calls, which the trace issue owns.
4. **Nondeterministic specs** (a spec allowing either of two writes): `Q`
   can carry a choice made by the program, as a ghost answer. No client yet;
   choice trees are `effects-direction`'s if concurrency comes.
5. **Whether `Runs` survives** as notation, or every chain moves to `Wp`.
   Decided by P2's probe.

## 11. How the design meets the principles

- **Logic in Heather.** The wp, its soundness, the loop rule, the layout
  and the landing facts are Heather; Rust producers only assemble the
  program value and name the witnesses.
- **Tactics everywhere.** Obligations are computed types, which a tactic can
  walk (`wp-obligation-tactic`); the routine witnesses are the tactic's.
- **Constructive.** Everything is by recursion and evaluation; no claim
  needs excluded middle, and `Sim` quantifies over histories rather than
  asserting a completed infinite behaviour.
