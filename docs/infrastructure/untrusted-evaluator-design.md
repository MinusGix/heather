# The untrusted evaluator

`crates/run` (`heather-run`) runs closed core terms with their types erased.
It exists because some of what the tools evaluate is never trusted, and the
kernel's evaluator is the wrong machine for that work.

## 1. Why a second evaluator

The kernel's evaluator serves conversion. It keeps a neutral spelling beside
every unfolded call so that two terms can be compared without unfolding, it
evaluates the motive and annotations an eliminator carries, its values are
typed, and everything a query forces lives in the query's arena until the
query ends. A conversion check reads all of that.

A *read* (`function_ir_source::evaluate_numbers`) reads none of it. It wants
the list of numbers a closed program evaluates to: the plan an optimizer walk
found, the bytes a lowering emitted. Run on the kernel's evaluator, a read's
cost is the checker's cost per step times the steps of an interpreter, and
its memory is every value it ever made. The optimizer's walks over one large
function were most of a cold compile for that reason, and the reason a read
of a large function sits at the address-space rail.

The answers of these reads are not trusted in the first place. An optimizer
walk proposes a plan and a checked replayer accepts or refuses it; emitted
bytes are stated as literals in a certificate the kernel checks. So the
evaluator that produces them can be any program at all, and the right one is
an interpreter.

## 2. What it is

- **Erasure** (`Machine::erase`). A core term becomes a `Code`: variables,
  functions and applications, numbers and `elim_Nat`, pairs, sums and `case`,
  tree nodes and their eliminators, calls of definitions. Types, levels,
  universe and context abstractions, equality proofs and `J` are dropped: a
  `J` is its case, a squash is its content. A definition is erased the first
  time it is called, once per run.
- **The machine** (`Machine::eval`). Call by need, as the kernel is: an
  argument, a constructor's field and a recursive answer are each computed
  when first read and once. An eliminator's step runs under the same
  variables core gives it (`elim_Nat`: predecessor and recursive answer; a
  tree: label, children, induction hypothesis). The hypothesis of `Wf` and
  `IWf` is a value that, applied to a position, walks the children tuple and
  eliminates the child found; `W`'s applies the children function. Values
  are reference counted, so a walk holds what is live and not what it has
  done.
- **Numbers.** Core `Nat` functions are recursors, which the kernel runs
  fast by classifying their folds. Here a number is a machine integer and
  the library's arithmetic is named by the caller (`Prims`: `Nat::add`,
  `sub`, `mul`, `half`, `twice`, `low_bit`, `div`, `mod`, `same`, `leb`,
  `BitVec::odd_bit`). One the library recurses through over a whole number
  must be named, or a run nests as deep as the number. A named definition is
  not believed: the first time one is called, its body is run as written on
  a handful of small numbers and compared with the direct operation, and one
  that disagrees is run as written from then on. A two-valued definition's
  answers are the values its own body gave, so the machine never has to know
  how `Bool` is represented.
- **Where it stops.** A form it does not run (codata, quoted code, a
  numeral past its integer width, a declaration without a body), a run past
  its step or nesting bound: `Stuck`, with a reason. It never answers wrongly
  on purpose, and a caller falls back.

## 3. How reads use it

`Reads::numbers_up_to` runs the untrusted machine first and the kernel's
evaluator where it is stuck. `HEATHER_READS=kernel` asks for the kernel's
evaluator only, and `HEATHER_READS=check` runs both and refuses a read they
disagree on, which is how a change to either is tested against the other.
`HEATHER_READ_TRACE=1` reports each read's steps and time on whichever ran
it, and says why a read was left to the kernel.

### 3.1 A session: one machine for a compile's reads

`compile-x86` reads hundreds of programs from one forked elaborator that
only ever defines more modules (`native::answers::Reading`). It keeps one
machine for all of them (`heather_run::Session`, `RunSession` in the
elaborator): what was erased stays erased, and a definition of no arguments
that one read evaluated is a value the next reads have. Constants are
positions from the start of Ψ, so what the machine kept reads the same as Ψ
grows.

That is what lets the optimizer's stages be values. A stage used to end by
spelling the function it made as text, and the next stage began by
elaborating that text; the elaboration was a fifth of a large compile. Now a
stage's module says

    fn stage_found() → Option<Found> { before().search }
    fn stage() → Function { found_made(stage_found(), before()) }

and the next stage's `before` is `stage`. The driver reads one small answer
(`found_kind`: nothing found, the function unchanged, or a new one) and reads
the spelling only of the stages the certificate keeps. The read's own name
is forgotten after each read (`Machine::forget`), so only the stage values
stay.

The kernel's evaluator has no such memory: a read it is left with evaluates
the whole chain of stages before it. Its fallback is therefore for the rare
stuck read, and a compile whose reads are mostly stuck is slower than it was
with literals; `HEATHER_READ_TRACE=1` shows each one and why.

## 4. Tactic and generator runs

A `by` tactic and a `generate`'s generator are `Tac` trees the host reads
one request at a time (docs/metaprogramming/host-elaboration-interface-design.md):
it calls the protocol's `host_*` functions on the tree to read the request,
answers it, and calls `host_resume` with the answer. Those calls are
untrusted in the same way as a read: whatever a tree asks, the host grants or
refuses, and whatever it ends with is elaborated and kernel-checked. So a run
reads its tree on this machine (`host.rs`, `Host::speak`).

- **One reading, two evaluators.** The protocol's reading is written once
  over a small trait (`Values`: call a `host_*` function, make a numeral, read
  one); `KernelValues` is the kernel's value domain and `MachineValues` this
  machine.
- **Its own thread.** The machine runs on a thread of its own stack
  (`with_machine`), and the elaborator stays on its thread, so the two speak
  over channels: the machine sends each step, and asks for a protocol
  function's position by name the first time it calls it; the host sends
  answers.
- **The kernel behind it.** Each step may spend a bounded number of machine
  steps. Where the machine fails (a form it does not run, that bound, its
  nesting bound), the kernel's evaluator is started on the same tree and
  handed every answer given so far, which brings it to the same step, and
  the run continues there. A failure costs the run again on the kernel's
  evaluator, never a different outcome. `HEATHER_READ_TRACE=1` reports each
  such hand-over.
- `HEATHER_READS=kernel` runs trees on the kernel's evaluator only, and
  `HEATHER_READS=check` runs both in step and refuses a run whose steps
  differ, as for reads.

What it bought: the generator's own evaluation was most of the kernel steps a
`runtime fn` declaration took (about two thirds of `Sha256::rounds`'s); what
is left is the gate's and the host's own work, which is then most of such a
declaration's time (issues/runtime-generator-link-cost.md).

## 5. What it does not change

No checked statement depends on this crate. The kernel still evaluates
everything in a certificate, every `refl`, every tactic's proof term (a
tactic's run only proposes it). If the machine were wrong, an optimizer
would propose a plan the replayer refuses, a certificate would state bytes
the kernel rejects, or a tactic would propose a proof the kernel refuses: a
failed check, and never a wrong accepted one.

## 6. Left

- The machine is a tree walker over linked environments. Resolved variable
  slots, unboxed numbers in environments and a flat code array are the usual
  next steps if its own speed starts to matter.
- Once the compiler compiles the library's own data structures, the walks
  can be compiled code and this crate retires.
