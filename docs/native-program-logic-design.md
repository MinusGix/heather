# Native code, rebuilt: interaction trees, one program logic, a compiler proved once

Status: **design, revised 2026-10-21 after Minus's review; not implemented.**
§10 records his answers to its open questions (2026-10-21, second review).
Milestone `hih-program-logic` (`docs/roadmap.md`). This doc replaces the open
question of `issues/native-one-program-logic.md` and §1 answers its three
questions.

The first draft (2026-10-20) proposed moving the existing native programs onto
one program logic, one program at a time. Minus's review changed the direction:

> the native work got kinda funky, where work that was more temporary testing
> ossified into real setups. We shouldn't be having to do huge work, our work
> should instead be intelligent, like proving compiler correct translation in
> a general sense. My leaning is burning a lot of it, waiting for the full tree
> library, and rebuilding from the ashes once we can.

So this design does three things:

1. It says what the native stack is **for** from now on: a compiler from an
   effectful source to x86-64 whose correctness is **one theorem proved once**,
   stated against interaction trees. Per-program machine proofs stop being how
   programs are proved (§2).
2. It says what **burns** now, what burns once the compiler replaces it, and
   what stays as the foundation (§3).
3. It keeps the program logic of the first draft, but as the **target side of
   that theorem**: the tools a compiler proof uses for each construct's code,
   and for the few runtime pieces written by hand (§4–§7). It is built on the
   tree library, which it waits for (§8).

## 1. The issue's three questions

**1. One step relation with derived rules, or a structured code tree with
Hoare rules?** One step relation at the bottom (`LinuxStep`: a fetched
instruction or a store, between syscalls). Above it, the labelled program
`Prog` of `Asm` items, with one computed weakest precondition and one loop
rule. No per-shape judgments: the five "this code runs" shapes go (§3).

**2. Do processes become FunctionIR regions with state edges?** Processes as
hand-written x86 libraries go away entirely. Programs are written in an
effectful source whose meaning is an interaction tree (§2.2). Whether that
source is FunctionIR grown with effect nodes or a separate layer over
FunctionIR's pure regions is the source round's first decision (§9, S3);
the lean is a small tree-shaped layer whose leaves are FunctionIR regions.

**3. Is `ir_v1`/certgen retired onto FunctionIR?** Yes, with the second burn
(§3.2). `issues/ir-v1-retirement.md` owns the timing.

## 2. Where native code is going

### 2.1 What went wrong

The stack was built program by program, each one a test of the layer below,
and each test became infrastructure:

- **Every program is proved at register level, by hand.** `wc`, `wc -l`, `tr`
  and the command are about 15k lines of process libraries (`lib/elf64_*`),
  3.2k of them the command written in assembly. Each new program meant new
  process proofs, then a refactor round to share them.
- **The checker pays per program.** A certificate is emitted and kernel-checked
  for every program, so certificate cost grows with code size, and native
  tests sit at the CPU rail.
- **Specs were never named.** `EofStep`/`EofEnd`, `eof_run` and
  `filter_events` are a spec language for "read until end of file, write as
  you go": interaction trees, written as history encodings, once per process.
- **Five execution relations** for overlapping code shapes, each a stage of
  the stack's history (`docs/native-architecture-review.md` §2.4).
- **Performance workarounds became library design.** Much of `Straight`'s
  shape (the caller names every slot, landings spelled in the stretch's own
  form) works around the elaborator's whnf
  (`issues/elab-whnf-copies-straight-continuations.md`).

### 2.2 The target shape

```
source program  ──denotes──▶  interaction tree over Linux events   (spec)
      │                                  ▲
   compile (a Heather fn)                │  Sim: the machine produces
      ▼                                  │  exactly the tree's traces
x86-64 bytes in an ELF  ──runs as──▶  LinuxStep between syscalls
```

- **Meaning.** A program denotes a tree over a container of Linux calls and
  answers (§4). Facts users care about (`stdout = spec(stdin)`) are proved
  about the tree, with no machine in sight.
- **Compilation** is a Heather function from the source to `Prog`
  (labelled `Asm` items), assembled by the existing label assembler.
- **Correctness** is one theorem, proved once by induction on the source:
  for a well-formed source `p`, the assembled image of `compile(p)` satisfies
  `Sim` at `denote(p)` (§5). Each source construct contributes one lemma
  about the code it emits, proved with the program logic (§6, §7).
- **Per-program cost** is running `compile` and instantiating the theorem.
  The first version runs `compile` by kernel evaluation (`refl` on the bytes),
  which costs what evaluating the compiler costs and no proof per program;
  running it natively is `hih-self`'s business later.
- **Logic in Heather.** The compiler, its theorem, the assembler and layout
  are Heather. Rust keeps parsing, the ELF writer and the encoder as
  untrusted plumbing, and is checked against Heather's encoding where they
  overlap.

This is CompCert's shape (a simulation proved per pass), at a much smaller
scale, with interaction trees for the observable behaviour as in Xia et al.
§5 (`docs/interaction-trees-fit.md` §6.2). It is translation proved once, not
translation validated per program.

## 3. What burns, what stays

### 3.1 Burn now (B1): the process stack

These exist only to prove `wc`, `wc -l`, `tr`/the filters and the command by
hand. Nothing else depends on them, and the rebuild does not reuse them.

| Where | What |
| --- | --- |
| `lib/` | every `elf64_*` module except `elf64`, `elf64_load`, `elf64_io` (which `x86_64_fetched_code` imports) and `elf64_calls` (the call examples' library, B2); `command_program`, `filter_program`, `decimal_line`, `field_line` |
| `crates/cli/src/native/` | the read-loop, read-filter and command producers (`read_loop.rs`, `read_filter.rs`, `read_command.rs`, `evaluate.rs`), and the `Filter` and `Command` profiles of `build-x86`, which now builds only functions of two `--arg`s |
| `crates/elab/src/function_ir_source/` | `filter_step.rs`, the filter step generator |
| tests | `native_wc`, `native_tr`, `native_filter`, `native_read_loop`; the elab process tests (`*_process.rs`, `*_refusals.rs` of the process layers, `command_refusals`, `field_line_*format`, `filter_step_generation`, `semantic_command_warmup` and its `command_prefix` support); the command warm-ups in `scripts/test`; the `wc` builds in `scripts/perf` |
| `examples/x86-native/` | `wc.hthr`, `wc_l.hthr`, `tr.hthr`, `tr_s.hthr`, `tr_d.hthr` |
| docs, issues | design docs of the burned layers get a one-line "burned in B1, see …" header, not deletion; their open issues close as not planned, with a link |

**Salvaged, not burned:** the pure specs. `decimal`, `decimal_line`,
`pad_left`, `places` and their lemmas, and `three_fields_line` (`wc`'s line on
a pipe) are `lib/std/decimal.hthr`; the counting folds' lemmas
(`fold_counts_filtered`, `fold_counts_len`, `fold_counts_runs`) moved into
`stream_filter`, which already held the filter's fold `filter_state`.
`stream_filter` and `filter_step_piece` stay (the structured generator's
filtered publication imports the latter, so it goes with B2), and with
`x86_64_asm` and the decimal spec they are checked by
`crates/elab/tests/native_foundation.rs`, since no program imports them until
the compiler does. `field_is_decimal` (the 7-column machine formatter's
equation) was a fact about a burned formatter and went with it.

**Kept for B2, not B1:** `linux_x86_64_fetch` and `x86_64_fetch_block` (first
listed here) are on the call profile's path: `build-x86 --callee` imports
both. So are `order.rs` and `support.rs`.

Before the burn, the last commit with the stack is tagged (`native-v0`, at
`189659d`), so the executables and proofs stay findable.

### 3.2 Burn when the compiler replaces it (B2): per-function certificates

The pure-function path (FunctionIR → x86 with a certificate per function,
`examples/x86-native/{branches,calls,…}`) still works and still exercises the
ISA model. It burns when the verified pure lowering (§9, S4) compiles the same
examples:

- `crates/elab/src/function_ir_x86_lower*`, `heather_emit.rs`, the
  `function_ir_source` publication and loop generators;
- `lib/function_ir_x86*`, `function_ir_loop_x86`, `function_ir_loop_trace`;
- `x86_64_structured_block`, `x86_64_access_code`, `x86_64_access_memory`,
  `x86_64_control_block`, `x86_64_control_flow`, the call composition
  modules (`x86_64_calls`, `x86_64_call_frame`, `x86_64_call_summary`, used by
  the CLI's call examples), and the `ExecuteBlock` family beyond
  `execute_block_normal`. `x86_64_fetched_code` imports the structured and
  access modules today, so B2 first moves `FetchedStep`'s dependencies onto
  the instruction forms alone;
- `elf64_calls`, `linux_x86_64_fetch`, `x86_64_fetch_block`, `filter_step_piece`,
  and in the CLI `order.rs`, `support.rs` and the call generator;
- in the structured generator, what only the burned process layers called
  and B1 left without a caller: `generate_elaborated_piece_x86` (a
  process piece's `Computes` contract) and the `filtered` publication;
- `ir_v1`, certgen and their tests (`issues/ir-v1-retirement.md`);
- not before their replacements exist: loops have no verified lowering yet
  (`issues/function-ir-lowering-loops.md`), and what proves a reflected
  region means its source function once the publication goes is
  `issues/function-ir-source-denotation-after-b2.md`;
- the remaining `native_*` CLI tests, replaced by the same programs through
  the compiler.

### 3.3 Stays: the foundation

- The ISA model and its byte boundary: `x86_64`, `x86_64_fetch`,
  `x86_64_data_read`, `x86_64_store`, `x86_64_fetched_code`,
  `x86_64_step_forms`, `x86_64_block`'s `execute_block_normal`
  (`issues/x86-64-machine-model.md` continues).
- The label assembler, `x86_64_asm` with `x86_64_layout` under it:
  codegen's data structure and its layout-by-evaluation, used by the
  compiler. `x86_64_asm_runs` (S4 round 2) holds its pure fetched-run
  lemmas: a block, a JMP and a two-armed branch, each proved over any
  program checked by `Prog::laid_out`. `x86_64_stack` (S4 round 3) adds
  the stack forms (frame slots, CALL, RET) and a process's `Stack` laws;
  `x86_64_stack_runs` adds state-level runs over them and a callee's
  contract; `x86_64_kept` holds what a block leaves.
- The Linux model: `linux_x86_64_io` (re-founded on the event container in
  S1), `linux_x86_64_determinism`, `linux_x86_64_entry`.
- ELF: `elf64`, `elf64_load`, and the Rust writer.
- FunctionIR's pure semantics (`function_ir`, `function_ir_loop`,
  `function_ir_certificates`), the source for pure regions.

## 4. Specifications are trees

Assumed from the tree library (`issues/interaction-trees-container-model.md`,
milestones `it-core`, `it-refinement`): container events, fuel-cut trees
with `Ret`, `Vis` and a `Cut` leaf, `bind`/`iter`, `is_trace_of`, and the
depth-indexed equivalence for laws through `Vis`.

**Linux's events as a container.** Split `LinuxEvent` into the call and the
answer:

```heather
inductive LinuxCmd { ReadCmd(fd, max), WriteCmd(fd, bytes), OpenCmd(path), CloseCmd(fd), StatCmd(target) }
inductive LinuxAns { Read(ReadResult), Write(WriteResult), Open(OpenResult), Close(CloseResult), Stat(StatResult) }
fn Answers(c: LinuxCmd, a: LinuxAns) → Type   // the answer fits the call: bytes ≤ max, errno 1..4095, …
```

Exit is the tree's `Ret`. What Linux leaves that no trace observes (RCX, R11,
a failed read's junk) is not an answer; the machine side quantifies over it,
as `LinuxRuns` does today.

**A spec is a tree** `t : ITree(Linux, BitVec(64))`, written with `bind` and
`iter`. `tr`'s spec is `iter` over "read a chunk; if empty, `Ret(0)`; else
write the fold's output", with the fold a pure function.

**What the logic evaluates is the tree's observation**, not the tree:
`next(t) : Exit(status) | Call(c, k) | Cut`, stripping `Tau`s by structural
recursion (a fuel-cut tree is well-founded). The fit doc's warning that
left-nested binds are quadratic to observe (§5 there) is why: the compiler
proof meets `next` of a *source construct's* denotation, one constructor at
a time, never a deep bind chain unfolded by the elaborator.

## 5. The judgment: `Sim`

```heather
// From `s`, along answers `h`, the machine meets the tree: Linux steps to a
// syscall whose request is the tree's call (or exit), and for every junk,
// RCX and R11, the state after answer `a` meets `k(a)` along the rest.
fn RunsAs<M>(io: LinuxIo<M>, t: Tree, h: List<LinuxAns>) → MachineState<M> → Type   // recursion on h
fn Sim<M>(io: LinuxIo<M>, t: Tree) → MachineState<M> → Type {
    λ s => (h: List<LinuxAns>) → Valid(t, h) → RunsAs(io, t, h, s)
}
```

- `Valid(t, h)`: every answer fits its call, and `h` ends where the tree
  returns. At `Cut`, `RunsAs` is `True`: a claim says nothing past the fuel,
  so the statement is "for every `n`, `Sim` at `approx(n, t)`", which covers
  every finite trace (fit doc §4). Liveness is what is lost; no native claim
  states it.
- `RunsAs` is `LinuxRuns`' arms factored (`Requests(io, s, c)` for the
  request, `answered(…)` for the state after), and bridged both ways:
  `RunsAs(t, h, s) ↔ LinuxRuns(trace(t, h), s)`. That keeps
  `linux_runs_every` (determinism): with it, `Sim` is trace *equivalence*
  with the tree, not only refinement.
- `Sim(io, t)` is closed backward under `LinuxSteps`.
- `trace(t, h) = is_trace_of`'s trace (by recursion on `h`), so "this code
  refines `t`" (`it-native`) is `Sim` plus that lemma.

The compiler's theorem is `Sim(io_linux(), denote(p))(io_initial(file(p), page,
gprs, flags))` for every page, registers and flags, with `file(p)` the ELF of
`compile(p)`.

## 6. The program logic: target-side tools

The compiler proof needs, for each source construct, a lemma "the code this
construct emits, run from a state where the construct's inputs are in place,
meets the construct's tree". Those lemmas are proved with these tools, once
per construct, not per program.

### 6.1 One computed weakest precondition

`Stretch` and `Straight` are weakest preconditions computed by evaluation and
proved sound once. They stop at syscalls and loops, and they differ only in
the memory they carry. `Wp` generalises them:

```heather
fn Wp<M, V>(io: LinuxIo<M>, view: View<M, V>, origin: BitVec(64), labels: Nat → Nat,
    l: Prog, n: Nat, post: Bool → Tree → V → MachineState<M> → Type) → Tree → V → MachineState<M> → Type
```

| Item | Obligation |
| --- | --- |
| `Block(is)` | `then(t, v, execute_block_normal(is, s))` |
| `Load`, `LoadByte`, `Store`, `StoreByte` | the view's arm: the caller names the value or place; access premises explicit |
| `Jcc(cc, x)` | `(flag = True → leaf at x) ∧ (flag = False → then(…))` |
| `Jmp(x)` | the leaf at `x` |
| `Proved(…, c)` | `c.pre(s) ∧ ((e) → c.post(s, e) → then(t, v', e))` |
| `Syscall` | by `next(t)`: the exit request; or `Requests(io, s, c) ∧ ((a) → Answers(c, a) → (junk…) → then(k(a), v', answered(…)))`, setting `passed`; or `True` at `Cut` |
| `Code`, `Piece`, `Refer`, `Hole` | `False` |

New items: `Syscall` (today it is `Code` bytes the wp cannot read), and
`Proved(bytes, len, measured, contract)`, code entering with a relational
triple (`pre`, `post(before, after)`, placement-independent `runs`). In the
compiler, `Proved` is how a pure FunctionIR region's lowering enters an
effectful construct's code: its contract is the pure lowering's theorem.

Views: the page (`Stretch`'s) and the frame of slots (`Straight`'s) are two
`View<M, V>` records. A view over `hih-memory-model`'s byte memory is a third,
with its access outcomes in the arms; a separation-style footprint is that
milestone's to add, and the view interface should not preclude it. The third
is `DataRegion::buffer_view` (`lib/linux_x86_64_byte_memory.hthr`): a
buffer in a data region of an `X86Profile`, its arms reading and
storing at an index into the buffer.

Proved once: `wp_runs`, per history: from `Wp(…, post)(t, v, s)` and a valid
`h`, `RunsAs(t, h, s)` follows from `post` at each leaf, at the leaf's tree
`t'` and remaining `h'`, with `h' = h` if the path passed no syscall and `h'`
shorter if it passed one. `wp_sound` is its `Sim` form.

### 6.2 One loop rule

```heather
theorem loop_at(…, l: Prog, inv: Nat → Tree → V → MachineState<M> → Type,
    body: (w, t, v, s) → inv(w, t, v, s) →
        Wp(…, from l, λ passed t' v' s' =>
            Either(Back(passed, w, inv, t', v', s'),   // at l, inv at w', and passed ∨ w' < w
                   Sim(io, t')(s')))                    // left the loop
        (t, v, s)):
    (w, t, v, s) → inv(w, t, v, s) → Sim(io, t)(s)
```

Proved once, by induction on the history's length and then the variant. A
pass that made a syscall consumed an answer; a pass that made none lowered
the variant. I/O loops (read until end of file, a write loop over short
writes, including `Wrote(0)`) need no variant; pure loops take what is left.
The compiler's `iter` lemma is one use of it.

### 6.3 Cost discipline

From the straight-code rounds (`docs/native-straight-runs-design.md`, "Keep
the computed type structural"):

- `Wp` reads constructors, registers and labels; numbers are `refl` facts or
  citations; slots, offsets and answers are named by the caller.
- End states are bound at every leaf and after every `Proved` item; no
  `let`-bound runs.
- `Wp` adds two continuation arguments and a view record where the
  elaborator's whnf is already the cost. The first tool round probes that
  with `scripts/perf ab` and specialises (two monomorphic wps, one soundness
  proof) if the record costs.
- Since the compiler proof uses these per construct, over *abstract* inputs,
  the obligations are small and fixed; nothing scales with program size. That
  is the main cost argument for the whole redesign.

### 6.4 As built (round S2)

`lib/linux_x86_64_wp.hthr`; the views it was built with now live on the byte
memory model (`lib/linux_x86_64_byte_memory.hthr`,
`lib/linux_x86_64_image.hthr`); the controls are `crates/elab/tests/linux_wp.rs`. Where the build differs from §6.1–6.2:

- **`Proved(index, bytes, len, measured)` names its contract in a table**
  (`contracts: Nat → Contract`, a parameter of `Wp`), not by a field. A
  contract is a pair of predicates over registers, so a field of type
  `Contract` lifts `Asm` a universe and every `Exists<Prog>`/`List<Asm>` with
  it; Heather's universes are not cumulative. `WpHonest` asks, once per
  program, that each `Proved` item's bytes run as its contract
  (`Contract::Runs`: from the precondition, a fetched run to the item's end,
  memory unchanged, the postcondition). `Syscall` is the two bytes `0f 05`.
- **The post sees a `passed` flag, and the loop invariant a ghost variant
  `w`**, as designed; `LoopPost` is `Back` (at the head, the invariant at
  some `w'`, and `passed ∨ w' < w`) or, on leaving, `Holds(v, memory) →
  Sim(io, t, state)` — leaving is proved from wherever it lands, with the
  view's own holding in hand to start a further `wp_sound`.
- **Jumps land by `wp_reach`**, a Bool over the items checked by evaluation
  (`trivial` at a literal program), which asks each JCC/JMP to land forward
  or back on its label's offset. `laid_out` asks forward only and loops jump
  back; the two should become one (see `issues/asm-landing-both-ways.md`).
- **Views** carry `Holds(v, m)` and four arms: `Word` and `Byte` (the caller
  names the value read), `Stores` (the caller names where it goes and the
  view after it) and `Asks` (what a call asks of memory). `ViewSound` proves
  each arm once against the access model. S2 built two views over the old
  fixed image (`elf64_io`): a page view and a frame view of 32 word slots
  plus the page. Both are gone (issues/io-image-on-byte-model.md): the
  process image is an `X86Memory` of the profile `X86Profile::io()`, the page
  and the frame are data regions of it, and a program sees either through
  `DataRegion::program_view`, the buffer view (`v` is the region's bytes; a
  store is a span of it) with the program's code resident. A word slot is a
  lemma over the buffer (`DataRegion::x86_word_stored`), not a view of its
  own. A view over two regions at once is
  `issues/wp-view-separating-product.md`.
- **Syscall answers** go through `linux_buffer`/`linux_stored`/`linux_left`:
  what Linux leaves in memory on answering is stated once, and the view's
  `Stores` arm is asked for it, so a view sees a read's bytes land.

Cost, from the probe (`--only --timings` on the controls, cached prefix):
the view record is not the cost — the pure loop's pass, over the frame view,
elaborates in about the time its gate takes. The I/O loop's pass, whose
syscall arm checks three answer branches against continuations carrying
`linux_answered`'s state, spends several times its gate in the elaborator's
whnf: the respelling `issues/elab-whnf-copies-straight-continuations.md`
names, now on `Wp`. So no monomorphic specialisation; the lever is that
issue's, and `drain_pass` is its workload now that `Straight` is gone.

## 7. The source and its compiler

Decided in round S3; the constraints the rest of the design puts on it:

- **Denotes trees.** `denote : Source → ITree(Linux, BitVec(64))`, compositional
  (`denote(Seq(a, b)) = bind(denote(a), …)`, `denote(Loop(…)) = iter(…)`).
- **Pure parts are FunctionIR regions**, compiled by the verified pure
  lowering (S4) and entering effectful code as `Proved` items.
- **Calls are explicit nodes** whose arguments are region outputs and whose
  answers are bound for what follows, matching `Vis(c, k)`.
- **The theorem is by induction on the source**, one case per construct,
  each a `Wp`/`loop_at` proof over abstract inputs, glued by `Sim`'s
  backward closure and the `bind` lemma ("code for `a` then code for `b`
  meets `bind(denote(a), denote(b))`").
- **State between calls** (registers, a frame) is the compiler's register
  and frame conventions, stated once as the invariant every construct's
  lemma preserves; this is where `Straight`'s frame view earns its keep.
- **Surface:** an effectful Heather program elaborating to this source is
  `effects-direction`'s question; the source is its target, whatever the
  surface becomes (uniqueness threading denotes the same trees, fit doc §6.5).
  Minus chose a uniqueness-threaded surface that denotes trees (§10, item 5).

## 8. What waits on what

| Needs | Before |
| --- | --- |
| Tier-2 inductives (landed, PR #88) and `tier2-value-parameters` | the tree library with events as a parameter |
| `it-core` (trees, `bind`, `iter`, laws up to depth-indexed equivalence) | S1 |
| `it-refinement` (`is_trace_of`, trace refinement) | S1's refinement lemma; S5 |
| S1 | S2, S3 |
| S2 | S3's construct lemmas |
| S4 (verified pure lowering, `hih-passes`) | S3's `Proved` regions; B2 |

B1 needs nothing and is independent of all of it.

## 9. Rounds

| Round | Submilestone | Issue | Done when |
| --- | --- | --- | --- |
| B1 | (none) | `native-burn-process-stack` | §3.1 deleted, specs salvaged, `native-v0` tagged; suite green without the burned tests. |
| S1 | `hih-pl-spec` | `native-linux-spec` | Linux events as a container, `RunsAs`/`Sim` over trees, the bridge to `LinuxRuns`, refinement lemma, and `tr`'s spec as a tree with its stdout fact. |
| S2 | `hih-pl-wp` | `native-one-wp`, `native-loop-rule` | `Wp` with `Syscall`, `Proved` and views; `wp_sound`; `loop_at`; probed for elaborator cost. |
| S3 | `hih-pl-source` | `native-effect-source-compiler` | The effectful source, `denote`, `compile` in Heather, and the correctness theorem proved once. |
| S4 | (`hih-passes`) | `function-ir-verified-lowering` | FunctionIR's pure regions lowered by a Heather function with its theorem proved once; B2 can start. |
| S5 | `hih-pl-first-program` | `native-first-compiled-program` | `tr` built from its source through the compiler, its claim from the theorem, its stdout fact from its tree; then B2. |

`wp-obligation-tactic` follows S2's obligations; with the compiler proof
over abstract inputs it matters less than in the first draft, and may not be
needed.

## 10. Open questions, and Minus's answers (2026-10-21)

Minus answered these on 2026-10-21, after reading a map of the native
state. His standing rule for the rebuild: **do the ideal version from the
beginning**, since building cruft into a core piece "is part of what caused
us to burn a lot of code".

1. **Abstract specs.** *Decided: abstract from the start.* The read in the
   spec is "a chunk of any size the program allows", not `ReadCmd(fd, max)`
   with the buffer size fixed into a program's meaning. S1 states the
   container that way (the call carries what the program asks for, and the
   answer's length is bounded by it), and specs are written over any chunk
   size. The design above still writes `ReadCmd(fd, max)`; read it as the
   machine-side call, related to the abstract one by the container
   morphism (`EventMap`) S1 defines.
2. **Contracts that make calls**: a `Proved` item whose post is a `Sim`, for
   called procedures that do I/O. Not needed until the source has
   procedures.
3. **Running the compiler in the kernel.** *Decided: kernel evaluation
   first* (`refl` on the bytes of `compile(p)`), measured in S5. The goal is
   to run the compiler at full native speed eventually, through a certified
   evaluation outside conversion (`hih-self`).
4. **Divergence, signals, concurrency** stay with
   `issues/linux-syscall-trace-model.md` and `effects-direction`. Liveness,
   which fuel-cut trees cannot state, is no longer deferred indefinitely:
   Minus wants the kernel round for coinductive types planned now
   (`issues/kernel-coinductive-types.md`), with heather-coq probing the
   worries.
5. **The surface.** *Decided: uniqueness threading that denotes trees*
   (`issues/effects-direction.md`).
6. **The source's shape (S3).** *Decided 2026-10-22: the layer over a total
   FunctionIR, loops split by totality* (`docs/native-effect-source-design.md`
   §11–§12). Before that: Minus liked the lean (a tree-shaped
   layer whose leaves are FunctionIR regions) but is unsure. The input for
   S3, from the same discussion:
   - **Split effects by where they live, not by IR.** *External* effects
     (syscalls, anything Linux answers) are the only ones that need trees,
     because the answer is chosen outside the program; they are the layer's
     constructs (a call binds its answer as `Vis` does, sequencing is
     `bind`, a loop is `iter`). *Internal* effects (memory, owned buffers,
     mutable locals) belong in FunctionIR as state edges, RVSDG style, with
     pure semantics: a `uniq Buf` is a value threaded through. An array load
     as a tree event would split a region per access. `run_state_bind`
     (`docs/itree-refinement-round.md`) is the theorem that the two
     readings agree. `hih-memory` needs the state edges anyway.
   - **What the layer costs.** Values live across a syscall cross a region
     boundary, so the layer, not the pure allocator, places them (§7's
     invariant between constructs); the first version will spill more than
     it needs to around syscalls, fixable without changing the theorem
     since placement is outside the proof. Passes that move pure code
     across a call (hoisting out of a read loop) see both levels.
   - **Where loops live** is the sub-question
     (`issues/function-ir-lowering-loops.md`): one loop construct in the
     layer, with a pure loop a layer loop without calls and FunctionIR
     regions loop-free, or FunctionIR keeping its own loops, lowered by a
     pure instance of the same rule.
   - **How to decide.** S3's first step writes `tr` both ways (the layer,
     and FunctionIR with effect nodes), each with its `denote` and the
     construct lemma it needs, before choosing.
   - **S3's design** (`docs/native-effect-source-design.md`, for Minus's
     decision) did that, and recommends the layer over a FunctionIR made
     the *total* level, with loops split by totality: a bounded loop in
     FunctionIR, the general loop in the layer.

## 11. How it meets the principles

- **Logic in Heather.** Compiler, theorem, assembler and layout are
  Heather; Rust is plumbing.
- **Tactics everywhere.** The intelligence moves from per-program proofs to
  per-construct lemmas proved once; what remains routine is a tactic's.
- **Constructive.** Recursion and evaluation throughout; `Sim` quantifies
  over finite histories rather than asserting infinite behaviour.
