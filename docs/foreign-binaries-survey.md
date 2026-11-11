# Foreign binaries: proving things about code Heather did not compile

Status: **survey and design sketch**, 2026-11-11, with Minus's answers of
the same day in §13. Speculative and not scheduled: no milestone needs it,
and Minus said it will not be done soon.
Owner: `issues/foreign-binary-contracts.md`. It extends
`docs/compilation-vision.md` in one direction (a foreign artifact as one more
producer of `Compile(f)`) and reads `docs/native-library-exports-design.md`
backwards (the export contract, required of a callee instead of promised by
one).

Sources: the library at master `8f47103`, with the lent-span footprint of
PR #551 (`Stack::Wrote`, `Stack::Lends`) read from its branch; two probes run
on the cloud box (§3 and appendices A and B, files under
`/mnt/project-files/foreign-binaries/`); and the related work of §10, which
is cited **from memory**, since the cloud box cannot fetch papers. Check an
entry before leaning on a detail of it.

The idea Minus asked about (2026-11-11): you want to link an external
program or shared library, or only to model another program without linking
it. Heather reads its machine code, and the tactics, proofs and analyses the
language already has for its own compiler are used to predict what the code
does and prove properties of it: that a function respects your memory and
does not write over your stack, and more of that kind. Linking becomes
safer, and the analysis tools get a hard, real workload.

---

## 0. The answer in brief

1. **The machine model never needed the compiler.** `MachineStep` fetches a
   form's bytes from memory at RIP and executes the form. Nothing in it
   mentions a `Prog`, a certificate or `compile-x86`. A theorem about
   foreign bytes is therefore an ordinary theorem today, and appendix A
   proves one: a function assembled by GNU `as` gets a `Site::Returns`
   contract by the same two rules a compiled function uses (§3).

2. **Reading a binary is untrusted search over a checked witness**
   (principle 3 of the vision). A disassembler proposes a `Prog`; the
   check is `assemble(prog) = bytes` by evaluation. The probe found why the
   check must go through the *encoder*: `decode_step_form` reads GCC's
   `lea rax, [rdi+rsi]` as a word store through RSP. That is no bug, since
   the decoder is documented as complete on emitted forms and silent about
   other bytes, and the step relation is stated over `step_form_bytes`, so
   the machine is not fooled. A reader of foreign code would be (§3.2).

3. **What can be stated is a ladder**, cheapest first: the code is closed
   and decodable; its footprint (`Wrote`, kept registers, return address,
   stack depth); it terminates without a fault; the system calls it may
   make; what it computes; what it leaks. Minus's example, "does not write
   over my stack", is rung 2, and it is the clause `Wrote` that PR #551
   introduces for Heather's own exports (§4).

4. **A foreign function with a proved contract is a `Compile(f)`
   instance.** The vision's picture has a "hand-written instances" box; a
   binary someone else compiled is the same box with a different author.
   The two plugs exist in the program logic: an `Asm::Proved` item (bytes
   that meet a register contract wherever placed) and a `Callee` (a
   function with a contract over a memory view). Linking is then a policy
   choice with a certificate, like every other choice of artifact (§6).

5. **The contract is the export contract read from the other side.**
   `docs/native-library-exports-design.md` §6 lists nine clauses that a
   Heather export promises a Rust caller. Calling foreign code turns each
   into an obligation on the callee and each caller premise into something
   Heather must provide. Three clauses change character: alignment and the
   red zone, which Heather's own code never uses and foreign code does, and
   the stack bound, which becomes a number proved about the callee (§6.2).

6. **Proof search is the analysis the optimizer already wants.** The
   obligations are weakest preconditions computed by the kernel, loop
   invariants proposed by an untrusted abstract interpreter and checked as
   post-fixpoints, and side conditions in bitvector arithmetic and span
   disjointness. Each of those has an open issue filed for the compiler's
   own sake (`wp-obligation-tactic`, `dataflow-checked-fixpoints`,
   `word-abstract-domains`, `wp-view-separating-product`, `bv-omega`). A
   foreign binary is the adversarial client for them: no source, no
   structure handed over, nothing emitted to suit the proof (§5).

7. **The distance is the instruction set, and it is measurable.** A census
   of real code (appendix B): the forms the model steps today are about a
   third of the instructions in `libc`, `libz` and `cat`, and no whole
   function. Two additions, the same operations at narrower widths and a
   general memory operand, cover another 36 to 51 percent. Getting to four
   functions in five needs SSE and thread-local storage, which is where
   the model's review burden lives (§7).

8. **Three things no proof reaches**: that the bytes analysed are the
   bytes that run (dynamic loading), what else writes memory while the
   callee runs (threads, signals), and the CPU beyond the model's ledger.
   Each becomes a stated premise, as the exports design already does
   under "outside the proof" (§8).

9. **Nothing needs doing now.** §11 lists five habits that keep the door
   open at no cost, and §9 says what the first cheap step would be if the
   idea is ever picked up: an *assumed* foreign contract, tracked like an
   axiom, that later analysis can discharge.

---

## 1. What exists, and what each piece gives a foreign binary

| piece | where | what it gives here | what it lacks for foreign code |
|---|---|---|---|
| step relation | `MachineStep` (`x86_64_stack.hthr`): a fetched instruction, a store, or a stack form, each `∃ form, FetchedFrom(memory, rip, bytes(form)) ∧ form executes` | a semantics of *bytes in memory*, parametric in the memory `M` | forms: only what the emitter writes (§7) |
| flags honesty | `Flags.defined`, `reads_defined` | reading an undefined flag has no step, so no proof can depend on one | nothing; foreign code needs this more than ours |
| assembly as data | `Asm`, `Prog`, `assemble` (`x86_64_asm.hthr`) | a structured reading of bytes whose correctness is an equation | items for a short jump, an indirect jump, a jump table |
| run rules | `Site::Moves`, `moves_block`, `moves_call`, `Site::Returns`, `returns_by` (`x86_64_stack_runs.hthr`) | Hoare-style rules over a resident `Prog`, memory-model generic | several are shaped like the emitter's output (`moves_branch` wants TEST, JE and a JMP over the else arm) |
| weakest precondition | `Wp`, `wp_sound`, `loop_variant`, `loop_bound` (`linux_x86_64_wp.hthr`) | one computed obligation over *any* `Prog` item, with a loop rule; `Callee::returns_by` proves a function's contract from its body's `Wp` | a tactic for the obligation (`wp-obligation-tactic`); views over more than one region |
| contracts | `Contract` (registers, memory untouched), `Callee` (over a view), `Asm::Proved`, `Asm::CallTo` | the slots where code proved elsewhere enters a program | nothing: neither says who produced the bytes |
| footprint | `Stack::Wrote`, `Stack::Lends`, `Readable` (PR #551); `Span`, `SpanSet` (`span_set.hthr`); `DataRegion` | "what a call may store", and "a span the call cannot disturb" | `Own` is a word at a frame offset; foreign code stores bytes anywhere it computes (§4.2) |
| process and system | `Sim`, `SimProgram`, Linux trees, `LinuxIo`, `X86Memory(profile)` with permissions | a meaning for a whole program as a tree of system calls | the system calls a real binary makes (`mmap`, `brk`, signals) |
| loader | `StaticElf64Loaded`, `io_elf_file` | bytes of *our* file shape resident at a fixed address | reading someone else's ELF: program headers, relocations, symbols (§8.1) |
| automation | `omega`, `grind`, `sets` over spans, `ring`, search rules | side conditions | bitvector goals as foreign code produces them (§5.3) |
| the other direction | `crates/linked`, `scripts/linked`, `compiled_returns` | Heather code called from Rust under a proved contract | this note is its mirror image |

The line to notice is the first. `docs/x86-64-reference-materials.md` §3
asked for "one bottom model, several proved views" with model
incompleteness kept apart from architectural nondeterminism and from
faults. Because that discipline was followed, the model is *partial and
honest*: on bytes it does not know, it has no step, and a theorem of the
shape "there is a run to the return address" cannot be proved through
them. An analysis built on it declines; it never mis-analyses. That is
principle 3's "a producer that cannot handle something declines" holding
for a client nobody designed it for.

## 2. What a theorem about foreign code says

The probe's statement, for bytes `48 89 f8 48 01 f0 c3`:

```
theorem add2_returns<M>(fetch, data, origin, stack: Stack<M>(fetch, data)):
    Site<M>(fetch, data, add2_prog(), Nil, origin).Returns(stack, 0, λ _ _ => True,
        λ _ s t => read_gpr(Rax, t.gprs) = read_gpr(Rdi, s.gprs).add(read_gpr(Rsi, s.gprs)) ∧
            t.memory = s.memory ∧ read_gpr(Rbx, t.gprs) = read_gpr(Rbx, s.gprs))
```

Unfolded: in any memory model, at any address, if those bytes are resident
and the machine is entered at their start with RSP in the stack and a
return address on top, then the machine steps to that return address with
RSP popped, the sum in RAX, memory as it was and RBX as it was. Three
things stand out.

- **It is total.** `Returns` asserts a run exists. For foreign code that is
  termination and absence of faults at once, since a faulting access has
  no normal step.
- **It is placement-independent**, like `Contract::Runs` ("bytes meet a
  contract wherever they are placed"). Position-independent library code
  gets this for free; code with absolute addresses gets a theorem about
  one `origin`.
- **Its trusted base is the model and the premise that the bytes are
  resident.** The disassembler, the control-flow graph, symbol tables,
  DWARF, the invariants, the analysis that found them: all untrusted.
  That is a smaller base than any binary analysis tool has, and the same
  base as Heather's own compiled code, minus the compiler's theorem, which
  is not needed because nothing is being compiled.

The policy "no per-program hand proofs" (principle 5) is about Heather's
compiler. It carries over as: no per-*binary* hand proofs. A generated,
kernel-checked proof per function is fine, as a certificate per compiled
program is fine; §5 is about generating them. The hand-proved stack that
was retired at tag `native-v0` was, in effect, foreign-binary verification
of our own emitter's output, and the program logic that replaced it is the
right tool for both.

## 3. Reading a binary

### 3.1 Three routes

**(a) Step straight off the bytes.** State `CodeResident(fetch, m, bytes,
origin)` for the raw bytes and prove each step by exhibiting its form.
Nothing is lifted. It is the most direct and it survives anything
(overlapping instructions, a jump into the middle of one), but every proof
re-reads bytes and there is no structure for `Wp` to recurse on.

**(b) Lift to a `Prog`, check by re-assembly.** An untrusted disassembler
(Rust at first, in Heather later, as generators moved) proposes a `Prog`
and the kernel checks `assemble(no_fills(), prog, last) = bytes` by
evaluation. From there the binary is "a program nobody compiled" and
`Site`, `Wp`, the loop rule and `Callee` apply unchanged. The probe does
this for two functions, one with a conditional jump. Cost is one
evaluation linear in the bytes, per function lifted; only the functions
reachable from the entry points one calls need lifting, and
`resident_split` cuts a library's residency into each function's.

**(c) Decompile into logic.** Above (b): produce an ordinary Heather
function `f`, or a FunctionIR function, together with the proof that the
bytes compute it, so later reasoning never sees machine state. This is
Myreen's "decompilation into logic", which carried seL4's proof from C
down to its binary. In Heather's terms the output is exactly a
`Compile(f)` instance whose code happens to be foreign (§6.1). FunctionIR
is a reasonable target for loop-free and simple-loop integer code, because
its meaning is already evaluable and its buffers are already values.

The recommendation, if this is ever built, is (b) as the base and (c) as
the layer that makes results usable, with (a) kept as the fallback for
code that has no `Prog` reading. They do not compete: all three end in
statements about `MachineStep`.

### 3.2 The finding: the decoder is not the witness, the encoder is

`x86_64_step_forms.hthr` says of `decode_step_form`: "complete on the
forms and claims nothing else; soundness on other bytes is not needed and
not stated". The probe shows what that means outside the emitter's image:

```
// lea rax, [rdi+rsi]; ret          (gcc -O2's add2)
theorem lea_misread(): decode_step_form([48, 8d, 04, 37, c3]) =
    Some(FormStore(StoreWord(WordStore(base := Rsp, source := Rax)))) { refl }
theorem lea_misread_bytes(): step_form_bytes(FormStore(StoreWord(WordStore(Rsp, Rax)))) = [48, 89, 04] { refl }
```

The decoder falls through its opcode cases to "a store". The machine does
not, because a step needs `FetchedFrom(…, step_form_bytes(form))` and the
store's bytes are `48 89 04`, not `48 8d 04`. So soundness is intact, and
the lesson is about design: **a reader of foreign code proposes with any
decoder it likes and checks by encoding.** The older
`decode_instruction` (`x86_64.hthr`) does have `decode_bytes_sound`, for
the register subset. A foreign-code decoder wants that theorem for
everything it reads, or wants to stay untrusted; staying untrusted is
cheaper and is the principle already in force.

It also suggests one small hardening that is independent of this note:
`decode_step_form` could end its ModRM fall-through in `None` instead of a
store, at no cost to completeness. It is not filed, because nothing
depends on it today.

### 3.3 What `Prog` cannot say yet

- **Indirect control.** `jmp rax`, `call [rip+got]`, jump tables. A
  jump-table item would carry the table and the proof that the index is
  below its length, turning the indirect jump into a finite case split.
  A truly computed target (a callback, a vtable) is a `Callee` taken as a
  premise: the caller of the foreign function supplies the contract of
  the function it passes in.
- **Calls out of the piece.** A foreign function that calls `malloc`
  either has `malloc`'s code lifted too, or takes `malloc`'s contract as a
  premise through `callees`, which is how `Wp` already treats `CallTo`.
  This is the right unit: prove `f` assuming contracts for what it calls,
  discharge or assume those separately.
- **Data in text, padding, overlapping code.** `Asm::Code` and `Piece`
  hold bytes that no proof runs, which covers padding and literal pools.

## 4. What can be stated: a ladder

Each rung is a statement over the same run; a higher rung does not
replace a lower one. "Automatic" means a decidable check or an analysis
with a checked result is plausible; "search" means invariants are needed.

| rung | property | stated with | effort |
|---|---|---|---|
| 0 | **Closed and decodable**: every reachable address starts a modelled form, every direct jump lands on one, no indirect control | a Bool judgment over the `Prog`, sound once | automatic |
| 1 | **Control returns**: the function ends at its return address, RSP popped | `Returns` (with `post` trivial) on loop-free code; rung 3 otherwise | automatic for straight code |
| 2 | **Footprint**: stores only into its own frame and spans lent for writing; callee-saved registers kept; reads only its frame, its code and spans lent | `Stack::Wrote`, `Kept`, `Lends`, generalised (§4.2) | automatic for compiler-shaped code, by the analysis of §5 |
| 3 | **Total**: terminates, no fault, stack use below a stated bound | `Returns` in full; `loop_variant` | search (variants), bounded loops automatic |
| 4 | **System calls**: none, or only within a policy | `Sim` against a tree, or a predicate on every trace (`io-footprint-facts`' `Io::Only`, one level down) | automatic for "none" (no SYSCALL form reachable) |
| 5 | **Result**: a stated property of what it returns and writes, up to the function `f` it computes (§13, answer 2) | an `ensures` over the contract; `Compile(f)` at the strongest | search within what the automation reaches, or decompilation (§3.1 c) |
| 6 | **Leakage**: constant-time under a named contract | `docs/constant-time-survey.md`'s labelled steps | automatic taint analysis, checked |

### 4.1 Rung 0 is a discipline over machine code

Principle 7: disciplines are decidable judgments over code plus one
soundness theorem. Rung 0 is that, with the code being x86 instead of
reflected `rt`: a checker `closed(prog): Bool`, a theorem "if
`closed(prog) = True` then every run from an entry stays inside the
program's instruction boundaries or leaves through a listed exit", and a
verdict per binary by `refl`. This is the shape of RockSalt, the verified
checker for Native Client's sandbox policy: prove the checker once, run it
per binary. It is the cheapest useful result and everything else stands on
it.

### 4.2 Rung 2 is `Wrote`, widened

Minus's example lives here. Today:

```
fn Stack::Own(stack, i, before, after) → Type {
    ∃ k word, k + 8 <= i ∧ after = stack.writes.store(before, stack.at(k), word_bytes(word))
}
fn Stack::Wrote(stack, i, before, after) → Type { Star(stack.Own(i), before, after) }
```

That is exactly "the callee stores only into its own room below the return
address", and `wrote_unchanged` gives the caller its frame back. Foreign
code needs the same relation over a wider `Own`:

- stores of one, two, four and eight bytes, at byte offsets;
- stores below RSP without moving it (the System V red zone, 128 bytes,
  which leaf functions use and Heather's emitter never does);
- stores into spans lent for writing, which the exports design's write
  half (§7 there) also needs.

The general form is a footprint as a `SpanSet`: `Wrote(S, before, after)`
is `Star` of single stores whose span lies within `S`, and "respects my
memory" is `S` disjoint from what the caller holds, decided by
`SpanSet::disjoint` where addresses are numbers. `wp-view-separating-product`
already says footprints should be span sets; this is one more client for
the same decision. The semantic premise `Lends` needs no change at all: it
quantifies over whatever `Wrote` is.

The read half matters more for foreign code than for ours. "Reads only
what it was lent" is not a safety property of the caller's data, but it is
what makes the result a function of the arguments, and it is what rules
out a callee that inspects the caller's frame.

### 4.3 Rung 4: a program as a set of traces

For a function, "no system call" is syntactic at rung 0. For a whole
foreign *program*, which Minus's message also covers (model it, do not
link it), the statement is `SimProgram(io, tree)` or weaker: every trace
of the binary satisfies a policy. That is a seccomp filter proved instead
of enforced. Two uses worth naming:

- **A subprocess as a specification.** If Heather code runs
  `/usr/bin/sort`, a theorem `SimProgram(io, sort_tree)` about that binary
  is what would let the caller's proof continue past the `execve`.
- **Differential specification.** GNU `cat` and Heather's `cat` refining
  the same tree is the strongest form of the GNU test suites the native
  milestones use today.

Both need the Linux model to grow well past what our tools call
(`linux-syscall-trace-model`), so this is the furthest part of the idea.

## 5. Finding the proofs

No one writes these by hand; the question is what generates them.

### 5.1 The obligation is computed

`Wp` is a function from a `Prog` and a postcondition to a type, and
`wp_sound` is proved once. For foreign code the kernel is the symbolic
executor: `Wp` of a block is `execute_block_normal` applied to an open
state, which the probe's proof discharges by `refl` on each conjunct.
A negative control (claiming the difference instead of the sum) is refused
by the kernel with `NotConvertible` at that `refl`.

### 5.2 Invariants are untrusted, their closure is checked

Loops and joins need invariants. An abstract interpreter proposes them,
and the proposal is checked as a post-fixpoint: this is
`dataflow-checked-fixpoints`, filed because liveness, `Ix::hi` and the
segments' `known` facts are each a private instance of it. The domains a
footprint proof needs are few:

- **Stack height**: RSP as "entry RSP plus a constant" at each program
  point. Compilers keep this invariant almost everywhere, and `.eh_frame`
  unwinding tables state it per address, so they are a free, untrusted
  hint.
- **Provenance of a word**: a constant, entry-RSP plus a constant,
  argument `k` plus a bounded offset, the entry value of a callee-saved
  register, or unknown. A store is in the frame, in span `k`, or
  rejected. A callee-saved register is kept because the value reloaded
  from a frame slot is the value spilled there, which is the memory
  view's read-over-write.
- **Intervals and known bits over words** for the bounded offset:
  `word-abstract-domains`.

With those, rung 2 for typical compiled C is an analysis result plus a
checked certificate. This is the claim Verbeek and others make for their
Isabelle-verified lifting of x86-64 binaries (return address integrity,
bounded control flow, calling-convention adherence, over large parts of
real binaries); it is not established here beyond one straight-line
function.

In the vision's words these are **facts**: `Wrote`, `Kept`, `Pure`,
`InBounds`, published as side-proofs with a cheap producer first and
search last (`docs/facts-on-demand-design.md`). A fact about a foreign
function and a fact about an `rt` function are the same class with
different producers, and a caller's optimisation that asks "does this
call disturb my buffer" should not care which.

### 5.3 Side conditions are where the tools get tested

The compiler's proofs avoid address arithmetic on purpose: stack addresses
are `next_rip(low, i)` with `i` a natural number, and `Lends` is stated as
stability so no load compares open addresses (exports design §4.2).
Foreign code allows no such choice. It computes addresses with `lea`,
`sub rsp`, scaled indices and masks, and the goals are bitvector goals:
`(rsp - 40) + 8*i` lies in `[rsp - 40, rsp)` given `i < 5`, no wrap.
That is `docs/bv-omega-design.md`, wrapped intervals, and `sets` over
spans under `BitVec::numbering(64)`, with `grind` for read-over-write
chains. Each exists in part and each has been tuned on goals the compiler
was built to keep easy. This is the sense in which the project would
"make the tools really powerful": it removes the option of shaping the
goal to suit the tactic.

## 6. Linking

### 6.1 A foreign artifact is a `Compile(f)` instance

Principle 2: the certificate is logical, which artifact runs is policy.
`Compile(f)` is code plus the proof that it agrees with `f`. If the code
is `memchr` from a C library and the proof is rung 5 for those bytes, the
instance is as good as one from `rt`, and choosing it over Heather's own
lowering is the same kind of decision as choosing between two
representations. The program logic has both plugs already:

- `Asm::Proved(index, bytes, len, measured)` with `Contract::Runs`: bytes
  that meet a register contract wherever they are placed, memory
  untouched. A position-independent foreign leaf routine, statically
  included, is this item verbatim.
- `Callee<M, V>` with `Callee::Returns`: a function at an address with a
  contract over a memory view. A foreign function with a frame and lent
  spans is this.

Neither records who produced the bytes, and they should stay that way
(§11).

### 6.2 The export contract, turned around

`docs/native-library-exports-design.md` §6, clause by clause, with
Heather as the caller:

| # | as an export (Heather promises) | calling foreign code (must be proved of the callee, or provided to it) |
|---|---|---|
| 1 | arguments in RDI, RSI, … | provided by the lowering; the callee's `pre` is stated over those registers |
| 2 | one word returns in RAX | proved (rung 5), or left unconstrained at lower rungs |
| 3 | RBX, RBP, R12 to R15 kept, RSP back | **proved**: `Kept`, `Returns` (rung 2) |
| 4 | stores only into its own room | **proved**: `Wrote` (rung 2). This is "does not write over my stack" |
| 5 | reads only its frame and spans lent | **proved**: the read half of rung 2 |
| 6 | 72 bytes of stack a level | **proved as a number** about the callee: its maximum depth, from the stack-height invariant and the call graph. The caller's `pre` then asks for that much room |
| 7 | alignment neither required nor provided | **must be provided**: compiled C assumes RSP is 16-byte aligned at a call and uses aligned SSE moves on its frame. The model needs the fault, or the contract needs the premise |
| 8 | no red zone used | **reversed**: the callee may store up to 128 bytes below RSP. Harmless to the caller, since that is below the callee's entry RSP, but `Own` must admit it, and a signal handler on the same stack must not run there |
| 9 | DF, x87, SSE state, MXCSR untouched, by inventory | **must be modelled or premised**: the ABI lets a callee clobber every XMM register and requires DF clear on entry |

The table's symmetry is the design point. `named-abi-contracts` asks for
"reusable named Heather contracts, usable by certified Heather code and
explicitly assumed foreign boundaries"; this note adds a third state
between certified and assumed: a foreign boundary whose contract was
*checked against the callee's bytes*.

### 6.3 A possible declaration

Provisional, and `runtime-extern-c-abi` owns the spelling of imports:

```
foreign "vendor/libz.a" sha256 "9f2c…" {
    fn adler32(adler: u32, buf: lent [u8]) → u32
        contract sysv_words_spans          // which clauses, by name
        level footprint;                   // rung required: assumed | footprint | total | function
}
```

- `assumed` is today's world everywhere else: the contract is an axiom.
  `docs/axiom-provenance-design.md` already tracks which theorems rest on
  which axioms, so a program's dependence on unchecked foreign code would
  be visible in its certificate rather than in a comment.
- `footprint` and `total` ask the analysis of §5 to discharge rungs 2 and
  3 and fail the build if it cannot.
- `function` adds `ensures result = Adler32::spec(adler, buf)` and needs
  rung 5.

The lifecycle is principle 4's: a boundary starts assumed, moves to
checked as the analysis learns to handle it, and the statement callers
cite does not change when it does.

### 6.4 Which bytes run

A theorem is about a list of bytes. The link must make those the bytes
that execute:

- **Static inclusion** (an object file's function copied into the
  image, as `scripts/linked` does in the other direction) makes the
  premise true by construction: `write-elf` places the bytes and
  `CodeResident` follows as it does for Heather's own code. This is the
  only fully honest mode and the recommended first one.
- **A shared library** is loaded by `ld.so` at run time from a file that
  can differ from the one analysed. A hash in the declaration pins the
  build-time file (SHA-256 is the `crypto-hash` milestone's subject); the run-time file is a
  premise, written next to the declaration the way the exports design
  writes Rust's `SAFETY` lines. Relocations and the PLT are more model:
  the bytes analysed must be the bytes *after* relocation.

## 7. The distance: what the model would need

Appendix B's census, objdump's reading of real code classified against
the forms `MachineStep` has (a text approximation, an upper estimate for
"in the model"). Share of instructions:

| class | `cat` | `libz` | `libc` |
|---|---|---|---|
| in the model today | 36% | 30% | 36% |
| memory operand with displacement, index or narrow width | 21% | 28% | 19% |
| the same operations at 32, 16 or 8 bits, or with an immediate | 19% | 23% | 18% |
| padding and CET markers (`nop`, `endbr64`) | 8% | 4% | 6% |
| `push`, `pop`, `leave` | 5% | 5% | 5% |
| `lea` | 5% | 5% | 5% |
| SSE and AVX | 1% | 2% | 6% |
| RIP-relative and `fs:` operands, indirect control, `cmov`, multiply and the rest | 5% | 3% | 6% |

Share of *whole functions* covered as classes are added in that order
(`libz`, 92 labelled functions; `libc`, 2301; columns are rounded): none
today; 14% and 7%
after padding and narrow widths; 45% and 21% after general memory
operands, `lea` and `push`/`pop`; 69% and 32% after the remaining integer
forms and `cmov`; 82% and 84% only after RIP-relative and `fs:`-relative operands
(globals, errno, the stack canary) and SSE; the tail is indirect jumps and string
instructions.

What that says:

- **The integer core is an orthogonal product, not a list.** Today's
  `Instruction` has a constructor per form (`AddRR`, `AddRI8`,
  `AddRI32`), which suits an emitter. Foreign code wants operation ×
  width × operand, with one ModRM/SIB reader, and the emitter's forms as
  derived views of it. `issues/x86-64-machine-model.md` already asks for
  "typed instruction and operand forms independently of byte encoding".
  The 32-bit forms carry the one rule every x86 model gets wrong once (a
  32-bit write zeroes the upper half, a 16- or 8-bit write does not), so
  they belong in the ledger with differential tests.
- **SSE is unavoidable for compiled C** even in integer code (struct
  copies, `memset` idioms), and brings a second register file and
  alignment faults. This is the largest single piece of new trust.
- **Every form is trust.** `docs/x86-64-reference-materials.md` §5's
  coverage ledger is the control. A model wide enough for foreign code
  is where importing or cross-checking against a machine-readable
  semantics (the Sail and K x86 models, ACL2's x86isa) stops being
  optional; the licence policy in §2 of that note applies. A
  per-instruction differential test against the real CPU is the kind of
  harness `native-differential-harness` describes for exports.
- **The decoder becomes a grammar.** A hand-written decision tree does not
  scale to prefixes, ModRM, SIB and displacement. RockSalt's decoder was a
  regular grammar run by derivatives; `regular-languages-by-derivatives`
  and `lexical-grammar-as-data` are the same technology, filed for the
  lexer.

## 8. What no proof reaches

1. **The loader.** §6.4. Also position: code with absolute relocations is
   proved at one address.
2. **Concurrency and signals.** `Wrote` describes what the callee stores.
   Another thread, or a signal handler on the same stack, stores too. The
   exports design already lists "the kernel does not write below RSP
   outside a signal frame the process set up" as outside the proof; the
   red zone makes it sharper.
3. **The machine beyond the model.** Self-modifying code is excluded by
   `Stack::keeps_code` and the permissions of `X86Memory`, which are
   premises about the loader. Speculation, timing and faults the model
   replaces by "no step" are outside, as for our own code.
4. **Undecidability.** Rung 0 can be made decidable by rejecting what it
   cannot follow. Above it, the analysis is incomplete by nature and says
   so by failing; `level assumed` is the escape hatch, and it is visible.

A sharper way to say what is gained: today a foreign call is trusted for
*everything*. With rung 2 it is trusted for nothing about memory and
registers, given the loader premise, and still trusted for what it
computes. That is the same shape as Rust's `unsafe` boundary, except that
the obligation is discharged against the callee's actual bytes instead of
being promised by a comment.

## 9. Rounds, if this is ever picked up

In order, each useful alone. None is proposed for scheduling.

- **F0. Assumed foreign contracts.** The declaration of §6.3 at `level
  assumed` only: an import is an axiom with provenance, callable from
  `rt` through `Callee`. No machine-code reading. This is ordinary FFI
  made honest, and `runtime-extern-c-abi` wants it anyway.
- **F1. Lift and close.** A Rust disassembler for the modelled forms,
  the re-assembly check, and rung 0 as a checked judgment. Demonstrated
  on functions assembled for the purpose, as in appendix A.
- **F2. Footprints for straight code.** `Wrote` over span sets, the
  stack-height and provenance domains on loop-free functions, rung 2
  automatic. First real answer to "does not write over my stack".
- **F3. The integer core.** The operand-generic instruction type with
  widths and general memory operands, the emitter's forms as views.
  This is the round with the largest trusted-base change and it is
  Minus's to review (kernel-adjacent in spirit, though not in the kernel).
- **F4. Loops and calls.** Checked fixpoints for invariants, callee
  contracts as premises, stack bounds over the call graph. Target: every
  function of a small real library (`libz`'s `adler32`, `crc32`).
- **F5. Decompilation.** Rung 5 for integer functions into FunctionIR,
  giving `Compile(f)` instances; and a first whole-program statement.
- **F6. SSE, TLS, shared objects.** Whatever the census says is next.

## 10. Related work

From memory, not re-read for this note.

- **Proof-carrying code and typed assembly.** Necula, *Proof-Carrying
  Code* (POPL 1997); Morrisett, Walker, Crary, Glew, *From System F to
  Typed Assembly Language* (POPL 1998); Appel, *Foundational
  Proof-Carrying Code* (LICS 2001). The original statement of "untrusted
  code plus a checkable proof of a safety policy". Heather's difference
  is that the producer of the proof is the consumer of the code.
- **RockSalt.** Morrisett, Tan, Tassarotti, Tristan, Gan (PLDI 2012). An
  x86 model in Coq with a grammar-based decoder, and a sandbox checker
  proved sound once. The model for rung 0. VeriWasm (Johnson and others,
  NDSS 2021) checks sandbox safety of compiled WebAssembly binaries by
  abstract interpretation, with the same division of labour.
- **Decompilation into logic.** Myreen, Gordon, Slind, *Machine-Code
  Verification for Multiple Architectures* (FMCAD 2008), and its use in
  Sewell, Myreen, Klein, *Translation Validation for a Verified OS Kernel*
  (PLDI 2013). The model for §3.1 (c): a function extracted from machine
  code with a theorem that the code implements it.
- **Verified lifting of x86-64 binaries.** Verbeek, Bockenek, Ravindran
  and coauthors: memory preservation of x86-64 binaries (SAFECOMP 2019),
  *Highly Automated Formal Proofs over Memory Usage of Assembly Code*
  (TACAS 2020), *Sound C Code Decompilation for a Subset of x86-64
  Binaries* (SEFM 2020), *Formally Verified Lifting of C-Compiled x86-64
  Binaries* (PLDI 2022). Closest to rung 2: Hoare graphs with invariants
  found automatically and exported to Isabelle, establishing return
  address integrity and calling-convention adherence. Their experience
  with which assumptions are unavoidable is worth reading in full before
  F2.
- **ACL2 x86isa.** Goel, Hunt, Kaufmann, *Simulation and Formal
  Verification of x86 Machine-Code Programs that Make System Calls*
  (FMCAD 2014). Proofs about real compiled binaries against a broad
  executable model; already a cross-check source in
  `docs/x86-64-reference-materials.md`.
- **Islaris.** Sammler and others (PLDI 2022): machine-code verification
  in Iris against the authoritative Sail models, with symbolic execution
  done by an untrusted tool whose traces are checked. The same split as
  §5.
- **Vale and its embedding.** Bond and others, *Vale: Verifying
  High-Performance Cryptographic Assembly Code* (USENIX Security 2017);
  Fromherz and others, *A Verified, Efficient Embedding of a Verifiable
  Assembly Language* (POPL 2019). Hand-written assembly proved correct,
  memory-safe and leakage-free, then called from a high-level language
  through a proved interoperation layer. The model for §6 and for rung 6.
- **Assembly in a proof assistant.** Ni, Shao, *Certified Assembly
  Programming with Embedded Code Pointers* (POPL 2006), for function
  pointers as contracts (§3.3); Chlipala's Bedrock (PLDI 2011); Jensen,
  Benton, Kennedy, *High-Level Separation Logic for Low-Level Code* (POPL
  2013).
- **CompCertO.** Koenig, Shao (PLDI 2021), in `docs/`: open components
  with language interfaces and calling conventions as simulation
  conventions. The right frame for stating §6.2's table once instead of
  per direction.

## 11. Habits that keep the door open

None of these asks for work; each is a choice current rounds are already
making, written down so it is not unmade by accident.

1. **Keep `MachineStep` about bytes in memory**, never about a `Prog` or
   an emitted form's provenance.
2. **Keep `Contract`, `Callee` and `Asm::Proved` silent on who produced
   the bytes.** A field recording "the compiler's certificate" would close
   the foreign plug.
3. **State footprints relationally** (`Wrote` as `Star` of stores, `Lends`
   as stability) and move toward span sets, as PR #551 and
   `wp-view-separating-product` do, so that widening `Own` changes one
   definition.
4. **Keep the coverage ledger's three-way split** (nondeterminism, fault,
   unmodelled) and keep "unmodelled" meaning "no step".
5. **When a decoder is written to be complete only, say so**, as
   `x86_64_step_forms.hthr` does. §3.2 is what happens to a reader who
   misses the sentence.

## 12. Questions for Minus

Answered in part on 2026-11-11: §13.

1. Is the right first-class notion the **assumed foreign contract with
   provenance** (F0)? It is the only part with near-term use, since
   `nh-library` and `runtime-extern-c-abi` will need imports anyway, and
   it fixes the statement that later rungs would discharge.
2. Does this belong under `heather-in-heather`, or is it a horizon area
   of its own beside `rust-in-heather` ("prove properties about code
   written elsewhere", at the binary level instead of the source level)?
   The issue is filed under `heather-in-heather` with `milestone: [none]`
   until you say.
3. For the model's growth, is **hand-written forms under the ledger**
   still the policy at foreign-code scale, or is importing a
   machine-readable semantics as the cross-check (never the authority)
   acceptable when the time comes?

## 13. Minus's answers (2026-11-11)

Given the same day, after reading the note. Recorded as said, with the
reading taken of each; where a sentence is this note's inference, it says
so.

1. **Two modes, both wanted.** An *assumed contract*, and *active
   verification*, "a smart linkage thing": you link to this code, so check
   that the function you call does what you say it does. This answers §12
   question 1: the assumed contract is worth having as its own mode and
   not only as a step toward the other. Where verification is out of
   reach, "you can't verify and you just have to assume, and that's an
   axiom. As expected."

2. **Verification is up to the abstraction the caller cares about.** "You
   have a sort function, you only care that it returns a sorted [list],
   you don't care about the implementation details." So rung 5 of §4 is
   too narrow as written: what is proved is a *stated property of the
   result*, of which "equals `f`" is the strongest case. Sortedness
   without permutation, a bound on a length, "the output buffer holds a
   valid encoding" are all contracts. The condition Minus puts on it: it
   "has to be something that your automated tactic prover or inference
   thing can verify". The contract language is therefore bounded by the
   automation, not by what can be stated, and a contract the automation
   cannot reach falls back to the assumed mode rather than to a hand
   proof.

3. **The probe's proof is too verbose to be the artifact** (§13.1). As it
   stands it is "basically unverifiable for [a] normal human to read. And
   even for an AI, that might be a bit rough." Some good way of embedding,
   or something smarter, is needed.

4. **Instructions.** Corrected by Minus the same day (the first message
   was dictated): instructions are not that hard to add; SSE is more
   complex, "but we'll want a high quality model of it regardless". So
   SSE is wanted for Heather's own sake, and foreign code is one more
   client of that model, not the reason for it. §12 question 3 (hand-written
   forms or an imported cross-check) is not answered by this.

5. **Code that calls back out is the harder half.** Outside code "can do
   absurdly crazy things to you and requires analyzing the whole program,
   which is another whole thing." A leaf function is a closed object;
   anything that reaches the rest of the process (callbacks, globals, the
   allocator, system calls) needs §3.3's premises for everything it
   touches, or the whole-program statement of §4.3.

6. **Wanted, not essential.** Corrected the same day: "while I do want
   this, it isn't an essential feature quite so much even if very cool."
   And in both directions: "we will want to call and be called by outside
   functions." Being called is `nh-library`; calling is this note and
   `runtime-extern-c-abi`.

7. **Not an `ensures` clause: a namespace** (§13.2). Minus is sceptical of
   §13.1's `ensures`: "this seems more like something [that] should be
   more of a namespace: you might have many proofs you want associated."
   The case to design for is "we want to link this large program with a
   model of how it works", such as SDL2 or, more practically, OpenSSL,
   "where you might want to relate many different state pieces and what
   other functions do".

§12 question 2 (which area) is still open.

### 13.1 What the statement and proof should look like

The probe's `add2_returns` fails as a thing to read for two reasons, and
neither is about foreign code:

- **The statement is spelled in machine terms.** A reader must unfold
  `Site`, `Returns`, a λ over two states and three conjuncts to learn
  "returns `a + b`, touches nothing". The contract is a System V word
  function; it should be said once, by name.
- **The proof restates the statement four times** (for `returns_by`,
  twice for `moves_weaken`, for `moves_block`) around three `refl`s.

A sketch of the target, with every name provisional:

```
// One predicate per named ABI contract (issues/named-abi-contracts.md):
// what "these bytes are a System V function of two words with this
// result" means. Its body is Returns + Kept(callee_kept()) + Wrote, with
// the registers and the footprint the contract's, not the caller's to spell.
fn SysV::Meets2(bytes: List<BitVec(8)>, ensures: BitVec(64) → BitVec(64) → BitVec(64) → Type) → Type

// The statement a person reads:
theorem add2_contract(): SysV::Meets2(add2_bytes(), λ a b result => result = a.add(b)) { foreign }

// or, at the surface, the declaration is the statement and the tactic is implied:
foreign "vendor/add.o" fn add2(a, b: u64) → u64 ensures result = a + b;
foreign "vendor/sort.o" fn sort(xs: lent mut [u64]) ensures xs.sorted();     // answer 2: a property, not the function
```

- The **embedding** is the named contract: a caller sees the Heather
  signature and the `ensures`, and cites `SysV::Meets2` only through the
  `Compile` instance it produces. The machine statement exists once, in
  the contract's definition, where it is reviewed once.
- The **proof** is one tactic, `foreign`: lift (propose a `Prog`, check
  by re-assembly), compute `Wp`, close what conversion and the arithmetic
  tactics close, and hand back the residue. That is
  `wp-obligation-tactic` with the lift in front of it. A failure names
  the instruction or the side condition it stopped at, and the user's
  recourse is `assumed`.
- What a human audits is then three things, each short: the declaration,
  the named contract's definition, and the list of axioms (assumed
  imports) the program rests on.

The probe was written without any of this on purpose, to show what the
library gives today; its length is the measure of what the embedding and
the tactic have to remove.

The named contract predicate and the tactic stand. The `ensures` clause on
a declaration does not survive answer 7: it gives a function one
postcondition, fixed where the function is declared, and has nowhere to
put state shared between functions. §13.2 replaces it.

### 13.2 A library is a namespace with a model

A leaf like `add2` has a result and nothing else. A real library is
different in kind: `SSL_read` means nothing without the connection
`SSL_new` made, the handshake `SSL_connect` did, and the context both
came from. What a caller wants is not one fact per function but a
**model**: the library's abstract state, what each function does to it,
and theorems about how the functions relate. And different callers want
different theorems, added over time, by people other than whoever wrote
the import.

Heather has already linked one large foreign program with a model of how
it works: Linux. The pieces are worth naming, because each is generic:

| for Linux today | what it is in general |
|---|---|
| `LinuxCmd`, `Events::linux()` (`linux_calls.hthr`, `linux_trees.hthr`) | the library's **calls** as a command container: one command per function, with its answer type |
| `linux_world`, `linux_world_co` | the **model**: an abstract state and what each call does to it, as ordinary Heather functions |
| `CallSystem<A, R>(E)` (`call_system.hthr`), `Sim`, `RunsAs` | a program that calls out, read along a tree over the container; nothing in `CallSystem` is about Linux |
| `LinuxIo<M>`, `LinuxRequests`, `linux_meets` | the **bridge**: how a call and its answer appear in registers and memory, and that the machine meets the model |
| theorems over worlds and trees (the tools' specs; `io-footprint-facts`' proposed `Io::Only`) | **facts about the model**, proved with no machine in sight, by anyone, anywhere |
| capabilities, `mut self` methods (`docs/effects-capabilities-design.md`) | how `rt` code holds and threads the state |

The bridge is the only part that mentions the binary, and for Linux it is
*assumed*: the kernel is not verified, `LinuxIo` is the axiom. So Linux is
this note's assumed mode, already built, for a library of about a dozen
calls. A foreign library is the same shape with a different container and
the bridge either assumed or checked.

As a namespace (every spelling provisional):

```
// 1. The model: plain Heather, no machine. Written by hand, by whoever
//    understands the library. This is "a model of how it works".
module OpenSsl {
    record Ctx { … }                                 // abstract state pieces
    record Conn { ctx: CtxId, state: Handshake, pending: List<u8>, … }
    record World { ctxs: Map<CtxId, Ctx>, conns: Map<ConnId, Conn>, errors: List<Error> }

    fn World::new_conn(mut self, ctx: CtxId) → Option<ConnId> { … }
    fn World::read(mut self, c: ConnId, n: Nat) → ReadResult { … }
    fn World::shutdown(mut self, c: ConnId) → ShutdownResult { … }

    // 2. Facts about the model: as many as anyone wants, added any time.
    theorem read_needs_handshake(w, c, n, early: w.conn(c).state ≠ Established): w.read(c, n).is_error() { … }
    theorem shutdown_twice(w, c): … { … }
    theorem read_keeps_other_conns(w, c, d, n, apart: c ≠ d): w.read(c, n).world.conn(d) = w.conn(d) { … }
}

// 3. The link: which symbol of which bytes plays which model operation,
//    and how the model's state appears in memory. One line per function,
//    each with its own evidence.
foreign "vendor/libssl.a" sha256 "…" as OpenSsl under sysv {
    repr World by OpenSsl::Represents;               // memory ⇄ model, as datarepr relates a layout to a spec type
    SSL_new      refines World::new_conn  assumed;
    SSL_read     refines World::read      assumed;
    SSL_shutdown refines World::shutdown  assumed;
    ERR_get_error refines World::pop_error checked;  // a leaf: the `foreign` tactic can do this one
}
```

What this arrangement gives:

- **Many proofs, one namespace.** The theorems of part 2 are ordinary
  theorems about ordinary functions. A client adds
  `OpenSsl::my_protocol_never_reads_after_shutdown` in its own module
  without touching the import. Nothing is attached to a declaration.
- **State is related across functions** because the functions are methods
  of one `World`, exactly as Linux's `read` and `open` share a file table.
- **Trust is per function and visible.** Each `refines … assumed` is one
  axiom with provenance (answer 1); each `checked` is discharged against
  the bytes. The lifecycle of §6.3 moves one line at a time, and theorems
  proved over the model do not notice.
- **The model is the abstraction** (answer 2). `refines` says the
  function's effect on memory, read through `Represents`, is *one of the
  behaviours the model allows*. A model that says only "the output is
  sorted" is a looser `World` method, not a different mechanism, and how
  loose to make it is the modeller's choice.
- **Callers use it like any effect.** An `rt` function holds a capability
  for the library's world and calls `conn.read(n)`; its meaning is a tree
  over `OpenSsl`'s commands; the compiler lowers each command to a call
  through the bridge. This is `effect-interfaces-over-carriers` with a
  foreign handler.

What it costs, and what is new:

- **`Represents` is the hard part of any checked line.** It relates heap
  structures the library owns to the abstract state: a separation-style
  invariant over memory Heather did not lay out. For assumed lines it is
  only named; for checked ones it is where the proof effort goes, and
  where answer 5's whole-program difficulty shows up, since a function
  that follows pointers into library-owned state needs the invariant of
  everything it can reach.
- **Callbacks invert the direction.** SDL2 calls the program's event
  handler; OpenSSL calls a verify callback. In the tree reading that is
  the *library* issuing a command the *program* answers, so the container
  needs commands in both directions. `CallSystem`'s `answered` is already
  a predicate transformer over resumptions, which is the right shape, but
  no current client uses it that way.
- **An assumed model can be wrong**, and then everything proved over it
  is about a library that does not exist. The mitigation is the one Linux
  uses: differential tests of the model against the real thing
  (`native-differential-harness`), and keeping models small and
  conservative (a call the model does not describe has no command, so no
  program using it compiles).
- **Models are shared artifacts.** A model of OpenSSL is a library in its
  own right, with a version it claims to describe. Which bytes it matches
  is the hash in the `foreign` line; one model may be linked against
  several builds, each with its own evidence lines.

So the unit this note should have led with is not "a function with a
contract" but "a component with a model and a per-function refinement",
with the leaf function as its smallest case: one command, a trivial
world, and a `checked` line. §6.1's reading still holds one level up: the
`foreign … as OpenSsl` block is an instance, for the whole command
container at once, of what `Compile(f)` is for one function.

---

## Appendix A. The probe

`/mnt/project-files/foreign-binaries/foreign_probe.hthr`, checked whole
by `heather check` at master `8f47103` (not in the library, so the gate
does not hold it). The bytes are GNU `as`'s output for `foreign.s` beside
it.

```
fn b(n: Nat) → BitVec(8) { BitVec::ofNat(n) }

// add2:  48 89 f8   mov rax, rdi
//        48 01 f0   add rax, rsi
//        c3         ret
fn add2_bytes() → List<BitVec(8)> { [b(0x48), b(0x89), b(0xf8), b(0x48), b(0x01), b(0xf0), b(0xc3)] }

// 1. The library's decoder reads them in the kernel, one instruction an offset.
theorem add2_reads_0(): decode_step_form(add2_bytes()) = Some(FormEmitted(EmitOrdinary(MovRR(Rax, Rdi)))) { refl }
theorem add2_reads_3(): decode_step_form(add2_bytes().drop(3)) = Some(FormEmitted(EmitOrdinary(AddRR(Rax, Rsi)))) { refl }
theorem add2_reads_6(): decode_step_form(add2_bytes().drop(6)) = Some(FormStack(ReturnNear)) { refl }

// 2. gcc -O2's version of the same function is misread (§3.2).
fn lea2_bytes() → List<BitVec(8)> { [b(0x48), b(0x8d), b(0x04), b(0x37), b(0xc3)] }
theorem lea_misread(): decode_step_form(lea2_bytes()) = Some(FormStore(StoreWord(WordStore(base := Rsp, source := Rax)))) { refl }
theorem lea_misread_bytes(): step_form_bytes(FormStore(StoreWord(WordStore(base := Rsp, source := Rax)))) = [b(0x48), b(0x89), b(0x04)] { refl }

// 3. Lifting: the program a disassembler would propose, checked by evaluation.
fn add2_prog() → Prog { then(then(Start, Block([MovRR(Rax, Rdi), AddRR(Rax, Rsi)])), Ret) }
theorem add2_lifted(): assemble(no_fills(), add2_prog(), Nil) = add2_bytes() { refl }

// max2:  mov rax, rdi; cmp rdi, rsi; jae done; mov rax, rsi; done: ret
fn max2_prog() → Prog {
    At(then(then(then(Start, Block([MovRR(Rax, Rdi), CmpRR(Rdi, Rsi)])), Jcc(AE, 1)), Block([MovRR(Rax, Rsi)])), 1, Ret)
}
theorem max2_lifted(): assemble(no_fills(), max2_prog(), Nil) = max2_bytes() { refl }

// 4. The contract of §2, by `Site::returns_by` over `Site::moves_block`.
theorem add2_returns<M>(fetch: FetchAccess<M>, data: ByteReadAccess<M>, origin: BitVec(64), stack: Stack<M>(fetch, data)):
    Site<M>(fetch, data, add2_prog(), Nil, origin).Returns(stack, 0, λ _ _ => True,
        λ _ s t => (read_gpr(Rax, t.gprs) = read_gpr(Rdi, s.gprs).add(read_gpr(Rsi, s.gprs))) ∧
            ((t.memory = s.memory) ∧ (read_gpr(Rbx, t.gprs) = read_gpr(Rbx, s.gprs)))) { … }
```

What it showed, beyond checking:

- The proof of `add2_returns` is about thirty lines for two instructions,
  nearly all of it restating the pre- and postcondition for
  `moves_weaken` and `moves_block`. The symbolic execution itself is three
  `refl`s. That ratio is the case for `wp-obligation-tactic`.
- `max2` lifts, but its contract was not proved: `Site::moves_branch`
  expects the emitter's TEST/JE diamond, so a CMP/JAE with fall-through
  goes through `Wp` and a memory view, which is the general route and a
  larger probe.
- The negative control (the difference claimed instead of the sum) is
  refused by the kernel at the block's `refl`.

## Appendix B. The census

`census.py` and `perfn.py` in the same folder. Method: `objdump -d -M
intel` on the cloud box's `/usr/bin/cat`, `libz.so.1` and `libc.so.6`
(2026-11-11), each instruction's text matched against the operand shapes
of `StepForm` (64-bit register pairs for MOV, ADD, SUB, AND, OR, XOR, CMP,
TEST; MOV of a 64-bit immediate; three SETcc; ADD of an immediate; shifts
by one and by an immediate; byte and word loads and stores through a bare
base register; RSP-relative spills and reloads; direct JMP, Jcc, CALL;
RET; SYSCALL), anything else assigned to the first class it fits.

Limits: text matching does not check the encoding, so "in the model" is
an upper estimate (objdump prints both encodings of `mov rax, rdi` alike,
and `decode_step_form` takes one). Functions are objdump's labels, which
for a stripped shared object are its dynamic symbols, so local functions
are merged into their neighbours. The numbers are for sizing the gap, and
would be redone against the decoder itself before any round planned on
them.
