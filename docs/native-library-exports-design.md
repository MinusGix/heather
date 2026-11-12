# Native library exports: a compiled function over memory its caller lends

Status: **proposed 2026-11-10; re-sequenced 2026-11-11** by Minus's answer,
"unify first and then export". The design of memory and of the contract
below stands; the rounds of §10 now land in the order
`docs/native-one-compiler-design.md` gives (its §5 has the mapping), with
the export itself last. **Built 2026-11-11, the read half's export**
(§6.1): `compile-x86` takes a `runtime fn` that reads its spans, the Rust
declarations are generated, and the first such function is linked and
tested with the contract's controls. **Built 2026-11-12, the scanner's
loop** (R3, §6.2): `scan_token` is one linked function, proved to be the
specification's scan of a token, and the Rust scanner calls it once for
each. The write half (R4) is not built. Owner: `issues/native-library-exports-design.md` (milestone
`nh-library`), which asks for this note before any code. It extends
`docs/compilation-vision.md` (§2.5 there points here) and revises
`docs/native-lexer-crypto-roadmap.md` §2, whose lean on the unit of export
had not been checked against the proofs and does not survive the check (§2).

The read half comes first and is designed in full: a function that reads a
span of bytes its caller lends, which is what compiles the scanner's loop
(`lib/lang/lexer/lexer_tokens.hthr`, `Accepted::longest`). The write half
(a hash's state updated in place) is designed far enough to show the read
half is not a dead end (§7), and is its own round.

The memory clause of the theorem (§4) is not a sketch: its definitions,
the lemmas the proof needs from them and the machine step of a read from a
lent span were checked by the kernel against the library as it stands, over
an abstract memory and for the byte memory model. The probe is appendix A.

## 0. Recommendation

- **The unit of export is a `compile-x86` function**, not a `Source`
  procedure behind a shim. `compiled_returns` already is a call contract
  met from outside, every export in `crates/linked` already is one, and the
  verified lowering has to learn byte nodes whichever way this goes.
- **A buffer is a value in every level's meaning and an address only in the
  theorem that ties a level to the machine.** FunctionIR keeps
  `BufferLoad(output, buffer, index)` over `Buffers()`, a list of byte
  lists, as it is. What the lowering adds is a *home* for each buffer: the
  words holding its base and its length. Static, borrowed, arena and frame
  buffers are homes that differ in where the base comes from.
- **A call's effect on memory is the stores it may make.** The theorem's
  memory clause is one relation, `Wrote`: memory after the call is memory
  before it under stores into the callee's own room on the stack (and, in
  the write half, into the spans lent for writing). Everything a caller
  wants kept is a consequence: its frame, the code, the spans it lent.
  This is the one notion of footprint for exports, calls and `Proved`
  items.
- **A lent span is a premise stated semantically**: no store the call may
  make changes what the span reads (`Lends`). The compiler's proof then
  never does arithmetic on an open address, as it does not today. Where
  addresses are numbers, in the byte memory model, the premise follows from
  the span and the callee's room sharing no address, and
  `lib/std/data/set/span_set.hthr` decides that.
- **A read is in bounds because a comparison says so.** `xs.byte_at(i)`
  keeps its total meaning (zero past the end). The lowering emits a bare
  load only under a comparison `i < xs.len()` known true on the path, and
  refuses otherwise; `rt` lowers `Get` under that comparison. A loop whose
  own test is the comparison pays for no second one.
- **The Rust declaration is generated** from the export's signature, with
  one safety line per premise of the theorem, so what Rust promises is
  written where the `unsafe` is and cannot drift from the certificate.

## 1. What exists

Two pipelines reach machine code.

- **`write-elf`** compiles a `Source` program (`lib/native/native_source.hthr`):
  a closed process with static buffers (`Buffer { capacity, initial }`),
  procedures that own their words and share the buffers, and a theorem
  about the whole process under the Linux model (`native_compile_correct`).
  Its byte nodes are compiled memory-resident.
- **`compile-x86`** compiles `runtime fn`s through the verified lowering
  (`lib/native/function_ir/function_ir_lower*.hthr`) and instantiates
  `compiled_returns` (`function_ir_compile.hthr`): called at its label with
  its arguments in the six argument registers and room on the stack, the
  code returns the source function's word in RAX, keeps the callee-saved
  registers, and leaves the stack above its return address as it was. The
  frame is the only memory, and `Stack<M>` (`x86_64_stack.hthr`) the only
  law about memory. The lowering refuses `BufferLoad` and `BufferStore`.

What is already in place for memory:

- FunctionIR has the byte nodes and their meaning. `StructuredRegion::run`
  (`function_ir_state.hthr`) threads `Buffers()` through a region, a load
  reading zero past the end of a buffer, and `run_empty` ties it to `eval`.
- The machine has the load forms: `ByteLoad` (`MOVZX r64, byte [base]`) and
  `WordLoad`, each a step that exists only where the access is granted
  (`x86_64_data_read.hthr`).
- `rt` has `Bytes(cap)` meaning `List<BitVec(8)>`, with `Get`, `Set` and
  `Fold` as syntax and meaning (`lib/native/runtime/rt.hthr`). `rt_lower`
  has no case for them.
- The byte memory model instantiates the access records and builds a
  `Stack` by proof (`x86_64_byte_memory.hthr`, `DataRegion::stack`), with
  the lemmas that say a store changes only the cells it writes.
- `crates/linked` links `generated/*.s` with `global_asm!`, declares each
  export `safe fn` on the strength of `_returns`, and
  `crates/cli/tests/native_linked.rs` holds the files to the compiler.

## 2. The unit of export

The roadmap leaned towards a `Source` procedure whose shared buffers are the
caller's, entered through a System V shim, so that a library would not be a
third pipeline. Checked against the proofs, three things go against it.

1. **`Source`'s theorem is about a process.** `native_compile_correct` is a
   simulation of a closed program under Linux, entered at the ELF entry
   point. A procedure entered from Rust has no such statement: it would
   need a new theorem about entry from outside, which is the theorem
   `compiled_returns` already is.
2. **A procedure's convention is not System V.** A callee there starts with
   only its parameters, returns only results and buffers, and the caller
   saves everything; calls are depth-bounded with a trap. A shim would have
   to be proved against both conventions.
3. **Practice has already decided.** Nine exports are `compile-x86`
   functions, with a gate and tests. The word functions of both targets
   are certified that way, and the loops around them are what is missing.

So an export is a function of the verified pipeline, and that pipeline
learns to read memory. This costs nothing the other route saves: the
verified lowering must lower byte nodes with values held in registers
across them in any case (`issues/function-ir-buffer-state-edges.md`, open
since October), and when it does, `Source`'s leaves can use the same case
with a literal base. The two pipelines converge on one lowering of a byte
node instead of growing a third.

## 3. One notion of buffer

A buffer has three faces, and the design keeps them apart.

- **In a level's meaning it is a value.** `rt`: a `List<BitVec(8)>`.
  FunctionIR: an entry of `Buffers()` named by a number. No meaning
  mentions an address. This is principle 1 of the vision (the certificate
  is logical) applied to memory: a reader of `f::agrees` or of a region's
  `run` never meets a pointer.
- **In the lowering it has a home.** A function declares, for each buffer
  it uses, which of its values hold the base address and the length
  (`Function.lent: List<Home>`, a home being two value ids and whether the
  buffer may be written). The home is operational: the meaning does not
  read the base word at all, and reads the length word only as the word it
  is. The instances the roadmap listed differ only here:

  | buffer | base comes from | length |
  |---|---|---|
  | borrowed (an export's parameter) | an argument word | an argument word |
  | static (`Source`'s slots, a constant table) | a literal, or the code's own address plus an offset | a literal |
  | arena line, slice | another buffer's base plus an offset word | a word |
  | frame scratch | the stack pointer plus a slot offset | a literal |

- **In the machine theorem it is a relation** between the home's words, the
  buffer's value and memory: the base word is `a`, the length word is
  `xs.len()`, and the span is lent (§4). Only this face mentions addresses.

`issues/source-buffers-as-views.md` asked whether a buffer should become "an
address held in a word plus a capacity". The answer is yes for the home and
no for the node: `BufferLoad` keeps naming a buffer, so the IR's meaning,
its passes and `rt`'s lowering proof stay free of addresses. A view (a
slice) is a buffer whose home is computed from another's; it costs no copy
and no new node.

**The surface type** is the specification's: a parameter `source: List<u8>`.
That an export's byte-list parameter is held as a lent span is the setup's
choice of representation (the vision's separate axis, its Q10), made by the
default setup for exported functions. A parameter costs two argument
registers, pointer then length, which is how Rust passes a slice's parts
across `extern "sysv64"`. The length is read in the source by an operation
(`xs.len()` as a word, a new `rt` primitive `Len`), exact because the
contract bounds a span below the canonical boundary.

## 4. The theorem

### 4.1 What a call may store

Today `CalleePost` says the stack from the return address up reads as it
did. With lent memory the caller needs more kept (its spans), and with
written spans it needs to know what was not kept. Stating each kept thing
separately does not scale and has no room for the write half. The clause
is instead what the call may have done:

```
// One store a function entered at stack offset i may make: a word of its
// own room, below its return address.
fn Stack::Own(stack, i, before, after: M) → Type {
    ∃ k word, k + 8 <= i ∧ after = stack.writes.store(before, stack.at(k), word_bytes(word))
}

// What a call entered at i may have done to memory.
fn Stack::Wrote(stack, i, before, after: M) → Type { Star(stack.Own(i), before, after) }
```

`Star` is `lib/std/relation/transition.hthr`'s. From `Wrote` and the laws
`Stack<M>` already has:

- the caller's words, the return address included, read as they did
  (`wrote_unchanged`, from `apart`), which is today's clause and a little
  more;
- code is resident where it was (`wrote_resident`, from `keeps_code`);
- anything else a caller can prove stable under stores below `i`.

The proof obligation inside the compiler is small: a fetched step leaves
memory as it was, a spill and a CALL each add one `Own` store, and runs
compose by `Star::trans`. The existing proofs carry `Unchanged` through
`Framed`; they would carry `Wrote` and read `Unchanged` off it.

### 4.2 A lent span

```
// Bytes xs read at a, below the canonical boundary.
fn Readable(data, memory, a, xs) → Type {
    a.toNat() + xs.len() <= 2^47 ∧ ∀ k < xs.len(), data.read(memory, next_rip(a, k)) = xs.nth(k)
}

// Lent to a call entered at i: nothing the call may store changes what it reads.
fn Stack::Lends(stack, i, a, xs, memory) → Type {
    ∀ after, stack.Wrote(i, memory, after) → Readable(stack.data, after, a, xs)
}
```

`Lends` is stated as stability, not as geometry, on purpose. The compiler's
proofs name stack addresses by their offsets from `low` and never compare
open addresses; a premise "the span lies outside `[low, low + i)`" would
bring address arithmetic into every load. With `Lends` a load's proof is
two steps: the memory now is `Wrote` from the memory at entry, so the span
reads `xs` here. Three lemmas are all the lowering needs: a lent span reads
its bytes (`lends_reads`), stays lent across the function's own stores
(`lends_after`), and is lent to a callee, which is entered lower
(`lends_deeper`).

The geometry lives where addresses are numbers. For the byte memory model:
a readable span that shares no address with the stack below offset `i` is
lent (`DataRegion::lends`, by `store_outside` and `BitVec::space_apart`).
Sharing no address is two spans being apart, which `span_set` decides from
their endpoints. Note that a span *inside* the caller's own frame, above
the return address, is lent: a Rust caller passing `&buf` of a local array
is covered.

### 4.3 The statement

`compiled_returns` grows a list of buffers and one premise for each:

```
theorem compiled_returns_lent<M>(functions, placement, program, lowered, evaluable, fetch, data, last, origin,
    stack: Stack<M>(fetch, data), f, below, arguments: List<BitVec(64)>, buffers: Buffers(), fits,
    answer: BitVec(64), evaluates: program_run(functions, f, arguments, buffers) = answer):
    Site<M>(fetch, data, program, last, origin).Returns(stack, asm_labels(program)(Succ(f)),
        λ i s => ArgsIn(arguments, argument_registers(), s.gprs) ∧ 72 * Succ(f) <= i ∧
            LentAll(stack, i, function_homes(functions, f), arguments, buffers, s.memory),
        λ i s t => read_gpr(Rax, t.gprs) = answer ∧ Kept(callee_kept(), s.gprs, t.gprs) ∧
            stack.Wrote(i, s.memory, t.memory))
```

`LentAll` says, for each home: the base argument is some `a`, the length
argument is `BitVec::ofNat(xs.len())` for the buffer `xs`, and
`stack.Lends(i, a, xs, s.memory)`. `program_run` is `program_eval` over
`run`. At no buffers the statement is today's, and today's becomes its
corollary, so the nine exports' certificates do not change shape.

The certificate's last equation is still the compiler's by `refl`: the
evaluation of the reflected function over open words *and open buffers* is
the source function. `byte_at` of an open list at an open index is stuck
the same way on both sides.

**Room for leakage.** `Returns` asserts a run `MachineSteps(s, t)` and says
nothing about it but its ends. A constant-time clause
(`issues/native-constant-time.md`) is a statement about the run's labels,
so it is a second theorem over the same run with the step relation
labelled (`lib/std/relation/labelled_transition.hthr`), not a change to
this one. The checked read of §5 branches on the index, never on a byte
read, which is the property such a clause would want of it.

## 5. Reads in bounds

`xs.byte_at(i)` is total: zero past the end. The machine's load is not: it
has a step only where the byte is granted. Something must bridge them, and
there are three places to put it.

- *In the load's code*, a compare and a branch inside every load. A
  dataflow block is straight-line, so this needs a conditional move the
  instruction set does not have yet, or an address masked into the frame.
- *In a fact*, an `InBounds` proof per read
  (`lib/lang/facts/in_bounds.hthr`). Right for an optimizer, wrong as the
  only way: a read nothing proves must still compile.
- *In the path.* The lowering's file would record which comparison bits
  are known true where it stands: it enters the true arm of a
  `Conditional` knowing its condition. A `BufferLoad(out, b, i)` is lowered
  to a bare load when the file knows a bit defined as
  `UnsignedLessThan(i, len(b))`, and refused otherwise. Which bit is the witness is the untrusted plan's
  to say and the checked lowering's to verify (principle 2).

The design takes the third and layers the others on it. `rt` lowers `Get`
as the conditional it means: under `i < len` the load, otherwise the
constant zero. That is always accepted and always correct. A source loop
that tests `at < source.len()` before it reads shares the comparison with
the read's own guard once conditions are value-numbered (the reflector
already numbers values), so the scanner pays one comparison a byte. An
`InBounds` fact later removes a guard as a pass with the fact as its law's
hypothesis, which is the vision's §2.3 unchanged.

What a load compiles to: the address `base + index` in a scratch register
by the 64-bit add the lowering has, then `MOVZX` at zero displacement, the
form `ByteLoad` already certifies. No new instruction is needed for the
read half. The add is `next_rip(a, k)` by `BitVec::iter_add_eq_add`, the
same step `displaced_at` takes for frame slots, with `k < xs.len()` and the
canonical bound keeping it from wrapping. This step is checked too
(`lent_load_step`, appendix A): from `Lends`, `Wrote` since entry, the
register's equation and the index below the length, the machine's
`ByteLoadStep` of `xs.byte_at(index)`.

## 6. The contract

The name is provisional (`issues/named-abi-contracts.md` owns naming):
**System V AMD64, words and lent spans**. A name selects this
specification; the evidence that a function meets it is its `_returns`.
Each clause is listed with what states it and the control that shows the
clause has teeth. Controls in Heather are theorems or expected refusals
under `lib/_tests`; controls that need a running process are tests of
`crates/linked` (`issues/native-differential-harness.md`).

| # | clause | stated by | negative control |
|---|---|---|---|
| 1 | Up to six words arrive in RDI, RSI, RDX, RCX, R8, R9; a span is two of them, pointer then length | `ArgsIn`, `LentAll` | a seventh word is refused by `compile-x86`, as today; an export declared with its span's parts swapped fails the reference test |
| 2 | One word returns in RAX | `Returns` post | (several results are §8) |
| 3 | RBX, RBP, R12 to R15 are kept and RSP is back above the return address | `Kept(callee_kept())`, `Returns` | a placement that puts a value in a callee-saved register: `lower_program` is `None` (the lowering checks its own code with `leaves_all`), a theorem by evaluation |
| 4 | The callee stores only into its own room below the return address, and into the bytes of a span lent to write (§7.1) | `Wrote`; `WroteIn` under the lending's marks | a store at or above the return address's offset is shown *not* to satisfy `Unchanged` for a differing word, so no function that made it could meet the post; a program that stores into a buffer its marks leave out has no proof of the certificate's premise; process tests put unmapped pages on both sides of a written span |
| 5 | The callee reads only its frame and the spans lent | the load's premise, §5 | a load with no known comparison: `lower_program` is `None`; a process test passes a span that ends at an unmapped page and reads at its length, and an empty slice (whose pointer dangles), expecting zero and no fault |
| 6 | The stack has `72` bytes of room a level of calls | `72 * Succ(f) <= i` | none in the proof's reach; the bound is a constant printed beside the declaration |
| 7 | Stack alignment is neither required nor provided | no premise mentions it; the code calls only compiled code | the process tests enter every export at both alignments |
| 8 | No red zone is used: the frame is opened by moving RSP first | `frame_allocate`; every store is at or above RSP | covered by clause 4's statement |
| 9 | The direction flag, x87, SSE and MXCSR are untouched | **not modelled.** Holds because the emitter has no instruction that writes them | an inventory test over `Instruction`; a model of DF is filed only when a string instruction is wanted |

**Outside the proof**, as now: that `extern "sysv64"` passes arguments so,
the assembler and the linker, that the kernel does not write below RSP
outside a signal frame the process set up, and the Rust caller's premises
below.

**What Rust promises, and where it is written.** `scripts/linked` writes
the declarations as well as the assembly: `generated/exports.rs`, from a
signature column in `EXPORTS.tsv` that the gate holds to the certificate's
own signature. For a function with a span the raw declaration is `unsafe`
and a generated safe wrapper takes `&[u8]`:

```rust
/// `scan_token` of lib/lang/lexer/lexer_scan.hthr. STACK: 144 bytes.
pub fn scan_token(source: &[u8], at: u64, previous: u64) -> u64 {
    // SAFETY (the premises of scan_token_returns, in order):
    // - arguments in registers: the declaration's order is the table's.
    // - length word is the span's length: `source.len()`.
    // - the span reads `source` below the canonical boundary, and no store
    //   below this call's return address changes it: a `&[u8]` is live,
    //   readable memory, which is never the unused stack below RSP.
    unsafe { raw::scan_token(source.as_ptr(), source.len() as u64, at, previous) }
}
```

The crate's one `unsafe` module is then generated in full, and a hand edit
to it is a gate failure. A word function stays `safe fn` as today.

### 6.1 As built (2026-11-11)

**The certificate.** `compile-x86` on a `runtime fn` whose generator
published `f::agrees_over` (one that reads spans) emits each function with
`Function::emit_lent` under the program's counts of lent buffers, read off
the program by evaluation and stated as a literal, and its `_returns` is
`compiled_returns_lent` at any file `now` lying at any `addresses` under a
`Loan`: the premise is `ArgsIn` and the stack's room as for words, and
`Stack::LentOver` (each span's two words are its address and its length,
the file is readable there); the post is `Stack::AnsweredOver` at the
source function applied to `now.span(j)` and the words, with the file left
as it was. `{prefix}_quiet` (no function stores into a buffer) is by
evaluation. A function that stores into its span (`f::runs_over`) is
refused by name: its contract has a clause more.

**The signature is the compiler's, the names are the table's.** The
assembly file states what its code takes, from the values the certificate
is stated with:

```
# signature: count_newlines(span, word) -> word
# stack: 144 bytes below the return address
```

`EXPORTS.tsv` gains a column, the parameters as Rust names them
(`text: span, count`). `heather linked-exports` (`heather_cli::linked`,
run by `scripts/linked`) writes `generated/exports.rs` from the two, and
refuses a row whose kinds are not the file's: a span declared as two
words, a word as a span, a parameter too few. So the declaration cannot
pass a pointer where the certificate says a count, and the stack figure
beside it is the theorem's. `crates/cli/tests/linked_exports.rs` holds the
file to its generator in every lane; the assembly is held to the compiler
by `native_linked.rs` as before.

**The first export** is `count_newlines`
(`lib/native/native_tool_spans.hthr`, `heather_linked::spans`).

**Where each clause's control is.**

| # | control | where |
|---|---|---|
| 1 | a seventh word, the function's own or a span's two among them | `native_linked.rs`, `what_the_contract_does_not_take_is_refused` |
| 1 | a declaration against the code's signature | `linked.rs`'s unit tests; `linked_exports.rs` on the real files |
| 3 | a value placed in RBX, RBP, RSP, R12 to R15 has no code | `function_ir_compile_tests`, `into_*_refused` |
| 3 | the callee-saved registers across a real call | `crates/linked/tests/spans.rs`, `both_stack_alignments` |
| 4 | a differing word stored at or above the entry offset is not `Unchanged` | `function_ir_compile_tests`, `store_above_is_not_unchanged` |
| 4 | a function that stores into its span is not exported | `native_linked.rs`, the same test |
| 5 | a load no comparison bounds, the wrong bound, the wrong arm, another buffer | `function_ir_lower_reads_tests`, `*_refused` |
| 5 | a count of lent buffers that is not the code's | `function_ir_compile_tests`, `first_byte_*_refused` |
| 5 | a span ending at an unmapped page, read at and past its length; an empty slice | `spans.rs`; the kernel is asked to confirm the next byte cannot be read |
| 6 | the stack figure | printed in the assembly and beside the declaration |
| 7 | both stack alignments | `spans.rs`, `both_stack_alignments` |
| 7, 9 | the code calls only compiled code | `compile-x86` refuses an emission holding a system call |
| 9 | the instruction inventory | `function_ir_compile_tests`, `Instruction::written`: a match with no default arm, so a new instruction is classed before the library checks |

Not done: clause 7 is exercised for the span exports only (the word
exports are entered at the platform's alignment by their own tests), and
the contract still has no name (`issues/named-abi-contracts.md`).

### 6.2 The scanner's loop (2026-11-12)

**What is linked.** `lib/lang/lexer/lexer_span.hthr`: `scan_token(source,
length, at, previous)` is the longest token of the span from `at`, after
a token of kind `previous`, answered as one word (the kind above the
offset just past the token, zero for a refusal). Its loop, `scan_from`,
is a measured `runtime fn` lent the span; a pass calls the automaton's
step at the span's byte (`scan_at`) and remembers the last accept
(`scan_last`), and where it stops is decided after the loop
(`scan_stopped`), so the loop has one way round. When it was written the
companions of a `decreases` function needed that
(`issues/decreases-no-companions-nested-match-calls.md`, fixed by #579);
it is kept because `scan_token_longest` is proved over it. The compiled
program is the loop with the whole automaton under it, one certificate.
`heather_linked::scanner::token` is the call; `Scanner` is what is left
in Rust, the iterator that drops whitespace and comments and hands out
values, which a compiled function cannot write into its caller's memory
before the write half.

**The theorem.** `scan_token_longest`: at a source whose length is the
length word and an offset inside it, `scan_token` is `Accepted::word` of
`Accepted::longest(scan_begin(previous), source.drop(at), at, None)`,
which is the call `Scanned::from` makes. It is by recursion on what is
left of the source (`scan_from_longest`), each step the loop's unfolding
at a test that is true or false. As §10 said of it, this is a theorem
about two Heather functions and not about compiled code; the certificate
is what takes it to the bytes.

**What it took**, each found by the loop and none special to it:

- *The generator's proof of a loop lent a span* compared the body's
  meaning at two spellings of one file and ran past the conversion
  budget; the family it proves is now keyed
  (`Fun::GuardedBy`, `docs/native-one-compiler-design.md` §2.3).
- *The certificate's `{prefix}_quiet`* was one evaluation of the whole
  program and ran out of the kernel's fuel with the automaton in it; it
  is proved a function at a time, as `{prefix}_evaluable` is
  (`program_quiet_drop`).
- *The register planner* lost a value in the loop's pass twice: a loop
  that calls has three registers free in its body. The loop was first
  linked with its source written round that (the state tested before the
  bound, the offset as the last parameter), and is written in the
  specification's order since the cause was fixed
  (`issues/function-ir-planner-register-pressure.md`). Three things
  fixed it. The verified lowering has a second form of a comparison of
  words, `CMP a, b; MOV d, 0; SETcc d` (`File::compare_over`): a MOV
  writes no flag, so the bit may take the register of an operand that
  dies at the comparison, which the XOR form cannot. The planner, with no
  register free, takes RAX if nothing live is there and else such an
  operand's register (`Node::crowded`). And a loop's body is planned with
  nothing read past a call but what its own calls cross, so the last
  values of a pass may stay in RAX. `compile-x86`'s refusal now names the
  function, the node, its place and what each register held, by
  evaluating the library's mirror of the emitter's tests
  (`lib/native/function_ir/function_ir_refusal.hthr`).

**Controls.** `tests/scanner.rs`: the scanner through `token` against
`heather_syntax::lex` on every source in the repository and on its
generated strings, as before the loop moved; and `token` against the
loop it replaced, kept in the tests as a Rust function over the three
linked automaton functions, from every offset of the lexer's sources and
of the probes, from past the end, and over bytes that are not text.
`tests/spans.rs`: a token that runs to the last byte before an unmapped
page (clause 5), and the loop entered at both stack alignments with the
callee-saved registers compared (clauses 3 and 7), which here is code
that calls compiled code.

**Not done.** The word's packing is read apart in Rust (`>> 56`, a
mask): that a kind and an end below 2^56 come back from `token_word` is
not a theorem yet, only tested. The crate holds the automaton twice, in
`scan_step`'s program and in `scan_token`'s, since an export is a
program of its own; the three automaton exports stay for the tests that
walk its states.

## 7. The write half, in outline

Not built by the read rounds; here to show they do not have to be redone.
The design is `docs/native-one-compiler-design.md` §2.6 (U4), which
changes one thing below: lending is stated as laws at every memory, and
`Lends` follows from them instead of being quantified over a larger
relation.

- A home marked writable adds its span's bytes to what the call may store:
  `Wrote` takes the footprint, the callee's room and the written spans.
  The post gains, for each, that the span reads the buffer `run` leaves.
- `Lends` for a read span quantifies over that larger relation, so a read
  span and a written span being apart is the caller's premise. Rust's
  `&`/`&mut` rules give it, which is why the generated wrapper may take
  `&mut [u8; 32]` beside `&[u8]`.
- `Set` builds a new buffer in the meaning. In place is sound when the old
  one is dead, which is `Unique` (`lib/lang/facts/unique.hthr`, built) and
  the file's lookup refusing a stale buffer
  (`issues/function-ir-buffer-state-edges.md`'s scope, unchanged).
- Byte stores exist as machine forms (`x86_64_store.hthr`).

### 7.1 As built (2026-11-12)

Most of the outline was built by U4 for a program that lends its own
buffers (`docs/native-one-compiler-design.md` §2.6): the laws of a loan
(`Loan`), the post over a changing file (`Stack::WroteIn`,
`Stack::AnsweredOver`), the store leaf, and `compiled_returns_run`, which
states a function's return over any lending that lets every buffer the
program stores into be written. What an export added is small, and is
the part that faces a caller who is not a Heather program.

- **Which buffers are written is data.** `compiled_returns_run` asks for
  `lending.written(b) = True` at every buffer `b` the program stores into,
  a premise about a function. A caller is told with a list:
  `program_stores_within(functions, marks)` says every store of every
  function is into a buffer `marks` marks, one walk of each function
  checked by evaluation a function at a time, and `program_stores_marked`
  turns it into that premise (`function_ir_writes.hthr`).
  `Lending::writing(counts, addresses, buffers, marks)` is the lending
  that lets exactly the marked buffers be written, and
  `compiled_returns_written` the theorem a certificate instantiates
  (`function_ir_compile.hthr`). `program_quiet` is the case of no marks,
  and a lending to read the lending with none.
- **`compile-x86` takes a `runtime fn` that stores into its span.** It
  reads the marks off the published program (`program_marks`), states
  them in the certificate (`{prefix}_marks`), proves `{prefix}_within`,
  and its `{prefix}_returns` is over any file whose first span is `span`:
  called with the span's address and the function's words, the file in
  memory under a `Loan` at that lending, the code answers the function's
  word and leaves the file with the function's span where `span` was and
  the rest as it was. The run is the generator's `f::runs_over`; nothing
  about the function is proved for the export.
- **The signature follows the code, not the type.** The assembly says
  `span mut` for a span some function of the program stores into
  (`# signature: raise_span(span mut, word, word) -> word`), and `span`
  otherwise: a function whose type ends in `Mutated` and that stores
  nothing is lent its span to read. `EXPORTS.tsv` writes the kind as
  `name: span mut`, and a row that lends a span the other way from the
  code is refused, in either direction.
- **The Rust wrapper takes `&mut [u8]`.** A lending to write asks five
  laws more of the caller's memory than one to read: the span's bytes are
  writable, a byte stored reads back, and a store there changes no other
  byte of any span, no word of the stack below the call and none of the
  code (`Loan::writable`, `stored`, `apart`, `keeps`, `keeps_code`). An
  exclusive borrow of initialised bytes gives all five, which the
  generated `SAFETY` comment says beside the call. What the caller keeps
  of a span beside the written one is `Loan::unwritten_reads`: a span the
  lending does not mark reads after the call as before
  (`unmarked_span_is_kept` in the compile probes).
- **The first such export is `raise_span`** (`heather_linked::spans`):
  letters raised to upper case in place, from an index to below a count.
  Tests in `crates/linked/tests/spans.rs`: against plain Rust on texts of
  every length with starts and counts on both sides of the length; the
  span inside a larger buffer whose other bytes a store would change; the
  span with an unmapped page on each side (the kernel asked to confirm
  both), ending at the upper one and starting at the lower; an empty
  slice; both stack alignments with the callee-saved registers compared.
- **Controls in Heather**: `function_ir_writes_tests.hthr` (the marks of
  a program whose callee stores, of one that stores into two buffers and
  of one that stores into none; not within marks that leave a stored
  buffer out, wherever the gap is) and `function_ir_compile_tests.hthr`
  (the lending lets the marked and no other; an unmarked span is kept;
  the certificate's premise has no proof for a hidden store).
- **Loops are written as loops.** #579 gave a `decreases` function's
  companions the two forms the generator had been written round, so
  `raise_span` makes its store as a statement before its own call, and a
  loop may leave from inside or call itself in two places
  (`runtime_span_tests.hthr`: `clear_from`, `clear_line`, `clear_text`).

Limits, each refused by name or filed: one span per writer
(`issues/runtime-loop-over-several-spans.md` for loops; a writer's
generator takes one span), six words in registers with the span's address
and length among them, and a byte read before a store and used after it
(`issues/rt-file-read-before-store.md`). In-place `Set` under `Unique`
(the third point of the outline) was not needed: a writer's meaning
threads the span, and the store leaf is proved against the file the run
leaves. SHA-256's state as a customer waits on
`issues/rt-fixed-arrays-and-tables.md`, as §10 says.

## 8. Results, tables, position, artifact

- **Results.** One word. The scanner's token is a kind and an end, packed
  into the word (the end is below the canonical bound, the kind above it),
  which needs nothing new. Two words in RAX:RDX is the System V answer for
  a two-word struct and belongs to `function-ir-multi-word-calls`; more
  than two go through a written span.
- **Constant tables** are spans lent by the linker instead of the caller:
  bytes placed after the code (`Site.last` already names them), read
  through the same load, the base formed from the code's own address. That
  is one instruction form, `LEA r64, [rip + disp32]`, and one premise, that
  the bytes after the code are readable as well as fetchable. It is also
  the whole of position independence: the code today has only relative
  jumps and calls, so it is position independent until it has a table.
  Owner: `issues/rt-fixed-arrays-and-tables.md`.
- **The artifact** stays assembly text carrying certified bytes. An object
  writer in Heather would have to be linked by a build script, which
  cannot run `heather`; `global_asm!` needs nothing. The checked-in files
  gain the signature column and the generated declarations (§6); the
  certificate itself is not checked in, since the gate rebuilds it and
  compares bytes.
- **Fallback.** The Rust reference for every export stays, as the path on
  hosts that are not x86-64 Linux and as the differential oracle.

## 9. What this supersedes

No new long-lived issue is needed; the rounds land on issues that exist.

| issue | what happens to it |
|---|---|
| `native-library-exports-design` | closes when this note is accepted and the rounds are logged where they land |
| `function-ir-buffer-state-edges` | becomes the lowering rounds: R1 is its read half, the write half its remainder |
| `x86-call-memory-footprints` | absorbed: `Wrote` is the call memory contract it asked for; closes with R1 |
| `source-buffers-as-views` | answered by §3; stays open for the view instances (arena line, static, frame) and its own done-when |
| `wp-proved-memory-contracts` | points at `Wrote` as the footprint of a `Proved` item; stays open for the `Wp` side |
| `runtime-default-setup-soundness` | owns R2, `Get` and `Len` in `rt_lower` with the theorem over `run` |
| `self-lexer-linked` | owns R3, the scanner's loop exported |
| `named-abi-contracts`, `runtime-extern-c-abi` | take §6 as the first named contract; alignment becomes a clause when imports exist |
| `native-differential-harness` | takes the process controls of §6 |
| `native-procedure-contracts` | untouched: `Source` procedures keep their own convention |

## 10. The rounds

Each is one PR, in this order, and each ends with something that runs.

- **R1. The lowering reads.** `Function.lent`, `program_run`, the file's
  known comparisons, `BufferLoad` lowered under one, `Wrote` carried in
  place of `Unchanged`, `compiled_returns_lent` with today's theorem as its
  corollary. Controls 3, 4 and 5 of §6 in Heather. A hand-written IR
  function that reads a byte certifies and runs.
- **R2. `rt` reads.** `Len`, `Get` lowered as its guard, `Tm::lower_sound`
  over `run`, the generator and `compile-x86` taking a `List<u8>`
  parameter, the signature column and generated declarations. A
  `runtime fn` that sums a span is exported and tested from Rust, with the
  process controls.
- **R3. The scanner's loop.** `scan_token` as a `runtime fn` over the
  source, an offset and the previous kind; a library theorem that it is
  `Accepted::longest` on the suffix at that offset; the Rust loop in
  `crates/linked/src/scanner.rs` reduced to calling it a token at a time.
  The existing test against `heather_syntax::lex` on every source in the
  repository is the acceptance. *Built 2026-11-12 (§6.2).*
- **R4. The write half** (§7), with SHA-256's state as its customer, after
  `rt-fixed-arrays-and-tables` gives the schedule and the constants a
  place. *The export is built 2026-11-12 (§7.1), with `raise_span` as its
  first function; SHA-256's state is not.*

R3's theorem is not a proof about compiled code: it relates two Heather
functions, one recursing on a list and one indexing it, and is proved once
in the lexer's library.

## 11. Decisions for Minus

1. **The unit of export** is a `compile-x86` function over lent spans
   (§2), reversing the roadmap's lean. This is the one that redirects
   work.
2. **`Wrote` as the one footprint** (§4.1), replacing `Unchanged` in the
   function compiler's post and absorbing the call-footprint issue.
3. **Reads guarded by a known comparison** (§5): total meaning kept, the
   check elided by the path first and by facts later.
4. **Generated Rust declarations** (§6), so the `unsafe` module is the
   compiler's output.

## Appendix A. The probe

Checked by the kernel on 2026-11-10 against the library on this branch, and
not committed as a module (the issue asks for no code before the note is
accepted), so the text is kept here. No part needed a new law on
`Stack<M>` or on the memory model. What the probe does not cover is the
lowering's bookkeeping: the file's known comparisons and the load's case
in `emit`, which are R1.

Over any memory, importing the x86 model, `x86_64_stack` and `transition`:

```
// Bytes `xs` read at `a`, below the canonical boundary.
fn Readable<M>(data: ByteReadAccess<M>, memory: M, a: BitVec(64), xs: List<BitVec(8)>) → Type {
    (a.toNat() + xs.len() <= Nat::pow(2, 47)) ∧ ((k: Nat) → k < xs.len() → data.read(memory, next_rip(a, k)) = xs.nth(k))
}

// One store a function entered at stack offset `i` may make: a word of its
// own room, below its return address.
fn Stack::Own<M>({fetch: FetchAccess<M>}, {data: ByteReadAccess<M>}, self stack: Stack<M>(fetch, data), i: Nat, before, after: M) → Type {
    Exists<Nat>(λ k => (k + 8 <= i) ∧ Exists<BitVec(64)>(λ word => after = stack.writes.store(before, stack.at(k), word_bytes(word))))
}

// What a call entered at `i` may have done to memory.
fn Stack::Wrote<M>({fetch: FetchAccess<M>}, {data: ByteReadAccess<M>}, self stack: Stack<M>(fetch, data), i: Nat, before, after: M) → Type {
    Star(λ (m: M) (n: M) => stack.Own(i, m, n), before, after)
}

// A span is lent to a call entered at `i`: nothing the call may store
// changes what it reads.
fn Stack::Lends<M>({fetch: FetchAccess<M>}, {data: ByteReadAccess<M>}, self stack: Stack<M>(fetch, data), i: Nat, a: BitVec(64),
    xs: List<BitVec(8)>, memory: M) → Type {
    (after: M) → stack.Wrote(i, memory, after) → Readable(data, after, a, xs)
}

// The caller's words, the return address included, are as they were.
theorem Stack::wrote_unchanged<M>({fetch: FetchAccess<M>}, {data: ByteReadAccess<M>}, self stack: Stack<M>(fetch, data), i: Nat,
    room: i <= stack.size, before, after: M, wrote: stack.Wrote(i, before, after)): stack.Unchanged(i, before, after) {
    Star::invariant(λ (m: M) (n: M) => stack.Own(i, m, n), λ (m: M) => stack.Unchanged(i, before, m),
        λ m n held step => j(sym(step.proof.right.proof), λ x _ => stack.Unchanged(i, before, x),
            stack.unchanged_trans(i, before, m, stack.writes.store(m, stack.at(step.witness), word_bytes(step.proof.right.witness)), held,
                stack.store_below(m, step.witness, i, omega(step.proof.left, room), step.proof.left, step.proof.right.witness))),
        before, after, stack.unchanged_refl(i, before), wrote)
}

// Code stays where it was.
theorem Stack::wrote_resident<M>({fetch: FetchAccess<M>}, {data: ByteReadAccess<M>}, self stack: Stack<M>(fetch, data), i: Nat,
    room: i <= stack.size, bytes: List<BitVec(8)>, at: BitVec(64), before, after: M, wrote: stack.Wrote(i, before, after),
    resident: CodeResident(fetch, before, bytes, at)): CodeResident(fetch, after, bytes, at) {
    Star::invariant(λ (m: M) (n: M) => stack.Own(i, m, n), λ (m: M) => CodeResident(fetch, m, bytes, at),
        λ m n held step => j(sym(step.proof.right.proof), λ x _ => CodeResident(fetch, x, bytes, at),
            stack.keeps_code(m, step.witness, omega(step.proof.left, room), step.proof.right.witness, bytes, at, held)),
        before, after, resident, wrote)
}

// A lent span reads its bytes, stays lent across the call's own stores, and
// is lent to whatever the call calls (entered lower).
theorem Stack::lends_reads<M>({fetch: FetchAccess<M>}, {data: ByteReadAccess<M>}, self stack: Stack<M>(fetch, data), i: Nat, a: BitVec(64),
    xs: List<BitVec(8)>, memory: M, lent: stack.Lends(i, a, xs, memory)): Readable(data, memory, a, xs) {
    lent(memory, Star::refl(λ (m: M) (n: M) => stack.Own(i, m, n), memory))
}

theorem Stack::lends_after<M>({fetch: FetchAccess<M>}, {data: ByteReadAccess<M>}, self stack: Stack<M>(fetch, data), i: Nat, a: BitVec(64),
    xs: List<BitVec(8)>, before, after: M, lent: stack.Lends(i, a, xs, before), wrote: stack.Wrote(i, before, after)):
    stack.Lends(i, a, xs, after) {
    λ later more => lent(later, Star::trans(λ (m: M) (n: M) => stack.Own(i, m, n), before, after, later, wrote, more))
}

theorem Stack::lends_deeper<M>({fetch: FetchAccess<M>}, {data: ByteReadAccess<M>}, self stack: Stack<M>(fetch, data), i, d: Nat, le: d <= i,
    a: BitVec(64), xs: List<BitVec(8)>, memory: M, lent: stack.Lends(i, a, xs, memory)): stack.Lends(d, a, xs, memory) {
    λ after wrote => lent(after, Star::monotone(λ (m: M) (n: M) => stack.Own(d, m, n), λ (m: M) (n: M) => stack.Own(i, m, n),
        λ m n step => Exists(step.witness, ⟨omega(step.proof.left, le), step.proof.right⟩), memory, after, wrote))
}
```

For the byte memory model, importing `x86_64_byte_memory` and `memory` as
well:

```
// A readable span that shares no address with the room below offset `i` of
// the stack is lent to a call entered there.
theorem DataRegion::lends(self r: DataRegion, i: Nat, room: i <= r.size, a: BitVec(64), xs: List<BitVec(8)>,
    outside: (a.toNat() + xs.len() <= r.low.toNat()) ∨ (r.low.toNat() + i <= a.toNat()),
    m: X86Memory(r.profile), readable: Readable(r.profile.data(), m, a, xs)): r.stack().Lends(i, a, xs, m) {
    let top = canonical_below_top();
    λ after wrote => ⟨readable.left, λ k inside =>
        Star::invariant(λ (n: X86Memory(r.profile)) (o: X86Memory(r.profile)) => r.stack().Own(i, n, o),
            λ (n: X86Memory(r.profile)) => r.profile.read(n, next_rip(a, k)) = xs.nth(k),
            λ n o held step => {
                let at = step.witness;
                let word = step.proof.right.witness;
                let value = r.toNat_at(at, omega(step.proof.left, room));
                let apart: BitVec::space(64).Apart(next_rip(r.low, at), 8, a, xs.len()) = match outside {
                    Inl(under) => BitVec::space_apart_above(64, next_rip(r.low, at), 8, a, xs.len(), omega(under, value),
                        omega(value, step.proof.left, room, r.canonical, top)),
                    Inr(over) => BitVec::space_apart(64, next_rip(r.low, at), 8, a, xs.len(), omega(over, value, step.proof.left),
                        omega(readable.left, top)),
                };
                let stored = r.profile.store(n, next_rip(r.low, at), word_bytes(word));
                let same: (r.profile.read(stored, next_rip(a, k)) = r.profile.read(n, next_rip(a, k))) =
                    r.profile.read_agree(n, stored.cells, next_rip(a, k),
                        r.profile.store_outside(n, next_rip(r.low, at), word_bytes(word), next_rip(a, k), λ p below => apart(p, k, below, inside)));
                j(sym(step.proof.right.proof), λ x _ => r.profile.read(x, next_rip(a, k)) = xs.nth(k), trans(same, held))
            },
            m, after, readable.right(k, inside), wrote)⟩
}
```

The machine step of a read (§5), importing `rt` for `byte_at`: a register
holding the base plus the index reads the span's byte, at any memory the
call's own stores have reached.

```
// Inside its length a list has the byte `byte_at` answers.
theorem nth_or_zero(xs: List<BitVec(8)>): (k: Nat) → k < xs.len() → xs.nth(k) = Some(xs.nth(k).unwrap_or(BitVec::ofNat(0))) {
    match xs {
        Nil => λ k h => false_elim(h),
        Cons(_, t) => λ k => match k {
            Zero => λ _ => refl,
            Succ(j) => λ h => nth_or_zero(t, j, h),
        },
    }
}

theorem List::nth_byte_at(self xs: List<BitVec(8)>, index: BitVec(64), inside: index.toNat() < xs.len()):
    xs.nth(index.toNat()) = Some(xs.byte_at(index)) {
    nth_or_zero(xs, index.toNat(), inside)
}

// A register holding base plus index reads the lent span's byte there, at
// any memory the call's own stores have reached.
theorem lent_load_step<M>(fetch: FetchAccess<M>, data: ByteReadAccess<M>, stack: Stack<M>(fetch, data), i: Nat, a: BitVec(64),
    xs: List<BitVec(8)>, entry: M, lent: stack.Lends(i, a, xs, entry), load: ByteLoad, index: BitVec(64), before: MachineState<M>,
    wrote: stack.Wrote(i, entry, before.memory), held: read_gpr(load.base, before.gprs) = a.add(index), inside: index.toNat() < xs.len()):
    ByteLoadStep<M>(data, load, xs.byte_at(index), before, byte_load_after(load, xs.byte_at(index), before)) {
    let readable = lent(before.memory, wrote);
    let address: (a.add(index) = next_rip(a, index.toNat())) = sym(BitVec::iter_add_eq_add(64, a, index));
    let top: (Nat::pow(2, 47) < Nat::pow(2, 64)) = Nat::leb_sound(Succ(Nat::pow(2, 47)), Nat::pow(2, 64), trivial);
    let value: (next_rip(a, index.toNat()).toNat() = a.toNat() + index.toNat()) =
        BitVec::offset_toNat(64, a, index.toNat(), omega(readable.left, inside, top));
    let at = trans(held, address);
    ByteLoadStep(
        canonical := j(sym(at), λ x _ => x.drop_low(47, 17) = BitVec::zero(),
            BitVec::drop_low_zero_of_lt(47, 17, next_rip(a, index.toNat()), omega(value, readable.left, inside))),
        present := j(sym(at), λ x _ => data.read(before.memory, x) = Some(xs.byte_at(index)),
            trans(readable.right(index.toNat(), inside), xs.nth_byte_at(index, inside))),
        execution := refl)
}
```
