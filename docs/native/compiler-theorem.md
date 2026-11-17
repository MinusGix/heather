# What compiling to x86-64 proves

This note states, in one place and in words, what Heather's native compiler
proves about the code it writes, what that proof assumes, and what it leaves
out. It is the page the README and the other docs quote. The theorems it
quotes are in `lib/native/function_ir/function_ir_correct.hthr`, which
restates the compiler's theorem (`function_ir_compile.hthr`) through names
that read; nothing there is proved anew, and every name unfolds to the
statement `compile-x86`'s certificates instantiate.

## The compiler's theorem

A program is a list of FunctionIR functions, each of which may call the
functions before it. `lower_program_roomed` turns it into machine code
(`Prog`) under a room table, or refuses. The compiler's theorem is proved
once, for every program and every table:

```heather
theorem compiler_correct<M>(functions: List<Function>, placement: List<Place>, rooms: Nat → Nat, code: Prog,
    lowered: lower_program_roomed(functions, placement, [], rooms) = Some(code), evaluable: program_evaluable(functions).IsTrue(),
    machine: Machine<M>, f: Nat, defined: f < functions.len(), arguments: List<BitVec(64)>,
    arity: arity_fits(program_arity(functions, f), arguments.len()).IsTrue()):
    code.Computes(machine, f, rooms(f), arguments, program_eval(functions, f, arguments))
```

In words: **whenever the lowering accepts a program, the code of each of its
functions computes what the program's evaluator says that function returns,
for every argument list of its arity, on every machine, wherever the code is
loaded.**

`code.Computes(machine, f, room, arguments, answer)` is `code.Returns(machine,
origin, last, f, room, arguments, answer)` at every load address `origin` and every
run of bytes `last` after the code, and `Prog::Returns` is the contract a
System V caller relies on. Entered at function `f`'s label with

- the arguments in RDI, RSI, RDX, RCX, R8, R9, and past the sixth on the
  stack just above the return address (`Stack::Passed`), and
- `room` bytes of stack below the return address; the theorem gives it as
  `rooms(f)`, function `f`'s row of the room table,

the machine runs to the return address and arrives there with

- `answer` in RAX,
- RBX, RBP and R12 to R15 as they were, and RSP just above the return
  address it popped,
- memory as it was except for stores into the function's own room below the
  return address (`Stack::Wrote`): the caller's frame, the return address
  and the code are untouched,
- the code still resident where it was.

The statement is total correctness. It says a run exists and ends at the
return address, not only that it ends there if it ends.

Two premises are about the program, and both are checked by evaluation.
`lowered` is the lowering's own result, which includes the stack's
accounting. A function's frame is sized by what it uses: eight words of
call slots if it calls and none if not, and a word for each callee-saved
register its placement saves (`Function::frame`, at most 112 bytes). The
lowering checks each function against its row of the table
(`Function::roomy`): the frame fits the row, a call's 24 bytes fit below
the frame, and what is left below holds each callee's row. A table that
does not fit is refused, so any table the lowering accepts is one the code
keeps to. `program_rooms_by` computes the least such table from what each
function saves, its frame and the deepest callee's room with a call's 24
bytes; `program_room` is that table with every function saving all six,
which every placement fits, and `lower_program` is the lowering under it. A
certificate states the table its placement asks for as a literal, so a
leaf that saves nothing asks for no stack below its return address. `evaluable` says every node is one
the evaluator gives a meaning to, and every call is to an earlier function
with the right number of arguments. The `placement` (which register holds
which value) comes from the planner, which is not trusted: the theorem holds
for any placement the lowering accepts, and the lowering checks the code it
writes against it (a placement that puts a value in a callee-saved register
is refused; `lib/_tests/native/function_ir/function_ir_compile_tests.hthr`
has the controls).

## What a certificate proves about one function

`heather compile-x86 file.hthr clamp` compiles a `runtime fn` and writes a
certificate beside the assembly. The kernel checks the certificate before
the assembly is written. It is the compiler's theorem at one program,
composed with one equation from the program's generator:

1. **The generator's agreement.** A `runtime fn` publishes the FunctionIR
   program it reflects to (`clamp::program`) and a theorem that the program
   computes the source function: `clamp::agrees(x, lo, hi): program_eval(clamp::program, 0, [x, lo, hi]) = clamp(x, lo, hi)`.
   It is checked by the kernel like any other theorem.
2. **The lowering, as a literal.** The certificate states the code
   (`clamp_code()`) and its room table (`clamp_rooms()`), and proves
   `lower_program_roomed(...) = Some(clamp_code())` by
   evaluation, a function at a time. It proves the program evaluable the
   same way.
3. **The bytes.** It proves that the code assembles to the bytes the `.s`
   file lists (`clamp_bytes`: `assemble(no_fills(), clamp_code(), []) = …`).

`compiled_computes` is the composition:

```heather
theorem compiled_computes<M>(functions: List<Function>, placement: List<Place>, rooms: Nat → Nat, code: Prog,
    lowered: lower_program_roomed(functions, placement, [], rooms) = Some(code), evaluable: program_evaluable(functions).IsTrue(),
    machine: Machine<M>, f: Nat, defined: f < functions.len(), arguments: List<BitVec(64)>,
    arity: arity_fits(program_arity(functions, f), arguments.len()).IsTrue(), value: BitVec(64),
    agrees: program_eval(functions, f, arguments) = value):
    code.Computes(machine, f, rooms(f), arguments, value)
```

At `clamp` it reads: **the bytes `compile-x86` wrote, called as a C function
with `x`, `lo` and `hi`, return `clamp(x, lo, hi)`.** A theorem about `clamp`
is then a theorem about what those bytes return. The probes in
`lib/_tests/native/function_ir/function_ir_correct_tests.hthr` show this
end to end at any lowering of `clamp`'s program: `clamp_computes`, and
`clamp_code_within`, where the code returns a word between the bounds
because `clamp_within` proved it of the source.

The certificate states its theorem through the same names. For
`sha256_t2` (`lib/native/crypto/sha256_round.hthr`) it reads:

```heather
theorem sha256_t2_native_returns<M>(machine: Machine<M>, a0, a1, a2: BitVec(64)):
    sha256_t2_native_code().Computes(machine, 0, 0, [a0, a1, a2], sha256_round::sha256_t2(a0, a1, a2)) {
    compiled_computes<M>(sha256_t2_native_program(), sha256_t2_native_placement(), sha256_t2_native_rooms(), sha256_t2_native_code(),
        sha256_t2_native_lowers(), sha256_t2_native_evaluable(), machine, 0, trivial, [a0, a1, a2], trivial,
        sha256_round::sha256_t2(a0, a1, a2), sha256_t2_native_agrees(a0, a1, a2))
}
```

`Prog::Returns` is what `compiled_returns` concludes, with no step between
(`returns_is_compiled_returns`), so the names add nothing to check.

Beside it the certificate states the same at every argument list, as one
line:

```heather
theorem sha256_t2_native_implements<M>(machine: Machine<M>):
    sha256_t2_native_code().Implements(machine, 0, 0, 3, sha256_round::sha256_t2) {
    λ a0 a1 a2 => sha256_t2_native_returns<M>(machine, a0, a1, a2)
}
```

`code.Implements(machine, f, room, n, spec)` takes the source function curried, a
value of `Words(n)` (`BitVec(64) → … → BitVec(64)`), and unfolds to
`(a0: BitVec(64)) → … → code.Computes(machine, f, room, [a0, …], spec(a0, …))`.
`Prog::implements_at` and `Prog::implements_of` go between it and
`Computes` at a list of `n` words, and `compiled_implements` is the
compiler's theorem in this form, from an agreement at every list of `n`
words.

A function of words is also the case of a function of spans lent nothing:
`Prog::computes_over_none` and `Prog::computes_of_over_none` turn
`Computes` into `ComputesOver` at `Lending::none()` and the empty file, and
back. So there is one contract, of which the plain one is an instance.

## Functions of spans

A function its caller lends byte spans to (as Rust does with `&[u8]` and
`&mut [u8]`) has the same theorem over memory it does not own:

```heather
theorem compiler_correct_over<M>(functions: List<Function>, placement: List<Place>, counts: List<Nat>, marks: List<Bool>, code: Prog,
    lowered: lower_program_lent(functions, placement, counts) = Some(code), evaluable: program_evaluable(functions).IsTrue(),
    within: program_stores_within(functions, marks).IsTrue(),
    machine: Machine<M>, top: Nat, addresses: List<BitVec(64)>, before: Buffers(),
    loan: Loan<M>(machine.fetch, machine.data, machine.stack, top, Lending::writing(counts, addresses, before, marks).spans()),
    f: Nat, defined: f < functions.len(), arguments: List<BitVec(64)>,
    arity: arity_fits(program_arity(functions, f), arguments.len()).IsTrue(), origin: BitVec(64), last: List<BitVec(8)>):
    code.ReturnsOver(machine, origin, last, top, Lending::writing(counts, addresses, before, marks), f, arguments, before,
        program_run(functions, before, f, arguments))
```

In words: called with each span's address and length among its arguments,
the spans holding `before` and lying anywhere the stack below `top` does not
reach (`Loan`), the code returns the word the program's run over the spans
ends in, and leaves the spans as the run leaves them. It stores nowhere but
its own stack room and the bytes of the spans `marks` lets it write
(`Stack::AnsweredOver`); every store the program makes is into one of those,
checked by evaluation (`within`). `compiled_returns_marked` is its form for a program whose functions lend
views of a span to each other.

A certificate does not state that form. It states the function by its
spans (`function_ir_borrows.hthr`, `docs/native/span-statements-design.md`):
a `Slice` is where a span lies and the bytes it holds, a `Borrow` is a
slice lent `Shared` or `Mut` (Rust's `&[u8]` and `&mut [u8]`), and

```heather
code.ComputesOn(machine, f, room, borrows, words, answer, leaves)
```

says that function `f`, called with `room` bytes of stack, each borrowed
slice's address and length and then `words`, returns `answer` and leaves the bytes `leaves` in
the slices, storing nowhere but its own stack room and the `Mut` slices,
wherever the code is loaded and wherever the slices lie that the loan's
laws hold (`Machine::Lends`). The addresses, the file, the marks and the
address and length words are read off the borrows, so the theorem has no
free word that a hidden clause ties to a span. For a function that writes
its first span, `ComputesInto` takes the source function's result
(`Mutated`): its word is the answer and its span is what the first slice
is left holding. This is what the SHA-256 functions linked into Rust are
stated with. For `copy_span` (`lib/native/native_tool_spans.hthr`), whose
Rust declaration is `copy_span(out: &mut [u8], text: &[u8], count: u64,
from: u64)`, the certificate reads:

```heather
theorem copy_span_native_returns<M>(machine: Machine<M>, s0, s1: Slice, a4, a5: BitVec(64)):
    copy_span_native_code().ComputesInto(machine, 0, 136, [Mut(s0), Shared(s1)], [a4, a5],
        native_tool_spans::copy_span(s0.bytes, s0.length(), s1.bytes, s1.length(), a4, a5))
```

It is `Prog::ComputesOver` at the borrows' lending by one lemma
(`Prog::computes_on`), and `compiler_correct_on` is the compiler's theorem
in this form. The certificate keeps the statement over any file as
`_returns_over`.

## What is assumed

The proof is checked by Heather's kernel, so the kernel is trusted. The
elaborator, the generator, the planner, the lowering's search and the
`compile-x86` driver are not: what they produce is a term the kernel checks.
Beyond the kernel, the theorem rests on these:

- **The x86-64 model** (`lib/std/arch/x86_64/`). Bytes are decoded and
  executed by a model written from the architecture manuals and checked
  against the hardware by differential tests, not proved about the
  processor. The model is sequential: one thread, no interrupts or signals,
  no other agent writing memory during the run.
- **The stack's laws** (`Stack` in `x86_64_stack.hthr`), which are premises
  of every theorem above, about whatever memory `M` is: the stack is a span
  of words below a canonical address that can be stored to and read back,
  storing one word leaves the others, code is never on the stack, every
  word of it reads as some word, and code below the canonical boundary reads
  as data where it was fetched from. They are proved of the byte memory
  model: any data region of it is a `Stack` (`DataRegion::stack`,
  `x86_64_byte_memory.hthr`), and the Linux image model has two: where the
  loader puts the process stack (`DataRegion::process_stack`) and inside
  the program's own data segment (`DataRegion::own_stack`,
  `linux_x86_64_image.hthr`). What is assumed is that those models are
  faithful to the processor's memory and to Linux's loader.
- **The loan's laws** (`Loan` in `x86_64_lending.hthr`) for functions of
  spans: the spans lie below the canonical boundary, a store into the stack
  below `top` misses them, and a store into a span the function may write
  stays inside it and misses the stack and the code. Rust's borrow of a
  slice is what makes them true; it is not proved.
- **The caller's half of the contract.** The code must be resident (the
  theorem is about a machine that holds those bytes at `origin`), entered at
  the label, with the arguments passed and the room its theorem states
  below the return address. Rust's generated declarations (`crates/linked/generated/exports.rs`)
  state the room as `STACK:` and declare the functions of words `safe`; that
  a Rust thread's stack has that room is assumed, not checked.
- **Printing the bytes.** The certificate proves the code assembles to a
  list of bytes. `compile-x86` writes the same bytes into the `.s` file as
  `.byte` directives, and the assembler and linker copy them into the
  binary. That copy is trusted.

### A whole program: what its theorem asks of the system

A program `write-elf` writes has no caller: its file is loaded and run by
Linux. The file's code is entry code and then the compiled program. The
compiled program asks, where it starts, for RSP at the top of a stack with
what the source needs (`Source::need`, a figure computed for the program
under its placement)
and RDI where the command line is; the entry code is what provides them
(`Source::runs_after`, `lib/native/native_compile_elf.hthr`). Which entry
code is a choice made when the file is written (`write-elf --stack`). Either
way the file has one record of what it presumes of the system, its
`Contract` (`docs/native/system-contract-design.md` §2): the certificate
states it (`<source>_elf_contract`, its lines by name in
`<source>_elf_presumes`), `write-elf` prints those lines, the file carries
them as an ELF note after its code (`Contract::note`, a claim a reader can
check only against the certificate), and the file's theorem,
`<source>_elf_runs` by `Source::elf_runs`, is about the file with that note
and takes the contract's `Start` as its one premise about the system. Its
conclusion is the contract's `Runs`.

**The system's stack** (`--stack system`, the default;
`stack_touched_entry`). The contract's `Start` is `SystemStart` (the theorem
behind it is `Source::elf_touched_runs`):

- **`loaded`**: the file's two `PT_LOAD` headers were honoured (its bytes at
  0x400000 readable and executable, the data segment zero-filled, readable
  and writable). The ELF loading rule, not proved of Linux.
- **`entry`**: the process starts at the header's entry address.
- **`placed`, `rsp`**: the entry RSP is a page and the program's stack room
  above the data segment's end, in the lower half of the address space.
  Nothing written says where a system puts its stack; this is taken on
  trust.
- **`argv`**: the command line is at and above RSP as the psABI lays it out.

Nothing is asked of what lies below RSP. The entry code stores a byte into
each page of the stack room before anything else runs, and the model has a
rule for what Linux does at such a store (`StackTouch`,
`lib/std/os/linux/linux_x86_64_stack_growth.hthr`): it extends the stack to
the address or ends the process with a signal, which is what mmap(2) and
getrlimit(2) say of a stack. So `Runs` is not the bare simulation: it says
the process runs to each store, that in every memory Linux may leave there
it runs to the next, and that after the last it simulates the source
(`TouchedRuns`). A process started under a stack limit below its room is
ended at one of those stores, before it has made a system call, and the
theorem says nothing false of it; before the touch it produced output and
then died mid-run (`docs/native/system-contract-design.md` §3, §4.3). The
last step identifies the state reached with one whose memory's type relies
on the room (`Alike`); that the two run alike is by inspection of the model,
not yet a lemma (`issues/elf-touched-runs-exact.md`).

**The program's own stack** (`--stack segment`; `stack_from_segment`). The
data segment is sized for the layout and the stack room after it, and the
entry code points RSP at the end of that room. The contract's `Start` is
`SegmentStart` (the theorem behind it is `Source::elf_segment_file_runs`), which is
`loaded`, `entry` and `argv` only: nothing is asked of the stack limit, of
growth, or of how much stack exec maps, and `Runs` is the simulation itself. What it costs: the stack's size is
fixed when the file is written, a limit on the data segment or the address
space kills the process at exec with a signal (before its first
instruction), and there is no guard page under the stack, so the proved
bound on its depth is all that keeps it off the data.

Under either, no register but RIP and RSP is assumed, and no flag. After the
start, each system call is answered as the model allows
(`LinuxCmd::Answers`: short reads and writes, any errno, a failed read
leaving anything in its buffer), and resumes with RCX, R11 and every
arithmetic flag unspecified, since the call convention promises none of
them. A descriptor is the low 32 bits of its word, as Linux reads it.
Signals are not modelled: a process killed by one (SIGPIPE on a closed pipe,
the kernel's out-of-memory kill) ends its run without an exit.

## What is not covered

- **The platform around the code**: the loader, the linker's placement of
  the bytes, stack alignment, and the Rust or C caller. The assembly file
  says so in its first line.
- **What the model leaves out**: timing and other side channels, faults the
  premises exclude (a stack too small is a broken premise, not a proved
  fault), and concurrent writers to a lent span.
- **The source language above the generator.** The theorem is about the
  program the generator reflected; that it is the `runtime fn`'s meaning is
  the generator's `agrees`, which is proved per function, not once.
- **Programs the lowering refuses.** The theorem says nothing about them,
  and `compile-x86` writes nothing for them.
- **Speed.** Nothing here is about how fast the code is.
- **The optimizer is not in this trust list**: it is proved, not trusted
  (below).

## Through the optimizer

`compile-x86` optimizes a program lent spans before lowering it
(`docs/native/optimizer-design.md`). Each pass is a `Stage` whose rewrite of
a function is proved to do nothing the old function could not
(`Rewrites`, `function_ir_stage.hthr`); `Stage::run_sound` lifts that to the
program, and pruning the functions nothing reaches is proved at the ones
reached (`prune_rewrites`, `function_ir_prune.hthr`). The certificate states the composition as
`ProgramRewrites(source, optimized, f)`: whatever the published program may
return and leave called at `f`, the optimized one may. The return theorems
then have `_through` forms (`compiled_returns_lent_through`,
`compiled_returns_unlent_through`, `Ending::returns_written_through`,
`Ending::returns_marked_through`) that take both programs: the code is the
optimized program's lowering, and the answer is the source program's run.
So the statement a reader quotes is unchanged by optimizing: the bytes still
compute the source function, and the passes, the search that plans them and
their plans are not trusted: the kernel checks that each stage makes the
optimized function from its plan. A function the search finds nothing for
is kept as it is (`HEATHER_OPTIMIZE=off` turns the optimizer off).

## Where the pieces are

| Piece | Where |
|---|---|
| The readable statements | `lib/native/function_ir/function_ir_correct.hthr` |
| Functions of spans stated by their spans | `lib/native/function_ir/function_ir_borrows.hthr`, `docs/native/span-statements-design.md` |
| The compiler's theorem as certificates cite it | `lib/native/function_ir/function_ir_compile.hthr` (`compiled_returns`, `compiled_returns_written`, `compiled_returns_marked`, `compiled_returns_unlent`) |
| The lowering and its proof | `lib/native/function_ir/function_ir_lower*.hthr` |
| What a caller keeps across a call (the frame rule) | `Stack::wrote_frame` in `lib/std/arch/x86_64/x86_64_stack.hthr`, `Stack::wrote_in_frame` in `x86_64_lending.hthr`; over the contract, `lib/native/function_ir/function_ir_frame.hthr` |
| The contract's controls | `lib/_tests/native/function_ir/function_ir_compile_tests.hthr` |
| The certificate's generator | `crates/cli/src/native/verified.rs` |
| The machine model | `lib/std/arch/x86_64/`, `docs/native/x86-64-execution-boundary.md` |
| The design of the one compiler | `docs/native/native-one-compiler-design.md`, `docs/native/native-library-exports-design.md` |
