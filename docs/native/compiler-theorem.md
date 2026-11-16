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
functions before it. `lower_program` turns it into machine code (`Prog`) or
refuses. The compiler's theorem is proved once, for every program:

```heather
theorem compiler_correct<M>(functions: List<Function>, placement: List<Place>, code: Prog,
    lowered: lower_program(functions, placement) = Some(code), evaluable: program_evaluable(functions).IsTrue(),
    machine: Machine<M>, f: Nat, defined: f < functions.len(), arguments: List<BitVec(64)>,
    arity: arity_fits(program_arity(functions, f), arguments.len()).IsTrue()):
    code.Computes(machine, f, arguments, program_eval(functions, f, arguments))
```

In words: **whenever the lowering accepts a program, the code of each of its
functions computes what the program's evaluator says that function returns,
for every argument list of its arity, on every machine, wherever the code is
loaded.**

`code.Computes(machine, f, arguments, answer)` is `code.Returns(machine,
origin, last, f, arguments, answer)` at every load address `origin` and every
run of bytes `last` after the code, and `Prog::Returns` is the contract a
System V caller relies on. Entered at function `f`'s label with

- the arguments in RDI, RSI, RDX, RCX, R8, R9, and past the sixth on the
  stack just above the return address (`Stack::Passed`), and
- `stack_room(f)` bytes of stack below the return address (136 a level, for
  the function and every function it may call),

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
`lowered` is the lowering's own result. `evaluable` says every node is one
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
   (`clamp_code()`) and proves `lower_program(...) = Some(clamp_code())` by
   evaluation, a function at a time. It proves the program evaluable the
   same way.
3. **The bytes.** It proves that the code assembles to the bytes the `.s`
   file lists (`clamp_bytes`: `assemble(no_fills(), clamp_code(), []) = …`).

`compiled_computes` is the composition:

```heather
theorem compiled_computes<M>(functions: List<Function>, placement: List<Place>, code: Prog,
    lowered: lower_program(functions, placement) = Some(code), evaluable: program_evaluable(functions).IsTrue(),
    machine: Machine<M>, f: Nat, defined: f < functions.len(), arguments: List<BitVec(64)>,
    arity: arity_fits(program_arity(functions, f), arguments.len()).IsTrue(), value: BitVec(64),
    agrees: program_eval(functions, f, arguments) = value):
    code.Computes(machine, f, arguments, value)
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
    sha256_t2_native_code().Computes(machine, 0, [a0, a1, a2], sha256_round::sha256_t2(a0, a1, a2)) {
    compiled_computes<M>(sha256_t2_native_program(), sha256_t2_native_placement(), sha256_t2_native_code(),
        sha256_t2_native_lowers(), sha256_t2_native_evaluable(), machine, 0, trivial, [a0, a1, a2], trivial,
        sha256_round::sha256_t2(a0, a1, a2), sha256_t2_native_agrees(a0, a1, a2))
}
```

`Prog::Returns` is what `compiled_returns` concludes, with no step between
(`returns_is_compiled_returns`), so the names add nothing to check.

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
checked by evaluation (`within`). This is what the SHA-256 functions linked
into Rust are stated with: a certificate's `_returns` for a function of
spans is `code.ComputesOver(machine, top, lending, f, arguments, file,
Ending(word := …, buffers := …))`, `Prog::ReturnsOver` at every load
address. `compiled_returns_marked` is its form for a
program whose functions lend views of a span to each other.

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
  `x86_64_byte_memory.hthr`), and the Linux image model places one where
  the loader puts the process stack (`DataRegion::process_stack`,
  `linux_x86_64_image.hthr`). What is assumed is that those models are
  faithful to the processor's memory and to Linux's loader.
- **The loan's laws** (`Loan` in `x86_64_lending.hthr`) for functions of
  spans: the spans lie below the canonical boundary, a store into the stack
  below `top` misses them, and a store into a span the function may write
  stays inside it and misses the stack and the code. Rust's borrow of a
  slice is what makes them true; it is not proved.
- **The caller's half of the contract.** The code must be resident (the
  theorem is about a machine that holds those bytes at `origin`), entered at
  the label, with the arguments passed and `stack_room(f)` bytes below the
  return address. Rust's generated declarations (`crates/linked/generated/exports.rs`)
  state the room as `STACK:` and declare the functions of words `safe`; that
  a Rust thread's stack has that room is assumed, not checked.
- **Printing the bytes.** The certificate proves the code assembles to a
  list of bytes. `compile-x86` writes the same bytes into the `.s` file as
  `.byte` directives, and the assembler and linker copy them into the
  binary. That copy is trusted.

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
| The compiler's theorem as certificates cite it | `lib/native/function_ir/function_ir_compile.hthr` (`compiled_returns`, `compiled_returns_written`, `compiled_returns_marked`, `compiled_returns_unlent`) |
| The lowering and its proof | `lib/native/function_ir/function_ir_lower*.hthr` |
| The contract's controls | `lib/_tests/native/function_ir/function_ir_compile_tests.hthr` |
| The certificate's generator | `crates/cli/src/native/verified.rs` |
| The machine model | `lib/std/arch/x86_64/`, `docs/native/x86-64-execution-boundary.md` |
| The design of the one compiler | `docs/native/native-one-compiler-design.md`, `docs/native/native-library-exports-design.md` |
