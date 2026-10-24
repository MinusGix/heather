# A Heather function in a native executable

From the repository root on x86_64 Linux with a C compiler/linker:

```sh
cargo build -p heather-cli
mkdir -p target/x86-native
(ulimit -v 8388608 -t 300; target/debug/heather compile-x86 \
  examples/x86-native/mix.hthr mix -o target/x86-native/mix.s \
  --cache-dir target/native-images)
cc -std=c11 -Wall -Wextra -Werror examples/x86-native/main.c \
  target/x86-native/mix.s -o target/x86-native/mix
./target/x86-native/mix
```

Expected output:

```text
mix(20, 22) = 81985529216486963; 10005 native cases passed
```

The command refuses existing assembly or certificate outputs. Remove those
outputs deliberately before rebuilding, or choose a fresh output name.

`mix.hthr` is the compiled program: it shares an addition, adds a full-width
constant, and XORs the results. The C file supplies `main` and checks boundary values and
10,000 deterministic pseudorandom pairs against unsigned C arithmetic.

## What `compile-x86` certifies

`compile-x86` compiles a function with `BitVec(64)` parameters (at most six)
and a `BitVec(64)` result, together with the word functions it calls,
through the verified lowering ([round 4 of the issue](../../issues/function-ir-verified-lowering.md)).
The body may use Add, Sub, AND, OR, XOR, `bitvec::ofNat` literals of any
size, `let`, calls, and tail-position matches on a test. A test is
`unsigned_lt_bit`, `signed_lt_bit` or `eq_bit` of words, `||`, `&&` and `!`
of tests, or a call of a `Bool` helper of words whose body is a test
(`branches.hthr`'s `composed` and `either`). Connectives and helpers become
conditionals on plain comparisons, each operand tested only where its
connective needs it. A source outside that fragment still takes the
per-function certificate described in the sections below, and the command
prints a note on stderr when it does.

The certificate does not reason about this particular program's
instructions. It reflects the source into a FunctionIR program and states:

- the program's lowering by `lower_program`, with the planner's placement,
  as a literal (`_lowers`, checked by evaluation);
- that the program evaluates to the source function at any arguments
  (`_agrees`). It is by `refl` when every match is on a comparison. A test
  through a connective or a helper has no conversion that commutes the
  source's `match` with the program's conditionals, so the certificate
  states the program's decision tree in source operations (`_expansion`),
  equal to the program by `refl` (`_expanded`) and to the source by
  `split_all` (`_expands`). Such a function cannot yet be called by another
  ([the issue](../../issues/function-ir-verified-decided-callees.md));
- the published bytes, a piece at a time (`_bytes`), and the exported
  function's offset (`_entry_at`);
- and `_returns`, which instantiates the theorem `compiled_returns`. Called
  at its label with its arguments in RDI, RSI, …, a return address at RSP
  and room on the stack below it, the code returns the source's value in
  RAX, keeps the callee-saved registers and RSP, and leaves the stack above
  the return address as it was.

The assembly is the whole program: each function's frame, body and RET,
with the exported symbol at its function's label. The platform ABI around
it (stack alignment, the C caller, the loader) is outside the proof.
`program.hthr` is a three-level example with calls in both arms of a
branch:

```sh
(ulimit -v 8388608 -t 300; target/debug/heather compile-x86 \
  examples/x86-native/program.hthr program -o target/x86-native/program.s \
  --cache-dir target/native-images)
```

Arguments arrive in RDI/RSI and the result leaves in RAX.

Proof support modules are bundled into the compiler. Source imports use the
normal loader with `lib/std`, `lib`, and additional `-L` directories. A source
module with a bundled library name must have identical contents. Optional
`--cache-dir` uses kernel-rechecked semantic images with exact build identity;
it does not enable the trusted declaration cache or stale-image replay.

## Nested source conditionals

*The per-function certificate.* `branches.hthr`'s shapes now take the
verified path above. This section describes the certificate that a source
outside its fragment still gets.

Ordinary `compile-x86` also accepts tail-position matches on
`bitvec::unsigned_lt_bit(64, ...)`, including nested matches in either arm.
`branches.hthr` supplies both shapes, retaining the original inputs in the
selected arithmetic leaf:

```sh
(ulimit -v 6291456 -t 120; target/debug/heather compile-x86 \
  examples/x86-native/branches.hthr nested_true \
  -o target/x86-native/nested_true.s --cache-dir target/native-images \
  --kernel-workers 1)
```

The shared recursive selector carries values by port ID and uses the existing
DAG lowering for comparisons and arithmetic. The generated `StructuredArtifact`
checks complete selected execution, branch targets, decoding, result agreement
with the actual source, preserved memory/registers, and the common exit address.
The public source artifact has no unresolved graph assumptions. A separate
checked equality ties the published literal bytes to this same code tree.
The `ret`, ABI, instruction fetch/loading, and host integration remain external.

The native source adapter accepts two word inputs and one word result. The
underlying structured backend additionally supports multiple prefix/results
with explicit register maps and one artifact per result over the same code.
The `generate_elaborated_typed_x86` certificate API connects those artifacts to
actual typed source calls, including Bool/BitVec inputs and scalar choice results.
Its public premises specify normalized argument placement; it does not extend
the native CLI calling convention.
`generate_elaborated_read_x86` additionally publishes a successful byte-load
prefix feeding a typed body, with explicit access/canonical-address premises
and exact bytes. The shared encoder serves both this API and existing CLI export;
the adapter does not select a loop bounds guard or provide a fetched entry point.

`AccessFragment` now composes those read/body certificates with ordinary selected
pure code and actual TEST/JZ branches. It checks literal published bytes and
forward branch spans. The bounds/address tests compile an unsigned guard and ADD
address calculation, connect them to Nat cursor proofs, and verify both granted
reads and end paths that need no read grant. See
[`function-ir-readonly-loops.md`](../../docs/function-ir-readonly-loops.md#bounds-selected-access-composition).
This certificate API still stops before a complete bounded-loop trace and does
not change the native CLI calling convention.

Leaf selection supports word arithmetic and zero-extended narrow constants,
copies, bitwise operations, unsigned comparisons and modular add/subtract (the
word's result, masked). Narrow signed comparisons remain future work. Register pressure
and branches outside the forward rel8 range are refused. Structured bodies are
currently assembly exports; `build-x86` retains its existing arithmetic/call
fragment. The native branch and structured-composition tests assemble all
three functions and check each on 10,036 input pairs.

## Direct executable, with no assembler or linker

```sh
cargo build -p heather-cli
(ulimit -v 8388608 -t 180; target/debug/heather build-x86 \
  examples/x86-native/mix.hthr mix --arg 0x14 --arg 0b10110 \
  -o target/x86-native/mix-direct --cache-dir target/native-images)
./target/x86-native/mix-direct
printf 'exit status: %s\n' "$?"
```

The exit status is 51. The two arguments are compiled into the executable;
there is no runtime argument parser. The example is a 233-byte ELF64 file,
with a companion `mix-direct.certificate.hthr`. It performs no output and
needs no C wrapper. Build to a fresh path when rebuilding.

The checked loaded-memory/fetch trace, source-result certificate, and exact
file image are described in [the ELF design](../../docs/x86-64-static-elf.md),
including the remaining Linux loading and syscall-delivery assumptions.

## Two functions with CALL and RET

```sh
(ulimit -v 4194304 -t 300; target/debug/heather build-x86 \
  examples/x86-native/calls.hthr caller --callee leaf --arg 20 --arg 22 \
  -o target/x86-native/calls --cache-dir target/native-images)
./target/x86-native/calls
printf 'exit status: %s\n' "$?"
```

Expected status: 197, the low byte of `(20 + 22) XOR 0x0123456789abcdef`.
The entry calls the wrapper, the wrapper calls the leaf, and both return
through an owned writable stack page. See [the call profile](../../docs/x86-64-calls.md)
for the convention, checked claims, and current source restrictions.

## A value kept across a call

```sh
(ulimit -v 4194304 -t 300; target/debug/heather build-x86 \
  examples/x86-native/stack_local.hthr caller --callee leaf --arg 20 --arg 22 \
  -o target/x86-native/stack-local --cache-dir target/native-images)
./target/x86-native/stack-local
printf 'exit status: %s\n' "$?"
```

Expected status: 40. The caller saves `left XOR right` in its own frame and
reloads it after a callee that clears R11. See [call memory effects and locals](../../docs/x86-64-call-frames.md).

## One callee summary, two placements

```sh
(ulimit -v 4194304 -t 300; target/debug/heather build-x86 \
  examples/x86-native/reused_callee.hthr caller --callee leaf --arg 21 --arg 1 \
  -o target/x86-native/reused-callee --cache-dir target/native-images)
./target/x86-native/reused-callee
printf 'exit status: %s\n' "$?"
```

Expected status: 3. Both calls use one generic callee summary, with the first
result feeding the second call. The caller retains its XOR local across both
calls. Each leaf writes its own private stack slot and restores RSP, leaving
the dead bytes changed. See [reusable callee summaries](../../docs/x86-64-call-summaries.md).

## Arithmetic and computed arguments around calls

```sh
(ulimit -v 6291456 -t 300; target/debug/heather build-x86 \
  examples/x86-native/composition.hthr caller --callee leaf --arg 20 --arg 22 \
  -o target/x86-native/composition --cache-dir target/native-images)
./target/x86-native/composition
printf 'exit status: %s\n' "$?"
```

Expected status: 3. This caller retains an OR result across two calls, swaps
the first call's arguments, and computes the second call's arguments. `let`
bindings and Add/Sub/AND/OR/XOR expressions are supported around calls to one
selected leaf, within explicit expression, call-count, and register limits.
See [source-call composition](../../docs/x86-64-call-composition.md) for the
checked boundary and current limits.

## A composed function with its own reusable summary

Add `--callable-caller` to the composition command (with a fresh output path):

```sh
(ulimit -v 6291456 -t 300; target/debug/heather build-x86 \
  examples/x86-native/composition.hthr caller --callee leaf --callable-caller \
  --arg 20 --arg 22 -o target/x86-native/callable \
  --cache-dir target/native-images)
./target/x86-native/callable
```

Expected status: 3. The entry now consumes the composed function's own summary,
which preserves the native ABI registers and protects the parent's return word.
This bounded profile reserves caller registers according to the leaf's actual
clobbers and fixes the incoming stack position; see [composed callers](../../docs/x86-64-composed-callers.md)
for the generic proof interface and limits.

The same command with `sharing.hthr` and a fresh output path demonstrates
shared arithmetic and call results (status 50 for 20 and 22). With
`multi_register.hthr`, a leaf uses RAX and R11 while caller values survive in
untouched registers (status 108). Both cases use `--callable-caller`.

`stack_save.hthr` exceeds the disjoint register pool and uses checked stack
saves/restores for R11 around two leaf calls. Use the same command with a fresh
output path and `--callable-caller`: status 88 for 20 and 22, or status 4 for
18446744073709551615 and 1. The save word occupies the caller's alignment slot;
checked non-overlap protects both the live saved value and the parent return.

`multi_stack_save.hthr` saves R10 and R11 simultaneously across a leaf call,
using two distinct words in a 24-byte frame that preserves call alignment. Run it with
`--callable-caller --callee leaf`: inputs 20 and 22 exit 66; inputs
18446744073709551615 and 1 exit 253. Checked disjointness preserves each live
saved word through writes to the other slot and the child return word, and
protects the parent return word.

## Programs with input: burned

The programs that read stdin (`wc -l`, `wc` as a command, `tr`, `tr -s`,
`tr -d`) were proved by hand, a process library per program shape, and were
deleted in B1 (docs/native-program-logic-design.md §3.1). The last commit
with them, their build recipe and this section's old text is `189659d` (tag
`native-v0`). They come back as programs of an effectful source whose meaning
is an interaction tree, compiled by a compiler proved correct once
(`issues/native-first-compiled-program.md`). Their specs survive:
`lib/std/text/decimal.hthr` (what `%d` and `%7d` print) and `lib/native/stream_filter.hthr`
(a filter's fold and the counting lemmas).
