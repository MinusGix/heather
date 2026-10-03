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

The initial command accepts a transparent function with two `BitVec(64)`
parameters and a supported binary expression as its result. The existing
elaborated-source reflector supports shared/nested Add, Sub, AND, OR, XOR,
and literal `bitvec::ofNat` constants within these expressions. Unsupported
operations and exhausted registers produce errors. Literals of any magnitude
below `2^64` check in work bounded by the width (`bitvec::ofNat` reads bits
from the top against run-compressed powers of two; see
[the closed issue](../../issues/bitvec-ofnat-large-literals.md)), and the
example's own constant is a full-width asymmetric one so that every immediate
byte is distinct. Loops, calls, memory, other signatures, and spilling are
not part of this command.

Arguments arrive in RDI/RSI and the result leaves in RAX. Temporaries use only
SysV caller-saved registers. The assembly consists of literal `.byte`
directives for the body and one `ret`; the system assembler and linker
supply ELF packaging. No assembler instruction selection changes the body.

Before writing output, Heather checks the source, the generated source-to-IR
and IR-to-x86 certificates, and an additional theorem equating the exported
literal bytes with the canonical encoding of the lowered instructions. A
wrong Rust encoding therefore fails certificate checking. The companion
`mix.certificate.hthr` records these declarations for inspection. Checking
it independently requires the same source and proof modules under the names
used by the native driver (including the x86 module aliases).

The proof covers the selected body under the existing machine model.
The `ret`, calling convention, C wrapper, loader, executable-memory setup,
and external assembler/linker remain outside the formal claim. Native tests
exercise that platform boundary; they are not proofs of it.

Proof support modules are bundled into the compiler. Source imports use the
normal loader with `lib/std`, `lib`, and additional `-L` directories. A source
module with a bundled library name must have identical contents. Optional
`--cache-dir` uses kernel-rechecked semantic images with exact build identity;
it does not enable the trusted declaration cache or stale-image replay.

## Nested source conditionals

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

The same file also supplies `composed`, whose Boolean helper `unequal` contains
a conditional. Compile it by replacing `nested_true` with `composed` in the
command above. Its helper and continuation use shared physical composition;
the generated artifact names the actual source function.

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

## Programs with input: stream filters

Every program that reads stdin is a stream filter
(docs/native-stream-filter-design.md). It has a step, which takes a state and a
byte and gives the next state and the byte it emits, if any. It has an initial
state, and a finish that prints from the final state after end of file. The
process around it is the library's (`lib/elf64_read_filter.hthr`). The process
reads a page, runs the step over each byte of the chunk with the state in R13,
R14, R15 and R8, stores what each byte emits behind the read cursor in the
same page, writes the chunk's output if there is any, and reads again until
the empty read. Then it runs the finish. A read or write interrupted by a
signal (EINTR) is retried; any other failure exits with status 1.

```sh
cargo build --release -p heather-cli
for p in wc_l:wc_l_program wc:wc_program tr:tr_program tr_s:tr_s_program tr_d:tr_d_program; do
  (ulimit -v 8388608 -t 900 -c 0; target/release/heather build-x86 \
    examples/x86-native/${p%%:*}.hthr ${p##*:} -o target/x86-native/${p%%:*} \
    --cache-dir target/native-images)
done
printf 'one\ntwo\nthree\n' | ./target/x86-native/wc_l      # 3
printf 'one two\nthree\n' | ./target/x86-native/wc          #       2       3      14
printf 'Hello, world!\n' | ./target/x86-native/tr            # HELLO, WORLD!
printf 'a\n\n\nb\n' | ./target/x86-native/tr_s              # a, b on two lines
printf 'a\r\nb\r\n' | ./target/x86-native/tr_d              # a, b, no carriage returns
```

A program is a `Filter` bundle (`lib/filter_program.hthr`). Its type names the
step, the initial state, the state's Nat fields (`counts`), the finish, and
`spec`, which is all of stdout as an ordinary Heather function of stdin. Its
value is the fact `spec(bytes) = filter_output(step, init, counts, finish,
bytes)`. The finish names positions in `counts` (`Line` prints the first,
`Fields` the first three), so the counts are written once. A counting program
proves that fact from one fact per printed count (`line_computes`,
`fields_computes`), and each of those from what one byte does to the count,
by the library's fold lemmas (`fold_counts_filtered`, `fold_counts_len`,
`fold_counts_runs`). A program that prints nothing after end of file
(`tr -s`, `tr -d`) proves it from what one byte emits (`quiet_computes`).
Byte tests are decided propositions: a step branches with `if b = '\n'` or
`if 'a' <= b ∧ b <= 'z'`, and a predicate a specification passes to
`filter` or `split_by` is the decision's bit, `decide_bit<b = '\n'>()`.
That each count grows by at most one per byte is the bundle's `advances`
field, shown by default (case analysis, then `omega`). A step the default
cannot show gets an error naming the case left, and `advances := …` by hand.
The file is checked as a whole, so a program whose facts don't fit its step is
refused at its own source, before anything is generated.

- `wc_l.hthr` is `wc -l`: `counting(line_step)` over a `Nat`, finishing with
  `Line`, which prints the count as a decimal line.
- `wc.hthr` is `wc`: `counting(wc_step)` over `WcState { lines, words, bytes,
  inside }`, finishing with `Fields`, which prints the first three fields as
  GNU `wc` prints them on a pipe (`%7d %7d %7d`). The state stays in
  registers across the reads, so a word split between two reads is counted
  once. What the counts mean is stated as a reader checks it: `wc_lines`
  counts the newlines, `wc_words` the non-empty pieces of
  `bytes.split_by(space)` (the C locale's POSIX whitespace), and
  `wc_bytes` the length. Each count's proof is what one byte does to it, by
  `split_all`.
- `tr.hthr` is `tr a-z A-Z`: `mapping(upcase)`, which keeps nothing between
  bytes and emits each byte's image.
- `tr_s.hthr` is `tr -s '\n'`: its state is whether the last byte was a
  newline, and a newline after a newline emits nothing, across reads too.
  Its specification is a recursion with the same state, and the proof is
  what one byte emits, by `split_all`.
- `tr_d.hthr` is `tr -d '\r'`: a `Stateless` step that emits every byte but a
  carriage return; stdout is `bytes.filter(kept)`.

The certificate's `{name}_native_runs` covers every history of reads and
writes, interleaved:
- chunks and EINTRs on the read;
- each chunk's short writes and EINTRs (a chunk that emitted nothing makes no
  write);
- the finish's own writes.

It ends at the empty read (exit 0), or at a failed read or write (exit 1).
`{name}_native_runs_every` adds that every run with those answers from Linux
is that run. `{name}_native_sends` shows that on a run that ends well, stdout
receives exactly `spec(stdin)`. A program with counts is covered for inputs
shorter than 2^64 − 4096 bytes, so no count wraps; one without counts (`tr`)
has no bound on its input. The finishes' lines cover counts below 10000 (a
decimal line) and 10^7 (three fields).

The step is compiled by the native compiler from the program's source
(`crates/elab/src/function_ir_source/filter_step.rs`) into one straight-line
piece. Its certificate is `lib/filter_step_piece.hthr`'s `StepPiece`: the next
state in place, whether the byte emits in RBX, and the byte in RDX. The store
is `mov [rdi], dl`, made whether or not the byte emits; the write cursor
advances by the flag and never passes the byte just read. The trace
(`lib/linux_x86_64_io.hthr`) records each syscall with Linux's response. Read,
write and exit are the only syscalls with rules
(`issues/linux-syscall-trace-model.md`). The printed line is computed by code
the native compiler generates from `lib/decimal_line.hthr`'s and
`lib/field_line.hthr`'s source functions. The machine has no divide or
multiply, so they use restoring chains of subtract-if-fits steps.
