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
copies, bitwise operations, and unsigned comparisons. Narrow modular arithmetic
and signed comparisons remain future work. Register pressure
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

## A program with input: `wc -l`

`wc_l.hthr` is a whole program. It reads stdin a page at a time, counts each
chunk's newlines with a certified loop into a running total, stops at the
empty read (end of file), and exits with the total. A read interrupted by a
signal (EINTR) is retried; any other failed read exits with status 1.

```sh
cargo build --release -p heather-cli
(ulimit -v 8388608 -t 900 -c 0; target/release/heather build-x86 \
  examples/x86-native/wc_l.hthr count_lines --read-loop --needle 10 \
  --advance line_body_advances --spec wc_l --computes count_lines_input \
  --folds line_body_folds -o target/x86-native/wc_l --cache-dir target/native-images)
printf 'one\ntwo\nthree\n' | ./target/x86-native/wc_l; echo $?
```

Expected output: `3`.

The certificate's `count_lines_native_runs` states the whole process against
the source. For every way the reads may split stdin into non-empty chunks,
with EINTRs anywhere between them, and ending at the empty read or at a
failed read, the written file has a run that reads them all and exits with
`wc_l` of their concatenation (the parent sees the low eight bits), or with 1
after the failure; `count_lines_native_runs_every` adds that every run with
those answers from Linux is that run. `wc_l` is an ordinary Heather function;
the program supplies it, the counting step, and three facts about the step
alone: it grows by at most one per byte (`line_body_advances`), it always
continues, the same way at every cursor (`line_body_folds`), and folded over
the input from zero it is `wc_l` (`count_lines_input`). Buffers, chunks and
everything machine-shaped come from the shared generators and the library's
process theorem (`lib/elf64_read_loop.hthr`,
[its design](../../docs/native-read-until-eof-design.md), and
[the fold contract](../../docs/native-wc-design.md) §3).

The trace (`lib/linux_x86_64_io.hthr`) records each syscall with Linux's
response: a read returns bytes or fails with an errno, and a write sends some
prefix of what it asked or fails. A failed read may leave anything in the
buffer. Read, write and exit are the only syscalls with rules
(`issues/linux-syscall-trace-model.md`, `docs/native-syscall-failures-design.md`).
The claims cover inputs shorter than 2^64 − 4096 bytes, so no count wraps.

### Printing the count

Add `--print` (and a fresh output path) and the program prints the count
instead of exiting with it:

```sh
(ulimit -v 12582912 -t 3600 -c 0; target/release/heather build-x86 \
  examples/x86-native/wc_l.hthr count_lines --read-loop --needle 10 \
  --advance line_body_advances --spec wc_l --computes count_lines_input \
  --folds line_body_folds --print -o target/x86-native/wc_l_print \
  --cache-dir target/native-images)
printf 'one\ntwo\nthree\n' | ./target/x86-native/wc_l_print
```

Expected output: `3`, and exit status 0.

The certificate's `count_lines_native_runs` now ends the trace with the write
loop's events, `write_events(decimal_line(n), writes, written)` for the total
`n`, for inputs with fewer than 10000 lines. It covers every way the writes
may return. Short writes resume after what was sent, EINTR retries, and any
other failure exits 1; a finished loop exits 0. `prints_the_line` shows that
on a run that ends well, stdout receives exactly `decimal_line(n)`. `decimal_line(n)` is `decimal(n) ++ [newline]`,
and `decimal` is an ordinary function: the digits of `n / 10`, then `n % 10`.
The line is computed by code the native compiler generates from
`lib/decimal_line.hthr`'s source functions. The machine has no divide or
multiply, so they use a restoring chain of subtract-if-fits steps. The
library proves that for every count below 10000 the stored word holds exactly
that line past its leading zeros. The word is stored with a `mov [r8], rax`
(`lib/std/arch/x86_64/store.hthr`) and written with `write(1, …)`
(`lib/elf64_read_print.hthr`).

## `wc`: lines, words and bytes

`wc.hthr` is plain `wc` (docs/native-wc-design.md). Its step folds a record,
`WcState { lines, words, bytes, inside }`, over each chunk; the state stays in
R13, R14, R15 and R8 across the reads, so a word split between two reads is
counted once. At the end the program prints the first three fields as GNU
`wc` prints them on a pipe, seven columns each:

```sh
(ulimit -v 8388608 -t 3600 -c 0; target/release/heather build-x86 \
  examples/x86-native/wc.hthr count_wc --read-loop --fields --needle 10 \
  --advance wc_body_advances --spec wc_lines --spec wc_words --spec wc_bytes \
  --computes count_wc_input --folds wc_body_folds -o target/x86-native/wc \
  --cache-dir target/native-images)
printf 'one two\nthree\n' | ./target/x86-native/wc
```

Expected output: `      2       3      14`, and exit status 0.

`--fields` takes `--spec` three times, in the order printed. What they mean is
stated as a reader checks it: `wc_lines` counts the newlines, `wc_words` the
non-empty pieces of the input cut at every whitespace byte (the C locale's
POSIX set, as `POSIXLY_CORRECT` has it), and `wc_bytes` the length.
`count_wc_input` proves the fold from the zero state computes them. The
certificate's `count_wc_native_runs` ends the trace with
`write_events(three_fields_line(wc_lines(input), wc_words(input), wc_bytes(input)), …)`
for counts below 10^7. The program may import the bundled proof library by
its bundled names (here `bitvec_omega`), which need not exist as files.
