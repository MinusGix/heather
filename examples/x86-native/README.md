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
byte is distinct. Source branches, loops, calls, memory, other signatures, and
spilling are not part of this command.

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

The proof covers the straight-line body under the existing machine model.
The `ret`, calling convention, C wrapper, loader, executable-memory setup,
and external assembler/linker remain outside the formal claim. Native tests
exercise that platform boundary; they are not proofs of it.

Proof support modules are bundled into the compiler. Source imports use the
normal loader with `lib/std`, `lib`, and additional `-L` directories. A source
module with a bundled library name must have identical contents. Optional
`--cache-dir` uses kernel-rechecked semantic images with exact build identity;
it does not enable the trusted declaration cache or stale-image replay.

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
