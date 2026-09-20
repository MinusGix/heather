# Bounded native scanning (experimental)

`compile-x86 --buffer-scan` compiles an ordinary Heather scanner body and places
it inside a reusable native byte-buffer loop. The decimal example parses
`123+4` into value `123` and cursor `3`. The same executable handles other input
strings after compilation. The parsing code uses registers and caller-owned
storage; it calls no allocator. C supplies input storage and output formatting.

This is an **experimental export**. The certificate checks the source body,
its live-register/memory frame, guarded machine entry to the body, its
refinement under the pure bounded scanner model, and the exact emitted bytes. It does **not yet establish a complete
machine execution trace for the surrounding loop**. That work is tracked in
[x86-buffer-scan-loop-refinement](../issues/x86-buffer-scan-loop-refinement.md).
The existing single-character `--buffer-cursor` profile retains its previous
certificate scope.

## Build and run

From the repository root:

```sh
cargo build -p heather-cli
mkdir -p target/decimal-demo
(ulimit -v 6291456 -t 120; target/debug/heather compile-x86 \
  examples/x86-native/decimal_step.hthr decimal_step --buffer-scan \
  -o target/decimal-demo/decimal.s --cache-dir target/native-test-images \
  --kernel-workers 1)
cc -std=c11 -Wall -Wextra -Werror examples/x86-native/decimal_main.c \
  examples/x86-native/scan_abi.S target/decimal-demo/decimal.s \
  -o target/decimal-demo/decimal

target/decimal-demo/decimal '123+4'       # ok 123 3
target/decimal-demo/decimal 'x123+4' 1    # ok 123 4
target/decimal-demo/decimal '18446744073709551615'
# ok 18446744073709551615 20
target/decimal-demo/decimal '18446744073709551616'
# overflow 1844674407370955161 19
```

As with other exports, output paths must be new. A failed certificate check
publishes neither assembly nor certificate.

The example driver accepts at most 256 bytes and an optional unsigned starting
cursor. Its command-line input cannot contain embedded NUL bytes, but the
native interface can. Overflow leaves the last valid value and the cursor of
the offending digit intact. A nondigit terminates a nonempty run successfully;
a run with no digits has its own outcome. Signs and leading whitespace are not
part of this decimal body.

## Reusable source interface

A body has type `BitVec(64) -> BitVec(64) -> ScanStep`: its arguments are the
zero-extended input byte and current accumulator. It returns `Next(value)`,
`Stop`, or `Overflow`. The source fragment supports scalar `let` bindings,
word literals, Add/Sub/AND/OR/XOR, and nested Boolean matches on unsigned word
comparisons. Comparison operands currently must be inputs or literals.
Unsupported forms are refused. Reflection is untrusted: a theorem compares the
normalized body against the actual checked source function.

`lib/std/byte_scan.hthr` defines the bounded loop independently of the compiler.
It begins with accumulator zero and permits at most 256 successful steps in
the native profile. It checks end-of-input before checking the remaining fuel.
If input remains when fuel is exhausted, it returns `limit` without loading
another byte. Consuming exactly 256 bytes at end-of-input succeeds. This bound
is explicit even for a body that always returns `Next`.

`examples/x86-native/count_spaces.hthr` compiles through exactly the same
profile. To link its example, pass `-DSCANNER=count_spaces` when compiling
`scan_abi.S`. This verifies that the loop and branch lowering contain no
decimal-specific instruction template. General recursive function compilation
and the showcase parser combinator representation remain future work.

## Native interface and checked boundary

The generated symbol accepts buffer address in RDI, byte length in RSI, and
starting cursor in RDX. It returns value in RAX, next cursor in RDX, and status
in RCX:

| Status | Meaning |
| --- | --- |
| 0 | Successful nonempty run |
| 1 | No accepted bytes |
| 2 | Body reports overflow |
| 3 | Iteration limit exhausted while input remains |

The SysV adapter in `scan_abi.S` exposes these results as a C struct. The
adapter, final RET, executable loading, instruction fetch, linking, and I/O are
external boundaries. The caller supplies a valid readable buffer for accesses
actually selected by the bounds/fuel checks. Concurrent buffer mutation is
outside the model.

Body arithmetic uses the existing source/FunctionIR/x86 certificates.
Conditional bodies use the x86 CMP carry flag and recursively checked branches.
Frame proofs preserve input/accumulator registers, the loop's R8–R11 state,
input memory, and ABI-preserved registers. Named frame lemmas avoid reducing
comparison flag arithmetic when proving register preservation.

`lib/std/arch/x86_64/scan_gate.hthr` proves one physical traversal from the
loop-head CMP at offset 29. It follows the bounds JAE, fuel CMP/JE, and
`MOVZX RDI,[R8+R10]`, using signed rel32 branch semantics. End-of-input takes
precedence over exhausted fuel. Neither early exit needs a readable address;
the byte-ready path requires a readable, low-canonical, nonwrapping address.
The trace includes ordinary checked CMP/MOV blocks and preserves memory, the
accumulator, R8–R11, and callee-saved registers. Generated theorems check the
concrete end/limit branch targets and the 33-byte fallthrough to the body.
This theorem starts at an arbitrary loop-head state; it does not yet compose
initialization, body execution, the backward edge, repeated iterations, and
final return blocks into one execution theorem.

Byte certificates compare against a library-defined generic layout containing
bounds checks, the byte load, body branches, backward edge, cursor/fuel updates,
and exit blocks. Each literal byte chunk comes from the output byte vector;
compositional equality proofs join those chunks. This keeps certificate checks
within the ordinary fuel limit. An encoding equality alone does not prove the
loop's execution. The guarded-entry theorem checks safe-read premises for one
traversal; the command retains the complete-loop limitation.

## Validation and remaining work

The separate `native_buffer_scan` acceptance target runs the same compiled
parser against an independent 128-bit decimal oracle, all 256 byte values at
all 257 positions in a 256-byte buffer, deterministic generated inputs,
maximum values and overflow, nonzero/oversized cursors, embedded NUL, input
immutability, and protected pages. It also exercises the 256-step limit with
an inaccessible following byte, compiles the independent space-counting body,
replays certificates, and rejects source/encoding/semantic mutations. Guard
controls independently remove each load premise, invert the bounds or fuel
condition, and change the read address or body-entry RIP. Memory and data
registers remain open; the wrong-RIP control fixes the code base to avoid
expanding unequal nested symbolic increments. The accepted RIP theorem is
general. All refusals must be semantic errors, not fuel exhaustion.

A theorem relating every successful word result to an unbounded natural-number
decimal fold is still open, alongside the complete native-loop trace.
[x86-buffer-decimal-parser](../issues/x86-buffer-decimal-parser.md) stays open
until those proof obligations are met. The runtime oracle is validation, not
that theorem.

Final plain suite for guarded entry: **2835 passed, 0 failed, 5 ignored**,
including both scanner acceptance tests. Native fixtures use per-run nonces
to avoid process-ID collisions across sandbox namespaces. Heavy composed-summary
fixtures run in separate processes under the same limits; aggregate child CPU
is tracked separately from the meaning of a single process's resource rail.
