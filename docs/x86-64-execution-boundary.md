# X86-64 bytes, decoding, and typed execution

Status: **encoding-normalizing register-byte boundary** (2026-08-27).

Heather's x86-64 work serves two equal customers: certified compilation into
machine code and proofs about machine code that already exists. Both routes
must meet at one decoded-instruction boundary and then use one architectural
execution relation. An encoder-owned semantics would exclude raw binaries; a
decoder-owned semantics would make compilation correctness depend on a second
meaning for instructions.

## The layers

The intended chain is:

```text
bytes in byte-addressed memory at RIP
    -- declarative fetch/decode -->
decoded instruction (typed form + consumed length + relevant encoding facts)
    -- canonical typed execution -->
normal or faulting architectural outcome
```

The full canonical `step` is the composition. `execute` is the reusable typed
component, not an alternate machine model. A compiler proves that its encoder
produces bytes which decode to the instruction it selected. A raw-code proof
starts with bytes and obtains the same decoded object. Textual assembly is an
input convenience; claims about a binary should quantify over the assembled
bytes rather than silently trusting the assembler.

## RIP belongs to the decoded boundary

An architectural operation such as `MOV r64,r64` does not determine its byte
length. Prefixes, extension bits, ModRM/SIB, displacements, and immediates do.
But length affects ordinary fallthrough and also value semantics:

- RIP-relative addressing uses the address after the instruction;
- relative branches add their displacement to that address;
- `CALL` stores that address as its return address;
- a not-taken conditional branch falls through to it.

Therefore `execute` consumes a `DecodedInstruction` with a length certified to
be in x86's 1--15 byte range. A later `DecodedAt` judgment supplies the separate
evidence that this instruction and length came from particular bytes. Execution
computes `next_rip = old_rip + length` for use
by the instruction rule. A normal result commits the rule's RIP; a fault rule
does not arise from an already-committed preliminary increment.

The first slice has no fetch, memory operand, branch, or fault. It nevertheless
carries decoded length now, because retrofitting it after `CALL` or RIP-relative
addressing would change every existing rule's meaning.

## Semantic forms and encoding facts

Typed semantic syntax rejects nonsensical operand combinations and records
widths, register classes, concrete displacements, and feature-sensitive forms.
Decoding may additionally retain encoding facts whenever the exact bytes affect
legality or behavior: prefixes, REX/high-byte restrictions, address-size and
segment selection, and `LOCK` applicability are examples. Encoding variation
with no architectural effect may normalize to one semantic instruction.

This gives three proof surfaces:

1. declarative decoding relates bytes to a decoded typed object;
2. typed execution relates that object and a state to an outcome;
3. encoding/layout proves emitted bytes decode to the intended object.

An executable decoder, XED cross-check, and native differential tests validate
these surfaces but do not replace the declarative relation or vendor manuals as
the architectural authority.

## First vertical slice

`lib/std/arch/x86_64/model.hthr` begins with `MOV r64,r64` and `ADD r64,r64`, all sixteen GPRs,
the six arithmetic flags, RIP, and an opaque memory parameter. The opaque
parameter makes memory preservation a real statement without prematurely
claiming a total byte store. Both operations are deterministic and fault-free
in this register-only scope, but their result is packaged through the generic
semantic-outcome vocabulary and coverage remains separate.

`ADD` computes carry structurally over the 64 bits. The generic bitvector
library proves that result equivalent to its unsigned arithmetic condition
`2^n <= toNat(a) + toNat(b)` at an open width; the machine rule therefore uses
an executable linear-width operation without weakening its mathematical
characterization.

The byte boundary uses `InstructionBytes` and the declarative `DecodedAt`
proposition for three-byte REX.W register-register encodings of `MOV`, `ADD`,
and `TEST`. The evidence retains the exact consumed bytes and start address.
Recognition is decomposed into exact list shape, REX.W extension bits, opcode,
and register-mode ModRM propositions. `MOV` admits both 89 and 8B direction
forms; `ADD` admits both 01 and 03. Their different ModRM operand roles
normalize into the same typed instruction. `canonical_encoding_decodes` puts
compiler-produced bytes into the broader proposition; independent byte proofs
use the same relation. Both compose with the one `Execute` relation through
`ExecuteAt`, and the consumed length is carried into RIP fallthrough by a
separate theorem.

This is deliberately not yet a total or executable decoder. Redundant and
legacy prefixes, memory ModRM modes, truncation, trailing bytes, and other
instructions have no `DecodedAt` proof in this slice. Nor does
`InstructionBytes` claim that a read from architectural memory succeeded:
fetch and its faults wait for the byte memory model. Invalid encoding,
unsupported coverage, failed fetch, and architectural execution fault remain
four different outcomes.
