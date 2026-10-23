# X86-64 bytes, decoding, and typed execution

Status: **executable encoding-normalizing register-byte boundary** (2026-08-28).

Heather's x86-64 work serves two equal customers: certified compilation into
machine code and proofs about machine code that already exists. Both routes
must meet at one decoded-instruction boundary and then use one architectural
execution relation. An encoder-owned semantics would exclude raw binaries; a
decoder-owned semantics would make compilation correctness depend on a second
meaning for instructions.

The [first certified call profile](x86-64-calls.md) extends the existing state
with normal-path near CALL/RET rules and an owned stack page. It checks their
canonical bytes directly; general CALL/RET decoding and fault outcomes remain
future work.

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

`lib/std/arch/x86_64/x86_64.hthr` begins with `MOV r64,r64` and `ADD r64,r64`, all sixteen GPRs,
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
`SUB`, `CMP`, and `TEST`. The evidence retains the exact consumed bytes and
start address.
Recognition is decomposed into exact list shape, REX.W extension bits, opcode,
and register-mode ModRM propositions. `MOV` admits both 89 and 8B direction
forms; `ADD` admits both 01 and 03. Their different ModRM operand roles
normalize into the same typed instruction. `SUB` similarly admits 29/2B and
`CMP` admits 39/3B. `canonical_encoding_decodes` puts
compiler-produced bytes into the broader proposition; independent byte proofs
use the same relation. Both compose with the one `Execute` relation through
`ExecuteAt`, and the consumed length is carried into RIP fallthrough by a
separate theorem.

`decode_bytes` is the executable view of this relation. A successful result is
a `ByteDecode(bytes)` carrying both the normalized instruction and its
`DecodesInstruction` witness, so soundness is enforced by construction;
`decode_instruction` erases that evidence behind a conventional
`Option<DecodedInstruction>` face. The active algorithm checks the exact
three-byte shape, rejects non-REX.W and non-register ModRM forms, extracts
REX.R/REX.B and both three-bit ModRM register fields directly, and certifies
the reconstructed REX and ModRM bytes with evidence-producing bitvector
equality. The original bounded 16×16 register-pair search remains available as
`decode_instruction_reference`; boundary tests compare it with the direct
path. [[x86-direct-bitfield-decoder]] retains the exhaustive malformed-input
agreement obligation before larger encoding families rely on it.
`decode_instruction_complete` now proves acceptance for every inhabitant of
`DecodesInstruction`, and successful reference results agree with the direct
path generally rather than by register enumeration.

This is deliberately not yet a total x86 decoder. Redundant and legacy
prefixes, memory ModRM modes, truncation, trailing bytes, and other instructions
have no `DecodedAt` proof in this slice. Nor does `InstructionBytes` claim that
a read from architectural memory succeeded: fetch and its faults wait for the
byte memory model. Invalid encoding, unsupported coverage, failed fetch, and
architectural execution fault remain four different outcomes.

## Standalone image export

The direct executable path now checks a restricted ELF64 image and a typed
entry/body/exit-request trace. Its exact claims and environmental assumptions
are owned by [the static ELF design](x86-64-static-elf.md). The restricted loaded-memory bridge is described below.


## Exact-span memory fetch (2026-09-07)

`lib/std/arch/x86_64/x86_64_fetch.hthr` adds the first memory-to-byte-span adapter.
`FetchAccess<M>` supplies a byte reader returning `Option<BitVec(8)>` and a
separate execute-permission predicate, both applied to the actual memory value.
The caller chooses these implementations; this interface does not itself prove
that a host OS provided the claimed memory or permissions.

`fetch_instruction_bytes` reads exactly the requested number of bytes. It checks
execute permission before attempting each byte read, reports the first denied
or missing address, and rejects a span crossing the end of the 64-bit address
space. A one-byte read at the last address is allowed; no successor address is
needed. An empty request reads nothing. Successful byte fetching alone places
no restriction on instruction encoding or length.

`FetchedFrom` identifies a supplied instruction span with those fetched bytes.
`ExecuteFetched` conjoins that fact, using `before.memory`, with the existing
`ExecuteAt` relation. Thus RIP equality, supported decoding, valid instruction
length, and architectural execution still come from the canonical model. Missing
memory and denied permission are fetch results; unsupported bytes can fetch
successfully but cannot satisfy the supported decoding relation. No new CPU
exception semantics is inferred from these adapter results.

This is an exact-span certificate boundary, not an incremental instruction-length
discovery algorithm. It avoids requiring all 15 possible instruction bytes to be
readable when a shorter instruction ends at a mapping boundary. The current
profile deliberately excludes wrapping instruction spans; canonical-address,
paging, and privilege rules still need a richer access implementation.

The x86 test rail checks concrete MOV fetch/execution, neutral bytes with an open
memory type, exact reads, missing tails, permission denial, unsupported decoding,
and the last-address/wrap distinction. Wrong byte, address, and permission proofs
are rejected.

`FetchedFrom` now carries structural `ReadableBytes` evidence. The generic
`fetched_result` theorem derives equality with the executable reader, so the
structural certificate and computational fetch agree. Byte composition checks
next-address equations explicitly and does not treat wrapping as valid.

## Restricted ELF loaded traces (2026-09-07)

`lib/std/os/linux/elf64_load.hthr` supplies the reader and execute policy for the fixed RX
file mapping, with no zero-fill tail. `lib/std/arch/x86_64/x86_64_fetch_block.hthr`
composes canonical fetched steps, and `lib/std/os/linux/linux_x86_64_fetch.hthr` ends the
trace with fetched syscall bytes and an exit-request contract.

The standalone producer now emits those witnesses against its actual file
bytes. Each proposed flattened successor state is checked against canonical
execution; a separately checked instruction-list equality connects the placed
trace to entry/body/exit instructions. Initial memory and RIP are fixed by the
image, while initial GPRs and flags remain arbitrary. See
[x86-64-static-elf.md](x86-64-static-elf.md) for the full contract and remaining
OS assumptions. Calls, writable memory, and other ELF profiles remain separate
extensions.
