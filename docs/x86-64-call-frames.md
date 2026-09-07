# Call memory effects and a live stack local

The internal integer call contract now carries `WritesOnly(read, writes,
before, after)`: at every address outside the declared write footprint, the
observable read result is preserved. The read carrier is generic; the ELF
instance uses `Option<BitVec(8)>`, preserving both bytes and read availability.
Equality of entire memory values is sufficient to establish this contract,
but is no longer required by its interface.

`CallMemoryPolicy` separates private locals, explicitly shared writable data,
and protected caller state. Both writable sets must be disjoint from the
protected set. Effects compose by union, and a child effect can be widened only
with a proof that its writes are included in the parent's allowance. A protected
read follows from the effect witness and disjointness. This is sequential frame
reasoning; it does not introduce a heap allocator or linear ownership checker.

Footprints do not grant access rights. Canonical execution still requires the
existing byte-access, address-wrap, and stack-capacity premises. Restoring RSP
is a separate obligation and does not require restoring dead local bytes.
Return slots and live caller slots must be protected where appropriate.

`NativeIntegerCallContract` names the current internal integer profile. It
retains the RAX result, return target, RSP restoration, and RBX/RBP/R12–R15
preservation fields. Flags and scratch registers have no preservation promise.
It is not a declaration of complete System V ABI conformance. Named external
ABI profiles, coverage of additional architectural state, and explicit foreign
conformance assumptions remain in `issues/named-abi-contracts.md` and
`issues/runtime-extern-c-abi.md`.

## Executable customer

`examples/x86-native/stack_local.hthr` expresses:

```text
caller(left, right) = leaf(left, right) XOR (left XOR right)
```

The producer computes `left XOR right` before the call and stores it in the
caller's eight-byte slot at 0x401ff0. The leaf deliberately clears scratch
register R11. After the leaf returns, the caller reloads its slot and combines
that value with RAX. Inputs 20 and 22 produce exit status 40.

The slot occupies the previously unused alignment reservation. The leaf's
return slot is below it at 0x401fe8; the caller's return slot is above it at
0x401ff8. CALL alignment and final RSP restoration are checked as before.
The new canonical forms are 64-bit register stores/loads at `[RSP]`, with an
explicit SIB byte and no displacement. The producer currently uses R11.

The callee contract is emitted before the reload proof. Each reload byte uses
its memory-effect field; the caller result proof uses its result field. The
arithmetic leaf has `NoWrites`, while separate library controls exercise private
writes that remain changed, protected live bytes, and combined local/shared
effects over neutral initial memory.

This source extension is deliberately bounded to the expression above with
unchanged argument order. Other source expressions, general locals/spills,
escaping stack addresses, and arbitrary call graphs are not inferred. Generic
frame allocation and reusable relocated callee summaries remain follow-up work.

The ELF and environment assumptions are those of [the call profile](x86-64-calls.md).

## Validation

Final plain full suite (2026-09-07), starting with a fresh native cache:
**2,490 passed, 0 failed, 5 ignored**. The forwarding and live-local integration
targets passed in 219.79 and 257.02 seconds respectively.

The live-local example builds a 341-byte ELF and exits with status 40. Focused
integration checks run both this example and the earlier forwarding caller;
both pass under the standard 4 GiB / 300 CPU-second limits. Negative controls
cover incorrect stack encodings, overlapping write/protected policies,
protected live/return bytes, and missing RSP restoration.

The test harness prepares the native proof-library image prefix in a separate
bounded encoder/corruption check before scheduling native integration targets.
This keeps a cold prefix rebuild and generated certificate checking from
competing for one child-process budget. Image replay uses the current build's
identity and kernel-checks the cached declarations.

The call certificate shares named concrete words across fetch, stack, return,
and result premises, so each 64-element vector is elaborated once. The literal
declarations and trace are composed as structured modules before rendering.
All byte observations and access permissions remain checked against the loaded
memory.
