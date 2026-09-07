---
title: Specify caller and callee memory footprints across calls
status: open
labels: [compiler,x86,memory,proofs]
created: 2026-09-07
updated: 2026-09-07
---

## Scope

Replace the first arithmetic leaf's whole-memory preservation requirement with
an explicit call memory contract. A callee may overwrite its own frame and leave
dead stack bytes changed after restoring RSP. Protect caller-owned live memory
and the return address while accounting for explicitly shared or writable data.
This issue owns the x86 call instance of frame reasoning, not a new general
separation logic or an allocator.

## Acceptance

- Describe caller-protected regions, callee frame bounds, return slots, and
  explicitly authorized shared-memory effects. State aliasing, disjointness,
  address-wrap, and access-policy premises.
- Separate restoring RSP from restoring memory contents. Permit callee-local
  bytes to remain changed while proving preservation outside authorized writes.
- Give composition rules for nested calls and frame allocation/release; a child
  must not acquire permission to overwrite a parent's live slot or return slot.
- Keep stack capacity, alignment, normal-return conditions, and byte access
  obligations explicit. No fault or termination guarantee follows from a frame
  predicate alone.
- Exercise neutral initial memory, a changed dead local, a live caller slot,
  authorized pointer effects, and overlapping regions. Reject a write to a
  protected live slot and corruption of a return address.
- Migrate the leaf memory contract without weakening the existing result,
  preserved-register, return-target, or fetched-execution claims.

## What it assumes from elsewhere

- [[state-location-and-frame-kit]] owns general locations and frame composition.
- [[byte-memory-access-model]] owns memory access and disjoint update laws.
- [[x86-calls-stack-frames]] supplies the existing near CALL/RET execution slice.
- [[named-abi-contracts]] owns naming and composing calling-convention policies;
  a convention alone does not determine a function's pointer effects.
- [[x86-caller-stack-locals]] supplies the first non-forwarding caller customer.

## Log

- 2026-09-07: Implemented WritesOnly over a generic observable read carrier, union composition, footprint inclusion, protected reads, and CallMemoryPolicy with disjoint private/shared writes. NativeIntegerCallContract now carries memory effects instead of whole-memory equality; the ELF instance preserves Option byte observations. Focused controls cover neutral memory, changed private bytes, combined shared effects, overlapping-policy rejection, protected live/return bytes, and missing RSP restoration. Generic frame allocation/release and extent/aliasing interfaces remain follow-up scope.
- 2026-09-07: Validated the migrated contract and live-local customer with the full fresh-native-cache suite: 2,490 passed, 0 failed, 5 ignored. [[x86-caller-stack-locals]] is complete; this issue retains generic frame allocation/release and extent/aliasing obligations.
