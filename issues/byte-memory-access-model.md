---
title: Develop byte-addressed memory and explicit access outcomes
status: closed
labels: [stdlib,semantics,runtime,design]
area: heather-in-heather
milestone: [hih-memory-model]
created: 2026-08-25
updated: 2026-10-21
---

Heather needs a specification-level memory on which reads and writes have
explicit outcomes.  A total function from addresses to bytes is useful for
algebra, but silently treating every address as readable and writable would
turn an omitted page/protection model into a false machine guarantee.  The
library boundary must therefore distinguish stored bytes from the access
policy/environment that can accept or reject an operation.

This is not initially a page-table model, allocator, cache model, or concurrent
memory model.  It is the reusable sequential byte-memory layer beneath binary
formats, interpreters, abstract machines, and eventually architecture-specific
normal-access theorems.

## Acceptance

- Choose address, byte-store, and access-policy interfaces without fixing them
  to x86-64 widths.  State where address finiteness and wraparound live.
- Define byte read/write outcomes and multi-byte reads/writes.  Endianness is
  an explicit packing choice, not an implicit property of memory itself.
- Prove read-after-write at the same address, preservation at distinct
  addresses, disjoint multi-byte update laws, and little-/big-endian
  pack/unpack round trips.
- State failed-access behavior precisely.  In particular, do not claim an
  updated store after a rejected write unless the chosen outcome semantics
  explicitly says so.
- Provide normal-path theorems that discharge an access-policy premise and
  expose the simple store update needed by higher-level arithmetic proofs.
- Exercise overlapping and wrapping multi-byte ranges and record the selected
  policy rather than leaving them to host-language behavior.
- Keep paging, privilege, alignment faults, atomics, ordering, devices, and
  allocation outside v1, with named extension seams for each.

## What it assumes from elsewhere

- **[[fixed-width-bitvectors]]** owns bytes, address-width arithmetic, and
  packing/slicing operations when that carrier is selected.
- **[[relational-semantics-refinement-kit]]** owns relation/outcome refinement;
  memory access uses it rather than creating a second refinement algebra.
- **[[state-location-and-frame-kit]]** owns general frame reasoning.  This
  issue supplies memory-specific disjointness and access facts to that layer.
- **[[memory-bound-certificates]]** owns platform allocation bounds.  This
  issue models accesses to an already supplied memory and makes no allocation
  promise.

## Log

- 2026-08-25: Filed from the requirement that omitted page tables and
  privilege checks remain visible as assumptions rather than becoming total
  loads/stores by accident.
- 2026-10-21: Landed as `lib/std/memory.hthr`, with `lib/std/vector.hthr` (`snoc`,
  `reverse`) and `lib/std/bitvec/bitvec_bytes.hthr` (packing). The design is in
  `docs/byte-memory-design.md`, which says where the model sits in the
  program-logic redesign. The showcase is `docs/showcase/memory_client.hthr`
  and the controls are `crates/elab/tests/lib_std_memory.rs`. Against the
  acceptance:

  - Address spaces are generic (`Space<A>`). Finiteness and wraparound belong
    to the space: `BitVec::space(n)` wraps modulo `2^n`, and its offset is
    `next_rip` at width 64; `Nat::space()` never wraps. The cell type is
    generic too (`Memory<A, C>`), with the policy (`perms`) a separate field.
  - Outcomes are `Result<_, Fault<A>>`. A refused write has no memory after
    it. Spans are checked whole first, so a refused span stores nothing and
    reports its first refused address (`refused_some`/`FirstRefused` makes
    that exact).
  - Laws: read-after-write (`get_set_same`, `get_set_span` under `Distinct`),
    preservation (`get_set_other`, `get_set_span_outside`,
    `get_set_span_apart` under `Apart`), and commutation of apart spans up to
    pointwise agreement (`set_span_comm`). LE/BE round trips are in
    `bitvec_bytes`.
  - Normal-path theorems: `*_allowed` for single, span and word access, with
    `read_write_le` as the whole path, and `buffer_reads`/`buffer_writes`
    discharging a whole bounded span of a buffer at once.
  - Wrapping and self-overlapping spans are exercised by evaluation, and the
    policy is recorded: a wrapping span continues at 0, and the later index
    wins on overlap.
  - Paging, privilege, alignment, atomics, devices and allocation are left
    out, and the design (§7) names a seam for each.

  Wiring the model into the x86 access records, `Stack` and a `Wp` view is
  `[[memory-model-machine-instances]]`.
