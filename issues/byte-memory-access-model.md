---
title: Develop byte-addressed memory and explicit access outcomes
status: open
labels: [stdlib,semantics,runtime,design]
created: 2026-08-25
updated: 2026-08-25
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
