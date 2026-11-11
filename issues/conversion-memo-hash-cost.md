---
title: Conversion's verdict memo hashes with SipHash, and PtrHasher leaves its low bits empty
status: open
labels: [kernel,conversion,performance]
area: kernel
created: 2026-11-10
updated: 2026-11-10
---

Two hashing costs seen while profiling for [[conversion-closed-pair-memo]]:

- **The per-query verdict memo** (`premises::VerdictMemo`, keyed at the
  value domain by a 37-byte tuple of closure addresses and scope lengths)
  uses the standard library's SipHash. With the walk in place it was about a
  tenth of the instructions conversion spent on `grind::by_diseq`
  (`hash_one` plus `Hasher::write`, callgrind). The keys are the arena's own
  allocations, not chosen input, which is the argument `value::PtrHasher`
  already makes for the arena's caches.
- **`value::PtrHasher::finish` returns the product of its multiply.** The
  low bits of a product depend only on the low bits of the factors, an
  aligned address has four zero low bits, and the table indexes buckets by
  the low bits of the hash: a `PtrMap` keyed by addresses uses a sixteenth
  of its buckets. `conv::PairHasher` rotates the product before returning
  it; the same one line would do there, and the two hashers could then be
  one.

## Acceptance

- Instruction counts (callgrind, one item) before and after each, and a
  `scripts/perf ab` on the showcase.
