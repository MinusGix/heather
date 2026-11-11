---
title: Conversion's verdict memo hashes with SipHash, and PtrHasher leaves its low bits empty
status: closed
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

## What was built

`value::PtrHasher` is the one hasher for tables keyed by the kernel's own
addresses and small integers: it rotates its state before each word and its
product before returning it, as `conv::PairHasher` did, and `PairHasher` is
gone. It now hashes the verdict memo, the closed-pair table, the checker's
`conv_memo`, `closed_convs` and `teles`, the arena's `bit_types` and the
substitution's lifted-payload memo, all of which were SipHash over identity
keys.

## Acceptance

- Instruction counts (callgrind, one item) before and after each, and a
  `scripts/perf ab` on the showcase.

## Log

- 2026-11-10: Built (2026-11-10). In the whole-gate profile after the lockstep walk (cloud
  box, cold `docs/showcase/calc_parser.hthr`, width one, callgrind inside
  `time_kernel*`), `Sip13Rounds::write` was 3.74% of the kernel's instructions
  by itself: 2.37% from the verdict memo's key, 0.70% from `ClosedConvBucket`,
  0.31% from an address pair, 0.24% from `ConvMemoBucket`. With the one hasher
  the same run is 12,989.7 M → 12,276.5 M instructions (−5.5%), with every
  counter identical. The `scripts/perf ab` was taken together with
  [[conversion-query-identity-environment]] and is in that issue's log:
  kernel gate −4.8% in seconds on the showcase, the sample sets separate.
