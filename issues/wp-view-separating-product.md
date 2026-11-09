---
title: Compose Wp views over disjoint regions (separating product)
status: open
labels: [native,memory,proofs]
created: 2026-10-22
updated: 2026-11-09
area: heather-in-heather
milestone: [hih-memory-model]
---

A `View` (`lib/std/os/linux/linux_x86_64_wp.hthr`) knows one thing about memory. The
process image's views (issues/io-image-on-byte-model.md) are each over one
data region: `DataRegion::program_view` sees the page or the frame, not
both. The burned frame view knew the page and the frame's slots together,
and a compiled function will need its stack (`DataRegion::stack`) and an
I/O buffer at once. A bespoke view per combination of regions is the cruft
to avoid; the general piece is a separating product.

## Scope

- A view local to a footprint: its `Holds` depends only on the cells at an
  address set `In` (permissions fixed, as stores keep them), and every store
  it allows lands in `In`. Over `X86Memory(x)` this is a record with `x` as
  a parameter, so two views of one profile compose; `DataRegion` has its
  profile as a field (implicit record parameters are not inferred from
  method calls), so a region's view builds the record at `r.profile`.
- The product of two local views with disjoint footprints: `Holds` both,
  `Word`/`Byte`/`Stores` either arm, `Asks` of every memory holding both.
  Sound because a store through one arm leaves the other's footprint
  (`X86Profile::store_outside`), so its `Holds` carries over by locality.
  The product is local to the union, so products nest.
- The buffer view of a region as a local view; `View::with_code` over the
  product as over one view.
- A control: a program that reads into the page and counts in the frame.

## What it assumes from elsewhere

- **[[address-interval-sets]]** owns address sets. Assumed here: a
  footprint is a `SpanSet` of addresses' numbers under
  `BitVec::numbering(64)` (`lib/std/data/set/span_set.hthr`,
  `lib/std/machine/memory.hthr`), disjointness is `SpanSet::Disjoint` (a
  `disjoint` verdict), and a store misses a footprint by
  `Numbering::outside`.

- **[[io-image-on-byte-model]]** owns the image profile, its regions and
  `DataRegion::program_view`. Assumed here: only that each region's view is
  the buffer view.
- **[[native-one-wp]]** owns `View`/`ViewSound`.

## Log

- 2026-11-09: 2026-11-09: footprints, their disjointness and the packing of regions are filed as [[address-interval-sets]] (docs/native-mathematics-survey.md §4); build the local views over them.
