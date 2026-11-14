---
title: Every process that records a verdict rewrites the whole verdict file, 64 MB in a seeded store
status: open
labels: [performance,testing,cache]
area: infrastructure
created: 2026-11-14
updated: 2026-11-14
---

The declaration-verdict store is one file (`entries-v1.tsv`, `crates/cache/src/store.rs`) holding a section per kernel, up to `MAX_KERNELS` of them ([[verdict-store-one-kernel]]). `Store::save_at` writes the whole file: it reads what is on disk, parses it, checks every other kernel's section against its checksum, unions its own, formats everything and renames the result into place. `Store::load` reads and parses the whole file to find one section.

That was sized for one process per run. The library gate's build step is a process per module (`heather check --build-jobs`, [[build-children-replay-their-imports]]), about 580 processes with the folder checks, and each one that records a verdict saves.

Measured 2026-11-14 at master efd0372 on a four-core cloud box, test-profile binary, self-checks off:

- The seeded CLI store's file is 64 MB: six kernels' sections, 92,000 entries in the current kernel's (11 MB), the other five carried through verbatim by every save.
- Build step over the seed of 2026-11-13 (257 commits behind): 444 s wall, 1550 CPU-s. `save_at` is on 23 of 157 stack samples of the children (15%), in the string growth, the rename and the other sections' checksums.
- The same step with the file cut to the current kernel's section first: 403 s, 1393 CPU-s. Each save still writes 11 to 14 MB.
- Loading the 64 MB file costs 0.13 s per process, with no save.
- An empty store has no such file to carry, which is part of why the whole library builds from nothing (369 s) faster than over a day-old seed.

## Directions

- A file per kernel beneath the store, so a process reads and writes only its own kernel's entries. [[verdict-store-one-kernel]] named this as the alternative to sections.
- Saves that append: new entries as a small file of their own beside the main one, folded in by whichever process finds more than a few. The whole-file argument in `save_at`'s comment (checksums cover bodies) holds per appended file too.
- Seed side only, no format change: `scripts/sentinel` publishes the current kernel's section and drops the rest. A fresh container never runs an older kernel. This depends on whether the seed keeps verdict files at all ([[sentinel-seed-follows-master]]).
- Entries within a section are never dropped: 92,000 for a library of about 30,000 declarations.

## Done when

A child of the gate's build step spends no measurable time in the verdict store beyond its own new entries.

## Log

- 2026-11-14: Filed from the third round of the PR lane speed thread, with the numbers above.
