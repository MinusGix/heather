---
title: Keep verdicts for more than one kernel in a shared store
status: closed
labels: [tooling, infrastructure, cache]
area: infrastructure
created: 2026-11-04
updated: 2026-11-04
---

The declaration-verdict store (`entries-v1.tsv`, `crates/cache/src/store.rs`)
carries one `kernel-semantics` header for the whole file. A reader whose
kernel differs discards every entry (`KernelChanged`) and its save overwrites
the file.

That was free with one checkout. With several sharing a store through
`HEATHER_CACHE_DIR` ([[shared-cache-dir]]), one worktree that edits anything
under `crates/kernel/src` and runs a suite wipes the verdicts every other
worktree was relying on, and they wipe its own in return: the store
ping-pongs between kernels and nobody keeps a warm one.

Wanted: entries kept per kernel fingerprint (sections of one file, or a file
per kernel beneath the store), a reader using only its own kernel's, and old
kernels evicted by age rather than by whoever saved last. Trust is unchanged:
a verdict is still only ever accepted under the kernel that recorded it.

## What it assumes from elsewhere

- **[[shared-cache-dir]]** owns where the store lives. Assumed here: only that
  several checkouts may share it.

## Log

- 2026-11-04: landed as sections of one file (format 4,
  `crates/cache/src/store.rs`, `docs/infrastructure/cache-v1-design.md` §8). Sections over a
  file per kernel: the one path keeps the loud format-bump route (`FILE` is
  never renamed), `cat` still shows everything the store knows, and a reader
  verifies only its own section's checksum, so the others cost a structural
  scan. Each `kernel` line carries the fingerprint, a last-used stamp and the
  section's checksum; a save merges its kernel's on-disk entries, carries
  every other intact section verbatim, drops sections idle for
  `MAX_AGE_SECS` (30 days) or beyond the `MAX_KERNELS` (16) most recent, and
  drops a damaged one. A warm run that recorded nothing renews its stamp once
  `REFRESH_SECS` (a day) old, else a fully warm kernel would age out. A
  format-3 file is read as one unstamped section, since only the shape moved,
  so landing this costs no shared store a cold run. `KernelChanged` now says
  how many entries and kernels it saw and that they are kept. Tests:
  `crates/cache/tests/end_to_end.rs` (sharing, eviction by age and count,
  stamp refresh, damaged section, format-3 read); the CLI stale-store test
  re-labels its section. Not changed: concurrent saves still race between
  read and rename, so a lost update is a miss, as before.
