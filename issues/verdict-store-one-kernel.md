---
title: Keep verdicts for more than one kernel in a shared store
status: open
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
