---
title: An import's image hit is replayed over its own world, then again into the importer's
status: closed
labels: [performance,cache]
area: language
created: 2026-11-16
updated: 2026-11-16
---

Measured and not taken (2026-11-16, PR #689, closed unmerged).

A process that checks a module replays each off-spine import of its closure
twice: once over the import's own canonical world (`check_held` calls
`world_before` for a hit too), and once into the checked module's world. The
first can be skipped for an import whose image is a hit: record the hit
without building its world, as `hit_into_process` does for the
process-world mode, and build its state only if a later spine needs it. The
checked module's world still replays every module of its closure through
the gate. One case needs a fallback: an import whose image is stale in a way
its key does not see (`OpenedProofChanged`) first fails inside a
dependent's world, so the session has to stop deferring and check those
imports eagerly.

Same binary, deferral on and off, 4-core cloud, verdicts warm:

| | eager | deferred |
|---|---|---|
| standalone warm check, `native_tools` | 3.1 s | 1.85 s |
| standalone warm check, `sha256_stream` | 2.76 s | 1.74 s |
| the gate's folder step (37 folders, 4-wide) | 48 CPU-s | 40 CPU-s |
| the gate's build step (workers) | 928 CPU-s | 896 CPU-s |

All 617 images were byte-identical, and plain `scripts/test` passed. The
gate gains a few percent because the build workers
(`docs/infrastructure/module-dag-design.md` §12) already hold most closures;
the gain is a second off a standalone warm check of a wide closure. Minus's
call: not worth a new fallback path in the loader's trust code. What is left
of a warm closure load is mostly image decoding.

Reopen if standalone closure loads become the cost that matters (many
`--only` probes, a language server). The branch's commit is 017052d.
