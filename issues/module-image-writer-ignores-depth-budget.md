---
title: The module-image writer publishes an image deeper than its reader's depth budget
status: open
labels: [cache,robustness]
created: 2026-09-29
updated: 2026-09-29
---

The cache refuses to publish an image past the reader's node budget
(`ModuleCacheError::OverBudget`, recorded as an `ImageRefusal`), because an
image the reader refuses is rebuilt on every warm run and says nothing. The
depth budget (`ModuleImageLimits::max_depth`, 2048) has no such check: the
writer counts nodes but not depth, so an image deeper than 2048 is written,
refused with `DepthBudget` at every load, and silently re-elaborated.

Nothing in the corpus is near it today. The `wc` certificate's published
byte tree was about 500 levels deep when it overflowed the old decoder's
stack ([[module-image-decode-depth-vs-stack]]). Programs with longer code
will grow those spines.

Shape of a fix: the writer tracks its maximum depth at the sites that count
`nodes` (a `Writer::node` wrapper mirroring `Reader::node`), and
`publish_as` refuses past `max_depth` with an `ImageRefusal::Depth` beside
`Nodes` and `Bytes`. The reader's depth is stack-safe at any budget now,
because the decoder sizes its own thread from `max_depth`, so the other option
is raising the budget (address space only, 4 KiB a level).

## What it assumes from elsewhere

- **[[module-image-decode-depth-vs-stack]]** owns the decoder's stack. Assumed
  here: only that the reader refuses a node deeper than `max_depth`.
