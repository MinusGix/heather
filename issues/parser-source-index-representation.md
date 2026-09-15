---
title: Make parser source identity explicit in the cursor representation
status: open
labels: [stdlib,parsing,proofs]
created: 2026-09-15
updated: 2026-09-15
---

## Problem

Cursor currently carries identity: source = source so equal-length distinct sources cannot collapse through the remaining offset and bound fields. This works, but clients deserve a principled account of value indexing and a less surprising representation if available.

## Scope and acceptance

Explain structural value indices versus nominal allocation identity. Investigate alternatives that retain actual source endpoints without accidental index collapse; keep definitionally equal sources interchangeable. Include open-source and equal-length source-swap controls. Avoid introducing generative identity merely for parser cursors.

Acceptance: documented representation decision, checked source preservation, and negative controls at advancement, cache construction and backtracking boundaries.

## What it assumes from elsewhere

[[parser-cached-cursor-cost]] owns caching and its performance comparison; this issue owns source-index semantics.
