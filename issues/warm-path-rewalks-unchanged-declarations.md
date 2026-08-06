---
title: "The warm cache path re-walks and re-hashes every unchanged declaration"
status: open
labels: [tooling, performance, cli]
created: 2026-08-06
updated: 2026-08-06
code: crates/cache/src/merkle.rs @ 33c65ef
---

After the structural walker ([[parallel-checking-and-caching]] log,
2026-08-06), a warm `heather check --cache lib/ir_v1.hthr` is ~2.2 s:
roughly 43% parse+elaborate, 57% walking and hashing declarations whose
source did not change. The encoder is no longer the lever — the v2 round
measured hashing at ~1.25 s total and SHA-256 itself was never the cost —
the lever is *not doing the walk at all* for unchanged material.

Two candidate shapes, recorded so the round that takes this starts from
the measurement, not the idea:

- **Per-`Rc` subtree hash memoization**: elaborated terms share structure
  aggressively (the Γ-spine and subst-sharing rounds made this more true,
  not less), so a `by_address` memo table over `Rc` identity during one
  run could collapse the walk to shared-prefix size. Address identity is
  only valid within a run — never persist it; it must not change which
  bytes are hashed, only skip recomputing them (the
  [[elaboration-determinism]] rule: pointer identity may change how fast,
  never what).
- **Skip elaboration too**: source-level chunking (hash the declaration's
  source text + resolved import interface hashes) to skip parse+elaborate
  for untouched declarations. Bigger prize (the remaining 43%), but it
  reintroduces a text-level identity beside the elaborated one, which is
  exactly the two-notions risk v1 refused — wants its own design pass
  against [[parallel-checking-and-caching]]'s architecture before anyone
  writes it.

## When

Triggered: when warm-run latency matters to an inner loop — e.g. an agent
session re-checking a large file after each small edit, or the daemon
round making warm checks the common case. One deliberate round, per the
accumulator discipline.
