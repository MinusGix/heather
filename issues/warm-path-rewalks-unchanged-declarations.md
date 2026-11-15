---
title: "The warm cache path re-walks and re-hashes every unchanged declaration"
status: open
labels: [tooling, performance, cli]
area: infrastructure
created: 2026-08-06
updated: 2026-09-17
code: crates/cache/src/merkle.rs @ 33c65ef
---

After the structural walker ([[parallel-checking-and-caching]] log,
2026-08-06), a warm `heather check --cache lib/certgen/ir_v1.hthr` is ~2.2 s:
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

## Log

- 2026-09-17: 2026-09-17: a datum for the memo candidate from [[merkle-walk-cold-share]] (closed): on the showcase the walker visits 51.8 M nodes against 24.7 M distinct addresses, ratio 2.1 (at most 3.8 on one walk), so the per-Rc memo is a 2x ceiling on what is now ~1.3 s of a 57 s cold check; the walk's other two costs (a double render per declaration, the scalar hash rate) are gone.
- 2026-09-17: 2026-09-17: the second candidate ("skip elaboration too") has its design pass and its own issue, [[declaration-slice-replay]] (`docs/infrastructure/declaration-slice-replay-design.md`): slices of the module image keyed by item source digest and accepted on the exact semantic prefix — the image's own identity pair at declaration granularity, so not a second notion of identity. This issue keeps the first candidate, the per-Rc walk memo, which a replayed slice still pays (0.6 s on the showcase edit).
