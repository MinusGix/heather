---
title: Find why grind calls slow down with itree in scope
status: closed
labels: [tactics,performance]
area: tactics
milestone: [tac-general]
created: 2026-11-06
updated: 2026-11-07
---

With `itree`/`coitree` imported, every grind call in `grind_tests` took
several times longer (the same kernel steps; a trivial call's time unchanged
without them), which put that probe module over its CPU rail on 2026-11-05;
the codata probes moved to `grind_codata_tests`. So something per call grows
with the scope rather than with the goal.

First suspects: name resolution (`Lookup`, `resolve`) or a host request that
walks the whole environment. Measure with `--timings` on one probe in both
scopes (the counters are the same, so the seconds and the host's own
attribution are what to read) before changing anything.

## Done when

The cause is named, and a grind call's cost does not grow with unrelated
imports (or this records why it must).

## What it assumes from elsewhere
- **[[grind-closure-cost]]** found it while making grind cheaper to import.
  Assumed here: only the measurement above.

## Log

- 2026-11-07: Done; the cause was not grind's lookups, and it is already
  gone on master. Measured with `--timings` (width one, `--cache`, a module
  of four fresh-named copies of `chain`, 36k kernel steps each, with and
  without `import itree; import coitree;`), every build in the same box:

  | compiler | library | without | with itree/coitree |
  |---|---|---|---|
  | #432 (6aa060a, filed) | #432 | ~35 ms | 4–13 s per call |
  | #438's parent | #438's parent | ~20 ms | 12.7 s, then ~5.4 s per call |
  | #438's parent | #438 | ~25 ms | 2.2 s first call, then ~30 ms |
  | #440 | #438's parent | ~25 ms | 0.16 s first call, then ~25 ms |
  | master | master | ~20 ms | 0.14 s first call, then ~20 ms |

  The kernel steps are the same in every cell. The cause is two things together:
  - `ModuleDelta::relocate` moved a module image whose position in the
    world differs from its canonical one. With itree/coitree in scope,
    tactic's and grind's images move. Before #440, `reindex_global` walked
    terms as trees, so the moved image came back unshared, and
    tactic/grind's Tac values, spelled as `W` encodings, share heavily.
  - The verdict store's Merkle walk hashed terms as trees too.

  gdb samples on the filed build split each call between the gate's
  `Inner::sync` → `merkle::interface_hash` and the tactic evaluator's
  `ValueArena::memo_closed` bounds walks (`bounds::Cache::compute_type`
  over the unshared terms).

  Taking #440's parts back one at a time over master's compiler, with
  #438's parent's library: reverting the relocation memo alone, or the kept
  Merkle prefixes alone, leaves calls fast. Reverting the Merkle node
  digests alone gives a 6.7 s first call, then fast. Reverting the memo and
  the digests together brings back ~5 s on every call, whether or not the
  kept prefixes stay. #438 removed the large `W` spellings from the
  library, which is why it fixed the cost on its own.

  What is left is master's first call in a module, ~0.1 s, which a
  non-grind item pays as well (a `refl` theorem first in the module costs
  the same). It does not grow with itree/coitree. The guard is
  `relocation_keeps_shared_nodes_shared` in
  `crates/kernel/tests/subst_laws.rs`; it fails with the memo removed.
  `grind_codata_tests` stays a module of its own, because joining it would
  add itree/coitree's closure to `grind_tests`'s cold gate. Its comment no
  longer cites this cost.
