---
title: Make large proof composition retain source sharing in the frontend
status: open
labels: [frontend,elaboration,performance,proofs,compiler]
area: language
created: 2026-08-31
updated: 2026-10-31
milestone: [lang-proof-modularity]
---

The compact FunctionIR validity experiment isolated two costs that should not
require generated staging declarations in a capable elaborator.

First, a balanced directory stored beneath one transparent function made every
logarithmic membership proof reconstruct the complete encoded tree. Splitting
the tree into one named function per persistent subtree changed 20-node lookup
items from roughly 0.5--0.8 seconds each to 0.01--0.05 seconds each without
changing the proof relation.

Second, after lookups were cheap, one nested `NodesIndexed` proof for 100 nodes
spent 68.9 seconds in frontend elaboration but only 7.5 seconds in the final
kernel gate. Replacing it with opaque suffix stages made every stage a small
constant-size item and made the complete focused 100-node test finish in 13.66
seconds including module setup.

Generated staging is a valid compiler technique, but it is compensating for
lost sharing rather than expressing semantic complexity. Diagnose which
frontend operations repeatedly normalize, clone, or re-elaborate the unchanged
directory/list spine.

## Acceptance

- A monolithic balanced-directory membership corpus scales by path length, not
  by rebuilding the entire directory for every lookup.
- A directly nested 100-node `NodesIndexed` certificate checks at a cost near
  the staged spelling and does not spend tens of seconds outside the kernel.
- Item timings attribute the improvement and retain separate frontend/kernel
  measurements.
- The staged compiler output remains accepted; this is an elaborator
  improvement, not a new requirement that generators emit one giant term.

## What it assumes from elsewhere

- **[[function-ir-validity-environment-scaling]]** owns the concrete compact
  validity representation and measurements. Assumed here: its staged source is
  the semantic and performance control.

## Log

- 2026-09-06: Datum (2026-09-06): after the kernel round on [[function-ir-x86-proof-scaling]], the generated x86 module's FRONTEND time is 1.5 s / 6.1 s / 20.3 s at 5 / 20 / 50 nodes (kernel 7.0 / 24.8 / 46.6 s), i.e. superlinear where the kernel is now ~linear; the boundary items (artifact, refines, protected) carry 11.8 s of frontend at 50 nodes. This is the next wall for the 100-node rail.
- 2026-10-31: 2026-10-31: Round P5 of docs/compiler-milestones-proposal.md (§6), milestone lang-proof-modularity, with [[let-fanout-diagnostic]]. Its done-when adds that 'split into stage theorems' retires from docs/proof-patterns.md.
