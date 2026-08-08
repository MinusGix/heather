---
title: The resolver's upcast assembles a fresh parent record per occurrence at an open carrier
status: open
labels: [elaboration,performance,traits]
created: 2026-08-08
updated: 2026-08-08
---

Found by the type-projection round (2026-08-08), as the finding that decided
its migration: `plus_zero_of_comm` written `<G: AddCommMonoid>` with
`G.plus(x, G.zero)` elaborates correctly and takes the library check from
0.7 s to 25 s. The cost is not the projection: `plus` and `zero` are declared
by ANCESTORS (`AddSemigroup`, `AddMonoid`), so each type projection builds its
goal at an ancestor and is answered by the resolver's upcast
(docs/traits-owner-dispatch-design.md §3, §7.1), which at an open carrier
assembles a fresh parent record over the child dictionary's projections —
once per occurrence, five times in that one small proof, each a Σ-tuple of law
types the kernel then compares by conversion.

Measured (2026-08-08, release, lib/std/algebra.hthr):
- exact-dictionary spelling (`requires a` / `G::AddCommMonoid.plus`): 0.7 s
- upcast projections in the statement only: 1.7 s
- upcast projections in the proof body too: 19–25 s

Shape of a fix: the assembled parent is rebuilt per occurrence, and layer 2's
derived table cannot hold it because the value depends on a local binder. A
per-declaration (per-Cx-prefix) memo of assembled upcasts, or emitting the
assembly once as a `let`-grade alias the occurrences share, are the obvious
levers; either must keep every proposal passing `checks_at`.

Until fixed, the library's `plus_zero_of_comm` keeps `requires` with the
measurement written beside it (the standing motive), and this issue is a NEW
ENTRY on the `requires`-removal prerequisite ledger
([[requires-placement-syntax]], 2026-08-07 INTENT entry): removal cannot
strand hierarchy-spanning proofs on a 25 s spelling.

Per the perf discipline (layer 2 §10's trial-cost entry is the doc home):
filed with its trigger, one deliberate round when picked up.

## What it assumes from elsewhere
- **docs/traits-owner-dispatch-design.md** owns the upcast rule (assembly, not
  projection, at open carriers). Assumed here: only that the assembly is per
  occurrence today.
- **[[traits]]** owns the resolver. The fix must not reorder the search
  (exact scope -> upcast -> registry) or bypass the kernel gate.
