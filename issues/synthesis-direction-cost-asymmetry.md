---
title: Layer 1's two parent-synthesis directions do not cost the same downstream
status: open
labels: [elaboration,performance,traits]
area: language
created: 2026-08-08
updated: 2026-08-08
---

Found by the named-upcast round's acceptance measurement (2026-08-08,
docs/traits-named-upcast-design.md): `bool_plus_zero`'s kernel gate costs
~2.1x `nat_plus_zero`'s at every scale measured — 7.9 s vs 2.9 s before the
read-through fix, 0.075 s vs 0.035 s after — so the fix rescaled the
asymmetry without touching it, which localizes it away from the upcast
entirely.

Likely owner, unconfirmed: the *direction* of layer 1's canonical parent
synthesis (docs/traits-layer1-design.md §4.4). Nat's chain is parent-first
(`AddSemigroup<Nat>`/`AddMonoid<Nat>` are declared, the child fills `plus`
by reference), Bool's is child-first (`AddCommMonoid<Bool>` is declared and
its parents are SYNTHESIZED record literals) — one extra global for
conversion to unfold on every path that reaches a Bool parent's field.

Worth one measured look when perf attention next lands on the traits line:
confirm the direction hypothesis (declare Bool's chain parent-first in a
scratch copy and re-measure), and if confirmed, decide whether child-first
synthesis should emit its parents by reference to the child's members
rather than as literals. Filed per the perf discipline: trigger recorded,
one deliberate round when picked up.

## What it assumes from elsewhere
- **docs/traits-layer1-design.md** owns both synthesis directions. Assumed
  here: only that they emit differently-shaped globals.
- **[[traits]]** owns the class layer. Nothing here questions the
  canonical-value discipline itself.
