---
title: Order-independent declarations within a package
status: open
labels: [frontend,elaboration,modules,parallelism,caching,design]
area: language
created: 2026-09-22
updated: 2026-09-22
---

Make declaration order irrelevant within a package, across files as well as
within one: imports decide visibility and namespacing, not elaboration order.
Motivating case: the 2026-09-22 `std` namespacing refactor, where `nat.hthr`
cannot state `instance Cmp<Nat>` beside the kit that fills it or use `List`,
because `algebra` and `list` import `nat`. Import order is a known Lean pain
point; the kernel-visible order should be discovered, not written.

Design proposal: `docs/language/package-order-independence-design.md` (status:
proposal). It owns the mechanism (demand-driven signature/body queries, cycle
classification, canonical Ψ order, instance heads first, staged parallelism,
declaration-keyed caching) and lists the open questions a design pass must
settle before any implementation round.

## What it assumes from elsewhere

- **[[mutual-recursion-declarations]]** owns group formation and the rank
  rule. Assumed here: only that both currently read declaration order, which
  this proposal removes; the replacement is decided in the design pass.
- **[[declaration-slice-replay]]** owns per-declaration replay. Assumed here:
  only that declaration-level results are the direction caching is already
  moving.
- **[[parallel-kernel-gate]]** owns kernel parallelism. Assumed here: only its
  submission-order determinism discipline.

Independent of [[receiver-dispatch-coinciding-readings]], which fixes the
name clash that prompted this without any ordering change.
