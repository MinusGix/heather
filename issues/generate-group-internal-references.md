---
title: Let a generated declaration cite an earlier member of its group
status: open
labels: [metaprogramming,elaboration]
area: tactics
milestone: [tac-host-interface]
created: 2026-10-28
updated: 2026-10-28
---

A `generate` publishes its declarations only after the generator's run ends
(docs/host-elaboration-interface-design.md §19), so no member can cite an
earlier member of the same group: `Lookup` does not find a name that is not
published yet, and there is no `Expr` for "the declaration this run will
publish as `T::cong_App`". A group whose later lemmas use earlier ones (a
lemma and its corollary, an equation lemma and the congruence built on it)
has to be split over several `generate`s today, which loses the
all-or-nothing publication.

## Acceptance

- A member can refer to an earlier member of its own group by a typed
  reference the run issues (not by name), checked against that member's
  statement.
- The group still publishes all or nothing; a refused earlier member is
  reported as the cause, not the later member that cited it.
- A probe in `lib/_tests/std/tactic` where the second member's body cites the
  first, and a negative control citing a member that is refused.
