---
title: Drop hand-fed le_max/max_le/le_min chains next to omega now that it splits max and min
status: open
labels: [omega,tactics,cleanup]
area: tactics
milestone: [tac-arith]
created: 2026-11-09
updated: 2026-11-09
---

omega splits `a.max(b)` and `a.min(b)` at Nat and Int since
[[omega-reads-min-max]] (docs/tactics/omega-measure-reduction-design.md §20), so a
`le_max_l`/`le_max_r`/`max_le`/`le_min`/`min_le_*` chain whose only job is
to feed an index or bound to the next step is now one `omega`.
sequence.hthr's `Converges::le`, `unique`, `add` and `squeeze` were dropped
in the landing round. About seventy calls remain outside nat.hthr/int.hthr:
creal.hthr (most), float `dyadic`, `interval`, `eft`, `error`, `series`,
`window`, analysis `supremum`, `closed_interval`, and algebra `lattice`
(the last is probably a lattice's own `⊔`, not Nat/Int `max`: check before
touching it).

Sweep module by module: replace the chain, check the module with
`--cache`, keep the drop when it closes. A chain stays when its terms are
ones omega cannot spell (`Converges::mul`'s witnesses projected through the
ordered-field dictionary; "Omega could not spell a natural expression" in
the refusal), when it feeds something other than an order goal, or when
the goal stacks enough reads that the split's branches cost more than the
chain: compare with `scripts/perf ab --source-patch` if a module slows.
