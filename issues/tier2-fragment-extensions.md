---
title: Tier 2: the parts of the W lowering left out of round one
status: open
labels: [inductives,elaboration]
area: language
created: 2026-10-20
updated: 2026-10-21
---

`docs/inductive-tier2-w-lowering.md` §1 lowers a fragment and refuses the
rest by name. Each item below is its own small round; none blocks the
interaction-tree library, which is why they are grouped.

- **Curried function fields** (`k: A -> B -> D`). Positions become a Σ of
  the domains, and a match arm rebinds `k` curried. Today: refused, "take a
  pair".
- **Several recursive fields beside a function field** (`Node(l: D, r: D)`
  in a declaration that also has `F(k: A -> D)`). Positions are then a sum,
  and rebuilding the children from an abstract `f` is η for sums (§2.2), so
  this needs either the children split per field (a Π over a Σ of codes) or
  a different encoding of the branching constructors.
- **Generated definitions.** The leaf predicate is named (`D#canon`,
  docs/inductive-tier2-w-lowering.md §13, 2026-10-21); `S`, `P` and the
  whole `⟦D⟧` stay inline. Naming `P` (and `W₀` with it) is the next lever if
  a later profile shows the remaining copies; nothing measured asks for it
  yet.
- **`inj` at a recursive field.** The plain child's projection needs `f`
  generalized (tier 1 §7's correction); a function child's injectivity is
  funext and stays refused.
- **Course-of-values windows** and **certificate/native generators**: both
  refuse a tier-2 type today.

## What it assumes from elsewhere

- **[[recursive-function-fields]]**: landed 2026-10-20; this is its residue.

## Done when

Each bullet is either lowered with four-axis tests or recorded here as
declined with its reason.

## Log
- 2026-10-21: The generated-definitions bullet is now measured, by the first
  real client (`lib/std/itree/itree.hthr`, `docs/itree-core-round.md`). Each law
  proved by induction over `ITree<R>(E)` (a four-arm `match` at a motive
  computed by a large elimination, `ITree::Same`) costs seconds of kernel gate
  at width one, and a callgrind profile of one of them (`bind_ret_r`) puts
  most of the gate in `conv_ty` (the W type's structural comparison, `ty_w`)
  and `ShiftLocal` copies of the inline spelling. The library's cold check is
  the suite's slowest target (`lib_std_itree`, most of the process's CPU rail
  spent building the prefix). Naming `⟦D⟧`, `P` and the leaf predicate is the
  candidate fix; the readback half of the cost was fixed in the same round
  (an `elim_W` induction hypothesis now reads back).
- 2026-10-21: **Leaf predicate named.** `D#canon := λ(Ā : Ty 0)(v̄).
  λ(t : W₀). canon t`, registered at declaration time over `D#tycode_fn`'s
  telescope, and the tier-2 lowering spells its second component as
  `El(app(D#canon^δ; ā, t))` at that profile (inline elsewhere). The size
  probe that chose it: for a four-constructor tree the inline predicate is
  about 97% of `⟦D⟧`'s spelling, `S` and `P` the rest. On
  `lib/std/itree/itree.hthr` (cold, width one, one machine) the whole check went
  from about two minutes to under ten seconds and the kernel gate fell by
  more than an order of magnitude, with the query, miss and step counts
  falling in proportion; `scripts/perf ab` numbers are on the PR. Counts
  move by design here (the terms are smaller); verdicts do not.

