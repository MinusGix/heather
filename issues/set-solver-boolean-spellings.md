---
title: Read native's Boolean membership spellings in the sets tactic
status: open
labels: [tactics,native,sets]
area: tactics
milestone: [hih-passes]
created: 2026-11-09
updated: 2026-11-09
---

The `sets` tactic ([[finite-set-membership-solver]],
`lib/std/tactic/set_tactic.hthr`) reads membership as `Mem(x, s)`, `¬Mem`,
`¬(x = e)`, inclusions (`a.Inside(m)` and any function type ending in a
membership), `False`, and the operations registered as `SetOpEntry`
(`++`, filters, `Cons`, native's `union`/`minus`). Native proofs also spell
membership as Booleans, and those spellings are most of the remaining
citations:

- `absent(x, s) = True` / `= False` (237 citations), `s.holds(x) = True`
  (44), `a.within(b) = True`, `disjoint(a, b) = True`, as hypotheses and as
  goals. Each is `¬Mem`, `Mem` or an inclusion through a lemma native
  already has (`absent_mem`, `absent_false_mem`, `holds_mem`, `within_mem`).
  A registry of spellings beside `SetOpEntry` (the predicate, the polarity,
  the lemma each way) would let the tactic read them without importing
  native, as the operation registry does.
- Register pools: `List<Gpr>` with `Gpr::absent_*` needs a `DecEq<Gpr>`
  instance before the tactic can run there.
- Migrating the remaining hand chains in `native_alloc`,
  `native_compile_homes` and `native_compile_perform` (the `mem_append_l/r`
  lambdas inside `nodes_checked_inside`, `mem_minus_cons`, `union_left/right`
  call sites) once the spellings are read.

Cost shape to keep in mind: the verdict enumerates 2^(atoms + elements +
predicates), so a literal list read element by element is the expensive
case; the reader keeps a call whose definition is a literal or a `match`
as one atom.
