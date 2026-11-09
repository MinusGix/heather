---
title: Read native's Boolean membership spellings in the sets tactic
status: closed
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

## Log

- 2026-11-09: Spellings done: `SetBitLaw`/`SetBitEntry` (a Boolean that reflects membership, or whose negation does); native registers `absent` (`absent_set_law` in native_alloc), and `holds` reads through its definition as `!absent`. `sets` reads `b = True`, `b = False`, `b.IsTrue()` as hypotheses and goals, `x = e` hypotheses (facts about `e` move to `x`), `∧` hypotheses by halves, and splits `∧`/record goals (`Clear`). `clear_of`, `absent_append_intro`, `holds_false_absent`, `union_left/right`, `mem_minus_nil/cons` are now `by sets()`. Two fixes on the way: `by` finds the tactic protocol through the import closure (a native module importing `tactic` got `pure` in scope, which made `node.pure().IsTrue()` ambiguous; diagnostic gap filed as [[chained-dot-ambiguity-reported-as-unbound]]), and Close commits each branch's proof before the next branch's `Blank` grows the world (a kernel LevelMismatch before). Left: relation spellings (`within(a, b) = True`, `disjoint(xs, ys).IsTrue()`) and inclusions whose conclusion is a spelling (`disjoint_mem`), `DecEq<Gpr>`, and modules upstream of native_alloc (`absent_append`, `absent_join` in native_source_io) which cannot see the registered law. A call costs about 0.15–0.6 s, most of it the tactic's own interpretation, not the table.
- 2026-11-09 (round 2): Relations done: `SetRelEntry { op, elim, intro, implicits }` (set_ops), the elim law turning `f(a, b).IsTrue()` into a function type the tactic reads at each element and the intro law proving it back; `disjoint` (elim `disjoint_mem`, intro `disjoint_of`) and `absent` are registered in function_ir_eval beside their definitions, so modules upstream of native_alloc see them (`absent_false_mem`/`absent_set_law` moved there), `within` in native_alloc (`within_mem`, new `within_of`). The table gains `FApart(a, b)` (`x ∈ a → x ∉ b`), so an inclusion whose conclusion is `¬Mem` or a spelling (`disjoint_mem`'s shape) is a fact; the spelling's conversion is composed after it (`set_comp`). `Tm::disjoint_tail`, `absent_join`, `present_of_mem` and `within_of_inside` are now `by sets()`. Left: `DecEq<Gpr>` for register pools, `= False` of a relation (needs a witness), and hand chains inside larger proofs (`moves_to_words`' `disjoint_mem` step) that are one citation, not a lemma.
- 2026-11-09 (round 3, closed): Register pools and element equalities. `DecEq<Gpr>` (x86_64, by `Gpr::same_reflects`); `Gpr::absent_from` is a `SetBitEntry` and `gprs_outside` a `SetRelEntry` (`gprs_outside_mem`/`gprs_outside_of`). A new `SetEqEntry { op, law, negated, implicits }` with `SetEqLaw` reads Boolean equalities between elements: `Gpr::same`, `Nat::matches`, `Nat::differs` (negated). A spelled equality hypothesis is the equation or disequation; a spelled goal becomes `x = y` (proved as `x ∈ [y]`, at `x` then at `y`) or `¬(x = y)` (proved as `False` under the equation, so the equation aliases the two elements). `Gpr::absent_head`, `absent_rest`, `absent_first`, `absent_mem` and `home_register_apart` are now `by sets()`. Not done, and not worth an issue of their own yet: `= False` of a relation (needs a witness), and one-citation steps inside larger proofs.
