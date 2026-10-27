---
title: Let mono read goals at a class-constrained carrier
status: closed
labels: [tactics,order,algebra]
area: tactics
milestone: [tac-general]
created: 2026-10-27
updated: 2026-10-27
---

`mono` ([[monotonicity-tactic]], `lib/std/tactic/mono.hthr`) knows the
concrete carriers `Rat`, `CReal`, `Int` and `Nat`: its registry names their
theorems (`Rat::add_le_mono`, …) and dispatches on their operations' globals.
A goal inside `section<A: OrderedField(≈, <, <=, +, *)>` is at none of them:
its `<=` and `+` are the dictionary's, and the laws it would need are the
class's (`OrderedAddGroup` translation, `OrderedField` products).

Wanted: the registry reads a goal at a class-constrained carrier, resolves
the order and the operations through the dictionary, and applies the class's
laws (stated once, as `Layer::thm`, per [[ordered-algebra-api]]). Then a
`Rat` or `CReal` goal could go through the class too, and the per-carrier
tables would shrink to the laws the classes do not state.

What to find out first: how `View` presents a dictionary operation (a
projection of a local, or a global applied to the dictionary), and whether
`apply`'s `Match` fills a class lemma's dictionary argument from the goal.
The `ring` tactic's relation reading ([[ring-modulo-a-relation]]) faced the
same question for `≈`.

## Log

- 2026-10-27: Done. `View` presents a dictionary's field reads as
  `HField(record, name, args)` (`A.inv(x)`, `A.unit`; they were `HOther`)
  and a dictionary's type as `HGlobal(class, name, [carrier, index…])`; the
  index operations (`+`, `<=`) were already the section's locals. `Match` did
  not fill a class lemma's dictionary (it left it, and the indices the
  conclusion does not mention, to the caller), so it now fills class
  parameters as a call does: from a dictionary in scope (the class's binder
  or a descendant's, upcast by resolution), and by resolution where the match
  has determined the class type. `mono` reads a goal whose relation is a
  dictionary's `<=`/`<` off a local of an ordered class (`OrderedField`,
  `LocatedAddGroup`, `OrderedAddGroup`, `PseudoOrder`, `StrictOrder`) and
  applies the class's laws, stated once in `ordered_field.hthr`; new there:
  `OrderedAddGroup::add_pos`, `LocatedAddGroup::add_lt_le_mono`,
  `add_le_lt_mono`, `add_nonneg`, `OrderedField::mul_pos_of_pos`,
  `neg_of_mul_neg`, `pos_of_mul_pos_nonneg`, `mul_le_mono_l/r`,
  `mul_nonneg`, `mul_le_mul`. The concrete carriers keep their own tables
  (`docs/monotonicity-tactic-design.md` §7). Probes:
  `lib/_tests/std/tactic/mono_tests.hthr`, `tactic_tests.hthr`.
  The image of `mono` grew enough to put a gate folder that loads it past the
  6 GiB rail; reshaping `mono_same`/`mono_closed` brought it below its size
  before this round, and the cause is filed as [[tactic-module-image-size]].
