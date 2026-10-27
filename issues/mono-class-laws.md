---
title: Let mono read goals at a class-constrained carrier
status: open
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
