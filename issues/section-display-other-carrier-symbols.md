---
title: Diagnostics in a section spell another carrier's relation by name, not by its symbol
status: open
labels: [diagnostics,notation]
area: language
milestone: [math-classes]
created: 2026-11-09
updated: 2026-11-09
---

Split from [[constraint-indices-from-carrier-designations]]. Since
[[section-symbols-capture-other-carriers]], `a <= b` at `Rat` inside
`section<K: OrderedField(≈, <, <=, +, *)>` reads `Rat::Le(a, b)`, but a
diagnostic there still prints `Rat::Le(a, b)`: crates/elab/src/display.rs
blocks spelling any symbol a binder installed (its rung-1 check), because
the resolver used to read such a symbol back as the binder at every carrier.

## Direction

Lift the block where the resolver now reads the symbol back as the
designation: the callee's declared operand carrier is nominal and is not the
binder's (the binder operation's first domain), and the operands are not
numerals alone. Display can read the first from the callee's telescope, as
`operand_carrier` already does.

## Acceptance

- A mismatch inside such a section prints `a <= b` at `Rat`, and the spelled
  form re-elaborates to the same term (a probe that round-trips it).
- `0 <= 1` at `Rat` (numerals alone) still prints by name.

## Log

- 2026-11-09: Filed as residue of [[constraint-indices-from-carrier-designations]].
