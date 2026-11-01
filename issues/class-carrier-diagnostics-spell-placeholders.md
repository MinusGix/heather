---
title: linarith's refusal at a class carrier spells the goal with the elaborator's placeholders
status: open
labels: [tactics,diagnostics,ergonomics]
area: tactics
milestone: [tac-arith]
created: 2026-11-01
updated: 2026-11-01
---

At a section's class carrier (`section<K: OrderedField(≈, <, <=, +, *)>`),
a `linarith` that fails shows its goal in the elaborator's internal
spelling of the section's operations and dictionary:

```text
error: `linarith` could not prove `#op<=@0_2(#constraint0.unit, #op+@0_3(#op*@0_4(d, d), #constraint0.unit))`: …
```

The goal was written `K.unit <= d * d + K.unit`. The facts' readings in the
same message are fine (`d^2 + d + 1 >= 0`); only the goal's display reaches
the placeholders (`#op<=@…` for the section's designated `<=`, `#constraint0`
for `K`'s dictionary). The user should see `K.unit <= d * d + K.unit`.

Shape of a fix: display the goal the way other error paths at a class
carrier do, resugaring an operator variable to its designation and the
constraint placeholder to `K` ([[diagnostic-operator-resugaring]]).
Found in the round that closed [[ring-atom-mentions-class-constant]].
