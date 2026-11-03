---
title: An if condition mixing a Bool and a proposition is refused
status: open
labels: [language,frontend,surface-syntax]
area: language
milestone: [lang-sequencing]
created: 2026-11-02
updated: 2026-11-02
---

`if b && n = 0 { … }` with `b: Bool` is refused: the condition is neither a proposition (`b` is not a type) nor a `Bool` (`n = 0` is a proposition), so neither reading of [[bool-conditions-and-literals]] applies. Code writes `if b && n.same(0)` or nests the `if`s.

A mixed connective could read each operand by its own type: a Bool operand as `b.IsTrue()` on the proposition side (so `Decide<b.IsTrue() ∧ n = 0>`, whose bit is `b && same(n, 0)` by the instances), or a proposition operand as its `decide_bit` on the Bool side. The proposition side keeps evidence available (`if h: b && n = 0`), so it is the likely choice. Not needed by any code yet; filed so the refusal is a known boundary rather than a surprise.
