---
title: An if condition mixing a Bool and a proposition is refused
status: closed
labels: [language,frontend,surface-syntax]
area: language
milestone: [lang-sequencing]
created: 2026-11-02
updated: 2026-11-03
---

`if b && n = 0 { … }` with `b: Bool` is refused: the condition is neither a proposition (`b` is not a type) nor a `Bool` (`n = 0` is a proposition), so neither reading of [[bool-conditions-and-literals]] applies. Code writes `if b && n.same(0)` or nests the `if`s.

A mixed connective could read each operand by its own type: a Bool operand as `b.IsTrue()` on the proposition side (so `Decide<b.IsTrue() ∧ n = 0>`, whose bit is `b && same(n, 0)` by the instances), or a proposition operand as its `decide_bit` on the Bool side. The proposition side keeps evidence available (`if h: b && n = 0`), so it is the likely choice. Not needed by any code yet; filed so the refusal is a known boundary rather than a surprise.

**Done 2026-11-03.** One correction to the framing first: `&&` binds tighter than `=` (issues/bool-operator-designations.md), so `if b && n = 0` is `if (b && n) = 0`, a Bool-and-Nat type error, and stays refused (`no instance for Decide<b && n = 0>`). The mixed forms are `b ∧ n = 0` and `b && (n = 0)`.

Built as the proposition side, as proposed: when neither whole reading applies and the condition is a connective (`∧`, `∨`, `↔`, a non-dependent `→`, `¬`, or `&&`/`||`/`!`), `Elaborator::mixed_condition` (crates/elab/src/lib.rs) rebuilds it with each `Bool` operand as `b.IsTrue()` (a Bool subtree is one operand) and the Boolean doubles as the connectives they decide, then decides that. `if b ∧ n = 0` is the match on `b && n.same(0)` (proved by `refl` at neutral `b` and `n`), and `if h: b ∧ n = 0` gives `h: b.IsTrue() ∧ n = 0`. Probes: `mixed_*` in lib/_tests/std/core/imperative_statements_tests.hthr; design note docs/language/decidable-if-expression-design.md.
