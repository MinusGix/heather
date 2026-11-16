---
title: Move the ordered-algebra class theorems to implicit points
status: open
labels: [stdlib,ergonomics,traits,tactics]
area: language
milestone: [math-classes]
created: 2026-11-08
updated: 2026-11-08
---

Since [[generic-theorem-implicit-points]], a class theorem whose points are
implicit is called like the carrier's own: `p({x, y, z: K}, a: x < y, b: y <
z)` checks as `p(h1, h2)` inside a section, at `Rat` and at `CReal`, and a
theorem with no point is pinned by its expected type (the probes in
lib/_tests/std/algebra/ordered_field_tests.hthr). The library still states
its theorems with explicit points: `StrictOrder::le_of_lt(x, y, h)`,
`PseudoOrder::le_trans(x, y, z, h1, h2)`, `OrderedAddMonoid::add_respects(…)`,
about 700 calls to the theorems of lib/std/algebra/ordered_field.hthr across
42 files on 2026-11-08.

## What to do

1. For each theorem, make implicit exactly the points an explicit, undefaulted
   hypothesis mentions (`le_of_lt(x, y, h: x < y)` → `({x, y}, h)`; `le_refl(x)`
   keeps its point, which only the result mentions; a point only a `:= infer`
   premise mentions stays explicit, since search needs it known).
2. Rewrite the calls. A call whose hypothesis is a tactic or another
   checking-only argument (`le_trans(a, b, c, h1, linarith)`) has no type to
   read `b` from: pass it by name (`le_trans(y := b, h1, linarith)`,
   docs/language/named-arguments-design.md §5).
3. `mono` builds its class-law calls by name and position
   (lib/std/tactic/mono.hthr's `class_law(…, [1], "OrderedAddMonoid::add_le_mono_l")`,
   `PushLaws`, `mono_try_global("StrictOrder::le_of_lt")`), so its table and
   the builder move in the same round. The tactic lemma-list round may have
   changed how those lists are written; read it first.
4. Then the carriers' duplicated copies (65 `CReal::`, 68 `Rat::` names that
   coincide with a class theorem's) can start to go, which is
   [[type-owned-namespaces]]'s.

## Acceptance

- `ordered_field.hthr` states its hypothesis-pinned points implicitly and
  every caller in lib/ checks.
- `mono`'s tests pass with the moved lemmas.
- One generic analysis file (`real_fn.hthr` or `closed_interval.hthr`) is
  restated with the implicit calls, and its elaboration counters are
  compared with `scripts/perf ab --source-patch` (implicit points add
  unification work per call; the counters say how much).

## What it assumes from elsewhere

- **[[generic-theorem-implicit-points]]** owns the inference. Assumed here:
  only that a call whose hypotheses mention every implicit point infers them.
- **[[mono-class-laws]]** owns how `mono` finds class laws. Assumed here:
  nothing about its shape; step 3 reads it.
