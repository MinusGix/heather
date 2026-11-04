---
title: Checking ⟨⟩ against a computed type costs more than the same verdict as a refl
status: open
labels: [kernel, performance, conversion]
area: kernel
created: 2026-11-02
updated: 2026-11-02
---

Found closing [[closed-verdict-evaluated-twice]]. Once `trivial` at a closed
`heavy(300).IsTrue()` leaves the verdict to the gate, the gate's check of
`⟨⟩` against the statement runs the same evaluation as `refl` at
`heavy(300) = True` (230,921 vs 230,921 eval steps, plus the elaborator's
4,096-step read budget), with the same `eval_drives`. It still takes more kernel
time and more memory than the `refl` does. Each verdict alone in its own file
(the probe is `lib/_tests/std/core/closed_verdict_tests.hthr`'s `heavy`), at
width 1, cold:

- `trivial` (`⟨⟩ : Unit` converted with `IsTrue(heavy(300))`) has a peak of
  about 88 MB and takes roughly a fifth more gate time;
- `refl`, `decide`, and `is_true_of_eq(refl)` (term conversion of
  `heavy(300)` with `True`) peak at about 67 MB.

The only difference is the conversion's shape: a cross-head *type*
conversion (`Unit` against an `El` of a code-valued call) against a term
conversion at `Bool`. The guess, not yet checked, is that the type side holds
the evaluation's intermediate values for the whole query (a closure or
environment the decoded `El` keeps alive). The term side drops them as it
goes. The extra pages are what the time pays for.

## Wanted

Find what the type-side conversion keeps alive, and make `⟨⟩` against a
computed type cost what the term conversion costs. Measure with
`scripts/perf ab` over the closed-verdict probe, reading `peak MB` per item
alone in a file (`peak_growth_kb` is a high-water mark, so an item placed
after a heavier one reads near zero).
