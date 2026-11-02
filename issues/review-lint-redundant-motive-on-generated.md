---
title: --review reports a redundant motive where the measure lowering wrote one
status: open
labels: [lint,match,diagnostics]
area: language
created: 2026-11-01
updated: 2026-11-01
---

Found by the slice-7 sweep of [[match-motive-sweep]] (2026-11-01). `heather check --review` reports "this explicit `match` motive is redundant" at five sites where no motive is written. Each site is the `decreases` clause of a measure-compiled `fn`, or a generated match inside one:

- `lib/_tests/native/runtime/rt_tests.hthr:240`
- `lib/_tests/std/tactic/omega_tests.hthr:268`, `:298`
- `lib/std/parser/parser_recursion.hthr:20`
- `lib/std/parser/parser_repetition.hthr:17`

The lint judges motives the measure lowering wrote, not motives in the source. Its fix span would delete source text that is not a motive.

## Done when
The lint fires only on motives written in the source. Measure-lowered and generated matches are excluded, and a probe pins it.
