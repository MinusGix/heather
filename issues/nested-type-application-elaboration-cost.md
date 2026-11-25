---
title: Elaborating a nested type application is superlinear in its depth
status: open
labels: [elaboration,performance]
area: language
milestone: [none]
created: 2026-11-25
updated: 2026-11-25
---

Found by [[reflected-languages-typed-by-construction]] (2026-11-25). Elaborating a nested type application costs the elaborator time superlinear in its depth, while the kernel's share stays flat. `fn ty_eq(x: T) → T { x }` with `T` the type `List<List<…<Nat>…>>` nested `k` deep, `heather check --timings`, release, width one:

| k | total ms | gate ms | queries |
|---|---|---|---|
| 16 | 1.5 | 0.0 | 35 |
| 32 | 6.5 | 0.1 | 67 |
| 64 | 31.0 | 0.1 | 131 |

About fivefold per doubling, all outside the gate (queries are linear). Not attributed: a stack sample of the `k = 64` item is the first step. It matters where types are data: a chain of steps typed by their source and target writes each intermediate type, so a chain of depth `n` writes types of total size quadratic in `n`, and this cost compounds it (the type-indexed chain's construction was most of its elaboration at depth 64, gate under a tenth of it).

## Done when

The table above grows linearly in `k`, or the superlinear part is attributed and a decision recorded.
