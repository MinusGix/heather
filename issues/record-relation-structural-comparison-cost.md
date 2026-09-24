---
title: Record-type relations compare structurally where a wrapper global compared by head: 6-24x kernel steps on calc_text's bodies
status: open
labels: [kernel,conversion,performance,records,representation]
created: 2026-09-24
updated: 2026-09-24
---

Replacing a spec-relation wrapper `fn GrammarSpec(…) -> Type { Grammar(…) }`
with the partially applied record `Grammar(level)`, and turning ∧-tower
relations into records, multiplies the kernel steps of the declarations that
compare those relations. Measured by [[showcase-spec-relations-as-records]]
(2026-09-24, `calc_text`, cold, width one): the whole file went 19.8 s → 22.0 s.
Per declaration, kernel steps:

| declaration | before | records, wrapper kept | records, wrapper gone |
|---|---|---|---|
| `factor_body` / `expr_body` | 6.3k | 40.8k | 150.5k |
| `close_body` | 6.8k | | 123.5k |
| `finish_text` | 12.5k | | 101.8k |
| `number_body` | 3.3k | | 48.2k |

Misses on `factor_body` went 312 → 3,637. Nothing else in the file moved.

So both halves cost. This was predicted by [[record-type-partial-application]]:
a global wrapper's partial application is a δ-stuck neutral spine that head
conversion compares before unfolding, while `Grammar(level)` is a λ over the
inlined record lowering, and two of those compare structurally, Σ tower and all.
The record-relations half is the same shape at `RunSpec`/`OpRun`.

This was a readability round and it landed as written (user verdict: a worse
cost is a sign the language needs another round, not a reason to keep the
wrapper). The lever belongs to the kernel-side structural pass,
[[elaborator-canonical-type-spelling]]: a record type former referenced by
name, compared by head like a global, instead of its inline lowering. Not
urgent at these sizes; it becomes urgent if a library relation takes this shape.
