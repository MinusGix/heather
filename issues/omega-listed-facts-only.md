---
title: omega reading only its listed facts
status: open
labels: [omega,performance,tactics]
created: 2026-10-19
updated: 2026-10-19
---

`omega(h…)` ([[omega-fact-arguments]]) adds the listed proofs to the facts
`omega` already reads from the context. It does not narrow that context, so
its cost still grows with every fact in scope. The 2026-10-16 data point from
the regular Cauchy reals stands: one `omega` over `j <= n` cost about three
times more with three unrelated `Rat` inequalities in scope, because each is
unfolded and inspected before relevance filtering drops it
(docs/regular-cauchy-reals-round.md, "Cost").

A mode that reads only the listed facts would bound the cost by what the
proof names, and would make every load-bearing fact visible at the call. The
question is its spelling and its relation to binders:

- Does a narrowed call still read the declaration's parameters (`h: x <= y`),
  or must those be listed too? Listing them is the most explicit; reading
  them keeps short proofs short.
- Is narrowing a separate spelling (`omega only(h…)`), or does any argument
  list narrow and a bare `omega` keep reading everything?

## Acceptance

- A decision on the two questions above, recorded here.
- `CReal::lt_respects` (or a probe shaped like it) closes with a narrowed
  call at about the cost of the call without the unrelated `Rat` facts in
  scope.
