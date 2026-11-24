---
title: omega reading only its listed facts
status: open
labels: [omega,performance,tactics]
area: tactics
created: 2026-10-19
updated: 2026-11-24
---

`omega(h…)` ([[omega-fact-arguments]]) adds the listed proofs to the facts
`omega` already reads from the context. It does not narrow that context, so
its cost still grows with every fact in scope. The 2026-10-16 data point from
the regular Cauchy reals stands: one `omega` over `j <= n` cost about three
times more with three unrelated `Rat` inequalities in scope, because each is
unfolded and inspected before relevance filtering drops it
(docs/library/creal.md, "Cost").

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

## Log

- 2026-11-05: gardener: cites a file it shares with [[theorem-witness-unfolding]] (`docs/library/creal.md`).
- 2026-11-24: Not decided here (it is Minus's). Related finding from the proof-tooling round on `word_map_laws` (docs/tactics/omega-measure-reduction-design.md §27): a written `omega`'s proof is now lifted into a lemma of its own at the gate, which removed the cost of the certificate being substituted with the body; what an inline call still pays over a lemma is the width of its leaves (every atom of every reflected fact) and the truncated-subtraction split taking facts newest first, which in a context full of distances spent its six splits on unrelated facts and got stuck. A narrowed call would remove both for the facts it does not name; a split ordered by connection to the goal would remove the second without a new spelling.
