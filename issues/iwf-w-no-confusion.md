---
title: absurd and payload inj on the IWf-on-W route
status: open
labels: [elaborator,indexed-families]
area: language
milestone: [math-metatheory]
created: 2026-10-25
updated: 2026-10-25
---

The `IWf` route's no-confusion (`absurd` between constructors, `inj` of a
payload field) reads the kernel `IWf`'s `Supi`. A family on the `IWf`-on-`W`
route (`docs/iwf-infinitary-design.md`, an indexed family with a recursive
function field) is `Σ(t : W₀). El(ok t m)`, so each needs a `W` twin: the
tag lives in `fst` of the shape under `fst` of the value. `inj` at a
*recursive* field stays out for tier 2 §9's reason.

The heather-coq port's inversion lemmas (the port assessment's
"inversion" blocker) are the customer: inverting a logical-relation
derivation at a constructor-headed type needs `absurd` for the arms that
cannot apply when they are not omitted by index inversion.

## Log

- 2026-10-25: Filed from the IWf-on-W round, §10 of the design
  ([[indexed-infinitary-families]]).
