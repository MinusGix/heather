---
title: absurd and payload inj on the IWf-on-W route
status: closed
labels: [elaborator,indexed-families]
area: language
milestone: [math-metatheory]
created: 2026-10-25
updated: 2026-10-25
---

The `IWf` route's no-confusion (`absurd` between constructors, `inj` of a
payload field) reads the kernel `IWf`'s `Supi`. A family on the `IWf`-on-`W`
route (`docs/kernel/iwf-infinitary-design.md`, an indexed family with a recursive
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
- 2026-10-25: Done on both forms of the `IWf` route (the kernel `IWf` form had no
  `absurd`/`inj` either, contrary to the design's §10), in
  `crates/elab/src/iwf_confusion.rs`: `absurd` between constructors, `inj`
  at a payload field (dependent fields included); `inj` at a recursive field
  refused with tier 2 §9's reason. Design §13, tests
  `crates/elab/tests/iwf_no_confusion.rs`.
