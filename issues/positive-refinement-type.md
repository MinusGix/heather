---
title: A refinement type for positions binder sugar cannot reach
status: open
labels: [stdlib,subtypes,design]
area: language
created: 2026-10-10
updated: 2026-10-10
---

[[pos-binder-sugar]] reaches only binders. A function domain
(`Pos<Nat> → Rat`, the shape of regular sequences and of CoRN's `Qpos`
approximations) or a container element (`List<Pos<Nat>>`) needs a real
refinement type: a record with a squashed or relevant field, and
expected-type packing at known positions. That is the bundled-type option
from `docs/library/positivity-evidence-design.md` §4 in full.

Deferred until [[regular-cauchy-reals]] asks for it.
[[subtype-transfer-and-evidence]] owns the evidence-policy comparison that
should choose between squashed and relevant fields.

## Log

- 2026-10-10: Filed from [[positivity-evidence]].
- 2026-11-05: gardener: cites a file it shares with [[pos-sugar-library-adoption]] (`docs/library/positivity-evidence-design.md`).
