---
title: A refused lifted decreases obligation reports the un-lifted retry's error, not its own
status: open
labels: [frontend,diagnostics,elaboration,proofs]
area: language
created: 2026-09-06
updated: 2026-09-06
---

Found by the [[omega-measure-at-constructor-pattern]] design pass
(2026-09-06, docs/omega-measure-reduction-design.md §1.1). `elab_measure_decl`
(`crates/elab/src/lib.rs`) lowers a `decreases` declaration with `lift = true`
first, one theorem `f#obl_N` per call site; when the checker refuses one it
re-lowers with `lift = false`, obligations back at the calls, and the writer
sees the *second* attempt's message. On the `drop1` reproducer that turned
"Omega's real shadow found no contradiction; atoms [list_len(Cons(h, xs)),
list_len(xs)]" (accurate, actionable) into "Omega could not spell a natural
expression" (about a binder the writer never wrote,
[[tier1-arm-binder-has-no-spelling]]). The first attempt's reason is already
recorded (`unfold_refusals` keeps "the lifted `f#obl_1` was refused (…)");
when both attempts fail the diagnostic should prefer it, or show both.

## What it assumes from elsewhere
- **[[termination-measures]]** owns the two-attempt lowering. Assumed here:
  only that the lifted attempt runs first and its refusal is kept.

## When
Triggered: the next `decreases` refusal a writer reports as pointing at nothing
they wrote, or the next round in `elab_measure_decl`.

## Log

- 2026-11-05: gardener: cites a file it shares with [[omega-guard-reads-nat-match]] (`docs/omega-measure-reduction-design.md`).
