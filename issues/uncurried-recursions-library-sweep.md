---
title: Sweep the library's hand-curried recursions and written motives onto IH generalization
status: open
labels: [stdlib,cleanup,elaboration,proofs]
area: language
created: 2026-09-05
updated: 2026-09-05
---

Follow-on to [[ih-generalization]] (landed 2026-09-05,
docs/tactics/ih-generalization-design.md). The landing round uncurried the six
definitions the issue named — `Le`, `leb`, `sub` (lib/std/num/nat.hthr),
`foldl`, `take`, `drop`, plus `List::nth` (lib/std/data/list.hthr) — and rewrote
`le_succ_r`, `le_trans`, `le_antisym`, `le_total`, `le_dec`, `le_add` in the
generalized style. What is left is mechanical and has no design content:

- `lib/std/num/nat.hthr`: the remaining `Succ(k, ih) => λ m => match m { … ih(…) }`
  lemmas (about a dozen, `grep -n 'Succ(.*, ih)'`), whose explicit ih binder
  and `(m: Nat) →` statement exist only because the parameter could not vary.
  Each becomes `theorem t(n, m: Nat): …` with `Succ(k) => match m { … t(k, …) }`.
- `lib/certgen/ir_v1.hthr`: the four explicit motives the 2026-07-31 log of
  [[ih-generalization]] lists (`step_mono`, `eval_mono_succ`, `le_add`'s
  copy, `add_loop_runs`); `fuel_monotone` is the keystone customer.
- `lib/certgen/certgen_code.hthr`: `sub(x)(y)` partial applications read as
  `sub(x, y)` now (both check; the partial form is a leftover spelling).

Not in scope: laws whose statement genuinely quantifies the varying argument
(`foldl_append`'s `(z: B) →`) — [[std-list-l2-prime-laws]] found those are
the statement, not a workaround, and they stay. Hypotheses that must reduce
under an inner `match` stay behind an arrow too (design doc §5).

## What it assumes from elsewhere
- **[[ih-generalization]]** owns the mechanism. Assumed here: only that a
  varying non-decreasing parameter is generalized when the `match` is in
  checking position.
