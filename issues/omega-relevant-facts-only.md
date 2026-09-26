---
title: omega reflects every fact in scope; reflect only those connected to the goal
status: open
labels: [omega,performance,proofs]
created: 2026-09-25
updated: 2026-09-25
---

`omega` reflects every fact in scope, whether or not it bears on the goal.
Its cost therefore grows with the context, not with the goal. The same goals
cost several times more inline than in a lemma of their own.

Measured 2026-09-25 on `lib/decimal_line.hthr` at 8dc93751, release build,
eight workers. Rewriting `times256_value` and `raise_value` with inline
`omega` for their doubling bounds and `v + v = v * 2` restatements took them
from 31 ms and 15 ms to 6.0 s and 1.8 s. That's about 375 ms and 185 ms per
call. The same kind of bound costs about 45 ms each in `doubling_bounds`,
whose context holds only its own hypothesis. No `div`/`mod` is involved. The
extra facts are word equations (`y_i.toNat() = v * 2^i`), each adding an
atom and an equality.

So "prove it in a lemma of its own" is the cheap way to use `omega` today,
and library proofs are shaped around that. A tactic that sends each side
condition to `omega` in place ([[bitvec-nat-lifting-tactic]]) would pay the
whole context at every call.

## Scope

Reflect only the facts connected to the goal. Start from the goal's atoms,
and close over facts that share an atom with what is already kept. Keep every
atom-free fact, since `1 < 0` in scope refutes anything.
- A fact outside the kept component can't help a *linear* refutation that
  uses the goal, but a contradiction among the dropped facts alone can.
  Either keep a fallback, a second attempt over the full context when the
  filtered one is stuck, or record why the fallback isn't needed.
- The same filter removes the failure in
  [[omega-respells-atoms-without-implicits]] whenever the badly spelled atom's
  fact is unrelated to the goal. That issue still owns the spelling itself.

## Acceptance

- `times256_value` with inline `omega` (the rewrite above) costs within a
  small factor of the lemma form. Pin its counts in
  [[omega-performance-telemetry]]'s rails.
- The respelling repro in [[omega-respells-atoms-without-implicits]] checks,
  since its goal doesn't use the badly spelled atom. A goal that does use it
  stays that issue's.
- Negative controls: a goal provable only through a chain of facts that share
  atoms still closes, and a satisfiable goal with an unrelated contradictory
  fact behaves as the fallback decision says.

## What it assumes from elsewhere

- **[[omega-div-mod-goal-cost]]** asked this as a question for `div`/`mod`
  atoms. This issue owns the filter, and that one keeps its attribution.
- **[[omega-local-proof-aliases]]** owns which local facts are visible at
  all. Assumed here: only that the filter runs after that collection.
