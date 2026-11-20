---
title: linux_determinism dies at the 300 CPU-s rail when it builds the read-loop images itself
status: open
labels: [testing,performance]
area: infrastructure
created: 2026-11-20
updated: 2026-11-20
---

In a plain `scripts/test` after a compiler edit, `crates/elab/tests/linux_determinism.rs`
is SIGKILLed at the 300 CPU-s rail whenever it is among the first targets to
start: it then checks the read-loop fixture's library modules from source
(`support/read_loop.rs`, `checker()`) before its own work. Started late, after
another target stored those images, it passes (163 CPU-s in one 2026-11-19 run).

Measured 2026-11-20 on a 4-CPU cloud box, the target alone at width one, cold
then warm:

| compiler | cold | warm |
|---|---|---|
| aab9058b3 (before #817) | killed at the rail | 219 user-s |
| 821beb336 (master) | killed at the rail | about 225 user-s |
| §3.8 branch (written paths) | not measured | 219 user-s |

So nothing recent regressed it: warm it already uses about three quarters of
the rail, and cold it is past it. Where the warm time goes: `determinism_refusals`
re-elaborates the whole of `x86_64_step_forms` for each of nine mutants (a
fresh-name `heather check` of that module over warm imports is about 30 s), and
then `linux_x86_64_determinism` for three more.

Same shape as [[linux-wp-cold-rail]], fixed there by cheaper proofs. Levers, unexamined: elaborate each mutant only up to the declaration the
mutation lands in plus the one that must refuse (`--only`'s replayed prefix,
`docs/infrastructure/check-only-design.md`); put the mutants in `lib/_tests` as
`// expect-error:` declarations over small fixtures, where the gate's images
make them cheap; or have the suite's warmup build the read-loop images before
the targets that need them start.

## Log

- 2026-11-20: Filed from the written-paths round (thread "Smooth the first hour
  of writing a runtime fn"), whose plain suite was otherwise green.
