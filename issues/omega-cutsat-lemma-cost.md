---
title: omega's CutSat lemmas lead the corpus after app@: complexity or overhead?
status: open
labels: [omega,performance,kernel,elaboration]
area: tactics
created: 2026-09-22
updated: 2026-09-22
---

After the app@ round the heaviest items in the perf corpus are `lib/std/omega.hthr`'s
CutSat lemmas (snapshot `perf/snapshots/2026-09-23T003909Z-local.json`, cold,
width one, release). They fall into two groups with different costs:

**Kernel-checking-heavy** (gate ~50–57 % of the item):

| item | total | gate | misses | steps | rescoped nodes |
|---|---|---|---|---|---|
| `cutsat_right_cut` | 758 ms | 57 % | 5,068 | 84,396 | 726,345 |
| `cutsat_left_cut` | 617 ms | 49 % | 6,038 | 95,608 | 860,939 |
| `cutsat_left_remainder_bound` | 220 ms | 55 % | 2,334 | 38,301 | 381,831 |
| `cutsat_cancel_middle` | 212 ms | 51 % | 2,431 | 39,415 | 348,574 |
| `cutsat_right_remainder_bound` | 173 ms | 51 % | 2,220 | 36,097 | 281,834 |

**Elaboration-heavy** (almost no gate; `decl_body` or `decl_type` 55–83 %):
`cutsat_right_dvd` 491 ms (body 78 %), `cutsat_right_witness_product`
232 ms (body 83 %), `cutsat_cooper_right_remainder_le_gap` 206 ms (type
55 %), `cutsat_cooper_right_cut` 186 ms, `cutsat_cooper_right_dvd` 163 ms.

**The question this issue exists to answer**: is this *complexity* — the
lemmas genuinely state and prove a lot — or *overhead* the checker and
elaborator pay per node? The two groups likely answer differently:

- The gate group rescopes 280–860 k nodes through `shift_global` per item
  (column `rescope`), which is a representation cost, not a proof-size one.
  Compare it against the certificate's own size before deciding.
- The elaboration group spends its time outside the kernel on statements
  that are not large; attribute `decl_body`/`decl_type` by phase
  (`elab_whnf`, `unify`, `resolve`, `omega_*`) before guessing.

Method: `--cache --only omega::<item> --timings` over a replayed prefix
(`docs/check-only-design.md`), one item of each group, then the phase
columns and `HEATHER_OMEGA_PHASES=1`. Earlier, closed round on the same
lemmas: [[omega-per-goal-elaboration-cost]] (2026-09-05; whnf probes on
computing propositions).

Priority note (user, 2026-09-22): the biggest single target, but the
`calc_parser` item ([[measure-obligation-omega-on-a-written-proof]]) comes
first because it is ordinary code.
