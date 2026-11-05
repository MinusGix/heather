---
title: Settle the slope bands the first cloud baselines leave
status: open
labels: [performance,benchmarking]
area: infrastructure
created: 2026-10-29
updated: 2026-10-29
---

On 2026-10-29 the kernel and frontend baselines were re-recorded on the
cloud box ([[cloud-benchmarks]]). Both had been recorded on the desktop:
kernel at 5cec674, frontend at f354d48, and the frontend file was missing
most of the families added since. Six declared bands are now left by the
measured slope. `--check` fails on a band left on either side
(`docs/frontend-benchmarking.md`), so a cloud `--check` is red until each one
is settled:

| family | band | cloud slope | side |
|---|---|---|---|
| kernel `wf/check-tree` | 0.85–1.35 | 0.64 (0.67 on a rerun) | below: the per-node cost falls with size, from about 150 to 72 ns/node; the desktop measured 0.99 |
| frontend `forded/computed-arms` | 1.85–2.55 | 0.30 | below |
| frontend `forded/declared-index-branching` | 0.90–1.65 | 0.43 | below |
| frontend `forded/occurrences` | 0.70–1.30 | 0.62 | below |
| frontend `scale/certified-dispatch` | 0.95–1.65 | 0.90 | below |
| frontend `rewrite/fa` | 1.10–1.80 | 1.83 | above, by a few hundredths |

Two kernel families with no band also moved far from the desktop's fit:
`conv/perturbed-pairs` went from 0.99 to 1.66 and `check/generated-terms`
from 1.04 to 1.56. Both have a case-count axis, so the slope is not a claim,
but a change that large is worth one look.

Below a band means the code became cheaper than the recorded claim, or that
on this box a fixed cost hides the size term at small sizes. Each wants a
reading: rerun it alone, look at the per-unit column, then either re-record
the band, with the reason in the family's doc comment, or file the
regression. `rewrite/fa` sits within run-to-run noise of its edge.

## Done when

A cloud `scripts/bench --check` and `scripts/bench-frontend --check` pass on
their bands, or each family left outside has a written reason.

## Log

- 2026-11-05: gardener: cites a file it shares with [[parallel-checking-and-caching]] (`docs/frontend-benchmarking.md`); [[prelude-clone-cost-grew]] (`docs/frontend-benchmarking.md`).
