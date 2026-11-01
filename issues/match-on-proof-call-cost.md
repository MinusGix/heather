---
title: Matching on a proof call's result costs as if the proof were evaluated
status: open
labels: [elaborator, kernel, performance]
area: language
created: 2026-11-01
updated: 2026-11-01
---

A `match` whose scrutinee is a call to a theorem (`match F.f2s_pos(..) as
.. { Exists(f, fh) => .. }`), or the projection of a let bound to one (`let w
= two_sum_pos(..); match w.left ..`), is far more expensive than the same
match on a variable. Moving the match into a helper theorem that takes the
proof as a parameter, or replacing it with `j` over an equation (and a
generic `Finite::neg_exists` for the negated case), keeps the proof
unchanged and drops the cost. Measured in `lib/std/num/float/eft.hthr`
(counters from `--timings`, width one, 2026-11-01):

| declaration | steps before | steps after | change |
|---|---|---|---|
| `Format::two_sum_neg` | 8.1M | 0.29M | final match moved to `Finite::two_sum_unflip` |
| `Finite::mul_err_H` | 2.07M | 0.28M | match on `prod_cells(..)` to a parameter, inner matches to `j` |
| `Finite::fast_two_sum_H` | 3.6M | 0.75M | match on `f2s_pos(..)` to `j` + `neg_exists` |
| `Finite::two_sum` | 6.6M | 0.36M + 0.33M | tail moved to `Finite::two_sum_tail` |

Both the elaborator's time and the kernel gate's fall, so both sides
reduce the scrutinee. The likely mechanism is whnf of the scrutinee looking
for a constructor to take the iota step: on a theorem application that
unfolds the proof, which reaches a constructor only after running the
proof's own case splits. Not confirmed in the code yet. A scrutinee whose
head is a theorem rarely needs unfolding at all.

Case splits on small decision lemmas (`double_or_over`, `half_float`,
`sterbenz_H` in `two_sum_pos`) still match on calls and cost less, but
`two_sum_pos` is still the module's most expensive declaration.

## What would close it

The elaborator and the kernel stop unfolding a theorem-headed scrutinee
when it cannot reduce to a constructor without δ on a theorem, and the
workaround rule in `docs/proof-patterns.md` §4 is retired. The four
declarations above, rewritten back to the direct match, are the probe:
their step counts should match the restructured ones.
