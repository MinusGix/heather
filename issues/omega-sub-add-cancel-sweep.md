---
title: Drop hand-fed sub_add_cancel facts next to omega now that it splits a - b
status: open
labels: [omega,tactics,cleanup]
area: tactics
created: 2026-10-30
updated: 2026-10-30
---

omega splits a truncated Nat subtraction into its two cases since [[omega-nat-truncated-subtraction]] (docs/omega-measure-reduction-design.md §16), so a `Nat::sub_add_cancel` let beside an `omega` call (or passed as `omega(s)`) is now redundant wherever the case's `b <= a` is itself among the facts omega reads. About sixty `sub_add_cancel` uses remain in lib/ outside nat.hthr (float round/error/float, bitvec, linux io, x86 asm table, itree trace); `Format::gamma_at` (error.hthr) was dropped in the landing round as the first one.

Sweep them module by module: drop the fact, check the module with `--cache`, keep the drop when it closes. A fact whose `b <= a` is not in omega's context stays (or becomes `omega(le)`), and one whose goal sits under several subtractions may cost more branches than the hand fact saves: compare with `scripts/perf ab --source-patch` if a module gets slower.
