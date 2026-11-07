---
title: big_operator_tests fails in the --pr lane over replayed images
status: open
labels: [testing, cache, rewrite]
area: infrastructure
milestone: [none]
created: 2026-11-07
updated: 2026-11-07
---

On master 89ea8bb, `scripts/test --pr -p heather-cli --test library` fails
`every_library_module_checks`: building `big_operator_tests` refuses two
`rewrite(Semiring::mul_range_l, …)` calls
(lib/_tests/std/algebra/big_operator_tests.hthr:262 and :273) with "the goal
… does not mention the relation's left side", although the goal prints the
left side verbatim (`c * range(#op+@0_1, n, …)`). The run replays
`big_operator` and its prefix from images of another build (563ea0802c7f,
the sentinel seed) while this binary is 98f4b75a49b3. A direct `heather
check --cache --expectations` of the same file with this binary's own
images passes. So a replayed image and a fresh elaboration disagree about
something `rewrite` compares, plausibly the per-prefix `#open` upcast
globals #462 introduced (`#op+@0_1` in the goal); the exact image policy
(the nightly sentinel) would show whether only the replay lane is affected.

Found by the located-suprema round ([[order-completeness-located-sup]]),
whose diff does not reach this module; it reproduces with that diff
removed.

## Log

- 2026-11-07: Filed.
