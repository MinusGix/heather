---
title: big_operator_tests fails in the --pr lane over replayed images
status: closed
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
- 2026-11-07: Root cause and fix. Not the image cache key: the replay only
  exposed a matching gap in `rewrite` that a fresh elaboration hits too.
  `Semiring::mul_range_l`'s left side `c * ∑ k < n, f(k)` is headed by the
  caller's operator *variable* `*`, and §6.2 of
  docs/tactics/equation-rewrite-design.md matched a local-variable head by `==`
  only (keyed conversion was for global heads). The sum's monoid inside it is
  an upcast of the `Semiring` dictionary, which #462 mints once per context
  prefix as an `#open` global. Fresh, the test's theorems share
  `big_operator`'s section prefix, reuse its minted global, and the spellings
  are `==`. Replayed from images the 919a001 sentinel build wrote, there is
  no minted global upstream (that compiler inlined the record), the test
  mints its own, and `==` fails. Reproduced on a fresh build with a prefix
  the section does not share (`<B: Type, A: Semiring(≈, +, *)>`), now
  `class_law_open_other_prefix` in big_operator_tests. Fix: a local-variable
  head is keyed like a global one (`keyable_head` in
  crates/elab/src/rewrite.rs; relation form and equation form): same head,
  arguments by conversion, under the same 256-candidate cap. Checked over the
  seeded sentinel stores with `--accept-stale-images`: the base binary gives
  the two errors at :262 and :273, the fixed one passes.
