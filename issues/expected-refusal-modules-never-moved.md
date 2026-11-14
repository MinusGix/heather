---
title: Modules with expected refusals are never moved by the early cutoff
status: open
labels: [tooling,caching,performance]
area: infrastructure
created: 2026-11-14
updated: 2026-11-14
---

A module with `// expect-error` directives is never moved by the early cutoff
(`docs/module-interface-cutoff-design.md`): under `--expectations`
`SemanticSession::check_in` sends a miss on such a module to `check_refusing`
before it looks for an image of the same source over another world, and
`publish_refused` stores no world record. So any edit below such a module
elaborates it again, however little of the edit it observed.

This follows a stated rule rather than an oversight: a refusal another build
recorded is not this build's verdict, and no kernel recheck can make it one
(`a_stale_image_of_refusals_is_elaborated_again`). A moved image is kept
honest by the kernel rechecking what it holds; a refused declaration leaves
nothing to recheck.

The cost, measured 2026-11-14 (4-core cloud box, release binary, self-checks
off, after [[registry-digest-taken-in-observer-coordinates]]): one
theorem appended to `nat`, gate build step. 152 of 554 modules carry
directives; they cost 339 CPU-s of the step's 750, against 375 s cold. The
other 402 modules cost 411 s, about a second each. Nearly every `_tests`
module has a directive or two among hundreds of accepted declarations.

Routes, none chosen:

- **Move the accepted declarations, elaborate the refused ones.** The image of
  a refusing module already holds its accepted declarations, and
  declaration-slice replay (`docs/declaration-slice-replay-design.md`)
  already reproduces unchanged declarations and elaborates the rest. A moved
  image whose refused declarations are each elaborated again over the moved
  world keeps the rule: every refusal is this build's verdict. It needs the
  world record on `publish_refused`, and lookups from the refused
  declarations in it.
- **Split the directives out**: keep refusals in small modules of their own,
  so the large test modules move. A library convention, no compiler change,
  and it leaves the cost where a module mixes them.
- **Trust the observation argument for refusals too**: a refusal is a
  function of the same observed world as an acceptance. This gives up the
  rule above on the stale lanes.
