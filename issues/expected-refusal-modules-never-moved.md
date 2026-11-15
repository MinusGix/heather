---
title: Modules with expected refusals are never moved by the early cutoff
status: closed
labels: [tooling,caching,performance]
area: infrastructure
created: 2026-11-14
updated: 2026-11-14
---

A module with `// expect-error` directives is never moved by the early cutoff
(`docs/infrastructure/module-interface-cutoff-design.md`): under `--expectations`
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
  declaration-slice replay (`docs/infrastructure/declaration-slice-replay-design.md`)
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

## Built: the first route

`SemanticSession::check_refusing` now looks, on the stale lanes, for an image
of the same source that moves onto this world, replays its accepted
declarations as slices and elaborates each refused declaration again
(`Elaborator::check_module_delta_refusing_from`). What makes that possible:

- A refused item leaves a slice of nothing in the journal
  (`DeltasMut::slice_failed`), so a module with refusals has one slice per
  item of its source and a later slice sits where the file has it.
- No slice of nothing is reproduced (`try_replay_slice`) unless the item is
  one whose elaboration does nothing (an import, a later member of a mutual
  group); the item is elaborated. That is also what stops a plain session from replaying a
  refusal out of a judging session's image, which the missing slice used to
  do by accident.
- An item refused where the previous delta has nothing leaves the prefix
  exact, so the declarations after it still replay.
- `publish_refused` carries a world record, and the image of a module that
  holds moved declarations is published as relocated: the exact lane
  elaborates it whole.

One thing the measurement found. What a refusal says can draw on a note an
earlier declaration left in the pass (`unfold_refusals`: why a function has
no unfolding or branch equation). A reproduced declaration leaves no note,
the refusal reads as a plain unbound name, and the directive is missed. Four
library modules have such a directive. A module that misses its directives
over moved declarations is put back (`Elaborator::return_to`) and elaborated
whole before it is judged. The converse stays open: a directive loose enough
to match the plainer reading is counted on the stale lanes where a whole
elaboration would say something else; the exact lane judges that.

Same measurement as above, both changes: 142 s wall and 499 CPU-s (user and
system), against 190 s and 689 with the digest fix alone. The 152 modules
with directives went from 339 s to 172 s, which is the per-module floor every
moved module pays ([[build-children-replay-their-imports]]).

Tests in `crates/cli/tests/semantic.rs`:
`a_module_with_directives_moves_what_it_accepted_and_judges_its_refusals_again`,
`a_module_with_directives_is_elaborated_again_when_it_observed_the_edit`,
`a_refusal_that_reads_differently_over_moved_declarations_is_judged_on_a_whole_elaboration`.
