---
title: Spell structured regions for write-elf's Rust allocator
status: closed
labels: [native,x86]
area: heather-in-heather
milestone: [nh-front]
created: 2026-10-29
updated: 2026-10-31
---

`write-elf` allocates in Rust (`crates/cli/src/native/allocator.rs`) over a
source read back as numbers (`Source::spelled`, native_source_spelled). The
spelling has only dataflow leaves: `StructuredRegion::spelled_region` is
`None` for every other region, so a source with a structured region
([[native-compile-wider-leaves]], 2026-10-29) spells `[0]` and `write-elf`
falls back to the Heather allocator evaluated on its fork, whose memory grows
with the tool ([[native-allocator-cost]]). Small tools such as `tr_upper`
are fine; a large tool with regions would hit the rail.

## Scope

- Spell every region form, and mirror `Homes::region_checked`'s live sets
  (and a region loop's set at its count) in the Rust allocator's `needs`,
  kept step for step with native_alloc as the rest of it is, with the
  allocator tests holding the two to agreeing.

## Also

- `refused(tr_upper()) = []` by `refl` runs out of kernel fuel
  (`lib/_tests/native/native_structured_tests.hthr`) while the smaller
  `tr_map` and the certificate `write-elf` checks for `tr_upper` both pass:
  evaluating the slot allocator's loop-set closure over a region loop with
  more live words is the likely cost. Look at it with the spelling work.

## Log

- 2026-10-31: 2026-10-31: hih-tools closed (docs/native/compiler-milestones-proposal.md §8). Moved to nh-front: [[runtime-fn-setups-design]] folds this in or closes it.
- 2026-10-31: Done on branch claude/project-thread-xhabhy: every region form spells (Stmt tag 7, `StructuredRegion::spelled_tagged`), write-elf's reader prints them, and the Rust allocator mirrors `region_needs`, `region_graph` and `weighed`; tr's region loop gets the same homes from both (`HEATHER_ELF_ALLOCATOR=both`, the tr CLI test). The `refused(tr_upper()) = []` fuel note moved to [[native-slot-allocator-refl-fuel]].
