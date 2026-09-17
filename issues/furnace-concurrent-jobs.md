---
title: Let the furnace run concurrent jobs, isolated per worktree
status: open
labels: [tooling,infrastructure,testing,performance]
created: 2026-09-16
updated: 2026-09-16
---

`furnace` (the remote build box; not this repo's code, but this repo is where
its requirements are discovered) syncs the project into **one** remote checkout,
so a second `furnace run` while a first is in flight re-syncs over the running
job's tree and deletes its `out/` files. The working rule today is to serialize
every job by hand.

That rule was affordable when furnace was for long builds. It is expensive now
that the loop is many short probes, and it is wrong in a second way: **two
worktrees of this repo cannot use the furnace independently.** Two sessions on
two branches is the normal state (`.claude/worktrees/*`), and either they
collide or one waits.

Wanted: concurrent jobs, isolated by source tree. The shape that seems to fit
the existing design: one remote checkout *per local worktree identity*, sharing
the cargo target cache the way separate worktrees already share `/work`
([[furnace-run-round-trip-latency]] is where the per-job cost of that sharing
belongs). A job's outputs land under its own checkout and are fetched from
there.

Things that have to be decided rather than assumed:

- **Target-directory sharing across concurrent jobs.** Two `cargo build`s
  against one `CARGO_TARGET_DIR` block on the same lock; separate dirs
  duplicate the cache on the volume. The volume is 150 GB and the repo's target
  is not small, so this is a real tradeoff, not a detail.
- **What happens when the same worktree launches twice.** Probably the second
  waits — but it should say so, not silently clobber.
- **Eviction.** Per-worktree checkouts accumulate and stale ones need to go.
  This is not hypothetical: stale worktree target directories filled the local
  machine's filesystem on 2026-09-05, and the remote cache volume is finite in
  the same way.

This issue is filed here because this repo is where the pain shows up; the fix
is a change to furnace itself.

## Log

- 2026-09-16: Filed after a session of strictly serialized 30-second probes.
