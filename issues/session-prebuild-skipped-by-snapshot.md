---
title: Run the session prebuild in containers started from the environment's snapshot
status: closed
labels: [testing,tooling,cloud]
area: infrastructure
created: 2026-10-29
updated: 2026-10-29
---

`scripts/session-start` (#130, guard added in #209) skipped its background
`cargo test --workspace --no-run` whenever `target/session-prebuild.log`
existed, meaning "a prebuild already ran in this container". But the cloud
environment starts containers from a snapshot of an earlier container, and
that snapshot holds the checkout's `target/` as it was when taken: on
2026-10-29 a fresh container's `target/` was dated 2026-10-26 20:55, with a
log reading only `session prebuild started 2026-10-26T20:55:28Z` (no exit
line) and only `heather_syntax`, `heather_numeral` and a few small
dependencies built. Every container since then skipped the prebuild, so the
first `scripts/test` in a thread paid the whole cold compile in the
foreground (seen in PR #258's thread: "only the syntax crate had been built").

## Fix (2026-10-29)

The guard is now a `flock` on `target/session-prebuild.lock` that the
detached build holds. A lock does not survive into a snapshot, so a new
container always prebuilds; a resumed session while the build runs still
skips; a resumed session after it finished reruns it as a no-op build.
Checked by hand with a stand-in for the build: start, skip while running,
start again after it ended.
