---
title: Tests name the library modules they import, not hand-ordered closures
status: open
labels: [testing,tooling]
area: infrastructure
created: 2026-10-25
updated: 2026-10-25
---

`docs/test-value-audit.md` §4.2: the elab tests hand-maintain library
closures, 891 `include_str!` lines in dependency order across about 105
files, some ordered for the image cache's sake. The lib-layout move (#145)
had to hand-edit the ones `scripts/lib-paths --fix` could not reach, and
every `include_str!` relinks its test binary on any edit to the file.

## Proposal

`support::library_for(&["rat"])` resolves imports through
`heather_cli::loader` (the CLI's own closure, which the export sweep already
uses) in place of the hand-ordered `MODULES` lists. The prefix key becomes
the root set and the image layer orders it. Loading at runtime means a
library edit stops relinking every binary that `include_str!`s the file
(`docs/testing-architecture-design.md` §2.2). The sentinel's exact lane
should see one run of it, since it touches image keys.

Split out of [[hthr-test-corpus]] when the corpus runner landed
(2026-10-25); this half is independent of it.
