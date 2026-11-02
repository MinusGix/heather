---
title: --pr library gate goes cold after a prelude change
status: open
labels: [testing,caches]
area: infrastructure
created: 2026-11-02
updated: 2026-11-02
---

A diff that changes the elaborator's prelude (`crates/elab/src/prelude.hthr`)
fails `scripts/test --pr` in the whole-library gate
(`crates/cli/tests/library.rs`): the `lib/std/analysis` and
`lib/_tests/std/analysis` folder children are killed at the CPU rail
(`signal: 9`). The same test passes in the exact lane
(`scripts/test -p heather-cli --test library`).

Seen on the binding-statements round (2026-11-01), whose prelude gained
`Bind`, `Pointed`, `Bind::seq` and `Pointed::ret`. Under `--pr` the gate's
build step (`--build-only`, `--accept-stale-images`) reported
`build: 2 modules built ahead`, so its plan treated the rest of the
library's images as usable; the analysis children then replayed
none of them ("0 semantic modules replayed") and checked their whole
closure cold, which is several times the per-process rail. A cold check of
`lib/std/analysis` alone costs the same on master and on the branch, so the
cost is the lane's, not the change's.

The build step's plan and the child's loader disagree about whether an image
written under another prelude is usable. Either the plan should build what
the loader will refuse, or the loader should relocate such images as it
does for other stale ones.

## Done when

A prelude-only change passes `scripts/test --pr`, with the library gate's
children replaying (or the build step building) every module.
