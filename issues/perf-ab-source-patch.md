---
title: scripts/perf ab compares two binaries, so it cannot A/B a library or showcase source change
status: open
labels: [tooling,performance]
created: 2026-09-19
updated: 2026-09-19
---

`scripts/perf ab` (2026-09-19, `perf/README.md`) builds two compiler binaries and
interleaves cold checks of a fixed corpus. That is the right shape for a kernel or
elaborator round and the wrong one for a *source* round: a change to `lib/` or to
a showcase is the same binary over two source trees, and `ab` would build one
binary twice, find the hashes equal, and refuse the run — correctly, by its own
rules.

The gap has a consumer already: [[showcases-predate-their-ergonomics]] and
[[record-type-partial-application]]'s showcase half both change `.hthr` text in a
file whose cold check is the thing at risk (it needs more than 8 GiB and cannot be
cached), so both want exactly this measurement and neither can have it.

Wanted: a `--source-patch FILE` mode that holds the binary fixed and reverses the
diff over the *sources* between samples, keeping everything the binary mode
already gets right — interleaving, the per-sample spread and the `separate` /
`SPREAD EXCEEDS THE DELTA` verdict, counters reported apart from seconds, the
load warning. Two things change: the provenance check becomes "the two source
trees differ and the binary is the same", the mirror image of today's assertion;
and the counters are no longer expected to be identical — for a source change they
are the *result*, since term growth is what the round is about, so the report
should stop calling a moved counter a behaviour change and instead rank the
columns that moved.

`ReversePatch` in `scripts/perf` already does the risky half (apply, restore,
re-hash every file the patch touched and refuse a half-applied restore), so this
is mostly wiring plus the inverted assertion. `scripts/perf ab-selftest` is where
the verdict logic is pinned.
