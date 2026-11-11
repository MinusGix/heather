---
title: --timings adds a quarter to the cold check it measures
status: open
labels: [performance,tooling,instrumentation]
area: infrastructure
created: 2026-11-11
updated: 2026-11-11
---

`heather check --timings` costs about a quarter of the cold check it measures, and most of that lands in the table's `other` column, where it reads as unexplained compiler time. Found while writing [[performance-overview-2026-11-11]].

## Measured

`docs/showcase/calc_parser.hthr`, cold into an empty store, width one, release binary at #553 plus the name-record fix, four interleaved samples on a quiet cloud box:

| | wall | user | sys |
|---|---|---|---|
| plain | 11.08 s | 10.84 s | 0.16 s |
| `--timings` | 13.74 s | 11.83 s | 0.80 s |

So 2.7 s more: 1.0 s of user time, 0.65 s of system time and about a second of waiting on the file system. The master binary at #552 shows the same gap (16.02 s plain, 18.40 s with the flag). The run has 2,626 declaration scopes, so this is about a millisecond a declaration.

Every `scripts/perf ab`, `scripts/perf snapshot` and `scripts/bench-probes` time carries it, on both sides of a comparison. Ratios are diluted (the showcase's −25% for #553 is −31% plain), and the `other` column of a run row (18% on the showcase) is mostly this.

## Where it comes from

`crates/elab/src/stats.rs`, per declaration scope:

- `scope` reads `/proc/self/status` for `VmHWM` (`peak_rss_kb`), and the guard's drop reads it again;
- `live_opened` and `live_closed` each rewrite the `<stem>.open.tsv` sidecar through `write_open`: a staged file is created and written, then renamed over the sidecar, or the sidecar is removed when nothing is open;
- `live_closed` appends the row to the live table.

That is two `/proc` reads, two file creations and two renames per declaration. The sidecar exists so that a run killed at the rail names the declaration that was running (`docs/instrumentation-design.md`), which only matters for a declaration that runs long.

## Options

1. Keep one descriptor open for the sidecar and overwrite it in place (`write_at` then `set_len`), with a final marker line so a torn write is recognisable. No directory operations.
2. Write the sidecar from a helper thread a few times a second, from a shared copy of the open stack. A killed run then names a scope at most that stale, and a declaration a rail kill lands on has been running far longer.
3. Read the high-water mark once per scope instead of twice (the mark only grows, so the closing read of one scope serves as the opening read of the next), from a descriptor kept open.

The user-time part has not been profiled. A callgrind pair of the same check with and without the flag would say whether it is the clock reads of the phase guards or the row formatting.

## Done when

A cold showcase check with `--timings` is within a few percent of the plain one, and a run killed at the rail still leaves the running declaration's name.
