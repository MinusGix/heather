---
title: Attribute a native tool's write-elf now that the per-process floor is gone
status: open
labels: [performance,native,testing]
area: heather-in-heather
created: 2026-11-11
updated: 2026-11-11
---

The native tool tests are the largest remaining suite cost after the library gate, and nobody has attributed one since the per-process floor fell. Found while writing [[performance-overview-2026-11-11]].

## Measured

2026-11-11, four-core cloud box, test-profile binary at width one:

- `crates/cli/tests/native_tools.rs`: 216 and 251 s in two exact-lane runs, 150 s in a `--pr` run, 76 s in the fast lane. `compiled_sort_runs_as_gnu_sort` 85 and 111 s, `compiled_tac_runs_as_gnu_tac` 71 and 97 s, `compiled_cat_files_runs_as_gnu_cat` 40 to 60 s, `compiled_decimals_round_trip_the_widest_words` 43 s.
- All native targets together are a quarter of the exact lane's CPU, about half of a `--pr` run's summed target time and a third of the fast lane's.
- `scripts/bench-probes --heavy`: loading the native world warm is 1.1 s (8.3 s on 2026-10-29), a warm `write-elf` of `yes_tool` 2.3 s (14.0 s), a cold one 4.8 s (43.7 s), and `head_n_tool` cold 21.3 s (127.5 s): 12.9 s of elaboration, 5.2 s of kernel, 3.2 s of image work, 1.0 s of hashing.

So the fixed floor is no longer the cost. What is left grows with the tool, and on `head_n_tool` 60% of it is the elaborator building the certificate.

## To do

Take a `--timings` table of `write-elf` for `sort_tool` and `tac_tool` cold and warm, and name the declarations and phases their time is in. Add the heavier one to `perf/bench/cases.tsv` ([[bench-probe-cases-stale-2026-11]]).

## Done when

The table exists in this issue's log and the follow-up it points at is filed.
