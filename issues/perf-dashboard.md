---
title: A perf diary and dashboard: what is slow now, and where it comes from
status: open
labels: [tooling,performance,measurement,testing,meta]
created: 2026-09-17
updated: 2026-09-17
---

Every perf issue in the tracker opens with "re-measure first", and the
question a round asks before choosing a target — *what is slow now, and where
does it come from* — had no standing answer: the suite's per-binary timings
were an append-only file nobody read back, `--timings` tables were taken per
probe and thrown away, and the quiet-server diary (`scripts/bench-remote`)
went down with its server. Rounds picked at the slowness in front of them
([[elab-emits-normal-form-of-matched-type-argument]] is the record of where that ends, 2026-09-16).

`scripts/perf` owns the answer. `snapshot` records, in one dated JSON keyed by
environment (`local`/`furnace`): the latest suite run per lane from
`target/test-target-timings-<lane>.tsv`; a corpus of files each checked
through the release CLI **wait** (cold at the default gate width — what a
person sits through), **cold**, **warm** and **edit** (one trivial
declaration appended, restored afterwards) at width one with `--timings`; and
from those tables the run row's every phase and counter, the module rows and
the heaviest declarations. `report` prints the phase split, per-file
concentration (top-1/top-5 share, p50/p90/max) and the heaviest declarations
with deltas against the previous same-environment snapshot; `serve` is the
dashboard (`scripts/perf-web.html`: the same tables, phase stacks, and
per-file history with one line per environment). `perf/README.md` has the
rules: seconds within one environment, counts across; a diary, not a gate.

## What it assumes from elsewhere

- **[[perf-tracking-consistent-environment]]** owns where a *gate's* numbers
  come from. Assumed here: only that a dated environment-keyed diary is the
  agreed home for wall-clock numbers, and that `local` and `furnace` differ by
  a roughly uniform constant, so a family that departs from it is the signal.
- **[[perf-instrumentation-consolidation]]** owns the `--timings` columns.
  Assumed here: the column names in `scripts/timings`, read by name.
- **[[check-single-item-measurement]]** would make a per-declaration probe
  cheap; the snapshot measures whole files and does not need it.

## Open

- The furnace has no snapshot yet; the first one gives the local/furnace
  constant per family. Taking one is `furnace run -- bash -c 'cargo build
  --release -p heather-cli && scripts/perf snapshot --env furnace'`, and the
  JSON has to come back with the checkout (the furnace `/work` dir is not
  the repo).
- The suite section reads the runner's history; a snapshot taken on a box
  that has not run `scripts/test` has none, and says so.
- `wait` is the only mode at the default width. If the parallel gate's
  scaling per file becomes the question, a width sweep is a flag away.

## Log

- 2026-09-17: 2026-09-17: Landed: `scripts/perf` (snapshot / report / list / serve),
  `scripts/perf-web.html`, `perf/README.md`, a CLAUDE.md pointer; first
  desktop snapshot `perf/snapshots/2026-09-17T182332Z-local.json` (quick
  corpus: omega, nat, calc_parser; width-one attribution plus a width-8 wait).
  What the first reading says, so the next perf round starts from it:

  - **The suite** (full lane, 2026-09-16): 201 binaries, 1422 s summed at width
    one; one binary is 179 s (`showcase_calculator`) and the next seven are
    50–69 s each — the x86 shards, certgen, parser_library, the cli bin tests.
    The top eight are 42% of the sum.
  - **Cold, corpus total**: kernel gate 59%, decl_body 13%, merkle_walk 6%,
    decl_emit 5%, everything else ≤4%. The gate share per file is 55–60% for
    omega and the showcase and 21% for nat. So on today's tree the kernel is
    still the majority of a cold check and the elaborator's body walk is the
    largest single non-gate phase; the **merkle walk being 6% of cold (16% of
    a width-8 wait, 2.2 s on the showcase's root module alone)** is the
    cheapest-looking surprise and has no issue.
  - **Concentration**: the showcase's top declaration is 22% of its cold time
    and its top five are 39% (`parser_primitives::complete_post` 11.1 s of
    53.8 s, then `close_body`, `number_grammar`, `factor_body`, `expr_body`);
    omega's top five are 49% (the cutsat lemmas); nat is flat. p90 per
    declaration is 21 ms (omega) / 62 ms (showcase) against a 1–1.5 ms median:
    the cost is in a handful of items, not a constant factor.
  - **Warm is not replay for the showcase**: 12.5 s unchanged versus 0.2 s for
    omega, because its image is over the 16 M node budget and gets rejected,
    rebuilt and re-published every run — filed as
    [[semantic-image-over-budget-republished-every-run]]. Edit costs the same
    12.6 s. For omega, edit is 3.1 s of a 9.7 s cold check, and that 3.1 s is
    elaboration (decl_body 28%, omega_check 19%, decl_type 17%) with the gate
    at 3 ms: the declaration cache removes the kernel from an edit but not
    the elaborator.
  - **Width 8 buys 1.5× on the showcase and 1.7× on omega** (36.7 vs 53.8 s;
    5.8 vs 9.7 s) at 2.8× the memory (4.9 GB vs 1.7 GB).
- 2026-09-17: 2026-09-17: the merkle-walk surprise from the first snapshot has an owner: [[merkle-walk-cold-share]].
- 2026-09-17: 2026-09-17: first use as a before/after instrument: the over-budget fix ([[semantic-image-over-budget-republished-every-run]], closed) was remeasured with `snapshot --only calc_parser --only omega` and read with `report`; the delta column showed warm unchanged in seconds and the phase table showed why (re-elaboration became replay). The second snapshot is on record.
- 2026-09-17: 2026-09-17: second use as a before/after instrument, [[merkle-walk-cold-share]]: the cache_hashes counter and merkle_walk column of the raw run rows showed the deferred gate's double hashing (2122 -> 1061 renders on the showcase's wait run) where the wall column, taken on a loaded box, showed nothing. Read the counts first.
