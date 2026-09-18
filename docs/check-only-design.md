# `heather check --only`: elaborate and gate one declaration, replay the rest

Status: design 2026-09-17, implemented the same day. Owner:
`issues/check-single-item-measurement.md`.

## 1. The problem, restated against the code that now exists

Every measurement probe cares about one declaration and pays for the whole
file: `docs/showcase/calc_parser.hthr` is ~50 s serial cold, and a probe
asking whether `close_body`'s query count moved spent all of it, four times
in one session. The issue's worry was the dependency closure — which earlier
declarations an item's type and body need.

That closure no longer has to be *computed*, because it no longer has to be
*skipped*. Since `docs/declaration-slice-replay-design.md` landed, a module
pass can reproduce any item from its stored slice — Ψ bindings through the
verdict store, registry events through the preflight checks — and elaborate
only the items it is told to. The prefix a probed item needs is every earlier
item, and replaying every earlier item is exactly the edit path's warm case.
So `--only` is a *selection* on the sliced pass, not new machinery: the
named items are elaborated from source and face the real kernel; everything
else in the module replays its slice.

## 2. The command

```
heather check --cache --only <item>[,<item>…] [--timings f.tsv] [--kernel-workers n] <file>
```

- An item is `name` (a declaration of the root module) or `module::name`
  (a declaration of any module in the closure, e.g. `omega::cutsat_left_cut`
  while checking the showcase). A mutual measure group is elaborated whole
  when any member is named — a group is one slice and one transaction.
- `--only` requires `--cache`: the prefix comes from the store. For a module
  with named items the pass ignores the source-keyed image (a hit would
  replay the whole module and elaborate nothing) and loads the module's
  *previous* image over the current dependency world
  (`load_previous`, the slice-replay index). No previous image is an
  error that says what to run: `heather check --cache <file>` once.
- Modules without named items take the ordinary path — an image hit, or
  elaboration and publication as today — so the dependency world the named
  module is replayed over is the one a full check would build.
- A module with named items is **never published** and its verdicts are
  **never written**: `--only` says nothing about the module, and leaves the
  store exactly as it found it. Concretely the verdict store is wrapped in a
  gate that answers *not admitted* for the named items and swallows their
  `accepted` — the kernel runs on them every time, and the store does not
  learn that it did.
- The gate is otherwise the cache's, so the replayed prefix is vouched for
  or kernel-checked exactly as on any warm run.

## 3. What a `--only` run reports

- Stdout: `<file>: ok (only) — 1 declaration elaborated for --only,
  95 replayed`. The bare `ok` and the `ok (cache)` line are both reserved,
  so a `--only` run can never be read as a check of the module.
- The `--timings` run row carries `only=<items>` in its `item` column.
  `scripts/timings` prints a banner on such a table, and `--diff` refuses to
  compare a `--only` table with a whole-run table or with a `--only` table of
  a different item set. That is the "impossible to quote against a
  whole-run number without noticing" the issue asks for.
- A named item that no module in the closure contains is an error after the
  pass (the pass must run to know: the name may be in a replayed module).

## 4. Comparability

A named item elaborates over a prefix whose Ψ, registries and scope are
identical to a full run's — that is what slice replay guarantees. What
replay does not reproduce is the *transient* state the earlier items'
elaboration would have left behind: elaborator memos (`result_only_memo`
is cleared per slice) and the kernel's glued-global state, where a binding
unfolded once by an earlier item stays unfolded for the later ones. So a
`--only` item's row can differ from its full-run row in two ways, and the
acceptance measurement (§6) says by how much:

- **Time** differs by whatever the warm state was worth, in either
  direction; treat it as a separate series, never as a delta against a
  whole run. `scripts/timings` refuses to diff the two.
- **Counts** are exact for an item whose conversions never touched a global
  an earlier item had already unfolded (`close_body`: identical to the
  unit), and off by the re-unfolding otherwise (`complete_post`: +136
  misses and +136 steps of 14,210 and 246,498, queries identical). The
  discrepancy is itself stable across `--only` runs, so a `--only` series
  is comparable with itself to the unit, which is what a probe loop
  needs. Where the +136 lands is a follow-up question for
  `issues/kernel-lazy-delta` territory, not this design's.

## 5. Cost against the code

- `crates/elab/src/module_delta.rs`: `SlicePlan.force` (item names) and
  `SliceReport.forced`; `check_module_delta_only(...)` installs the plan with
  a force set; `try_replay_slice` declines a forced item; the pass records
  which forced names it met. ~60 lines.
- `crates/elab/src/lib.rs`: the item loop asks the plan before replaying,
  by the item's name and its group's names. ~20 lines.
- `crates/elab/src/gate.rs`: `Except` — a gate wrapper that answers `false`
  for a set of names and forwards everything else. ~40 lines.
- `crates/cli/src/main.rs`, `semantic.rs`: `--only` parsing; the session
  takes the per-module force map, routes a forced module through
  `load_previous` + `check_module_delta_only`, skips its publish; the run
  scope label; the output line; the unseen-name error. ~120 lines.
- `scripts/timings`: banner and diff refusal. ~25 lines.
- Tests: `crates/elab/tests/slice_replay.rs` — a forced item is elaborated,
  every other item replayed, the delta equals fresh elaboration's;
  `crates/cli/tests/check.rs` — `--only` without `--cache` and without a
  previous image are errors; a `--only` run prints the reserved line, labels
  the run row, and leaves the verdict store's counts unchanged; an unknown
  name is an error.

## 6. Acceptance measurement

Release CLI, width one, the desktop, 2026-09-17, the showcase over
`-L lib/std -L lib/std/parser`:

| run | wall | `complete_post` total / gate ms | misses | queries | steps |
|---|---|---|---|---|---|
| full, cold store | 47.8 s | 9,825 / 5,622 | 14,210 | 3,698,442 | 246,498 |
| full, warm store | 4.0 s | (replayed) | | | |
| `--only parser_primitives::complete_post` | 13.5 s | 9,643 / 5,861 | 14,346 | 3,698,442 | 246,634 |
| the same, again | 13.5 s | 9,705 / 5,923 | 14,346 | 3,698,442 | 246,634 |
| `--only close_body` | 7.0 s | 2,315 / 1,639 (full: 2,594 / 1,810) | 2,572 (=) | 1,319,176 (=) | 32,579 (=) |

A probe of the corpus's heaviest declaration is 13.5 s instead of 48 s,
of which 9.7 s is the declaration itself; the rest is replaying 20 modules
and the previous image's decode. The probe loop the issue was filed from
(four probes in a session) goes from ~200 s of checking to ~54 s.
