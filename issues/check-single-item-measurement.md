---
title: Check and time one declaration instead of its whole module
status: closed
labels: [tooling,performance,elaboration,caching,testing]
created: 2026-09-16
updated: 2026-09-17
---

Almost every measurement probe cares about one declaration, and pays for the
whole file. `docs/showcase/calc_parser.hthr` takes about 50 s serial; a probe
asking "did `close_body`'s query count move" spends all of it, and on the
furnace that 50 s sits inside a 2–3 minute round trip
([[furnace-run-round-trip-latency]]). Four such probes on 2026-09-16 cost most
of a session's wall time and produced five numbers.

Wanted: `heather check --only <item>[,<item>…]`, which elaborates and gates
exactly those declarations and whatever they depend on, and reports timings for
them. The dependency closure is the hard part and the reason this is an issue
and not a patch:

- A declaration's *type* may need earlier declarations elaborated; its *body*
  needs whatever it calls. The honest version elaborates the prefix it needs
  and gates only what was asked, rather than pretending the item is standalone.
- With `--cache`/semantic images, the prefix may be replayable rather than
  re-elaborated, which is where the actual saving comes from — this may be
  mostly a *front-end* for the cache rather than new machinery.
- Timings for a partially elaborated module are comparable to a full run's only
  if the gate did the same work. It must be impossible to quote a `--only`
  number against a whole-run number without noticing; a marker in the TSV is
  the cheap version.

Not a verdict mechanism: `--only` says nothing about the module. It is a
measurement and iteration tool, and should probably refuse to be combined with
anything that produces or publishes an image.

## What it assumes from elsewhere

- **[[relocatable-semantic-module-images]]** and the cache design own replaying
  a prefix. Assumed here: only that replaying a prefix and then elaborating a
  suffix is already the normal path, so the new part is the selection, not the
  resumption.

## Log

- 2026-09-16: Filed from the `calc_parser.hthr` rounds, where every probe
  elaborated 96 items to read 5.
- 2026-09-17: Implemented (docs/check-only-design.md). The dependency closure is not computed: since slice replay, every item that is not named replays its slice and the named ones elaborate from source — `check_module_delta_only` in the elaborator, `SemanticSession::with_only` + `check_only` in the CLI (loads the module's previous image, never publishes), `gate::Except` wrapping the verdict store so the named items face the kernel every run and the store does not learn they passed. `--only` needs `--cache`; without a previous image it says to run `heather check --cache` once; an unknown name is an error after the pass; the output line is the reserved `ok (only) — N elaborated for --only, M replayed`; the timings run row carries `only=<items>` and scripts/timings prints a banner and refuses to diff a --only table against a whole run or a different item set. Measured on the showcase (release, width one, desktop): a probe of parser_primitives::complete_post is 13.5 s against 47.8 s for the cold whole run, the item's own row 9.7 s; queries reproduce exactly, misses and steps are +136 (of 14,210 / 246,498) and stable across --only runs — warm kernel state (glued globals unfolded by earlier items) that replay does not rebuild; close_body reproduces to the unit. Times are a series of their own, by design. Closing; the +136 is a note for the lazy-δ line, not a defect here.
