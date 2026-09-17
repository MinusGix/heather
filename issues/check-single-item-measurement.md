---
title: Check and time one declaration instead of its whole module
status: open
labels: [tooling,performance,elaboration,caching,testing]
created: 2026-09-16
updated: 2026-09-16
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
