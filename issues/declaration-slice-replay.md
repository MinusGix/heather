---
title: "Replay unchanged declarations of an edited module from its previous image"
status: open
labels: [tooling, performance, caching, elaboration, design]
created: 2026-09-17
updated: 2026-09-17
---

After an edit, a module is a source-digest miss and is elaborated from
scratch, although the declaration-verdict store then admits every unchanged
declaration at the gate: the run re-elaborates everything to reach terms it
does not check. On the showcase that is 4 s of an 8.3 s edit check at width
one, plus 1.1 s to re-encode the whole image (`perf/snapshots`, 2026-09-17,
`edit` mode).

`docs/declaration-slice-replay-design.md` is the design: record item
boundaries (slices) in the module delta and image; on a source miss, replay
the previous image's slices in order while each item's source digest matches
and the semantic prefix is still exact, elaborate from source at the first
difference, and resume replaying when a re-elaborated item's slice comes out
structurally equal (a proof edit). The identity pair is the module image's
own — source selects, the semantic prefix decides — at declaration
granularity; trust is unchanged, every replayed binding faces the gate.

## Acceptance

- A `ModuleDelta` carries one slice per item or measure group, partitioning
  its bindings, events and warnings; the image format stores the table.
- After each edit shape in the design's §7 list, the sliced replay produces
  a delta equal to fresh elaboration's, and the negative shapes replay
  nothing past the edit.
- The store finds the previous image for `(module, dependencies)` under the
  same freshness policy as any image; a previous image from another build is
  not consulted under `Exact`.
- `scripts/perf`'s `edit` mode on the showcase drops by at least the
  re-elaboration share measured in the design's §1, with the replayed count
  on the `(cache)` line.

## What it assumes from elsewhere

- **[[semantic-module-images]]** owns the format and the identity pair this
  reuses.
- **[[warm-path-rewalks-unchanged-declarations]]** owns the verdict walk
  that a replayed slice still pays; this issue took its second candidate.
- **[[relocatable-semantic-module-images]]** owns the upstream-edit shape;
  slices stay positional so that refinement remains possible.
- **[[semantic-cache-lifecycle]]** owns keeping and evicting previous images.

## Log

- 2026-09-17: Filed from the design pass the perf dashboard's edit numbers
  asked for, after the replay-verdict round made the edit path's remaining
  cost visibly the elaborator ([[perf-dashboard]] log). Two rounds: the
  in-process half (slices in the delta, the sliced pass, the differential
  tests), then the persistent half (format, previous-image index, CLI).
