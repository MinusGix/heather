---
title: "Replay unchanged declarations of an edited module from its previous image"
status: open
labels: [tooling, performance, caching, elaboration, design]
area: infrastructure
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
- 2026-09-17: 2026-09-17: the in-process half landed. `ModuleDelta` carries one `ItemSlice` per item (source text, start offset, Ψ/event/warning ranges; a measure group is one slice at its first member keyed by every member's text); `check_module_delta_from(module, src, deps, &previous)` runs the sliced pass inside both module passes (atomic and error-collecting), replaying a slice through `recheck_extension` (inline, beside the pool) and the event preflight, relocating its spans through the image codec, and elaborating from source otherwise; the prefix flag is kept honest at each item's end by comparing the re-elaborated contribution's interface projection with the previous slice's. `crates/elab/tests/slice_replay.rs` runs fifteen shapes at widths one and four against fresh elaboration: unchanged, append, proof edit, two proof edits, reformatting, `fn` body edit, insert, delete, reorder, rename, a mutual group reformatted and edited, a different dependency world, a forged slice, a broken edit. Datum (release, width one, in process, verdict store installed): the showcase module with one declaration appended re-checks in 0.72 s sliced against 4.7 s fresh, 96 replayed, 1 elaborated. Open: the persistent half (slice table in the image, previous-image index in the store, the CLI's source-miss path, the `(cache)` line's replayed count).
- 2026-09-17: 2026-09-17: the persistent half landed. The semantic image (format `HTHMOD` 7; an older image is an ordinary unsupported-format rebuild) carries the slice table — each item's exact text, start offset and three ranges — and the entry scope; the store keeps one newest-image pointer per (module, dependency world) written after each publish, and `load_previous` loads it under the ordinary freshness policy with the warnings attached; the session's source-miss path checks through `check_module_delta_from` when a previous image exists, reports an unusable one as a notice, and the `(cache)` line ends with `N declarations replayed after an edit`. Tests: `module_images.rs` (slices round-trip, the pointer follows the newest publish, `Exact` ignores another build's previous image and `AcceptStale` takes it), `check.rs` (an edited fixture replays its unchanged declarations and kernel-checks the appended one). Datum through the CLI (release, width one, desktop): the showcase with one declaration appended 8.3 s → 5.5 s, 96 replayed; what remains is the previous image's own decode-and-drop (~2 s for 29 M nodes, now attributed to `image_decode`), publish 1.0 s, the verdict walk 0.5 s and the relocation encode/decode — the replayed declarations are nearly free. Acceptance: slices partition and round-trip; the fifteen edit shapes match fresh elaboration; the previous image is found by (module, dependencies) under the freshness policy; the edit mode dropped by more than the re-elaboration share (4 s of 8.3). Next on this path: incremental publish, incremental walk, and taking the previous image's decode off the critical path.
