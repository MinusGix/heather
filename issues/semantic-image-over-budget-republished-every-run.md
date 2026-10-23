---
title: An over-budget semantic image is rejected, rebuilt and re-published on every warm run of the showcase
status: closed
labels: [tooling,caching,performance,elaboration]
created: 2026-09-17
updated: 2026-09-17
---

Found by the first `scripts/perf snapshot` ([[perf-dashboard]], 2026-09-17):
an **unchanged** `docs/showcase/calc_parser.hthr` costs 12.5–15 s on a warm
run at width one, where `lib/std/tactic/omega.hthr` costs 0.2 s. The warm run's
stderr says why:

    cache: stored module `calc_parser` is unusable (semantic image was
    rejected: module image exceeds its syntax-node budget) — rebuilding

`ModuleImageLimits::max_nodes` is 16 M (`crates/elab/src/module_image.rs`);
the showcase's image is past it. So every warm run of the showcase pays, in
order: decode the image up to the budget (`image_decode` 1.1 s), reject it,
re-elaborate all 96 declarations with the declaration cache (`decl_body`
2.5 s, `decl_emit` 0.9 s; 144 accepted, 0 gated), walk the interface closure
(`merkle_walk` 1.1 s), and **publish the same over-budget image again**
(`image_publish` 1.5 s) for the next run to reject. Reproduced on three
consecutive runs of one cache dir. The edit mode is the same 12.6 s, so for
this file "nothing changed" and "one declaration changed" cost the same, and
neither is replay.

Two halves, in the order they should land:

1. **Don't publish what the reader will refuse.** The writer knows the node
   count; an image past the decode budget should not be written (and the
   decoder should not be asked), which alone returns ~2.6 s of the 12.5 s
   and removes the wasted disk. A stored marker "too large to image" would
   keep the next run from trying.
2. **Why is the image past 16 M nodes.** 96 declarations at 16 M syntax nodes
   is 170 k nodes per declaration on average, and the file's largest items are
   the parser combinator instances whose emitted types the normal-form
   emission issue already prices ([[elab-emits-normal-form-of-matched-type-argument]]:
   ×3.5 per combinator layer). The budget is a symptom the emission size
   owns; raising it would trade a rejection for a slower decode.

## What it assumes from elsewhere

- **[[semantic-module-images]]** owns the image format and its limits.
  Assumed here: only that the limits are the reader's and the writer does
  not consult them.
- **[[elab-emits-normal-form-of-matched-type-argument]]** owns the emitted
  size. Assumed here: only that the showcase's items are on its curve.
- **[[perf-dashboard]]** is where the warm column that found this lives.

## Log

- 2026-09-17: 2026-09-17: Both halves of the small fix landed, and the budget is raised as
  the user asked (it bounds decoding work, not allocation, and was not
  principled at 16 M): the writer counts syntax nodes at exactly the sites the
  reader charges (`Writer::nodes`, `ModuleDelta::to_image`), `publish` refuses
  an image past `max_nodes` with `ModuleCacheError::OverBudget { nodes, limit }`
  and writes nothing, and `max_nodes` is 256 M. The showcase's image is
  **29.4 M nodes**. Measured on the desktop at width one
  (`perf/snapshots/2026-09-17T184149Z-local.json` against `…T182332Z`):

  | showcase, unchanged | before | refusal alone (16 M) | refusal + 256 M |
  | - | - | - | - |
  | warm wall | 12.5–13.7 s, re-elaborated | 9.5 s, re-elaborated, no decode/publish | 12.9 s, **replayed** |
  | of which | decode 1.1 + elaborate 2.5 + publish 1.5 + merkle 1.1 | — | decode 2.1 + kernel recheck 7.2 |
  | edit wall | 12.6 s | — | 10.8 s |

  So the warm run is now what it claims to be — 20 modules replayed, 0
  declarations elaborated — and it costs what a replay of this module costs:
  a 2.1 s decode of 29 M nodes and a 7.2 s kernel recheck, against the cold
  gate's 15.8 s (5.1 M conversion queries against 5.7 M). That the honest
  replay is *slower* than the refused-image path is not a regression of this
  fix; it is the replay's own price, which [[semantic-replay-phase-attribution]]
  owns (its parallel recheck applies at width > 1; the wait number was 35.2 s
  against 36.7 s). Edit is 10.8 s and is now cheaper than warm, because the
  declaration cache skips the gate where the replay re-runs it. Closing: the
  scope here was the rejected-and-republished loop, and it is gone. The image's
  size is [[elab-emits-normal-form-of-matched-type-argument]]'s.
