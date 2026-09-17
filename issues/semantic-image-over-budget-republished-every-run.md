---
title: An over-budget semantic image is rejected, rebuilt and re-published on every warm run of the showcase
status: open
labels: [tooling,caching,performance,elaboration]
created: 2026-09-17
updated: 2026-09-17
---

Found by the first `scripts/perf snapshot` ([[perf-dashboard]], 2026-09-17):
an **unchanged** `docs/showcase/calc_parser.hthr` costs 12.5–15 s on a warm
run at width one, where `lib/std/omega.hthr` costs 0.2 s. The warm run's
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
