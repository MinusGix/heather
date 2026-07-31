---
title: Fixed syntax schemas are rebuilt fresh per check; cache or share their skeletons
status: open
labels: [kernel,performance]
created: 2026-07-31
updated: 2026-07-31
---

The `code/check-identity-recursor` profiles from the
[[subst-visits-closed-subtrees]] round (2026-07-31) show the time going
into *building*, not comparing: `rec.rs::branch_specs` rebuilt per check
(~2%), `term::nth`/`term::wf_step_telescope` materialized fresh with six
`elem.shift_local(k)` walks per `nth`, and `Vec<CtxEntry>`/
`Vec<GlobalBinding>` clone/drop at ~5–8% — on a family whose whole cost
is one-shot construction of 52 branch telescopes that are then traversed
once and dropped.

These are **fixed syntax schemas** parameterized by a handful of pieces
(level, element type, context shape). Candidate shapes, in increasing
ambition:

1. Build the level-/type-generic skeleton of each schema once
   (lazily, per process) and instantiate by substitution — the
   instantiation traversals then run over shared `Rc`s, which the bounds
   cache and a future reflexivity check ([[conv-pointer-equality-reflexivity]])
   both feed on.
2. Memoize whole schema instances keyed by their parameters (the
   pointer-keyed cache pattern from `bounds.rs` extends, but keys here are
   structural, so it needs an equality or interning story — costlier to
   get right in the trusted base).

Why this issue exists beyond the microbench: it is the likely *closer* of
[[bounds-metadata-taxes-one-shot-checking]] — the accepted ~1.4× there is
paid exactly on these fresh, global-saturated telescopes, and telescopes
that are shared instead of fresh stop paying the marker stage at all.

Danger note: `rec.rs`/`typing.rs`/`conv.rs` share the telescope tables
precisely so they cannot drift (the wf-former lesson). Any caching layer
must keep that single-source property — cache *outputs* of the one
constructor, never a second transcription.

## What it assumes from elsewhere

- **[[bounds-metadata-taxes-one-shot-checking]]** owns the measured tax.
  Assumed here: only that one-shot fresh terms are where it is paid.
