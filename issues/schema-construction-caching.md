---
title: Fixed syntax schemas are rebuilt fresh per check; cache or share their skeletons
status: open
labels: [kernel,performance]
created: 2026-07-31
updated: 2026-08-01
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

## Log

- 2026-08-01: Datum from [[type-definitions]], and it points the OPPOSITE way from this issue's worry about named abbreviations costing conversion time. Naming the `Refines` statement shape in lib/ir_v1.hthr as a delta-transparent type-valued `fn` — replacing three verbatim spellings and three more inside refines_trans_conv's hypotheses — took the file from 35.96s to 32.90s release (-8.5%), and the debug test binary from 204 to 194 CPU-s. Two mechanisms, both worth remembering over the number: (i) the statement is ELABORATED once instead of six times, which is elaborator work this issue does not otherwise measure; (ii) conversion compares a delta-STUCK head, and conv.rs's delta_lazy only unfolds when the comparison would otherwise fail — so a successful comparison of two identical abbreviations never touches the body at all. The implication for caching: naming is itself a sharing mechanism at the SOURCE level, and it is free. Where this issue's schemas are concerned that suggests checking whether the expensive instantiations are ones a surface-level name could have shared, before building a cache to share them after the fact.
