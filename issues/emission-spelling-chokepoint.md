---
title: One emission chokepoint for annotation spelling, and a walker that finds the next disagreeing site
status: open
labels: [elaboration,representation,tooling]
created: 2026-09-06
updated: 2026-09-06
---

Filed from [[emission-site-respell-audit]]'s round (2026-09-06). All four of
its rows, and both riders, were one failure: an emission site copied a type
verbatim from wherever it happened to read it — a binder's type, a `whnf`
result, a decoded code — while a sibling site respelled the same type
(`respell_ty_deep`). Every fix was "route this site through
`respell_emitted`", and the invariant now lives in about a dozen call sites
(`application.rs`, `inductive.rs` ×4, `wf.rs` ×3, `gendefs.rs`) plus
docs/annotation-component-respell-design.md §2.4.

## Shape

1. **One chokepoint.** An `emit_ty(cx, ty, depth)` (today's `respell_emitted`:
   `decode_deep`, then `respell_ty_deep`) that every constructor of a `Term`
   or `Type` with an annotation slot goes through, so a new emitter cannot
   forget it. Structural reads keep taking the inline copy — the line of
   docs/wf-shape-code-design.md §4 is unchanged; only the *emitted* slot is
   funnelled.
2. **A walker.** A debug-time (or `value-metrics`) pass over a checked
   declaration's term and statement that flags any annotation slot whose
   content `respell_emitted` would change — i.e. any site still writing a
   spelling the chokepoint would not. Run it on the library in a test, so the
   next disagreeing site is found before the sampler has to attribute it.
   Two sites the audit already knows the walker would list: a `Lam`'s `dom`
   is copied off the expected Π rather than respelled on its own (agreement
   by luck while every Π it meets is respelled), and `build_ctor`'s label
   type at a constructor literal ([[conv-miss-residual-rows]]).

## What it assumes from elsewhere

- **[[elaborator-canonical-type-spelling]]** owns the invariant. Assumed
  here: only that "one spelling for every type the kernel compares against
  itself" is the target; this issue is the mechanism that keeps it.
- **[[emission-site-respell-audit]]** (closed) owns the audit's numbers.
