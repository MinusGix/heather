---
title: One canonical spelling for every type the kernel compares against itself
status: open
labels: [elaboration,inductives,representation,performance,design]
created: 2026-09-06
updated: 2026-09-06
---

Filed from the 2026-09-06 x86 kernel round. Exact first-difference excerpts
of the expected-vs-inferred conversion misses on the five-node
FunctionIR/x86 module showed one declared type written three ways inside one
module: fully inlined (`Σ(…)((Σ…`, 50–300 K characters), through a named
code (`El (u475^δ)`), and as a boxed code literal (`El «(«Σ…»`). Whenever two
spellings meet, the kernel unfolds and walks the larger one in the value
domain; that was ~4.6 s of the module's ~7.7 s of kernel time. The
registration boundary that leaves the x86 model types unnamed is
[[inductive-spelling-codes-nonrecursive]]; this issue is the invariant that
boundary is a special case of.

The three spellings each have an owner today: the inline lowering is what
the recognizers fingerprint (`lower_instance` is the identity the guards
anchor on — the shape-code round's deliberate choice); the named codes are
`GenDef::TyCode`/`ShapeCode`/`ArityFn` respelled site by site behind
structural guards; the boxed literal is what the code layer writes. Every
site that fails a guard silently falls back to inline, and the kernel is
where the fallbacks are paid for.

## Direction

- Decide the canonical spelling per role (statement, annotation, value,
  code payload) and make the *recognizers* see through names rather than
  the emitters guess which copy the recognizer wants — the reverse of the
  shape-code round's mechanism 3, which moved `whnf` back to the inline
  copy to keep readers spelling-insensitive.
- A checked invariant rather than a convention: a debug-only pass over an
  elaborated module that reports two spellings of one declared type meeting
  in a conversion miss (the round's `Tc::conv_ty` miss sampler, filed under
  [[perf-profile-build-target]], already produces the datum).

## What it assumes from elsewhere

- **[[wf-shape-annotation-slots]]** owns the shape-code mechanism and its
  guards. Assumed here: only that guards decline site by site today.
- **[[inductive-spelling-codes-nonrecursive]]** owns the first concrete
  slice; this issue is not a prerequisite for it.

## Log

- 2026-09-06: First slice landed ([[inductive-spelling-codes-nonrecursive]], 2026-09-06): flat declarations' payloads and suffix sums are named and the whole-type code is spelled over the names; monomorphized Wf copies respell shape and arity alike. The sampler that produces this issue's datum is landed behind value-metrics ([[perf-profile-build-target]]); its residual rows are on [[unnameable-annotation-occurrences]].
- 2026-09-06: Latent look-alike found by [[inductive-spelling-codes-nonrecursive]]'s round: the structural guards compare against lowerings, and a lowering can coincide with a *tag type* (a nullary payload at tag 0 is `Σ(Unit). Unit`, the digit-1 component of every later tag type). Any future guard that names sub-declaration components must be positional or must exclude tag types explicitly; the whole-type guard is safe only because no fieldless single-constructor declaration holds tag 0.
- 2026-09-06: Owners filed for the round's residue: [[tag-types-collide-with-lowerings]] (the structural-guard hazard), [[emission-site-respell-audit]] (the no-new-definitions half of the residual rows), [[conv-miss-sampler-item-attribution]] (the datum's missing column), [[recursive-spine-codes]] (the mechanism's other half).
