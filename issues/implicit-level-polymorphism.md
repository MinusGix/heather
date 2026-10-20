---
title: Type parameters implicitly polymorphic in their level
status: open
labels: [frontend,elaboration,design]
area: language
created: 2026-07-27
updated: 2026-07-27
---

Deferred from [[surface-universe]], which makes `<A: Type<n>>` spellable with `Type<0>` as the default.

The alternative considered and put off: rather than defaulting an unannotated `<A>` to level 0, make it **implicitly polymorphic in its level** — the declaration is generic over the level and each use site instantiates it.

Why it is not the default now:

- Quantifying over a level is `UPi`, which is layer m by construction
  (`typing.rs:461`, `Level::Omega`), so an implicitly level-polymorphic `fn`
  is not a single layer-p declaration at all. It is the generator shape of
  [[surface-universe]] §7 (`∀ℓ. □(⊢ T_ℓ)`) with the quantifier hidden, which
  means it wants [[generators-in-the-language]] first.
- The elaborator would have to decide *which* levels a declaration is
  instantiated at, i.e. level inference — explicitly ruled out of
  [[surface-universe]] ("levels are written or zero, never inferred") to keep
  [[elab-unifier-completeness]]'s "no level constraints exist below layer m"
  true.

So this is not a small default-flip: it is level inference plus the generator
layer, and it should be picked up after both. What it buys is real, though —
without it, a level-generic library is n written copies or an explicit
generator, and the "90% automation" framing of [[surface-universe]] §7 is
exactly this feature.

