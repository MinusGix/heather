---
title: Decide whether <A> type parameters become kernel families (Option as a Type → Type value)
status: open
labels: [design,kernel,elaboration,inductives]
area: language
milestone: [lang-sequencing]
created: 2026-10-31
updated: 2026-10-31
---

Item 1 of the fundamental-improvements memo of 2026-10-31 (Claude Doc, https://claude.ai/artifact/Y2Jo9y9Mgd52QdguvaL43s). **Minus is unsure about this one (2026-10-31)**, so this is a
decision round: it measures the case first and recommends for or against.

The question: should `inductive Option<A>` mean what `inductive Option(A: Type)`
already means, a kernel family over its parameter, with `<A>` only marking the
parameter as inferred at use?

## Where things stand

- Value parameters are kernel abstractions. A probe on `3099a7d`
  (`docs/language/sequencing-surface-design.md` appendix P1) passes
  `inductive Box(A: Type)` as `M: Type → Type`, and generic code over it
  computes by `refl`.
- `<A>` parameters are substituted at each use, so `Option<Nat>` and
  `Option<Bool>` are unrelated kernel types (`docs/inductives/inductive-tier0-lowering.md` §2).
  That doc says the choice was forced because the surface had no first-class
  types then, and that a `ΠΠ ℓ⃗`-abstracted encoding becomes possible with
  universe polymorphism.

## What the round answers

1. **What per-use substitution costs today**: elaboration time and kernel term
   size on generic-heavy modules (`scripts/perf report`, `--timings`). A small
   number weakens the case to "language cleanliness only".
2. **What it would retire**:
   - pieces 1–2 of [[higher-kinded-classes]] (a bare `Option` as a value; the
     unifier's `?M(A) =?= Option<A>` becomes first-order);
   - trial-by-kernel-check resolution's reason (`docs/language/classes/traits-layer2-design.md`
     §3.1: a monomorphized carrier cannot be read back);
   - one kernel object per generic theorem or instance.
3. **What it costs**:
   - universe levels: level-polymorphic families or cumulativity, checked
     against `docs/delam/04–06`;
   - tier 1/2 lowerings (W, IWf) taking a parameter telescope;
   - migration of every `<A>` declaration's kernel form (the surface spelling
     stays, as the `<…>` type-arguments decision requires).
4. **The alternative**: keep `<A>` monomorphized and do only [[higher-kinded-classes]]'s
   three pieces.

## Done when

A short note with the measurement and a recommendation, decided by Minus,
before [[higher-kinded-classes]] starts (since that round is either three
patches or this round's first step).

## Log

- 2026-10-31: [[higher-kinded-classes]] landed without this round: pieces 1–2 did not need <A> as kernel families, because tier-0/1 generic declarations already register D#tycode_fn : Π(A : Ty 0). Ty l, which is the constructor value, and the unifier's ?M(A) ≟ Option<A> is first-order against its respelling. This round no longer gates it; what remains of the case is the cost side (per-use substitution, trial-by-kernel-check resolution, level profiles other than all-Ty 0). docs/language/classes/higher-kinded-classes-design.md §6.
- 2026-11-05: gardener: cites a file it shares with [[dependent-field-injectivity]] (`docs/inductives/inductive-tier0-lowering.md`); [[inductive-compiler]] (`docs/inductives/inductive-tier0-lowering.md`); [[tier2-type-code-functions]] (`docs/language/classes/higher-kinded-classes-design.md`).
