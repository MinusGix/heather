---
title: Front-end sugar over the fixed-former kernel
status: open
labels: [kernel,frontend,design]
created: 2026-07-23
updated: 2026-07-23
---

Mental-development / tracking issue, not a work item yet. The
[[kernel-v1-extensions]] thesis is deliberately: **a small fixed former set
in the trusted kernel + encodings + front-end sugar** covers the language,
so the sugar layer is where usability actually lives. Nothing tracks that
layer yet; this is the placeholder so it gets designed rather than accreted.

The kernel is *maximally explicit on purpose* (fully annotated eliminators,
explicit levels, de Bruijn, Tarski El-decoding). Everything a programmer
would tolerate writing is sugar the front-end elaborates away. This issue is
the running list of what that sugar has to do and the constraints it must
respect. It is **not** the elaborator design — it is the requirements the
elaborator will be checked against.

## What the sugar must cover (grows as formers land)

- **Implicit annotations / elaboration.** The kernel does *zero* implicit
  insertion (DESIGN.md "Type checking"): `app` carries `l,l',S,T`; `fst`/`snd`
  carry `S,T`; `Λ ℓ⃗`/`$ l⃗` are explicit. The front-end has to synthesize
  all of these from context. This is the big one and it interacts with the
  [[box-synthesis-gap]] (elaborators must emit `letbox`, not β-redexed
  meta-functions, for boxed code in inference position).
- **Σ sugar (now concrete, motivates the whole issue).** Named-field records
  and non-dependent `A × B` desugar to `Σ`; `(a, b)` to annotated `pair`;
  `p.field` / tuple patterns to nested `fst`/`snd`. η-for-pairs (as landed)
  is what makes `let (a, b) = p` transparent. The IR nodes that "carry more
  than one field" — the original concrete motivation for Σ in the issue —
  want exactly this.
- **Sum sugar (positive counterpart of Σ).** Surface `A + B` desugars to
  `Sum`; `inl e` / `inr e` to the annotated intros (both summands + levels
  synthesized from the expected type); a `match e { inl x => … | inr y => … }`
  to the fully-annotated `case` (9 fields: `l,l',l''`, `A`, `B`, the motive
  `z. M`, both branch bodies, the scrutinee). Because sums are *positive*
  (no η, unlike Σ), the motive `M` is not recoverable by projection and must
  come from the checking type — so `match` is only inferable when its result
  type is known (checking position) or annotated; this is the concrete place
  the elaborator meets the checking-descent constraint below. Enums /
  tagged-union IR nodes (the original motivation for sums) are nested
  `A + (B + (C + …))` with named constructors mapping to injection chains.
- **Levels.** `⊔`/`ω`/level variables are checker-internal; surface syntax
  needs level inference or a polymorphism-by-default story so users do not
  write `ΠΠ ℓ⃗`.
- **Encodings vs. types.** The Tarski `El`/encoding split (`Nat` the type vs.
  `«Nat»` the code) is a kernel artifact; the surface should not force the
  distinction except where code is genuinely being manipulated (`box`).
- **Modal layer.** `box`/`letbox`/the recursors are the compelling feature
  but the rawest syntax; sugar for common intensional-analysis patterns is
  where Heather's value shows.

## Constraints

- **Checking-descent invariant** ([[box-synthesis-gap]]): eliminators stay
  inferable, intros checkable, so the meta-ANF story is unaffected — the
  elaborator output must preserve this.
- **Trusted base unchanged.** Sugar lives entirely in the front-end; it emits
  core terms the existing kernel checks. No new trusted code.
- **Auditable lowering.** Ideally each sugar construct has a documented,
  mechanical desugaring (like the fixed formers have documented telescopes),
  so the front-end is reviewable against the kernel rather than magic.

## Log

- 2026-07-23: Opened as a mental-development tracker once Σ landed and made
  the multi-field-IR motivation concrete. No elaborator yet; this collects
  requirements as formers accrue.
- 2026-07-23: Sums landed ([[kernel-v1-extensions]]); added the `A + B` /
  `inl`/`inr` / `match` sugar requirement. Note the positive/negative split:
  Σ's motive is recoverable by projection (η), a sum's is not — `match` needs
  its result type from context, sharpening the checking-descent constraint.
