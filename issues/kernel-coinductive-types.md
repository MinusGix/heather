---
title: Coinductive types in the kernel, planned now
status: open
labels: [kernel,coinduction,metatheory,design,effects]
area: kernel
created: 2026-10-21
updated: 2026-10-21
---

Minus's decision (2026-10-21): plan the kernel round for coinduction now,
instead of waiting for a customer that needs liveness. heather-coq has
already probed the neighbourhood (`probes/ItreeDepthBisim.v`,
MinusGix/heather-coq#9) and can probe further where there are worries. His
words: "might as well get full proper power sooner".

## Why

The interaction-tree library (`docs/itree-core-round.md`,
`docs/itree-refinement-round.md`) is finite. Trees are cut at fuel, and a
program is a growing family. That states safety, refinement and
termination of deterministic programs well. It cannot state liveness over
unbounded interaction ("every request is eventually answered"), fairness,
or concurrency, and fuel has to be hidden inside `Program` so that
statements do not name it. [[kernel-v0-scope]] put coinduction out of v0,
and [[effects-direction]] has listed it as the cost of interaction trees
since July.

## Options for the design round

1. **A negative M former** (final coalgebras of containers, observed by
   `out`). It comes with `corec` and the β rule `out(corec(f, x)) ≡
   map(corec(f), f(x))`, which fires only under `out`, so conversion stays
   decidable. There is no definitional η. Bisimilarity is a propositional
   relation, and "bisimilar implies equal" is either an axiom in the same
   family as the funext tier 2 already assumes, or left out, with
   bisimilarity as the working equivalence. This is the negative
   presentation (copatterns, primitive projections), which avoids the
   subject-reduction failure of Coq's positive `CoInductive`. It is the
   most likely answer.
2. **M derived from W and Nat as a limit of approximations** (Ahrens,
   Capriotti and Spadotti, "Non-wellfounded trees in HoTT", 2015). This
   needs no kernel change. Heather's fuel-cut trees already are the
   approximation chain, and an M element is a coherent sequence of them.
   But equality needs funext, and `corec` computes only level by level.
   It is worth building first as the cheap probe of what the library
   would gain, and it is also how Lean would have to receive exported
   coinductive terms (see below).
3. **Guarded recursion with clocks** (Guarded Cubical, CloTT). Productivity
   is enforced by typing, and coinduction comes through Löb. This is the
   most power and the most metatheory, and it interacts with DeLaM's
   layers as a modality ([[multimodal-modalities]] lists it as a road to
   liveness).
4. **Sized types**: not recommended. Agda's experience with consistency
   is the warning.

## Questions for heather-coq

- Normalisation and decidable conversion with option 1's β rule alongside
  the existing formers (W, Wf, IWf, layers), and with the strip rule and
  `sEq`.
- Whether "bisimilar implies equal" is consistent with Heather's axioms
  (funext, and whatever the setoid model validates), and whether it
  should be stated over `Id` or `sEq`.
- How codes and quotation (layer m) see an M type: can a `Code` mention
  one, and does `corec` under a quote stay inert?
- The depth-indexed probe's result in reverse: that `Π n. euttₙ` over the
  approximations equals bisimilarity on the M type.

## Constraints from elsewhere

- **Export** (`docs/export-fragment-design.md`). Lean 4's kernel has no
  coinductive types, and mathlib builds M types as limits, so an exported
  M term would arrive as option 2's construction on the Lean side, possibly
  without option 1's β rule holding definitionally. Minus (2026-10-21):
  export does not have to match the language; Heather works differently
  and may grow more special. So this is a note for the exporter (a
  realisation, or an unexported fragment), not a constraint on the choice.
- **The tree library stays.** Coinductive trees would come with `approx(n)`
  into today's fuel-cut trees, so every finite theorem, including the
  native `Sim` stated over approximations, carries over unchanged.

## Scope of the first round

A design document (`docs/kernel-coinduction-design.md`) choosing between
the options, with heather-coq probes for the questions above. Then a
kernel round that adds the former, its typing and conversion rules,
`Debug` gated by `node()` (`crates/kernel/src/fmt.rs`), and the
elaborator surface (`coinductive` declarations, or `codata` with
copatterns).

## What it assumes from elsewhere

- **[[effects-direction]]** owns what the surface's effectful programs
  denote. Assumed here: only that some of them will want infinite
  behaviour.
- **[[interaction-trees-container-model]]** (closed) recorded the
  depth-indexed probe this round builds on.
