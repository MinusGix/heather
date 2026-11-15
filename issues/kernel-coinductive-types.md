---
title: Coinductive types in the kernel, planned now
status: open
labels: [kernel,coinduction,metatheory,design,effects]
area: kernel
created: 2026-10-21
updated: 2026-10-22
---

Minus's decision (2026-10-21): plan the kernel round for coinduction now,
instead of waiting for a customer that needs liveness. heather-coq has
already probed the neighbourhood (`probes/ItreeDepthBisim.v`,
MinusGix/heather-coq#9) and can probe further where there are worries. His
words: "might as well get full proper power sooner".

## Why

The interaction-tree library (`docs/itrees/itree-core-round.md`,
`docs/itrees/itree-refinement-round.md`) is finite. Trees are cut at fuel, and a
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
   bisimilarity as the working equivalence. (Correction, 2026-10-21: tier
   2 does not assume funext; `lib/std/itree/itree.hthr` states its laws up to
   `ITree::Same` because Heather assumes none.) This is the negative
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

- **Export** (`docs/library/export-fragment-design.md`). Lean 4's kernel has no
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

A design document (`docs/kernel/kernel-coinduction-design.md`) choosing between
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

## Log

- 2026-10-21: Design written, for review: `docs/kernel/kernel-coinduction-design.md`.
  Recommends option 1 in its **indexed** form (shapes depend on the index,
  children's indices computed, nothing stored), introduced by a
  **primitive corecursor** (each child a new seed or an existing tree, so
  constructors are exact under `out`), β under `out`, no η, no
  identification axiom; guarded recursion deferred, sized types rejected.
  Library probe checked in (`crates/elab/tests/coinduction_probe.rs`): the
  sum-of-coalgebras encoding `Nu` already has `out ∘ unfold` by `refl` but
  sits a level above its events (`ITree::bind` at `Nu` is `LevelMismatch`),
  and the limit encoding `Lim` is small but coheres only up to `Same` and
  has no usable `out`; a kernel `M` is `Nu` with the level dropped. Answers
  for the questions above, as proposals for heather-coq: the relation at
  `M` by observations (`∀ n. MRelₙ`), never mentioning the carrier (design
  §9 Q1); bisimilarity's shape equation over `Id` with `J`, since `sEq` has
  no eliminator after `transp`'s removal; the bridge `Bisim ⇔ Π n.
  Same(approx)` needs UIP on the shapes (§4). `Sim`'s converse has a
  kernel-free route too (§6.1).
- 2026-10-21: Kernel round landed (design §10 step 3, on Minus's "Let's
  implement now", ahead of heather-coq's §9 check): `Type::M`,
  `Term::Corec`, `Term::Out` and their values, typing at layers p and m,
  β under `out` in both reducers from one schema (`term::m_out_corec`),
  conversion of design §2.1 in both checkers (structural `M`, corec
  congruence by coalgebra, `corec` against anything else refused, `out`
  neutral by its scrutinee), module-image and Merkle tags, export refusal.
  `crates/kernel/tests/m.rs` covers the four axes with the negative
  controls (two corecs of one tree, corec against a neutral, `t` against
  `in(out t)`, the copying coalgebra); `M`, `corec` and `out` joined the
  random and well-typed generators and the evaluator differential. Still
  open: heather-coq's §9 Q1–Q3 (the relation, decidability, the bridge),
  the elaborator round (§10 step 4) and the library (§10 step 5).
- 2026-10-22: Elaborator round (design §10 step 4) implemented: [[codata-elaborator]], `docs/inductives/codata-elaborator-design.md`. It needed one more kernel change: bodied term definitions at layer p in Ψ, since `M` has no codes and every declaration was bound at c. Follow-ups are [[codata-indexed]] (`Bisim`/eutt need it), [[codata-nested-guards]] and [[codata-codes]]. Next is the library (§10 step 5), milestone `it-coinductive`.
- 2026-10-22: Codes round (design §10 step 6, brought forward): `TmM`, the four `ty_m`/`tm_m`/`tm_corec`/`tm_out` branches, and `M`/`corec`/`out` at layer c, so codata declarations are bound at c and the round-1 p-layer extension is gone (`docs/kernel/kernel-m-codes-design.md`, [[codata-codes]]).
- 2026-11-05: gardener: cites a file it shares with [[codata-up-to-friends-round-2]] (`docs/inductives/codata-elaborator-design.md`); [[export-codata-m]] (`crates/kernel/tests/m.rs`); [[formal-power-series]] (`docs/inductives/codata-elaborator-design.md`); [[kernel-refusal-without-a-checking-site]] (`crates/kernel/src/fmt.rs`); [[tier2-fragment-extensions]] (`docs/itrees/itree-core-round.md`).
