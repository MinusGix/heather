---
title: Interaction trees over container events, cut at fuel: check the investigation against code
status: open
labels: [effects,semantics,design,research]
created: 2026-09-24
updated: 2026-10-08
---

Owns the follow-ups of `docs/interaction-trees-fit.md` (the 2026-09-24
investigation of Xia et al., `docs/3371119.pdf`): interaction trees with
**container events** (`Cmd : Type<l>`, `Resp : Cmd -> Type<l>`) over trees
cut off at fuel, with no kernel coinduction. The doc argues this keeps
everything at one level, needs no `Type`-indexed families, and fits
`simulate`'s `converges`/`fuel_monotone` interface; this issue owns checking
that argument against real code.

## Questions, in order

1. **The depth-indexed bisimilarity conjecture** (doc §3.7). **Answered
   yes, 2026-10-08** (heather-coq `probes/ItreeDepthBisim.v`, MinusGix/heather-coq#9;
   see the Log). For deterministic trees over container events, `Π n. euttₙ`
   (inductive Tau peeling, index consumed by `EqTau`/`EqVis`, everything
   related at index 0) coincides with the greatest fixed point, provided
   the Vis clause's command equality is proof-irrelevant.
2. **The library**, once the surface can write it: `Events`, the fuel-cut
   tree, `bind`/`iter`/`mrec`, `is_trace_of` (the paper's Fig. 20, already
   inductive), trace refinement, and the bridge to
   `converges`/`fuel_monotone`. Check the doc's claim that the Fig. 5
   structural laws are definitional in this encoding.
3. **A handler**: interpret a state-event container into world threading
   (doc §6.5), to test the claim that the two leanings of
   [[effects-direction]] compose rather than compete.

Kernel coinduction (a negative `M`, doc §3) is **not** in scope; it waits
on a customer that needs liveness or concurrency.

## What it assumes from elsewhere

- **[[inductive-compiler]]** owns tier-2 (W-lowered) surface inductives.
  Assumed here: only that a recursive function-typed field (`k: Resp(c) ->
  ITree`) eventually becomes writable. Questions 2–3 wait on it; question 1
  does not.
- **[[effects-direction]]** owns the effects decision. This issue supplies
  evidence, not the verdict.
- **[[linux-syscall-trace-model]]** owns the machine trace; doc §6.1 sketches
  it as this issue's first customer.

## Log

- 2026-10-08: Q1 answered yes, in Coq: heather-coq `probes/ItreeDepthBisim.v`
  (MinusGix/heather-coq#9, no axioms). Over container events with arbitrary
  (possibly infinite) responses:

  - `eutt_gfp_omega`: the Knaster–Tarski gfp equals `Π n. euttₙ`. gfp ⊆
    approximants is unconditional. The converse merges one proof of
    `c1 = c2` per index in the Vis clause, so it assumes those proofs are
    equal (`UIP_Cmd`; free for decidable `Cmd`). For Heather: write the Vis
    clause with `sEq` (definitionally irrelevant), or with `Id` only over a
    `Cmd` that is a set. Whether it fails for a non-set `Cmd` is unchecked.
  - `euttI_iff`: the doc's single inductive family over `Nat` (base case
    relating everything at 0, `EqTau`/`EqVis` at `S n`, peeling at any `n`)
    matches the iterated-step form.
  - Usable without the gfp (Heather's predicative position): reflexive and
    symmetric with no hypothesis; transitive and a `bind` congruence by
    induction on the index; absorbs Taus. So setoid rewriting along it needs
    no coinduction.
  - Design constraint, checked: `EqTau` must consume the index (an
    inductive Tau-Tau rule fails at `spin`, `spin_not_euttT`). Index 0 must
    also relate everything, else every derivation is finite and `spin`
    again fails; that one is argued, not checked.
  - Boundary: Milner's image-infinite LTS (`Br(λn. aⁿ)` against it plus
    `a^ω`) satisfies every approximant and fails the gfp, so choice trees
    (doc §6.2) reopen Q1. Nothing the finitary route needs is lost for
    deterministic trees.
