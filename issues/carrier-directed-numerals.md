---
title: "Carrier-directed numerals: make 3 : Int solve the same problem as -3"
status: open
labels: [frontend,elaboration,notation,stdlib,traits]
created: 2026-08-19
updated: 2026-08-20
---

Numerals currently infer `Nat` unconditionally, with one checking-position
exception for `Fin`. That makes this work:

```heather
-OfNat(3)
```

but not this:

```heather
-3
```

The parser is not the missing piece. `-3` already has the unsurprising syntax
tree “prefix `-` applied to numeral `3`”; inventing an atomic negative integer
literal would only hide the fact that positive `3 : Int` has the same gap.

The desired rule is carrier-directed numeral elaboration. A numeral checked at
a carrier `A` should resolve that carrier's canonical embedding of `Nat` (an
`OfNat`-shaped class or equivalent registry entry), while inference with no
carrier may retain today's `Nat` default. Once `3` can elaborate as
`OfNat(3) : Int`, `-3` naturally becomes `neg(OfNat(3))` through the ordinary
prefix designation; there is no separate negative-literal semantic path.

## Design questions

- Whether the embedding is indexed by the numeral value, as Lean's `OfNat` is,
  or is one operation `Nat -> A`. Heather's existing value-indexed classes can
  express either, but the latter matches `Int::OfNat` and avoids one instance
  per numeral.
- How an expected carrier reaches a numeral nested under a homogeneous prefix
  operator. Today operator resolution probes an applied operator's operand by
  inference, so the numeral chooses `Nat` before the surrounding result can
  teach it `Int`. This needs metavariable/expected-type flow, not a parser
  special case for `-`.
- Whether a bare numeral in a genuinely inference-only position defaults to
  `Nat` immediately or leaves a constrained carrier metavariable until the
  enclosing expression settles it. Existing Nat-heavy source must remain
  deterministic and unchanged where no other carrier evidence appears.
- The existing `Fin` numeral rule must remain the bounds-checking interpretation
  at `Fin`, not be accidentally routed through a generic embedding.

## Acceptance

- Positive numerals check at `Int` through the same public embedding used by
  named source: `3 : Int` elaborates definitionally as `OfNat(3)`.
- `-3 : Int` is precisely prefix negation of that positive numeral and computes
  as `NegSucc(2)`; the AST contains no negative-literal node.
- Numerals at `Nat` and `Fin` retain their current terms and diagnostics.
- A second carrier can provide its own embedding without affecting `Nat` or
  `Int`, and a carrier with none gets a source-directed resolution diagnostic.
- Open uses and nested operator uses are covered, not only closed computation.

## What it assumes from elsewhere

- **[[prefix-negation-notation]]** owns unary `-`; this issue owns only the
  numeral nested beneath it.
- **[[notation-extensibility]]** owns the general boundary between fixed syntax
  and carrier-directed meaning.

## Log

- 2026-08-19: Split from the unary-negation implementation. The round chose the
  semantic equation `-3 = -(3)`, and refused an Int-only parser lowering:
  positive and negative numeral notation should gain carriers together.
- 2026-08-19: Landed as the single-operation `Numeral<A>` class described in
  `docs/carrier-directed-numerals-design.md`. Checking at a non-Nat/non-Fin
  carrier resolves `ofNat : Nat -> A`; inference still defaults to the exact
  historical Nat term. Expected results, non-numeral operator siblings, and an
  equation's right endpoint provide the bounded bidirectional anchors needed
  by `-3`, `3 + a`, and `3 = OfNat(3)` without delayed metas. `Int` registers
  its constructor, generic `<A: Numeral>` source resolves through local
  evidence, missing instances show the ordinary search trace, and no negative
  literal node or carrier-specific parser rule was added.
- 2026-08-20: Reopened from the standard-library review. The promised negative
  numeral path is not actually accepted in a direct Int checking position:
  with `as_int : Int -> Int`, `as_int(-1)` reports that the operand has type
  `Nat` where `Int` was expected. The landed tests cover a positive numeral at
  an expected carrier and prefix negation over a non-numeral carrier value, but
  not their composition. Acceptance still requires `-1 : Int` to flow the
  expected result carrier through prefix-operator resolution to the numeral.
