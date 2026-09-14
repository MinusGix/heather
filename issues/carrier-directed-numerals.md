---
title: "Carrier-directed numerals: make 3 : Int solve the same problem as -3"
status: closed
labels: [frontend,elaboration,notation,stdlib,traits]
created: 2026-08-19
updated: 2026-09-14
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
- 2026-09-14: Revisited against the current tree. The recorded direct
  `as_int(-1)` refusal no longer reproduces; a lightweight independent Sign
  carrier also accepts negative arguments, nested negation, record fields,
  and generic local Numeral evidence. The remaining defect is the shared
  leftmost-numeral criterion: `let b = -(1 + a)` misses an Int anchor inside
  the operand, and `1 + a = 1` lets the right numeral impose Nat despite
  `a : Int`. Replaced it with one search for the first inference-capable
  non-numeral leaf under operator notation, used by both operator probing
  and equation endpoint order. Ordinary calls remain leaves and all-numeral
  inference keeps the Nat default. Design and boundaries updated in
  `docs/carrier-directed-numerals-design.md`; acceptance is covered by
  `carrier_numerals.rs` and the actual Int consumer in `lib_std_int.rs`.
  Compatibility controls caught why a non-numeral leaf is not sufficient:
  `one<A: Numeral>()` needs an expected result, and `identity(one())` hides
  the same need from the syntactic checking-only classifier. Candidate
  probes now run in isolated clones and skip failures; numeral-led checking
  keeps its existing expected-result hint. No numeral metavariable queue or
  general heterogeneous-operator solver is introduced (a deliberate boundary,
  not remaining acceptance work).
- 2026-09-14: Benchmark check: furnace reports shape-only, 18 comparisons
  within thresholds and 93 timing comparisons skipped for the committed
  desktop baseline's CPU/toolchain mismatch (exit 3). The desktop run against
  that baseline reports 28 timing regressions (exit 1), including
  `nat/step-once`, `nat/step-into-closed-body`, and arithmetic normalization.
  This is not a green timing gate. Verified no diff in `crates/kernel`,
  `Cargo.toml`, `Cargo.lock`, or `scripts/bench`; that script builds only the
  kernel package, so these flags do not measure this elaborator change.
  The existing owner of comparable timing gates is
  [[perf-tracking-consistent-environment]]. No baseline was rewritten.
- 2026-09-14: Final verification (2026-09-14): all six focused carrier-numeral tests pass, including direct and indirect result-only generic calls. The full scripts/test passes: 2,623 passed, 0 failed, 5 ignored. Existing operator, library Int, frontend benchmark smoke, and native certificate acceptance are included. Acceptance complete; the benchmark timing limitation is recorded above.
