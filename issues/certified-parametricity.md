---
title: Automatically prove parametricity of supported functions
status: open
labels: [metaprogramming,relations,proofs,design]
area: tactics
created: 2026-09-04
updated: 2026-09-24
---

Treat parametricity as a property that a certifying program can automatically
prove for a particular definition. Heather's intensional code access prevents
assuming unrestricted parametricity of all well-typed programs; it does not
prevent deriving strong per-function relational theorems.

## Acceptance

- Generate relational interpretations and kernel-checked proof terms for a
  useful supported fragment, beginning with polymorphic list operations.
- Quantify over admissible relations and expose constraints explicitly. A
  single instance of respectfulness is not the full parametricity theorem.
- Handle opaque constants via supplied relational certificates; record code
  observers as explicit boundaries needing their own rules or obligations.
- Demonstrate reuse of one parametricity theorem for setoid compatibility and
  correspondence between implementations, including higher-order arguments.
- Exercise one dependent signature with the dependent transport owner. Account
  for universes, contextual/modal levels, and proof-relevant witnesses rather
  than importing a pure-type-system translation unchanged.
- Show a positive automatic example and a code-inspection example for which
  the proposed general relational statement cannot be automatically justified.

## What it assumes from elsewhere

- **[[relational-transfer-core]]** owns relational interpretations of functions.
- **[[setoid-auto-lifting]]** owns compositional certificate generation.
- **[[dependent-relational-transport]]** owns dependent relation requirements.

Reference: `docs/proofs-for-free-bernardy-jansson-paterson-2012.pdf`; its
pure-type-system result is background, not a theorem about Heather.

## Log

- 2026-09-04: Filed from the setoid and general transfer design discussion.
- 2026-09-24: Two leads (2026-09-24). (1) Beyond per-function certificates there is a *layer* question: code at layers c/p cannot observe code (□ and the recursors are layer m), so free theorems plausibly hold for every layer-p definition as a metatheorem, with only layer-m definitions needing per-function certificates. If true, it would tell the generator which definitions need no evidence at all; it is a ch. 07-style argument, not a generator feature. (2) Altenkirch, Chamoun, Kaposi, Shulman, *Internal Parametricity, without an Interval*, POPL 2024 (`docs/2307.06448.pdf`): parametricity as a small MLTT extension. Background for what an internal statement would look like, not a proposal to adopt it.
