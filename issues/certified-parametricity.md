---
title: Automatically prove parametricity of supported functions
status: open
labels: [metaprogramming,relations,proofs,design]
created: 2026-09-04
updated: 2026-09-04
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
