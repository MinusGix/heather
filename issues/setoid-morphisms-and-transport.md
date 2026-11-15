---
title: Transfer operations and theorems across related representations
status: open
labels: [stdlib,mathematics,setoids,automation,design]
area: mathematics
created: 2026-09-02
updated: 2026-09-04
---

Grow from respectful functions to homomorphisms, embeddings, and equivalences,
then explicit predicate, theorem, and algebraic-structure transport. Setoids
are one application of the shared heterogeneous relational calculus.

## Scope and acceptance

- Separate certifying an existing operation, constructing a new operation,
  transferring a theorem, and assembling a transported structure. List the
  input evidence each needs; compatibility alone cannot construct a function.
- Keep directional correspondences useful. Prove equivalences only with the
  necessary coverage, reflection, and inverse evidence; preserve assumptions
  and restricted domains in transferred statements.
- Validate manually with unreduced rationals, a closed subtype, a
  function-valued representation, and two implementations of one abstraction.
  Include a non-transferable observation and a genuinely directional example.
- Prove one abstract theorem once and instantiate/transfer it across two
  presentations. Prefer this over translating representation-specific proofs.
- Real-presentation comparison remains the forcing larger customer; initial
  examples must not wait for all real constructions to land.
- Judge quotient competitiveness by actual proof work: contextual rewriting,
  calculation chains, higher-order consumers, and precise remaining goals.
  Do not assume intricate quotient proofs are automatically easier, or treat
  the absence of unrestricted identity elimination as an ergonomic verdict.
  Record the actual dependent contexts needing extra structure.

## What it assumes from elsewhere

- **[[relational-transfer-core]]** owns transfer rules and relation properties.
- **[[setoid-core-api]]** owns setoid morphisms and pointwise comparison.
- **[[relation-indexed-algebra]]** owns reusable relation-indexed theories.
- **[[subtype-transfer-and-evidence]]** owns subtype lifting and evidence policy.
- **[[dependent-relational-transport]]** owns the dependent stress test.
- **[[setoid-auto-lifting]]** owns boxed-code proof generation.
- **[[real-presentation-comparison]]** owns concrete real maps and assumptions.
- **[[datarepr-separation]]** owns executable representation synthesis. Share
  relational certificates where appropriate without taking over its compiler
  interface, invariants, outcomes, or cost policy.

Reference guide: `docs/showcase/setoid-transfer-references.md`.

## First interface derivation probe

Use **[[finite-set-client-design]]** as the small concrete abstraction boundary:
empty/singleton/union/membership and cross-view image, with explicit observation
laws and an extensionality principle. Derive compatibility signatures from a
chosen relational interpretation; do not infer mathematical operation semantics
from field types. Compare two implementations via heterogeneous operation
certificates, rather than assuming self-compatibility proves correspondence.

Whole-interface generation should start from explicit abstract carriers and
operation dictionaries. A list carrier does not pick sequence, multiset, or set
semantics by itself, and current module organization is not abstract sealing.

## Log

- 2026-09-02: Filed separately from auto-lifting so concrete mathematical
  transport determines what automation should eventually produce.
- 2026-09-04: Expanded from the agreed relational-transfer design; implementation remains open.
- 2026-09-04: Added finite sets as the client-first interface/correspondence probe.
