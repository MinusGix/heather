---
title: Polynomial functors as the vocabulary for interfaces, events and wiring
status: open
labels: [semantics,effects,design,research]
area: interaction-trees
created: 2026-09-24
updated: 2026-09-24
---

Investigate **polynomial functors** as the shared vocabulary for program
interfaces: event signatures, syscall boundaries, and how components are
wired together.

## Why

- Heather's branching data is already containers (`W`, `Wf`), and
  `docs/itrees/interaction-trees-fit.md` §2 recommends container events
  (`Cmd`, `Resp`). Polynomial functors are the algebra of containers:
  composition, parallel product ⊗, and **dependent lenses** (morphisms of
  interfaces, forward on commands and backward on responses). Those are the
  subevent inclusion `E -< F`, handler composition, and plausibly a syscall
  or calling-convention boundary.
- Aberlé (2026) builds exactly the verification side: polynomial functors as
  interfaces, free-monad Kleisli maps as implementations, dependent
  polynomials as pre/postconditions, composed by wiring diagrams, with Mealy
  machines as coalgebraic operational semantics, all in dependent type
  theory.

## Reading

- Niu, Spivak, *Polynomial Functors: A Mathematical Theory of Interaction*
  (monograph) — `docs/papers/2312.00990.pdf`.
- Aberlé, *Compositional Program Verification with Polynomial Functors in
  Dependent Type Theory* (2026) — `docs/papers/2604.01303.pdf`.

## Acceptance (an investigation)

A note answering: (1) which constructions are writable over today's
`Type<l>`/Σ/Π at one level (a lens should be); (2) whether
[[linux-syscall-trace-model]]'s events and [[named-abi-contracts]]'
conventions are naturally polynomials and lenses; (3) whether Aberlé's
dependent-polynomial specifications could state the loop certificates'
pre/postconditions more compositionally than the current records.

## What it assumes from elsewhere

- **[[interaction-trees-container-model]]** owns the event container.
  Assumed here: only its `Cmd`/`Resp` shape.

## Log

- 2026-11-05: gardener: cites a file it shares with [[cost-aware-semantics]] (`docs/itrees/interaction-trees-fit.md`).
