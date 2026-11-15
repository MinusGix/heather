---
title: Recover a context and apply one supplied relation proof
status: closed
labels: [relations,setoids,metaprogramming,testing]
created: 2026-09-04
updated: 2026-09-04
---

Connect [[bounded-relational-context-generator]] to a theorem-writing client:
recover a shared context from the two goal endpoints and a named local relation
proof, generate its compatibility certificate, and apply it to that proof.

## Acceptance

- Generate a checked ordinary proof for repeated occurrences beneath append.
- Preserve unchanged occurrences, use fresh names, and reject unexplained
  differences or reversed proofs without guessing symmetry or reduction.
- Reuse the existing certificate planner; expose missing observer obligations
  and resume when their evidence is supplied.
- Refuse false certificates and leave length's missing compatibility unproved.
- Keep the original assumptions, check goals without axioms, leave the caller's
  session unchanged, and bound the structural fragment explicitly.
- Supply runnable examples and independently check generated source through
  Furnace; finish with the required plain full test suite.

## Boundaries

This is a source-driver entry point over an ordinary theorem hole. Native tactic
syntax, boxed-code/meta-layer integration, compound proof endpoints, and
relational calc remain with [[setoid-auto-lifting]]. It does not extend the
existing identity `cong` solver or claim a complete preservation procedure.

## Log

- 2026-09-04: Began the authorized single-rewrite round. API, source driver,
  proof-construction tests and `docs/showcase/contextual-rewrite-round.md` are in place;
  verification is in progress.
- 2026-09-04: Initial 19 focused tests passed. An added identity control exposed reliance on an input import of relation_props; both generator entry points now add absent helper imports without duplicates. The parser requires imports before declarations; a negative regression preserves that restriction. Expanded checks are running.

- 2026-09-04: Completed structural recovery, ordinary proof generation, and bounded refusal controls. All five demo modes behaved as expected; saved generated source passed an independent CLI check. Plain Furnace suite passed: 2,336 passed, 0 failed, 5 ignored (21 setoid/generator/rewrite tests). An interrupted first full run was replaced by this completed run.
