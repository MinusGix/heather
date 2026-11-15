---
title: Build a checked Heather-side API for declarations and proof construction
status: closed
labels: [metaprogramming,elaboration,proofs,design]
area: tactics
milestone: [tac-host-interface]
created: 2026-09-08
updated: 2026-10-28
---

The reusable x86 callee round (`cb877f2`) still assembles scoped names, dependent
applications, intermediate equalities, and proof bodies in Rust. Structured
emission helps, but expression leaves and references can still be strings.
A Heather generator should be able to construct a small checked declaration
group and publish it in the caller's scope, with useful errors at construction.

## Acceptance

- Choose one bounded customer from `crates/cli/src/native/calls.rs`: a successor
  witness, frame-preservation lemma, or trace-composition declaration group.
- Design typed/scoped references, binders, applications, expected-type checking,
  and named intermediate facts without resolved-name string round trips.
- Preserve hygiene and source provenance; explain how a group refers to earlier
  declarations and how failed construction avoids partial publication.
- Separate pure code construction from host checking/publication capabilities.
  Initial host implementation may remain Rust; clients should be Heather code.
- Kernel-check all output. Construction typing does not by itself establish
  source-semantic preservation, and a generator's correctness is a separate proof.
- Exercise open types, neutral arguments, dependent binders, and malformed output.
- Compare the small customer with its current Rust producer before planning a
  wholesale migration. API shape and implementation sequence remain open.

## What it assumes from elsewhere

- [[host-elaboration-interface]] owns access to the active compiler and environment.
- [[scoped-declaration-generators]] owns invocation and scope publication.
- [[generators-in-the-language]] owns the broader migration.

## Log

- 2026-10-21: Retargeted by docs/metaprogramming/host-elaboration-interface-design.md §10: the named customer (crates/cli/src/native/calls.rs) was burned in B1 (PR #90). This issue becomes round R4 of that design: a `Publish(group)` host request that kernel-checks a small declaration group and publishes it in the caller's scope only if every member passes.
- 2026-10-26: Precedent: mengine's kernel API (docs/surveys/mengine-survey.md §1.2, §6) builds terms only through constructors that type-check and return null on failure, each node carrying its type and minimal context, so errors surface at construction. It makes every caller trusted; here the output stays kernel-checked as this issue requires, so take the error-at-construction shape, not the trust model.
- 2026-10-28: Round R4 built (docs/metaprogramming/host-elaboration-interface-design.md §19). `generate g(args);` runs a `Tac<List<Decl>>` at module level; new requests Assume (a parameter or binder local under a given one), Ctors (a type's constructors, fields and constructor function, by R3's twice-recorded skeleton), AsType and Publish; `Expr` gains Blank (a hole the application's domain check solves), Pi and Equation. Members are read back in the run (parameter telescope, body against statement, no unsolved holes), then elaborated as the same source declarations with checked-term leaves, all in one session transaction: a refused member publishes nothing. Customer: lib/std/tactic/derive.hthr's `congruences(T)`, `T::cong_C` per constructor by `cong`/`trans`; against lib/kernel_model/kernel_reduction.hthr's hand-written `Tm::cong_*` the statements match up to case, except `cong_proj`/`cong_run`, which hold their non-`Tm` field fixed (not migrated). Probes lib/_tests/std/tactic/derive_tests.hthr (11 refusals: wrong body, unchained parameters, goal in a generator, rollback, name collisions, dependent field, non-type), crates/elab/tests/tactic_generate.rs (cross-module use, parser refusals, forged references). Follow-ups: [[generate-group-internal-references]], [[generate-in-sections]], [[generator-ctors-open-types]] (the open-types axis); found on the way: [[literal-needs-module-names-wrong-module]].
