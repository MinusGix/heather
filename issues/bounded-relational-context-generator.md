---
title: Prototype bounded context certificate generation with explicit rules
status: closed
labels: [relations,setoids,metaprogramming,testing]
created: 2026-09-05
updated: 2026-09-04
---

Exercise the context proof constructors with a bounded, explicit source-level
prototype. This is not completion of [[setoid-auto-lifting]]: boxed-code analysis,
meta-layer integration, recursion, dependent contexts and search remain there.

## Acceptance

- Generate an independently checkable preservation definition for an ordinary
  function with fixed parameters, nested applications and repeated occurrences.
- Select relations from an explicit requested contract and operation signatures.
- Report a missing observer certificate with its exact goal and binder context;
  supplying it and rerunning succeeds without silently changing assumptions.
- Leave raw length unproved at membership equality, and link an independently
  checked refutation. Reject a false supplied certificate or wrong operation map.
- Bound traversal and reject ambiguous rules. Leave the caller's session unchanged.
- Supply a runnable driver, documented scope, and final plain Furnace validation.

## Related

- [[relational-transfer-core]] owns the shared rules.
- [[setoid-auto-lifting]] owns the broader generator and contextual rewriting.
- [[generators-in-the-language]] owns migration into the meta layer.

## Log

- 2026-09-05: Started the authorized bounded generator round. Source-level
  prototype, explicit driver, and acceptance tests are in place; validation is
  in progress. See `docs/showcase/relational-generator-round.md` for the prototype boundary.
- 2026-09-04: Focused Furnace suite: 13 passed. Corrected expression emission to reconstruct supported AST nodes rather than slice grouping parentheses from parser spans. Full-suite and standalone-driver verification are in progress.
- 2026-09-04: LANDED: bounded source-level generator, explicit driver, and saved independently checked source. Thirteen focused tests pass; final plain Furnace suite: 2,328 passed, 0 failed, 5 ignored. All four driver modes returned expected exit codes, blocked modes emitted no source, and the saved module passed ordinary heather check. The broader boxed-code/meta-layer implementation remains with setoid-auto-lifting.
