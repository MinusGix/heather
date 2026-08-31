---
title: FunctionIR validity certificates grow quadratically with the list environment
status: closed
labels: [compiler,proofs,performance,function-ir,design]
created: 2026-08-31
updated: 2026-08-31
---

The direct `RegionValid` certificate generator removes repeated decision
procedures, but a compiler-sized certificate is still not compact. The current
validity proposition accumulates a list of defined ports. For every node it
requires:

- `FreshPortIdEntries`, a disequality against every accumulated port; and
- `HasPortEntries` constructor paths whose length is the operand's position in
  that list.

Thus a linear chain produces quadratic proof syntax and kernel work even when
the host-side traversal is linear. In the focused generator test, an eight-node
chain checks as part of a roughly 12-second suite. Experimental 20- and
100-node versions did not complete within 60 and 90 seconds respectively.

## What it assumes from elsewhere

- **[[function-ir-validation-proof-cost]]** owns the direct generator and the
  reference-checker comparison. Assumed here: direct proof emission already
  avoids rerunning the recursive equality decisions.

Requiring monotonically increasing IDs would compress the particular
freshness argument, but it is not a satisfactory semantic restriction. Port IDs
are stable graph identity, not schedule position: the two valid `sum4`
schedules intentionally define IDs 4 and 5 in opposite orders.

## Directions

- Prove global uniqueness of stable IDs once, separately from per-schedule
  availability.
- Represent the typing/availability environment with compact lookup evidence:
  a balanced map, dense stable-ID table, or an equivalent finite-map
  abstraction rather than linear list paths.
- Consider a rank or membership relation for schedule availability so a
  permutation changes only scheduling evidence, not graph identity.
- Keep the executable reference validator and direct generator targeting the
  same proposition while comparing certificate size and kernel time.

The representation should not add a trusted lookup oracle. Compact generated
evidence must still reduce to ordinary kernel-checked terms.

## Acceptance

- Both `sum4` schedules remain valid without renumbering ports.
- Certificates for chains and nontrivial DAGs have near-linear or
  linearithmic, rather than quadratic, size and checking cost.
- A graph with at least 100 simple nodes validates quickly enough for an
  ordinary compiler test.
- A stale or malformed compiler-side model still produces a theorem rejected
  by the kernel.

## 2026-08-31: resolved by the V2 prototype

`RegionValidV2` separates a balanced stable-ID directory from schedule ranks.
The directory records each port's width and exact input/node origin, proves
global uniqueness through threaded search bounds, and uses cardinality to rule
out phantom entries. Node operands carry a directory fact plus an availability
rank, so the two `sum4` schedules validate without renumbering IDs.

The performance result depends on preserving sharing in emitted source. Named
subtree functions and opaque subtree-order/port-lookup facts prevent each
lookup from reconstructing the complete directory. Named node-list suffixes
and `NodesIndexed` stages prevent the final theorem from elaborating one giant
nested term. Before suffix staging, the final 100-node certificate item alone
took 68.9 seconds; afterward the complete focused 100-node test, including
module setup, completed in 13.66 seconds. The old relation's 100-node probe had
not completed in 90 seconds.

Both schedules, a 100-node chain, host-side malformed-model rejection, and a
stale-model/kernel rejection now pass. Adoption without converting back to the
quadratic proposition is tracked by [[function-ir-validity-v2-adoption]].
