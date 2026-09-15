---
title: Reduce checker cost for proof-carrying parser composition
status: open
labels: [frontend,parsing,performance,proofs]
created: 2026-09-15
updated: 2026-09-15
---

## Problem

The independent calculator grammar proof exposes substantial checking cost in
composing `Result<Certified<...>,Failure<...>>`. Initial versions exceeded the
6 GiB test rail, both with the default gate and with serial checking. Splitting
production bodies, flattening `Certified`'s success fields and using generic
Result eliminators allowed the full theorem and its refusal tests to check.
The serial diagnostic run still took 139 seconds for the calculator target.
This is an observation about the checked fixture, not an attribution to any
particular compiler subsystem.

The old shape nested `parsed: Success(source,begin)` and
`evidence: R(source,begin,parsed.end,parsed.value)`. The current shape exposes
value/end/forward/evidence directly. Nested concrete Result matches were
replaced by `result::fold` and `and_then`; see `expr_body`, `factor_body` and
the parentheses helpers in `docs/showcase/calc_parser.hthr`. Generic higher-order
certified finishing was also more expensive in this client than small concrete
production helpers. Do not infer proof erasure from successful projections.

## Scope and protocol

Profile elaboration, generated types/terms, conversion and retained state
separately, using a reduced production-composition fixture and the full checked
calculator. Identify the contribution of concrete indexed record instantiation,
nested elimination and generic dictionary arguments. Also inspect `selected_head`'s use of the list eliminator when only the head
witness is needed. These are hypotheses to investigate, not established root
causes.

Use `scripts/test`, keep the resource rails, isolate loading from proof checking,
and compare the same gate width. The acceptance fixture currently selects one
worker; establish the default parallel-gate cost separately. Record checked
outputs/refusals and deterministic counters before interpreting wall time.
Preserve the open grammar theorem, source/span invariants and empty axiom audit.

## Acceptance

- A reduced reproducer and an attributed cost explanation.
- A cheaper checked representation or implementation, with the same guarantees.
- Both ordinary and proof-carrying parser clients remain usable.
- No larger cap or silently trusted image substituted for actual checking.

## What it assumes from elsewhere

- [[parser-grammar-soundness]] owns the independent grammar and success theorem.
- [[parser-certificate-ergonomics]] owns user-facing certificate composition.
- [[parser-cached-cursor-cost]] owns cursor traversal and representation costs;
  this issue owns checking semantic evidence even on short inputs.
