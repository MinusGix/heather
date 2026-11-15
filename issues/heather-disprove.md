---
title: heather disprove: a counterexample before anyone pays for a proof
status: open
labels: [tooling,testing,design]
area: tactics
created: 2026-08-05
updated: 2026-09-04
---

From the 2026-08-05 riff under [[ai-facing-tooling]]. Not scheduled.

A counterexample searcher over a *statement*: enumerate small instances
of the quantified variables, evaluate both sides with the fuel-bounded
kernel evaluator, print the first failing instance with its bindings
(`xs = Cons(0, Nil), n = 1: lhs = None, rhs = Some(0)`). Type parameters
instantiate at Nat or a small finite type — sound for disproof, since a
counterexample at one instance kills the universal.

Why it earns a place: the most expensive failure mode a model has is
spending a large budget proving a mis-stated lemma, and mis-stated
*intermediate* lemmas dominate agent failures in every comparable
ecosystem. A ten-millisecond "false, here is the instance" beats any
prover feature on saved tokens.

Scope discipline for a first slice:
- Conclusion must be computable (`=` on computables, decidable
  predicates).
- Hypotheses: decidable only, generate-and-filter; hypothesis-free
  first.
- **Honesty is a hard requirement**: "no counterexample in N instances"
  must never read as "true" — the output grammar should make the two
  unconfusable, for humans and parsers alike.

## What it assumes from elsewhere
- **[[surface-declaration-generator]]** owns term/instance generation
  machinery. Assumed here: only that it can be pointed at a statement's
  telescope rather than at whole declarations.


## Set-operation compatibility customer

**[[finite-set-client-design]]** supplies a concrete compatibility claim:
raw-list length as finite-set cardinality. Validate the two representations
`[1,2]` and `[2,1,1]`, their extensional set equivalence, and unequal Nat results
before reporting a refutation. This requires evidence for the premise, not
only different computed outputs. At this concrete finite Nat example membership
comparison can be decided or proved directly.

`docs/showcase/three-small-transfer-experiences.md` specifies the human rendering and
the repair suggestion. A stuck generator or bounded search without a witness
reports its actual status; it does not claim this refutation occurred.

## Log

- 2026-09-04: Added the tiny raw-length/cardinality experience as a
  hypothesis-bearing counterexample customer.
