---
title: Could the ownership design's reflected languages be typed by construction? Measure a type-indexed and a code-indexed family
status: open
labels: [kernel,elaborator,design,ownership]
area: heather-in-heather
milestone: [nh-ownership]
created: 2026-11-25
updated: 2026-11-25
---

An investigation, asked for by Minus: could the new reflected languages of `docs/language/ownership-design.md` (level 1, level 2, and the steps of a place) be typed by construction, and what stands in the way?

[[ownership-steps]] chose untyped steps interpreted in one universal value type, for two reasons it recorded: a step typed by its source and target is an inductive family indexed by `Type`, "a universe above what the kernel evaluates cheaply (Tarski universes; no data quantifies over `Type` in the library)", needing an existential over each intermediate type; and a shape universe with a list of values inside the value type is a nested inductive, which the elaborator refuses (`docs/inductives/mutual-inductive-design.md` §1), so it wrote a mutual group. Every reflected language in the tree is untyped syntax with typing recovered by synthesis, presumably for the same reasons. Neither cost has been measured.

## Scope

A measurement and a judgment, with small probes; no change to the kernel or the elaborator.

- **A family indexed by types.** Write typed steps as a family over `Type` (source and target), a chain of them, their denotation, and an apartness decider on two chains. Measure what the kernel pays to elaborate the declarations and to evaluate the decider and a denotation, against `lib/lang/ownership/steps.hthr` on the same inputs. Say where the cost is (the recursor's motive, the gate, conversion at the indices, universe levels) and whether it is a shape or a constant.
- **A family indexed by codes.** The same with a small data universe of shapes as the index and a decoding to types. Measure the same things. Say what the elaborator refuses on the way (a nested occurrence, a decoding in an index) and which existing design note owns each refusal.
- **What exists.** `issues/indexed-families.md`, `issues/indexed-families-at-any-index-type.md` (closed), `issues/indexed-family-recursion-gate-cost.md` (closed), `issues/nested-inductives-container-fields.md` (open), `docs/inductives/` (`inductive-indexed-lowering.md`, `per-instantiation-type-codes-design.md`, `wf-shape-code-design.md`, `mutual-inductive-design.md`), `crates/kernel/DESIGN.md` on universes and codes. Read them first; much of the answer may be written down.
- **The judgment.** For each of the three languages the design needs (steps; level 1's terms; level 2's values and operations): would typing by construction remove real proof work (name the lemmas in `steps.hthr`, `value_steps.hthr` and `place_check.hthr` that exist only because a term may not fit), what would it cost, and is the blocker the kernel, the elaborator, or neither.

## Done when

The probes are in `lib/_tests` (or a scratch module named in the log if they should not stay), the measurements are reported as shapes with what dominates, and the log gives a recommendation: stay untyped, index by codes, or index by types, with what would have to be built for the second or third.

## What it assumes from elsewhere

- **[[nested-inductives-container-fields]]** owns nested inductives at the surface.
- **[[ownership-steps]]** (closed) owns the untyped steps this is measured against.
