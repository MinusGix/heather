---
title: Ownership: the universal value as a native value tagged with its code (sixth experiment)
status: open
labels: [ownership,library,design]
area: heather-in-heather
milestone: [nh-ownership]
created: 2026-11-25
updated: 2026-11-25
---

The sixth ownership experiment (docs/language/ownership-design.md §18.4 item 4). Five experiments built the checker so that its soundness theorem is stated once, over a reflected body and a meaning function. Their headline results were two: a source function pins to its reflected body's meaning by `refl`, and a residual is discharged by the source's own proof by conversion. Both were shown only where every object is a `List<Nat>`. A real function has records, lists of records and type parameters, and the library's universal value (`Val`, `value_steps.hthr`) would make the meaning compute on an encoding.

The proposal under test: **the universal value is a native value tagged with its code.**
- `Shape` is a closed, first-order code: a word, a sequence, or a named type.
- `El(tys, c)` decodes it by large elimination.
- A second environment gives each named type its structure: opaque, or a record's field paths.
- `Dyn(tys)` is a code with a value of its decoding, used as the single sort of `StepModel`.

## Scope

New files only: `lib/lang/ownership/coded.hthr` and `lib/_tests/lang/ownership/coded_tests.hthr`.
1. Codes, the decoding, the environments, `Dyn`, a cast that computes, and `decide_self` without UIP.
2. The step model at `Dyn` with its `StepModelLaws`.
3. A fixture meaning.
4. Pins: a field of an element of a list of records, a write of one, a generic function at an open `T`, an `if h:` guarding a read, and calls passing a record and a window.
5. Residuals as the source writes them.
6. The control through `Val`.
7. Cost at doubling sizes against uncoded bodies.

Refuted by any of these: a pin over a record that is not a conversion; a cast that does not reduce on closed codes; UIP needed; a universe restriction; non-linear cost or a large factor.

## What it assumes from elsewhere

- **[[ownership-site-facts-into-the-checker]]** owns the checker whose pins, residuals and restated conjunction this mirrors in a fixture.
- **[[reflected-languages-typed-by-construction]]** (closed) measured code-indexed syntax; this keeps the syntax untyped and types only the values.
- **[[uip-from-decidable-equality]]** was expected to be needed and was not.

## Done when

Items 1 to 7 are answered with probes in `lib/_tests`, the log reports what pins by `refl` and the measured shapes, and `ownership-design.md` §18.4 has the result as its item 4.

## Log
