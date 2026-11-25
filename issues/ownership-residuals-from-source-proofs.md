---
title: Discharge a checker's residual from the proof the source carries: the pin, the shape of the term, the kernel's cost
status: open
labels: [ownership,library,design]
area: heather-in-heather
milestone: [nh-ownership]
created: 2026-11-25
updated: 2026-11-25
---

The first of three untested points in `docs/language/ownership-design.md` §18.4: discharging a residual obligation from the proof the source already carries. The design's sixth stage (every `runtime fn` moved to the new pipeline) stands on it, and every experiment so far discharged its residuals with a hand-written term and `omega`.

## Scope

- **Source functions that carry their proofs**, written as ordinary Heather over lists: one that reads an element under a parameter proof (`inside: ∥i < xs.len()∥`, the arena's `read` in miniature); one that writes an element while holding a view of a later window, its apartness from a hypothesis of an `if`; one that calls another and passes its own proof on.
- **Each one's body by hand in the checker's language** (`lib/lang/ownership/call_check.hthr`, extended only if a residual kind is missing: a bound, `Below(i, n)`).
- **The pin**: the reflected body's meaning equals the function, by conversion.
- **The discharge**: each residual, stated at the reflected environment's words, proved from the source function's own hypothesis through the pin. The proof term must have a mechanical shape a generator could emit from the function's elaborated body (which holds the proof at that site, in that context): say what the shape is.
- **Cost**: what the kernel pays to convert the residual's statement to the hypothesis's, per site and as the body grows (measure at doubling sizes, `docs/proof-patterns.md` §7).

## What refutes the design

The discharge is not a short term of a fixed shape; or the conversion's cost grows faster than the body; or a proof that reads a `let`-bound value (see [[found-proof-over-let-bound-read]]) cannot be carried.

## Done when

The three functions have their pins and their soundness theorems with no hand proof beyond the mechanical shape, the cost is reported as a shape, and the log says what a generator must emit per site.

## What it assumes from elsewhere

- **[[ownership-checker-call-and-write-view]]** (closed) gives the language, residuals and `check_sound`.
- **[[ownership-checker-loans-and-joins]]** is extending that module; this issue adds probes and at most a residual kind.
