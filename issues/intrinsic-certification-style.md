---
title: Intrinsic certification: functions that return their correctness proof, split at elaboration
status: open
labels: [design,frontend,proofs,compiler,metaprogramming]
area: heather-in-heather
created: 2026-08-15
updated: 2026-08-15
---



Spun off the [[impl-declaration-surface]] discussion (2026-08-15),
user-ratified as an exploration to DOCUMENT with sketched examples — "an
interesting idea to explore to allow the best representation wherever the
library author wants to write it" — not an immediate build.

The idea: a definition returns its result *paired with* the proof of its
pointwise correctness statement — `(v, p : abs(v) = spec(abs(r)))` — so
the proof is co-designed with the code and **the induction hypothesis is
the recursive call**: no separate closing lemma. Sub-properties get
certified en route, which is exactly where intricate code wants it (user's
examples to sketch: sorting functions, intricate accessors — "proofs I
create during evaluation are very useful for proving I'm correct as I
run").

The two boundaries, from the discussion:

- **Pointwise only.** The proof component talks about the *result value*,
  never the function being defined, so `refines`-shaped statements work
  with no self-reference. Function-level statements (two calls compared,
  `refines_inv` over the body as an object) are extrinsic by nature — the
  registry's extrinsic artifacts stay the foundation.
- **Split at elaboration, never at runtime.** The runtime path needs a
  plain erasable body, and [[theorem-field-projection-oom]] is the live
  warning against projecting proofs off values. The intrinsic form
  elaborates by duplicating the recursion skeleton — values into `body`,
  proof components assembled into the closing induction — i.e. a
  certifying generator emitting exactly the two-parallel-structures shape
  reprgen already emits. Third route for filling the obligation record,
  beside `derive()` and `via`.

Deliverable when picked up: a design-doc section or standalone sketch
with 2–3 worked examples (sorting is the canonical one), the surface
spelling question (how the pair-return is written without noise), and the
splitter's obligations. Nothing in the v1 obligation-record design may
preclude it.

## Log

- 2026-08-15: Checked against the v1 design and NOT precluded (docs/language/classes/obligation-records-design.md §7): obligation slots are exactly the 'somewhere' an intrinsic definition's split-out proof components have to go, and §1.1's state machine does not assume the filler is a human-written proof declaration — a route fills slots, the kernel checks the filling, provenance records which route did it. The splitter is therefore a third route beside derive() and via derived, addable without touching §1-§6.
- 2026-08-15: Still precluded by nothing, and the pointer moved (2026-08-15): docs/language/classes/obligation-records-design.md §7 was rewritten when the round dropped file-wide slots. The somewhere an intrinsic definition's proof components go is no longer 'obligation slots' but CLAUSE ROUTES — the third route beside derive() and via_derived(p) is a clause saying 'this owner's obligations are filled by the splitter of definition f', and it fits with no change: a route produces the proof, the kernel checks it, provenance records which route did it. Two things the round makes easier for this: routes are ordinary applications in clause position rather than keywords, so a splitter route needs no grammar; and inline-first removed the open state, so §7 no longer has to assume a gap in time between a declaration and its certificate — the splitter emits both at once, which is what an intrinsic definition is.
