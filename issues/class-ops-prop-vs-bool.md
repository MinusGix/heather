---
title: Class operations across the kerneltime/runtime split: Prop laws, Bool programs, certificates between
status: open
labels: [design,traits,compiler,stdlib,delam]
created: 2026-08-07
updated: 2026-08-07
---

From reviewing `Cmp<A>` (le: A -> A -> Bool with `= True` laws, 2026-08-07). The question 'should le be A -> A -> Prop (or SProp)?' dissolves differently in Heather than in Lean, because of the hard kerneltime/runtime split the whole Compile design is about: a class operation is a kerneltime value, and HOW IT RUNS is a separate, certificate-carrying claim (a Compile instance for the dictionary's operations — untouched territory, noted at [[compile-typeclass-design]]). So Bool-vs-Prop stops being one API decision and becomes two:

- **Specification side**: the mathematical relation, naturally Prop-valued (`le: A -> A -> Prop`, laws as implications) — and with [[sprop-strict-prop]] landed, plausibly SProp-valued where irrelevance is wanted.
- **Program side**: the decision procedure, Bool-valued, the thing a Compile instance will certify and run.
- **The bridge**: a decidability class tying them — `DecCmp<A> extends Cmp<A> { leb: A -> A -> Bool, le_dec: (x y) -> leb(x,y) = True <-> le(x,y) }`-shaped — so 'they behave the same' is a field with a proof, exactly the house pattern (the same shape as the override #agrees certificates and the Compile cert itself).

The landed `Cmp` (Bool + `= True`) is the honest v1: it is the DECIDED class with the spec inlined as its own decision. When Prop-valued classes are wanted (real math: partial orders with undecidable le), add the spec-side class and make today's Cmp the decidable refinement rather than renaming.

Open sub-questions, recorded not answered: whether SProp fields in classes interact with the record lowering at all today; what a Compile instance FOR A DICTIONARY looks like (per-instance? per-class-with-carrier-Compile?) — that is the 'compile instances for typeclass functions' thread, deliberately untouched by the traits rounds so far and probably the next Compile-side design round after [[datarepr-separation]].
