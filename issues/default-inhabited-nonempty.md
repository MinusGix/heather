---
title: The inhabitation ladder: Default -> Inhabited -> Nonempty
status: open
labels: [frontend,stdlib,design,traits]
created: 2026-08-07
updated: 2026-08-07
---

User decision 2026-08-07, from reviewing lib/std/algebra.hthr's `Default<A>`: keep `Default` as the programming-side class (it implies a NATURAL default — 0 for Nat/Rat/Real, empty list — not mere inhabitation) and add the math-side ladder as separate classes rather than renaming:

- `Default<A>` — a canonical value. Programming-facing; already landed.
- `Inhabited<A>` — SOME value, no canonicality claim. Data-level (a field holding a witness). `Default extends Inhabited` (or a derivation): every default inhabits, sharing the field by flattening.
- `Nonempty<A>` — MERE existence, propositional. This is not a data class at all: it wants propositional truncation / a squashed existential, i.e. it is blocked on [[sprop-squash]] (deferred SProp formers). `Inhabited -> Nonempty` is then a derivation, not an extends (the field types differ in kind).

Rationale over Lean's two-way split (Inhabited/Nonempty): Heather mixes programming and math in one library, and 'has a good default' / 'has a value' / 'is not empty' are three different claims with three different consumers. Exotic structures get Inhabited without being forced to bless a Default.

Do the Default→Inhabited step whenever the library next grows; the Nonempty step waits for its former. Watch the [[inherited-members-undispatchable]] interaction if extends is used for the first step.
