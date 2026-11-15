---
title: The inhabitation ladder: Default -> Inhabited -> Nonempty
status: open
labels: [frontend,stdlib,design,traits]
area: mathematics
milestone: [math-specific-choice]
created: 2026-08-07
updated: 2026-10-26
---

User decision 2026-08-07, from reviewing lib/std/algebra/algebra.hthr's `Default<A>`: keep `Default` as the programming-side class (it implies a NATURAL default — 0 for Nat/Rat/Real, empty list — not mere inhabitation) and add the math-side ladder as separate classes rather than renaming:

- `Default<A>` — a canonical value. Programming-facing; already landed.
- `Inhabited<A>` — SOME value, no canonicality claim. Data-level (a field holding a witness). `Default extends Inhabited` (or a derivation): every default inhabits, sharing the field by flattening.
- `Nonempty<A>` — MERE existence, propositional. This is not a data class at all: it wants propositional truncation / a squashed existential, i.e. it is blocked on [[sprop-squash]] (deferred SProp formers). `Inhabited -> Nonempty` is then a derivation, not an extends (the field types differ in kind).

Rationale over Lean's two-way split (Inhabited/Nonempty): Heather mixes programming and math in one library, and 'has a good default' / 'has a value' / 'is not empty' are three different claims with three different consumers. Exotic structures get Inhabited without being forced to bless a Default.

Do the Default→Inhabited step whenever the library next grows; the Nonempty step waits for its former. The [[inherited-members-undispatchable]] interaction is resolved (2026-08-08, owner-keyed dispatch + scope upcast): `extends` no longer costs receiver dispatch, so the first step can use it freely.

## Log

- 2026-08-16: Scope note (2026-08-16): trivial-hypothesis auto-discharge does NOT ride this ladder after all — the mechanism chosen on [[true-prop-trivial-hypotheses]] is per-binder default argument values (home: [[named-arguments]]), because the licensing property is binder intent, not type inhabitedness. This ladder stays motivated by its own customers.
- 2026-10-26: Squash has landed ([[sprop-squash]]), so `Nonempty<A> := ∥A∥` is no longer
  blocked. Two facts from Baillon et al., FSCD 2026 (`docs/papers/LIPIcs.FSCD.2026.5.pdf`)
  bound the ladder. The missing arrow `Nonempty<A> → Inhabited<A>` for every `A`
  is full choice (their Fact 7). Its specific, axiom-free form for a countable
  carrier with a decidable predicate (MathComp's `choiceType`) is constructive
  epsilon, which Heather cannot state as a theorem today; see
  [[squashed-termination-evidence]].
