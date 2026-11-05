---
title: Default operator symbols per class, overridable at the binder
status: open
labels: [design,traits,ergonomics]
area: language
created: 2026-08-09
updated: 2026-11-02
---

Filed ahead of need, from the operators round's close (2026-08-09). Once the
library reaches `Lattice`, order chains, and friends, the symbol slot's
per-declaration spelling stops scaling: every generic theorem over a lattice
writing `<A: Lattice(∧, ∨)>`-shaped binders to get its notation is the kind
of ceremony that makes people stop writing the notation. Those classes have
*natural* defaults — meet is `∧`, join is `∨`, the order is `<=` — and a
class should be able to say so once:

> a class **advertises** default symbols for its indices/fields, and a binder
> that names the class without naming symbols gets that notation installed —
> exactly as if the user had written the symbol slot themselves.

**Why the override must stay.** The ability to *not* take the default is
load-bearing, not a corner: decision theory, refinement, and any setting
where one carrier holds several instances of the class wants to assign
symbols per-binder (`⊑` for the refinement order while `<=` means the
numeric one, two lattices side by side under distinct spellings). The
default is sugar for the common binder, never a constraint on the unusual
one.

**Design tensions to record, not yet resolve:**

- **No fourth rung.** A default that expands to the binder's own symbol slot
  keeps the three-rung ladder intact — the default is rung 1 you didn't
  type, resolution never consults a new table, and designations (per
  *carrier*) are untouched. Any design where the class default is consulted
  at symbol-resolution time instead is a new rung and should be refused on
  that ground.
- **No nomination.** The default names a *spelling* for a bound index; it
  never picks which structure a carrier has. `<A: Lattice>` with defaults
  installed binds notation for *its own* index binders; two instances at one
  carrier stay equals. If a proposed semantics can't say that sentence, it
  is the coherence question re-entering through the notation door.
- **Collisions.** Two constraints with overlapping defaults
  (`<A: Lattice + Order>` both advertising `<=`) must be a refusal at the
  binder that asks the user to spell one explicitly — the same shape as
  §5.2's uniqueness rule, extended over advertised symbols.
- **Where the advertisement lives.** Decided (2026-08-09, user review): NOT
  the `as` symbol from [[binder-symbol-as-notation]] — `as` is body-local, so
  a class can use notation privately without claiming it is a good default
  for everyone. `Semigroup`/`Monoid` are the motivating case: they lean
  toward advertising *nothing* (an operation that might be `append` has no
  honest default symbol) while still writing `∙` in their own laws. The
  advertisement, when it comes, is its own declaration form; its shape is
  what stays open.

## What it assumes from elsewhere

- **[[class-alias-roles]]** owns transparent domain-role aliases that may
  advertise their own notation and prefer an alias-named instance. This issue
  owns the default package inherited from an ordinary class, not that
  role-specific resolution rule.
- **[[strict-order-presentation]]** owns whether an order's strict symbol is a
  derived notation expression or names a second class index, and requires the
  paired defaults to collide/override as one package.
- **[[binder-symbol-as-notation]]** owns symbol-notation on named binders.
  Assumed here: only that the symbol slot's installation is the mechanism a
  default expands to.
- **[[notation-extensibility]]** owns the lexicon. Assumed here: `∧`/`∨`-class
  symbols arrive either as curated tokens or via whatever extension mechanism
  that issue lands.
- **[[class-ops-prop-vs-bool]]** owns the order hierarchy this issue's main
  customers live in. No assumption beyond its existence.

## Log

- 2026-08-09: Decision recorded from user review (2026-08-09): the as-notation of [[binder-symbol-as-notation]] does not double as the advertised default — local niceness and claimed defaults are different speech acts; Monoid leans toward advertising nothing.
- 2026-11-02: From [[strict-order-presentation]] (closed 2026-11-02, docs/strict-order-presentation-design.md §2.3): both order relations are class indices, so no derived-notation expression is needed. The one requirement left here is that `(≈, <, ≤)` is advertised and overridden as one package. Today every order binder spells all three, so no collision can arise yet.
- 2026-11-05: gardener: cites a file it shares with [[class-inherited-field-implementations]] (`docs/strict-order-presentation-design.md`); [[class-parent-names-resolve-in-client-scope]] (`docs/strict-order-presentation-design.md`).
