---
title: "Type-owned namespaces: names attach to subjects, reachability through evidence"
status: open
labels: [frontend, syntax, elaboration, design, modules]
created: 2026-08-05
updated: 2026-08-05
---

Direction issue, not scheduled — filed from the 2026-08-05 namespace
discussion (the round after [[modules]] v1 landed), so the design is
written down rather than re-derived. The prompt: `cong_nat` should be
`nat::cong` — a name wearing its namespace as a suffix — and a prover
needs mass accessibility that Rust-style selective import does not give,
while typeclasses "capture a good chunk but not wholly."

## The claim

The natural namespace is the **subject** — a type (`Nat`, `Le`,
`Option`) or a structure (`Monoid`) — not the file. Files are storage;
subjects are what names organize around. Proposal, in two coupled halves:

1. **Type-owned namespaces, checked.** A declaration form attaches
   theorems/fns to a type: `Le::refl`, `Nat::cong`, `Option::map`. The
   `Type::member` grammar exists since [[modules]] (constructors qualify
   by type); this opens membership beyond constructors and fields, and
   the attachment is a checked declaration, not a Lean-style naming
   convention.
2. **Reachability through evidence.** A member of `T`'s namespace is in
   scope wherever a `T` is in evidence, by the one-resolution-judgment
   direction (docs/modules-design.md §8):
   - *Elimination-shaped* members reach through a **receiver** —
     `p.trans(q)` with `p : a = b`; the method fallback is already
     receiver-directed, so this is Lean dot-notation landing on built
     machinery.
   - *Introduction-shaped* members reach through the **expected type** —
     bare `refl` at goal `Le(n, n)` resolves to `Le::refl`. This
     subsumes [[ctor-resolution-by-expected-type]] (constructors are the
     special case).
   The duality is bidirectionality itself: synthesis position, the
   arguments are the evidence; checking position, the goal is.

   Extension for function-subject lemmas (`add_comm` is "about" `add`):
   the goal's **head symbol may pick the namespace** (coarse, stable);
   full unification picking the *lemma* stays banned, per the growth
   invariant.

Consequence for the collision problem: the ambient bare namespace
shrinks to genuinely ambient names; subject-owned lemmas are reached
through evidence at zero import cost and zero pollution, which is the
accessibility profile proof text actually needs.

## Where typeclasses sit

A structure is a record type, so its theory is its own type-owned
namespace (`Monoid::assoc`). Instance resolution adds a second
**evidence relation**: nominal membership is "this value *is* a `T`";
class membership is "this type *has* a `T`-instance." Same judgment, two
relations — one definitional, one semantic. Typeclasses are the semantic
half, capturing exactly the lemmas stable under transport along
instances; Nat-specific facts (computation lemmas, inversions, induction
schemes) are the nominal half's. Neither subsumes the other, and the
"these assumptions only" boundary role is the little-theories reading:
structure = theory, instance = interpretation, reachability-through-
instance = transport.

## The Better-than-Lean line (why not just copy)

Lean has the same ingredients (namespaces, dot-notation, `open`,
classes) and loses where our invariants hold:

- Lean disambiguates overloads **by elaboration success** — try every
  interpretation, keep what typechecks. That is what the growth
  invariant forbids: growth elsewhere can reinterpret existing text.
  Here, evidence may *shrink* the candidate set, never race candidates;
  residual ambiguity errors with origins named.
- `open` is precedence-ordered pollution; the base layer here stays
  [[modules]]' ambiguity-at-use, and evidence-reachability removes most
  of the need for mass-open.
- Namespaces are checked attachments, so `Le::refl` cannot drift from
  `Le`.

## Honest gaps

- **Forward reasoning** (`let h = sub_zero(n);`) has no evidence in
  hand; those sites keep the v1 regime (bare-if-unambiguous, qualify
  otherwise). The design is strictly additive over [[modules]].
- Rewrite-direction / normal-form tension between `Nat::add` facts and a
  future `Monoid::op` statement of "the same" fact is a tactic-layer
  problem no naming scheme solves.
- `nat::cong` is spellable today by renaming `cong_nat` → `cong` inside
  the module; deliberately not done — if this issue lands, its name is
  `Nat::cong`, and one rename beats two.

## What it assumes from elsewhere

- **[[modules]]** (closed) owns the base regime and the two invariants.
  Assumed here: ambiguity-at-use stays the floor; `Type::member`
  qualification stays.
- **[[ctor-resolution-by-expected-type]]** owns the constructor special
  case; if this issue lands first, it absorbs that one.
- **[[compile-typeclass-design]]** owns instances. Assumed here: only
  that instance resolution exists someday; the second evidence relation
  waits for it.

## When

A scheme round wants: the attachment syntax (impl-block vs qualified
declaration head), the evidence judgment written against the elaborator's
actual checking/synthesis split, and the method-fallback unification.
Triggered by the first library round that hurts without it — plausibly
the prelude layer-2 round or the first file that wants two order kits.
