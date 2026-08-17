---
title: "Decide: the class of P ∨ ¬P, derived where the relation is recursive"
status: open
labels: [design,traits,frontend,stdlib]
blocked-by: [std-logic-module]
created: 2026-08-16
updated: 2026-08-16
---

A function that branches on a proposition needs a term that produces the
branch. `insert(x, Cons(h, t))` must pick a side on `x <= h` for **arbitrary**
`x` and `h`, so it needs

```heather
class Decide<P> { dec: P ∨ ¬P }
```

and an instance found by resolution. This issue owns that class, its
derivation, and the boundary between it and [[compile-typeclass-design]].

## Why the object must exist, whatever it is called

Three things get confused here, and separating them is most of the design:

1. **Elaboration-time proof search** answers "is `Le(3, 5)` inhabited?" for
   *closed* arguments. It works today and is the `h := infer` case of
   [[guarded-to-option-adapter]]. It cannot serve `insert`, whose body is one
   closed term quantified over all `x` and `h`.
2. **A decider** is that same answer made *uniform*: a term
   `(n, m: Nat) -> n <= m ∨ ¬(n <= m)`. Some such term must exist for
   `insert` to be definable at all; the only alternative is pushing the
   obligation onto every caller. `Decide` is therefore not machinery layered
   on top of the definition — it is the name of a thing the definition
   already requires.
3. **Classical LEM would typecheck and be useless.** An axiom
   `lem : (P: Type) -> P ∨ ¬P` makes `insert` check, and then
   `insert(3, [1,2])` never reduces, because `lem(…)` is a neutral constant
   with no reduction rule. The content of `Decide` versus classical
   disjunction is exactly *"this disjunction reduces"*.

## Why it is not `Bool`, and why there is no sort boundary

`Decide<P>` already **is** the Bool, with the evidence attached; `decide` is
the projection that throws the proofs away. In Lean the two are separate
public objects for two reasons, neither of which applies here:

- **Erasure.** Lean's `Prop` is irrelevant and erased, so a decision cannot be
  eliminated out of it into `Type` — that would observe which proof you were
  handed. Hence `Decidable p : Type` indexed by a `Prop`, a genuine two-object
  split. **Heather keeps proof relevance** (the standing position, restated
  2026-08-16), so `P ∨ ¬P` is an ordinary type and `insert` eliminates it
  directly. No sort boundary, no split.
- **Proof size.** `ble(n, m) = True` is a small proof where a derivation is
  large. Under [[nat-order-kit]]'s recursive `Le` the proposition itself
  reduces to `True` at closed arguments, so reflection is already free and
  this reason evaporates too.

The consequence for the library: **no `Bool` in any spec API and no `= True`
anywhere.** `Bool` stays a data type for when Booleans are the subject
(Boolean algebra, circuits) and inside generated code.

## Derivation, not duplication

The pain to avoid is Lean's: write `Nat.decLe` by hand, prove it correct, and
maintain it beside the relation. A decider for a structurally recursive
proposition is **mechanically derivable from the recursion** — which is the
generator story this project is already built on. Under `nat-order-kit`'s
definition (a), `le_dec` is a five-line structural recursion whose correctness
is definitional; deriving it is the natural next step, not a stretch.

Composition instances are what earn the class rather than a naming
convention: `Decide<P> -> Decide<Q> -> Decide<P ∧ Q>`, the `∨` and `¬` cases,
and the bounded-quantifier cases. Resolution assembles those; a convention
cannot.

**User note (2026-08-16):** `Decide` may later warrant *special* treatment —
a custom elaborator pass automating parts of it beyond what ordinary instance
resolution is smart enough to do — on the grounds that it is core enough to
earn the exception. Recorded as a direction, not scheduled; the ordinary class
comes first and is what would measure whether the exception is needed.

## Decide is not Compile

Recorded as **decided**, answering sub-question 1 of
[[class-ops-prop-vs-bool]]: they stay distinct.

- `Decide<P>` says a case-analysis term exists and reduces. Kerneltime.
- A `Compile` instance says the resulting machine code is sane, with cost and
  representation evidence.

Decidable-but-insane is easy to exhibit (a bounded search over 2^64 cases
decides; nobody should run it), so `Compile` strictly refines `Decide` in
demand, and neither carries the other's content. Three consumers, three
demands: elaboration-time search (closed arguments, needs neither), `Decide`
(uniform kerneltime branching), `Compile` (executable, with cost evidence).

## What it assumes from elsewhere

- **[[std-logic-module]]** owns `Or`/`Not` and the `∨`/`¬` spellings. Assumed here: only that they
  exist.
- **[[class-ops-prop-vs-bool]]** owns the kerneltime/runtime split. Assumed
  here: only its 2026-08-16 log, which this issue's "not Compile" section
  answers rather than restates.
- **[[compile-typeclass-design]]** owns `Compile`. Assumed here: only that it
  demands executable code plus a correctness theorem, which is strictly more
  than a reducing case analysis.
- **[[instance-shorthand-syntax]]** owns one-field instance ergonomics.
  Assumed here: nothing; `Decide` is simply a good customer for it.
- **[[decided-case-convoy]]** owns the elaboration of a case split on a
  decided predicate. Assumed here: only that branching on `dec` is the same
  shape its convoy already handles.

## Acceptance

`le_dec` and `eq_dec` at `Nat`; `insert`/`isort` in `lib/list_algos.hthr`
restated with no `Bool` and no `= True`; the composition instances for `∧`,
`∨`, `¬`; and the restatement's before/after recorded as the measurement of
what the class has to provide (the method [[list-algorithms-exercise]]
established).

## Log

- 2026-08-16: Filed out of the std-API design discussion. The turn that
  produced it: the two-object Prop/Bool split looked foundational until proof
  relevance was reaffirmed, at which point the elimination restriction that
  forces it in Lean simply does not apply — `Decide` drops from a blocking
  design question to a one-field class plus a derivation.
