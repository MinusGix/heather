---
title: "Decidable if expressions over propositions"
status: closed
labels: [frontend,syntax,elaboration,traits,stdlib]
created: 2026-08-19
updated: 2026-08-19
---

Carrier APIs now expose propositional comparisons and `Decide<P>` instances,
but selecting a value still exposes their implementation:

```heather
fn max(a, b: Int) -> Int { or_pick(le_dec(a, b), a, b) }
```

The intended source form is:

```heather
fn max(a, b: Int) -> Int {
    if a <= b { b } else { a }
}
```

Here the condition is a proposition/type `P`, not a Boolean value. Elaboration
resolves `Decide<P>`, obtains `P ∨ ¬P`, and lowers to the ordinary dependent
case split on `Inl`/`Inr`. This is the source-branching decision already made
by [[class-ops-prop-vs-bool]]: logical source branching asks for `Decide`; a
later compiled program may additionally require `Compile`, but source typing
does not conflate the two.

## Evidence in branches

The full form must allow the decision evidence to be named, because many
branches prove something rather than merely choose data. Recommended shape:

```heather
if h : a <= b {
    // h : a <= b
    ...
} else {
    // h : ¬ (a <= b)
    ...
}
```

An unbound `if P { ... } else { ... }` is the convenience form when neither
branch uses the evidence. Reusing `h` at the two branch-local types matches the
fact that the branches are disjoint scopes. The exact punctuation should be
checked against `match h : e`, but the semantics are fixed by the lowering.

The result motive must be synthesized over the decision scrutinee, not merely
over the proposition text, so dependent results receive the same convoy as an
explicit `match decide<P>()`. A refusal should name the written condition and
the missing `Decide<P>` search trace.

## Boundaries

- A `Bool` is data, not automatically a proposition. `if b` over raw Bool
  should either remain outside this slice or be an explicitly separate
  constructor match; do not reintroduce `= True` into specification APIs.
- This does not make every `Decide` proof efficient at runtime. That is the
  `Compile`/data-representation boundary.
- `if let` and `let else` are separate pattern-sugar questions.

## Acceptance

- `if a <= b { b } else { a }` resolves the open `Int` order decision and is
  definitionally equal to the explicit `or_pick`/match spelling.
- The evidence-binding form checks both branch-local types and supports a
  dependent result.
- Missing, ambiguous, and recursively failing decisions report through the
  existing resolution trace with the condition's source span.
- Closed Nat/Int comparisons compute; an open carrier with a local
  `Decide<P>` dictionary branches without consulting a global instance.
- A raw Bool condition has an explicit, tested disposition rather than being
  accepted accidentally.

## What it assumes from elsewhere

- **[[decide-class]]** owns the evidence class and its derived connective
  instances.
- **[[class-ops-prop-vs-bool]]** already decided that source `if P` demands
  `Decide<P>` rather than `Compile<P>`.
- **[[decidable-equation-carrier]]** remains necessary before equality
  conditions can resolve generically by instance.

## Log

- 2026-08-19: Filed from the post-I-prime review of `Int::max`/`min`. Their
  `or_pick(le_dec(...))` bodies are small and correct but expose the decision
  representation that ordinary source branching should hide.
- 2026-08-19: LANDED. Proposition-directed `if` lowers to ordinary
  `match decide<P>()`, with optional same-name evidence in the disjoint
  branches, dependent checking, constant-result inference, and source-shaped
  resolution diagnostics. Raw `Bool` is deliberately rejected. `Int::max`
  and `Int::min` are the representative library uses. Design record:
  `docs/decidable-if-expression-design.md`.
