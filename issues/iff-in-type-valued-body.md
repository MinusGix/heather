---
title: Parse parenthesized logical equivalence inside a Type-valued function body
status: closed
labels: [frontend,syntax,parser,stdlib]
created: 2026-09-04
updated: 2026-09-17
---

The manual Mergeable round encountered this exact failure while defining list
membership equivalence:

```heather
import logic;
import list;

fn SameMembers<A>(xs, ys: List<A>) → Type {
    (a: A) → (Mem(a, xs) ↔ Mem(a, ys))
}
```

The observed diagnostic on the parenthesized connective is:

```text
parse error: expected `)`, found Iff
```

The working definition is:

```heather
fn SameMembers<A>(xs, ys: List<A>) → Type {
    (a: A) → Iff<Mem(a, xs), Mem(a, ys)>
}
```

The unparenthesized spelling `(a:A) → Mem(a,xs) ↔ Mem(a,ys)` is a separate
precedence/scope matter: it produced an unbound right-hand `a`. Do not silently
change arrow/Iff precedence to repair this issue. Parentheses should provide
the unambiguous intended grouping.

## Acceptance

- Parse and elaborate the parenthesized reproducer to the intended dependent
  function returning Iff; compare with the named-constructor spelling.
- Cover both type-annotation and Type-valued-body contexts, with an open bound
  variable used in both connective operands.
- Check adjacent parenthesized conjunction/disjunction cases so the fix handles
  the grammar boundary rather than special-casing SameMembers. Record their
  actual behavior first; only the Iff failure is established by this report.
- Preserve existing connective/arrow precedence and ordinary term grouping.
- Replace the workaround in `std/list_setoid` only after the equivalent spelling
  checks, and update the realized showcase's gap table.

## What it assumes from elsewhere

- **[[std-logic-module]]** owns the logical connectives and their notation.
- **[[quantifier-notation-in-type-arguments]]** owns the related, distinct
  quantifier/type-argument grouping gap; this issue owns Type-valued bodies.
- **[[manual-mergeable-round]]** supplies the observed failing and working
  spellings; its implementation is complete using the explicit Iff form.

## What it turned out to be

`Parser::no_iff` — the flag that suppresses `↔` while a function type's
**codomain** is read, which is what makes `↔` looser than `→` — was documented
as working "exactly as `no_eq` suppresses `a = b`" and did not: `no_eq` is
lifted inside any bracket, so a parenthesis is its escape hatch, and `no_iff`
was never lifted anywhere. The restriction therefore reached the whole subtree
rather than the codomain's own spine, and a `↔` inside *any* delimiter under a
codomain was refused. `∧`/`∨` were never restricted, which is why only `↔`
showed it.

Measured on the failing tree (2026-09-17), with `h:` an annotation and every
`↔` parenthesized — the point being that the bracket kind does not matter:

| spelling | before | after |
| --- | --- | --- |
| `(P ↔ Q)` | ok | ok |
| `P → (Q ↔ R)` | **parse error** | ok |
| `P → (Q → R ↔ S)` | **parse error** | ok |
| `P → ¬(Q ↔ R)` | **parse error** | ok |
| `P → Or<Q ↔ R, S>` | **parse error** (and a `>`-is-not-an-operator hint, which is wrong about the cause) | ok |
| `(P ∧ Q)`, `P → (Q ∧ R)`, `(P ∨ Q)`, `P → (Q ∨ R)` | ok | ok |
| `P → Q ↔ R → P` | ok | ok |

The fix lifts the restriction in exactly two places — `Parser::expr`, which
covers every expression-side bracket because every one of them parses its
contents through it, and `Parser::ty_atom`, which covers the type-side ones
(the parenthesized group, `D<A, B>`'s arguments, `[T; n]`, `Squash`, `Code`).
`expr` restores the flag *before* the `↔` decision and `ty_atom` restores it
around its two fallthroughs to `expr`, which are the codomain's spine — that
restore is what keeps `P → Q ↔ R` reading as `(P → Q) ↔ R`.

Nothing in the arrow/`↔` precedence changed, and the unparenthesized
`(a: A) → Mem(a, xs) ↔ Mem(a, ys)` still leaves the right-hand `a` unbound,
exactly as this issue asked.

## Log

- 2026-09-04: Filed after the user requested an owner for the parser friction
  found during the manual Mergeable round. No parser change in this filing.
- 2026-09-17: CLOSED. `crates/syntax/src/parser.rs`: brackets lift the codomain
  `↔` restriction. `lib/std/list_setoid.hthr` now writes
  `(a: A) → (Mem(a, xs) ↔ Mem(a, ys))` and the whole module — including every
  downstream `Iff(mp := …, mpr := …)` proof — checks unchanged, which is this
  issue's "compare with the named-constructor spelling". Tests:
  `a_bracket_lifts_the_codomain_iff_restriction` (spelling) in
  `crates/syntax/src/parser.rs`, and
  `a_parenthesised_connective_is_readable_inside_a_codomain` plus
  `every_bracket_inside_a_codomain_admits_a_connective` (meaning, both
  directions against the named spelling, with an open carrier and the binder
  used in both operands) in `crates/elab/tests/logic.rs`.
  `docs/manual-mergeable-round.md`'s gap table row is closed.
  Two adjacent findings were filed rather than folded in, both confirmed
  pre-existing by rebuilding the parent commit:
  [[binder-headed-arrow-as-connective-operand]] (`(a: A) → P(a) ↔ R` is a
  parse error rather than the documented looser reading) and
  [[pi-codomain-record-mismatch-panics-kernel]] (a refusal against
  `(a: A) → And<P(a), R>` aborts the process on a kernel invariant).
