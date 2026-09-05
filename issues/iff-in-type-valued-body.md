---
title: Parse parenthesized logical equivalence inside a Type-valued function body
status: open
labels: [frontend,syntax,parser,stdlib]
created: 2026-09-04
updated: 2026-09-04
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

## Log

- 2026-09-04: Filed after the user requested an owner for the parser friction
  found during the manual Mergeable round. No parser change in this filing.
