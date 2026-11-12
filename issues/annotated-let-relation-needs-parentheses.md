---
title: A `let` annotated with `<` or `<=` does not parse without parentheses
status: open
labels: [frontend,syntax,parser,ergonomics]
area: language
created: 2026-11-12
updated: 2026-11-12
---

```heather
theorem le(a, b: Nat, h: a <= b): a <= b { let k: a <= b = h; k }
```

```
error: parse error: expected `=`, found LtEq
```

The same with `<`. `let k: (a <= b) = h;` parses, and so does an equality annotation written bare (`let k: a = b = h;`, [[annotated-let-swallows-the-equals]], which settled the `=` case). So a relation other than equality in a `let` annotation needs parentheses and nothing says so: the message points at the operator, not at the fix.

Found writing `lib/lang/lexer/lexer_span.hthr`, where every `let` that names a bound is spelled `let below: (i.toNat() < length.toNat()) = omega;`.

## What would fix it

Either the annotation is parsed as a proposition up to the statement's last top-level `=` (relations bind tighter than the `let`'s own `=`), or the parse error says "write the annotation in parentheses". The first is the one a reader expects, since a theorem's result type takes `a <= b` bare.

## Done when

The declaration above checks as written, or its error names the parentheses.
