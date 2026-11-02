---
title: "Render resolved operations with their operator notation in diagnostics"
status: open
labels: [frontend,diagnostics,notation,ergonomics]
area: language
created: 2026-08-20
updated: 2026-11-02
---

Kernel-term diagnostics currently recover a global application as a named call:
`add(a, b)`, `mul(a, b)`, `pow(a, n)`, and so on. Source-AST diagnostics can
preserve a symbol that was written, but after elaboration the `Speller` sees
only the resolved global and its arguments. The result is technically accurate
and needlessly unlike Heather source.

Recover the preferred operator spelling when the resolved operation, fixity,
arity, and operand carrier justify one. The headline examples should read
`a + b`, `a * b`, and eventually `a ^ n`, with comparisons, Boolean operators,
append, prefix negation, and later designated operators following the same
rule.

This is an inverse-resolution problem, not a global `name -> symbol` table.
The same declaration may be designated differently at different carriers or
under different scopes, and a local symbol binder can shadow a designation.
The display must therefore use the diagnostic site's visible designation table
and the elaborated operand type, print notation only when the inverse is
unique, and otherwise retain the named call. Parentheses must follow the
surface precedence and associativity rules.

`^` is intentionally an acceptance target rather than a claim about today's
grammar: Heather does not currently give `pow` a `^` designation. Add that
surface spelling through the ordinary operator/designation mechanism first;
the printer must not invent notation that a user could not write.

## Acceptance

- Kernel-term diagnostics render every currently designated operation with
  its applicable infix or prefix spelling when the inverse is unique.
- `pow` gains a writable `^` spelling and diagnostics render it as infix.
- Mixed-carrier tests cover symbols such as `+` at Nat and Int and prove the
  carrier, not the global's basename, selects the display.
- Ambiguous, shadowed, first-class, partially applied, and un-designated calls
  retain a faithful named spelling.
- Nested operators are parenthesized according to the actual surface grammar.
- No registry key or elaboration decision depends on the pretty-printed form.

## What it assumes from elsewhere

- **[[stdlib-operator-spelling-locality]]** owns where standard-library
  designations are declared. Assumed here: those rows are available in the
  importing elaborator.
- **[[notation-extensibility]]** owns the future operator lexicon and
  precedence policy. Assumed here: a printer consumes that policy; it does not
  define a second one.

## Log

- 2026-08-20: Filed after the inductive-display round made kernel diagnostics
  source-like enough that named calls such as `pow(a, n)` became the next
  conspicuous mismatch. Surface-AST rendering already preserves written
  operator nodes; this issue owns the harder kernel-to-surface inverse.
- 2026-09-15: 2026-09-15: a second customer for the resugaring pass: [[wrong-dictionary-field-refusal-names-projection]] — a named projection reference now appears in a wrong-field refusal where the declaration's name used to.
- 2026-11-02: grind's failure report is a customer: it spells `-(a + OfNat(k).isucc())` as `neg(add(a, isucc(OfNat(k))))` ([[grind-library-sweep]]).
