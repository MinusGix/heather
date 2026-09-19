---
title: An indexed record's type cannot be partially applied, so clients declare do-nothing fn wrappers
status: open
labels: [frontend,elaboration,syntax,ergonomics]
created: 2026-09-18
updated: 2026-09-18
---

An indexed record's type cannot be partially applied, so every client that
needs "this record, as a relation" declares a `fn` wrapper that does nothing
but apply it.

```heather
record Grammar(level: Nat, value: Nat) { at_level: level = level }
fn takes_relation(rel: Nat → Nat → Type) → Type { rel(0, 1) }
fn direct() → Type { takes_relation(Grammar) }
// error: `Grammar` is a constructor of `Grammar`, which is not the expected type here
```

The wrapper is the only reason `GrammarSpec` exists in both calculator
showcases:

```heather
fn GrammarSpec(level: Nat, source: List<Char>, begin, end: Cursor<Char>(source), value: Expr) → Type {
    Grammar(level, source, begin, end, value)
}
```

`docs/showcase/calc_text.hthr` passes `GrammarSpec(level)` to
`parser_contracts::Certified`, whose `relation` parameter is
`(source) → Cursor → Cursor → A → Type`, and `RunSpec(cls)` / `OpRun(target)`
are the same pattern at their own relations. A reader asks what the wrapper adds
over the record, and the answer is nothing — which is the tell.

Note the diagnostic names the *constructor*, not the type: at a `Type`-expected
position a record name should be read as its type, and the partial application
of an indexed record type is a type-level function of its remaining indices.
`Reply`, `Checked` and `Post` are genuine abbreviations that compute; these
wrappers are not.

Found while reviewing `docs/showcase/calc_text.hthr` (2026-09-18,
[[sequence-parser-source]]) against a reading of it as a language-quality
target: the showcase carries three such wrappers and each one is noise a reader
has to step over.
