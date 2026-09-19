---
title: An indexed record's type cannot be partially applied, so clients declare do-nothing fn wrappers
status: open
labels: [frontend,elaboration,syntax,ergonomics]
created: 2026-09-18
updated: 2026-09-19
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

## Log

- 2026-09-19: 2026-09-19: Counted on `docs/showcase/calc_text.hthr` (561 lines), which raises
  this issue's weight: the three do-nothing wrappers are the small half.

  The large half is **29 positional projections into anonymous conjunctions** — 4
  `op.evidence.left.left`, 4 `close.evidence.left.right`, 7 bare `.left`, 14 bare
  `.right`. A reader cannot tell what `op.evidence.left.left` denotes, and the file
  shows both spellings of the same job side by side: `Grammar` is an indexed record
  and its consumers read `l.span`, `inner.yields`, `atom.at_level`; `RunSpec` and
  `OpRun` are ∧ towers over the library's `Certified` relation slot and their
  consumers index by position. `WellFormed`'s arms are the same tower on the
  specification side — `(((l.tier() = 1) ∧ l.WellFormed()) ∧ tr.all(is_space)) ∧
  ((r.tier() = 0) ∧ r.WellFormed())` — and `And(And(And(…)))` on the construction
  side, 20 `And(` calls in the file.

  Honest scoping, because it changes the order of work: nothing *forces* the ∧
  spelling today. A spec relation can be a record plus a wrapper `fn`, which is
  exactly what `Grammar`/`GrammarSpec` already are. So the showcase half — make
  `RunSpec` and `OpRun` records with named fields — lands without this issue, and
  should land first: it takes the wrapper count from three to about five and turns
  the language case from cosmetic ("a reader steps over three lines") into
  structural ("every named-field spec relation costs a wrapper"). That is the
  argument this issue wants, and it is cheaper to produce than to assert.

  One caution for whoever does that showcase half: this file already needs more
  than 8 GiB cold and its semantic image is 483 M nodes, so it is not in the suite
  ([[elaborator-canonical-type-spelling]]). Records add Σ layers to exactly the
  term family measured at 27× there. Measure the cold check before and after.
