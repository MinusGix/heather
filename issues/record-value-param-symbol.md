---
title: Extend `as` to record/inductive value parameters when a customer shows up
status: open
labels: [design,frontend,ergonomics]
area: language
created: 2026-08-11
updated: 2026-08-11
---

Promoted out of [[binder-symbol-as-notation]]'s closing log (2026-08-11) so it
stays findable: a closed issue's log is where decisions rest, not where open
questions live.

The op-as round refused `as` on a `record`/`inductive` value parameter at
parse time, reasoning that such a parameter "is a term the fields mention, not
a binder with a body to spell." User review flagged the reasoning as thin, and
it is: a record's field types *do* mention the parameter, which is
structurally the class-head case —

```heather
record Cayley<A>(op as ∙: A -> A -> A) {
    law: (x, y: A) -> (x ∙ y) ∙ x = x ∙ (y ∙ x),
}
```

wants its notation exactly as `Semigroup` does. The honest ground for the
refusal is that no such record exists yet and the installation machinery lives
in class lowering (`Inductive::op_symbols`, installed in `lower_ctor` where
field types elaborate — which records share, so the extension is plausibly
small). When a record whose fields state laws over an operation parameter
shows up, lift the parse-time refusal (`valparam_list`'s `symbols` flag,
crates/syntax/src/parser.rs) and let the existing installation carry it; the
negative controls of the op-as round apply unchanged.

## What it assumes from elsewhere

- **[[binder-symbol-as-notation]]** (closed) owns the as-device and its
  scope/uniqueness rules. Assumed here: only that a class head's installation
  path is the one records would reuse.

## Log

- 2026-11-05: gardener: cites a file it shares with [[generate-in-sections]] (`crates/syntax/src/parser.rs`); [[requires-placement-syntax]] (`crates/syntax/src/parser.rs`).
