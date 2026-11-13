---
title: A numeral in a conditional's first arm fixes Nat before the other arm is read
status: open
labels: [frontend,elaboration,notation,ergonomics]
area: language
created: 2026-11-12
updated: 2026-11-12
---

```heather
fn pick(c, d: Bool, w: u64) → u64 { if c { 0 } else if d { w } else { 0 } }
theorem motive(c: Bool, w: u64, h: c = False): pick(c, True, w) = w {
    j(sym(h), λ b _ => (if b { 0 } else { w }) = w, refl)
}
```

```
error: this has type `u64`, but `Nat` is expected here
4 |     j(sym(h), λ b _ => (if b { 0 } else { w }) = w, refl)
  |                                           ^
```

An `if` (or a `match`) with no expected type takes its type from its first arm. A numeral there has no carrier, so it defaults to `Nat`, and the next arm is then refused for being what the whole expression was meant to be. The function `pick` itself is fine because its result type is the expected type; the trouble is only where the conditional is inferred, which is every motive that restates a body.

A neighbour of [[all-numeral-relations-default-to-nat]] (a relation whose operands are all numerals), but here one operand does have a carrier and it is one arm away.

Found in `lib/lang/lexer/lexer_span.hthr`: the motives over `scan_stopped` could not restate its `if` chain, so `scan_stopped_by` exists to give the arms a declared type, and motives use a `match` whose first arm is the typed one.

## What would fix it

A numeral arm stays a literal-class metavariable until the arms are joined, as the operands of `+` already are; the default to `Nat` applies only when every arm is a numeral. The equation's other side (`= w`) is a second source of the type that is also ignored today.

This changes what the elaborator infers, so it needs the whole-library re-elaboration before it merges (CLAUDE.md).

## Done when

The theorem above checks as written, and `scan_stopped_by` can go.
