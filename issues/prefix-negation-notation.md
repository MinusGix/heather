---
title: "Prefix negation notation: carrier-directed -a, beginning at Int"
status: closed
labels: [frontend,syntax,notation,stdlib,ergonomics]
created: 2026-08-19
updated: 2026-08-19
---

`std/int` has a complete `neg : Int -> Int` kit but no surface spelling for
negation. Proofs therefore say `neg(a)` where their addition, multiplication,
and order neighbors say `a + b`, `a * b`, and `a < b`.

The desired first customer is straightforward:

```heather
theorem neg_add(a, b: Int): -(a + b) = -a + -b
```

This should be carrier-directed notation, not a parser-global rewrite to the
bare name `neg`: more numeric carriers will eventually define distinct
negations, and importing them together must not make `-a` ambiguous once the
operand's carrier is known. The likely declaration shape is an explicitly
prefix designation beside `int::neg`, for example:

```heather
designation prefix - at Int := neg
```

## Design boundary

The designation key must distinguish **fixity/arity**. Prefix negation and a
future infix subtraction both naturally use `-` at `Int` but designate
different operations. A symbol-only key would incorrectly make them duplicate
rows. This issue owns the prefix slice and the key distinction it requires; it
does not require infix subtraction to land at the same time.

Unary precedence should be conventional: tighter than multiplicative infix
operators, so `-a * b` is `(-a) * b`, while `-(a + b)` is explicit. The lexer
must continue recognizing `->` as one token/window, and repeated negation
`--a` must parse without being mistaken for a comment or an arrow fragment.

Negative numeral syntax is adjacent but not silently included. Today a numeral
is a `Nat`, so `-3` cannot merely be carrier-resolved from its operand in the
same way as `-a : Int`. The first acceptance uses `-OfNat(3)`; a direct negative
literal needs its own expected-type/coercion decision, now owned by
[[carrier-directed-numerals]].

## Acceptance

- `designation prefix - at Int := neg` (or the settled equivalent) lives beside
  `neg`, and `-a` elaborates to the same term as `int::neg(a)`.
- Parenthesized, nested, and precedence-sensitive uses check at open integers.
- A second carrier can designate its own unary `-` without ambiguity at a
  resolved operand.
- Prefix and infix designation slots do not collide.
- `->` and the existing `¬` prefix parser remain unchanged.

## What it assumes from elsewhere

- **[[surface-operators]]** and **[[stdlib-operator-spelling-locality]]** own the
  carrier designation model and the policy that defining modules own rows.
- **[[notation-extensibility]]** owns the long-range openness of the operator
  lexicon. This bounded slice adds one fixed prefix symbol without deciding the
  general notation language.

## Log

- 2026-08-19: Filed from the post-I-prime review. `Int` is now the conspicuous
  carrier whose binary/order surface is complete while unary negation remains
  named at every use.
- 2026-08-19: Landed. `-` is a fixed prefix token parsed as an ordinary applied
  operator symbol; `designation prefix - at Int := neg` installs its meaning.
  Prefix/infix fixity is part of the designation key, unary precedence is above
  multiplication, and `--a`, `-OfNat(3)`, open carriers, and a second synthetic
  carrier are checked. The lexer still claims `->` before the single `-`.
  `-3` deliberately parses as `-(3)` but refuses today because `3` still infers
  `Nat`; [[carrier-directed-numerals]] owns making both `3 : Int` and `-3 : Int`
  work without an Int-specific negative-literal node.
