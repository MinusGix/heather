---
title: "List membership notation"
status: open
labels: [frontend,syntax,notation,stdlib,lists,ergonomics]
area: language
created: 2026-08-20
updated: 2026-08-20
---

Give `list::Mem(a, xs)` the ordinary relational spelling `a ∈ xs`, with
`\mem` as the expected editor/input mnemonic for `∈` rather than as a second
semantic operator. Negated membership should compose from the existing tight
negation, `¬(a ∈ xs)`; a separate `∉` token can be considered only if real
source pressure justifies it.

The relation is polymorphic in the element type, so this is also a useful test
that a designated relation can recover its carrier from the list operand and
does not need a global bare-name rewrite.

## Acceptance

- `a ∈ xs` elaborates to `list::Mem(a, xs)` at open element types.
- Membership composes with `¬`, `∧`, `∨`, quantifiers, and equality at the
  expected comparison precedence.
- Importing another membership-like relation does not silently shadow this
  notation; ordinary carrier resolution or an explicit qualification applies.
- The standard list API uses the notation in public theorem statements.

## Log

- 2026-08-20: Filed from the standard-library surface review.
