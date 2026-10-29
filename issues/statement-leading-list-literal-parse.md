---
title: A theorem statement cannot start with a list literal: [1] ++ … parses as a vector type
status: open
labels: [frontend,syntax]
area: language
created: 2026-10-29
updated: 2026-10-29
---

A theorem statement is parsed as a type, and a leading `[` in a type
starts a vector type `[T; n]`, so a statement about a list literal on the
left does not parse:

```
theorem app_lit(): [1] ++ [2] = [1, 2] { refl }
// parse error: expected `;` (a vector type is `[T; n]`), found RBracket
```

Probe on master 4f0ac27 ([[proof-patterns-audit-2026-10]]); recorded in
memory on 2026-10-25 (lib/_tests corpus round). The workaround is to put
the literal on the right or write `Cons(1, Nil)`. In expression position
`[x]` after a lambda now parses fine, so this is the one place left.

The expression-side counterpart is [[list-literal-left-of-append]] (no
carrier for `[x] ++ ys`); this issue is only the parse.

## Acceptance

- `[1] ++ [2] = [1, 2]` parses as a statement; `[Nat; 3]` still parses as
  a vector type in the same positions. Mirrored in tree-sitter-heather.
