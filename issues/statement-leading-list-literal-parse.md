---
title: A theorem statement cannot start with a list literal: [1] ++ … parses as a vector type
status: closed
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

## Log

- 2026-10-29: Fixed: the type grammar's `[` rule (parser.rs, `ty_atom_rules`) committed to the vector reading before seeing a `;`. It now speculates like `D<A, B>`: the element parses as a type and only a following `;` commits; anything else rewinds (memoised, site `SITE_TY_VEC`) to the expression grammar, whose `[` arm already decides by the first separator. Every `[T; n]` the type rule took parses exactly as before, including the type-only element forms (`Ctx`, `TyCode(g)`, `$a`). Tests: parser unit test `statements_may_start_with_a_list_literal` (params and results, nesting, malformed vectors keep their message, a 200-deep nest), probes in lib/_tests/std/data/list_tests.hthr. tree-sitter-heather already parsed the form (`vector_expression` is a `_type_atom`); a fixture pins it. The issue's own example now parses and stops at the carrier refusal of [[list-literal-left-of-append]], pinned there as an `expect-error`.
