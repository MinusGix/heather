---
title: Sections whose head is spliced into every member
status: closed
labels: [frontend,syntax,ergonomics]
area: language
created: 2026-10-26
updated: 2026-10-26
---

A run of declarations that share a leading context repeats it on every head:
`<A: OrderedAddGroup(≈, <, <=, +)>` on 32 consecutive heads in
`ordered_field.hthr`, `({fetch: FetchAccess<M>}, {data: ByteReadAccess<M>},
self stack: Stack<M>(fetch, data), …` on the x86 stack theorems, `(self F:
Format, x: Rat, h: Nat, st: Bool, a: F.Approx(x, h, st), …` in float rounding.
`scripts/signature-census` ranks every such run.

Build `section<…>(…) { fn … theorem … }`: the section's `<…>` and `(…)` lists
are prepended to every member's own, in the parser, and nothing after the
parser sees a block. Design, the alternatives it was weighed against, and why
it splices rather than using Lean's mention rule: docs/language/sections-design.md §4–§5.

## Acceptance

- A spliced member and its hand-written twin are the same term (`refl`), at a
  concrete and an open carrier; nested sections concatenate.
- Generic, implicit, `self`, solver-default (`:= infer`) and constraint
  (`<A: C + D>`) section binders all splice; the member's own binders follow.
- Refusals, each with its reason: a generic or implicit section binder the
  member's head does not determine; a member binder named like a section
  binder (today a repeated value parameter silently shadows); two `self`;
  any item but `fn`/`theorem` inside; a section with neither list.
- A type error in a section binder is reported once, with the member count,
  not once per member.
- `--only Owner::name`, module images, early cutoff and mutual-group adjacency
  unchanged (a member inside a section is an ordinary `Item::Decl`).
- tree-sitter grammar, Zed, LSP outline and `book/` updated; `section` no
  longer refused, `given`/`context` still refused by name.
- One library file migrated as the acceptance client (ordered_field.hthr is
  the census's first), with `scripts/timings --diff` showing identical count
  columns.

## What it assumes from elsewhere

- **[[requires-placement-syntax]]** owns `given`, bundles and the constraint
  clause. Assumed here: only that a section's `<…>` list is the declaration
  grammar it already decided (`<A: Monoid>`, `+`).

## Log

- 2026-10-26: Built (PR #191, 2026-10-26). `section<…>(…) { fn … theorem … section … }` is a
  parser splice (`section_items`, `splice_sections` in
  `crates/syntax/src/parser.rs`): type parameters section-then-member; values as
  section solver params, member solver params, section written params, member
  written params; nesting concatenates outermost first. Refused: a generic or
  `{}` binder the member's head does not determine (token scan of explicit
  parameter types and the result, closed through determined implicits' types),
  a member binder rebinding a section name, two `self`s, an empty head, and any
  item but `fn`/`theorem`/`section`. Tests `crates/elab/tests/sections.rs`
  (refl twins at an open carrier and at `Nat`), parser unit test, tree-sitter
  `section_declaration` with a corpus case, book chapter. CLI prints identical
  errors once with a count. `ordered_field.hthr` migrated into five sections
  with `scripts/timings --diff` count columns identical.
