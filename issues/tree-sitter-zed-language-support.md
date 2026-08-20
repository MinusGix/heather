---
title: "Add a low-maintenance Tree-sitter grammar and Zed language extension"
status: open
labels: [tooling,editor,syntax,zed]
created: 2026-08-20
updated: 2026-08-20
---

Heather files have no structural editor support. Build a Tree-sitter grammar
for `.hthr`, then package it in a Zed language extension with highlighting,
bracket matching, indentation, outline entries, and useful text objects.

The maintenance constraint is the important part: Heather's parser is moving,
and a hand-copied second grammar will drift. Establish a small, checked syntax
corpus shared with the real parser and make grammar updates fail visibly when
the surface changes. Prefer generated token/keyword/operator inventories where
the source parser exposes them cleanly; do not try to generate Tree-sitter's
entire CST grammar mechanically from the recursive-descent parser.

Zed currently requires a registered Tree-sitter grammar for a language
extension and uses query files for highlighting and structural features. See
the [official Zed language-extension documentation](https://zed.dev/docs/extensions/languages)
and [Tree-sitter grammar guidance](https://tree-sitter.github.io/tree-sitter/creating-parsers/3-writing-the-grammar.html).

## Acceptance

- A standalone `tree-sitter-heather` grammar parses the supported syntax,
  including Unicode connectives/operators, nested patterns, declarations,
  proof blocks, quotations, and error recovery over incomplete edits.
- A differential fixture corpus is accepted by both Heather's parser and the
  Tree-sitter grammar, with explicit negative and recovery fixtures.
- CI detects stale keyword, punctuation, and fixed-operator inventories.
- A Zed extension recognizes `.hthr` and supplies at least `highlights.scm`,
  brackets, indents, outline, and function/type text objects.
- Local development and release/update instructions are documented; the Zed
  extension pins the grammar revision deliberately.

## What it assumes from elsewhere

- **[[surface-syntax]]** owns Heather's grammar. This issue mirrors its landed
  surface for editor tooling and does not create editor-only syntax.
- **[[machine-readable-syntax-manifest]]** owns the shared lexical inventory
  and drift check. This issue still owns Tree-sitter's CST grammar, recovery,
  queries, and Zed packaging; those cannot be generated from a token manifest.
- **[[notation-extensibility]]** owns future open-symbol lexical policy.
  Assumed here: the grammar follows the decided character classes and curated
  binder list when those land.

## Log

- 2026-08-20: Filed with Zed as the primary consumer. Official Zed docs confirm
  that one Tree-sitter grammar plus query files is the normal route for syntax
  highlighting and structural editor support.
