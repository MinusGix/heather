---
title: "Provide a TextMate grammar for VS Code-family editors"
status: open
labels: [tooling,editor,syntax,vscode]
area: language
created: 2026-08-20
updated: 2026-08-20
---

Provide lightweight Heather syntax highlighting in VS Code and other editors
that consume TextMate grammars. This is deliberately lower priority than
[[tree-sitter-zed-language-support]]: the initial target is readable source,
not structural parsing or an LSP.

The grammar should share inventories and fixtures with the Tree-sitter/editor
work wherever practical. Regex scopes cannot and should not pretend to parse
dependent syntax; resilience on incomplete files and useful highlighting are
the goals. VS Code's official [syntax highlighting guide](https://code.visualstudio.com/api/language-extensions/syntax-highlight-guide)
defines the TextMate grammar contribution and language registration surface.

## Acceptance

- A minimal extension registers `.hthr`, comments, brackets, and a Heather
  language identifier.
- The TextMate grammar scopes declarations, binders, types, constructors,
  literals, comments, keywords, Unicode connectives, and operators sensibly.
- Representative library files have snapshot/tokenization fixtures, including
  malformed and partially written source.
- Keyword and fixed-symbol inventories are checked against the same canonical
  data used by other editor integrations where possible.
- Packaging and local installation are documented; publication is a separate
  explicit decision.

## What it assumes from elsewhere

- **[[tree-sitter-zed-language-support]]** owns the richer structural grammar
  and shared drift fixtures. Assumed here: only that common lexical inventories
  can be reused without making TextMate depend on Tree-sitter at runtime.
- **[[machine-readable-syntax-manifest]]** owns the keyword, punctuation, and
  operator inventory this regex grammar consumes or validates against.
