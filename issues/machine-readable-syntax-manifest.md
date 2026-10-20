---
title: "Export one machine-readable manifest of Heather's lexical surface"
status: open
labels: [tooling,syntax,editor,testing]
area: language
created: 2026-08-20
updated: 2026-08-20
---

Heather's lexer and parser are the authority for the language, but every
editor integration needs overlapping static facts: file suffixes, keywords,
declaration introducers, comments, delimiters, fixed punctuation, Unicode
connectives, operator symbols, fixity, precedence, and associativity. Copying
those inventories into Tree-sitter, TextMate, Zed, documentation, and future
preview integrations guarantees quiet drift.

Export a small, versioned, machine-readable syntax manifest from the same Rust
data that drives the real lexer/parser wherever practical. The manifest is not
a second grammar and must not make parsing data-driven: it describes the stable
lexical and precedence facts external tools can safely consume. Recursive
grammar structure, contextual disambiguation, recovery, and semantic
resolution remain owned by the parser and by each consumer's grammar.

The first design task is to remove accidental duplication inside the parser
itself. For example, infix recognition, bare operator-symbol recognition, and
fallback resolution currently have related but non-identical tables. Shared
typed declarations should generate the manifest and feed those internal views
without forcing unrelated concepts into one table.

## Proposed contents

- manifest schema/version and Heather file suffixes;
- reserved and contextual keywords, with their roles;
- comment and literal delimiters;
- fixed punctuation and Unicode connective/binder tokens;
- operator spelling, fixity, precedence, and associativity;
- lexical character-class policies once [[notation-extensibility]] lands;
- explicit exclusions for facts that require parsing or elaboration.

## Acceptance

- The checked-in manifest is generated deterministically from compiler-owned
  declarations and CI fails when regeneration changes it.
- Parser tests prove the exported operator precedence/associativity agrees with
  actual parses, rather than trusting the serialized numbers alone.
- Tree-sitter and TextMate builds consume or validate against the manifest's
  relevant inventories; neither maintains an unchecked keyword/operator copy.
- Schema changes are versioned and consumers fail clearly on an unsupported
  version.
- Adding a keyword or fixed operator has one authoritative compiler edit plus
  deliberate consumer updates, with drift reported by the ordinary test path.
- The manifest does not claim to encode Heather's full grammar or name/operator
  resolution environment.

## What it assumes from elsewhere

- **[[surface-syntax]]** owns the language grammar. This issue exports a
  tooling view of landed lexical facts and never becomes an alternate syntax
  specification.
- **[[notation-extensibility]]** owns which future symbols are classified by
  fixed tables versus Unicode properties. The manifest records that decision
  after it lands.

## Log

- 2026-08-20: Filed from the editor-support discussion. The intended economy
  is a shared lexical contract and differential fixtures, not mechanically
  generating a Tree-sitter grammar from Heather's recursive-descent parser.
