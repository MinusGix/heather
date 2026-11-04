---
title: Regenerate the tree-sitter parser for binding statements and `varies`
status: open
labels: [tooling,editor]
area: infrastructure
created: 2026-11-01
updated: 2026-11-02
---

`tree-sitter-heather/grammar.js` and `syntax-inventory.json` learned
`let x <- e;`, `←`, the expression statement `e;` and the nested bind
`<- e` with layer 1 of docs/sequencing-surface-design.md (§13), but
`src/parser.c` was not regenerated: the cloud container could not fetch
`tree-sitter-cli`. Until it is, editors parse a binding statement as an error
node. Run `tree-sitter generate` and `tree-sitter test` in
`tree-sitter-heather/`, add a corpus case, and add `"<-" "←"` to both
`highlights.scm` files (left out so that the queries do not name a node the
current parser lacks).

The `varies A` clause on `inductive`/`record`/`codata`
(docs/lambda-carrier-instances-design.md §7.1, rule `varies_clause`) is in
`grammar.js` and the inventory since 2026-11-02 and waits on the same
regeneration; add a corpus case for it too.

## Log

- 2026-11-02: `⊓` (the meet, multiplicative rung) joined `grammar.js`, the inventory and both `highlights.scm` on 2026-11-02 and waits on the same regeneration. `tree-sitter-cli` installs in the cloud container now (`npm install` in `tree-sitter-heather/` succeeded), but `tree-sitter generate` stops on the current `grammar.js` before reaching the new symbol: `Unresolved conflict for symbol sequence: 'generate' '{' if_expression • '}'`, between `statement_form` and `_expression` (the statement `if` the imperative-statements round added). That conflict needs a precedence or a `conflicts` entry first.
