---
title: Regenerate the tree-sitter parser for binding statements
status: open
labels: [tooling,editor]
area: infrastructure
created: 2026-11-01
updated: 2026-11-01
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
