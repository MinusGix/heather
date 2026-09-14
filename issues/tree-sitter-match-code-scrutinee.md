---
title: Parse an ordinary match on a variable named code in Tree-sitter
status: open
labels: [tooling,editor,syntax]
created: 2026-09-14
updated: 2026-09-14
---

The whole-library Tree-sitter corpus reports an ERROR at zero-based rows
99–100 of `lib/std/arch/x86_64/call_summary.hthr`, where `CallPremises` starts
an ordinary `match code { Nil => ... }`. Heather itself accepts this module.
The compiler's corresponding ambiguity was fixed by [[match-scrutinee-named-code]].

Discovered during [[result-propagation]] validation. Reproduced with the
unchanged HEAD grammar and generated parser in a separate `/tmp` checkout,
using the same unchanged source file and a separate Tree-sitter cache. It is
not introduced by the propagation productions.

Reproduce from `tree-sitter-heather`:
`XDG_CACHE_HOME=/tmp/heather-tree-sitter-cache node_modules/.bin/tree-sitter parse ../lib/std/arch/x86_64/call_summary.hthr --quiet`.

Resolve the head-expression/quotation ambiguity while preserving actual
`code { expression }` quotations. Add this ordinary scrutinee as a corpus case.
