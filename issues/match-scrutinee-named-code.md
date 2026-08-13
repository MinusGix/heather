---
title: A scrutinee named `code` parses as a quotation
status: open
labels: [frontend,parser,diagnostics]
created: 2026-08-13
updated: 2026-08-13
---

Found writing the showcase (docs/showcase/README.md, friction 1, 2026-08-13): in
`fn run(code: List<Tok>) { match code { ... } }` the parser sees `code {` and
commits to the quotation form `code { … }`, so an ordinary variable named
`code` cannot be matched on (or start any expression a `{` follows). The
error is baffling at the site: ``expected `}` to close the quote`` pointing
at the first match arm.

The quote parse guards only on `Ident("code") + LBrace` (parser.rs, `code {`
lookahead), which is exactly the shape `match <var> {` produces. Options, not
decided here: bind-aware lookahead (a local named `code` in scope wins over
the quote form), a real keyword (breaks the "plain variable named `code`
works everywhere else" property the current lookahead exists to keep), or
keeping the grammar and making the diagnostic name the collision and the
rename that fixes it. Whatever the fix, the diagnostic should stop blaming
the brace.
