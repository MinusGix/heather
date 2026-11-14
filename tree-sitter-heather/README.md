# tree-sitter-heather

Tree-sitter grammar for the [Heather](https://github.com/MinusGix/heather)
proof language. It intentionally owns the concrete syntax tree, while
`syntax-inventory.json` and the fixtures under `test/fixtures` keep its lexical
surface aligned with Heather's recursive-descent parser.

## Development

Requires Node.js 20 or newer.

```sh
npm install
npm run generate
npm test
../scripts/check-tree-sitter
```

`npm run generate` refreshes the checked-in `src/parser.c`, `grammar.json`, and
`node-types.json`. The repository-level check also validates every Zed query,
parses the positive fixtures with both parsers, confirms negative/recovery
fixtures are rejected by Heather, parses Heather's checked library corpus with
Tree-sitter, and verifies the fixed lexical inventory.

When Heather gains a keyword, update the Rust parser and
`syntax-inventory.json` in the same change. A fixed symbol is a row of the token
kinds' table, `TOKEN_KINDS` in `lib/lang/lexer/lexer_kinds.hthr`, which the Rust
lexer matches by (`crates/linked/generated/kinds.rs`, written from it by
`scripts/linked`); the check reads the spellings there and wants each in
`grammar.js`, but those the parser refuses (`rejected_fixed_tokens`). The drift
check will name whichever side is stale. CST productions remain hand-maintained in `grammar.js`; they
must not be generated mechanically from the recursive-descent parser.

## Release

Run the full check, commit the generated sources, and tag a semantic version.
Then update the grammar `rev` and extension version in
`editors/zed/extension.toml` to the exact release commit. Never point the Zed
extension at a branch: its revision is deliberately immutable.
