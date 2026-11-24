# Heather for VS Code

Syntax highlighting for `.hthr` files: a TextMate grammar
(`syntaxes/heather.tmLanguage.json`) plus comment toggling, bracket matching
and auto-closing for `( ) [ ] { } ⟨ ⟩ ⟦ ⟧`.

The Zed extension (`editors/zed`) highlights from the Tree-sitter grammar;
VS Code cannot, so this grammar is lexical. It follows the same conventions:

- Keywords are those of `tree-sitter-heather/syntax-inventory.json`. Heather's
  keywords are contextual, so a word used as a field, named argument or
  member (`within: …`, `prefix.written`) is left as a name.
- Capitalized names are types and constructors; a name before `(` is a call.
- `rule theorem`, `register def`, … colour the prefix as the generator.
- `// expect-error: …` lines mark the directive.

## Install

From the repository root, link the folder into VS Code's extensions and
reload the window:

```sh
ln -s "$PWD/editors/vscode" ~/.vscode/extensions/heather
```

(For VSCodium the directory is `~/.vscode-oss/extensions`.) To build a
`.vsix` instead: `cd editors/vscode && npx @vscode/vsce package`.

## Checking a grammar change

Tokenize library files with `vscode-textmate` and look for text left without
a scope, or dump the scopes of a sample line by line; `Developer: Inspect
Editor Tokens and Scopes` in VS Code shows the same per token.
