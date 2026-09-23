# Heather for Zed

This extension recognizes `.hthr` files and provides Tree-sitter highlighting,
matching brackets, indentation, outline entries, function/type text objects,
and compiler diagnostics plus names through `heather-lsp`.

## Language server

Install the server somewhere on Zed's `PATH`:

```sh
cargo install --path crates/lsp
```

The server checks an opened file, including its import closure, from the
buffer Zed sent rather than from the last saved copy. It checks again when the
file is saved. Edits between saves update document and workspace symbols but
do not run the compiler on every keystroke. This keeps large standard-library
modules responsive while still making save the natural diagnostic boundary.

Open the Heather repository as the Zed project. The server automatically adds
`lib/std`, `lib`, and the project root to Heather's module search path, so a
file anywhere under `lib/` can resolve its standard-library imports.

## Local development

1. Run `npm install` in `tree-sitter-heather`, then run
   `scripts/check-tree-sitter` from the repository root.
2. Install `heather-lsp` as above, then run `scripts/zed-dev-extension` from
   the repository root (the script itself is independent of its working
   directory, so an absolute invocation works from anywhere). It creates the
   ignored `editors/zed/.dev` extension with a local Git snapshot of the
   current `tree-sitter-heather` working tree, including uncommitted changes.
   The language config and queries remain linked directly to
   `editors/zed/languages`.
3. In Zed's Extensions page, choose **Install Dev Extension** and select the
   printed `editors/zed/.dev` directory. Rerun the script and choose **Rebuild**
   on the extension after grammar changes. Use `zed: open log` if compilation
   fails.

Only the grammar is snapshotted; the queries and Rust extension shim are
symlinked live. So a grammar node added in `tree-sitter-heather` and referenced
from a query loads against a snapshot that predates it, and Zed drops the whole
language with `Error loading highlights query … Invalid node type <name>` in
the log — with no other symptom than highlighting that stops.
`scripts/check-tree-sitter` therefore refreshes an existing `.dev` on every
run; a **Rebuild** in Zed is still what recompiles the new revision.

The published `extension.toml` stays untouched and release-ready throughout;
there is no tracked local URL to remember to restore and no Git
`skip-worktree` state hiding future manifest updates.

Before release, set the published manifest's `rev` to the exact commit that
contains the generated parser. Bump the extension version whenever the grammar
pin or queries change, run `scripts/check-tree-sitter`, and submit the extension
repository/revision update to the Zed extensions registry.
