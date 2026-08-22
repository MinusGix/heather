# Heather for Zed

This extension recognizes `.hthr` files and provides Tree-sitter highlighting,
matching brackets, indentation, outline entries, and function/type text
objects.

## Local development

1. Run `npm install` in `tree-sitter-heather`, then run
   `scripts/check-tree-sitter` from the repository root.
2. Run `scripts/zed-dev-extension` from the repository root (the script itself
   is independent of its working directory, so an absolute invocation works
   from anywhere). It creates the ignored `editors/zed/.dev` extension with a
   local Git snapshot of the current `tree-sitter-heather` working tree,
   including uncommitted changes. The language config and queries remain linked
   directly to `editors/zed/languages`.
3. In Zed's Extensions page, choose **Install Dev Extension** and select the
   printed `editors/zed/.dev` directory. Rerun the script and choose **Rebuild**
   on the extension after grammar changes. Use `zed: open log` if compilation
   fails.

The published `extension.toml` stays untouched and release-ready throughout;
there is no tracked local URL to remember to restore and no Git
`skip-worktree` state hiding future manifest updates.

Before release, set the published manifest's `rev` to the exact commit that
contains the generated parser. Bump the extension version whenever the grammar
pin or queries change, run `scripts/check-tree-sitter`, and submit the extension
repository/revision update to the Zed extensions registry.
