# Heather for Zed

This extension recognizes `.hthr` files and provides Tree-sitter highlighting,
matching brackets, indentation, outline entries, and function/type text
objects.

## Local development

1. Run `npm install` in `tree-sitter-heather`, then run
   `scripts/check-tree-sitter` from the repository root.
2. For uncommitted grammar work, temporarily change the grammar repository in
   `extension.toml` to an absolute `file:///.../heather` URL; keep
   `path = "tree-sitter-heather"`.
3. In Zed's Extensions page, choose **Install Dev Extension** and select this
   `editors/zed` directory. Use `zed: open log` if grammar compilation fails.

Before release, restore the HTTPS repository and set `rev` to the exact commit
that contains the generated parser. Bump the extension version whenever the
grammar pin or queries change, run `scripts/check-tree-sitter`, and submit the
extension repository/revision update to the Zed extensions registry.
