---
title: "Lint imports that contribute nothing to a module"
status: open
labels: [tooling,lint,frontend,modules,ergonomics]
area: language
created: 2026-08-22
updated: 2026-09-16
---

Report an import only when removing it would leave the module's elaboration
unchanged. A textual name-use scan is insufficient: imports can contribute
instances, class ancestors, designations, constructors, and qualified names
without the imported module's name appearing in the final expression AST.

This is also the first lint whose answer exists only at module completion.
Extend the source-lint runner with a module-finalization phase and record which
module supplied each successful resolution, instance search, designation, and
other import-mediated decision. An import is unused when none of those routes
depends on it and it is not required transitively to make another used import
load.

Selected imports deserve a finer message: `import m::{a, b}` may use `a` but
not `b`. Removing an unused selected name is safe even when some other semantic
service from `m` is used; removing the whole import is not.

## Acceptance

- Entirely unused imports and unused members of selected import lists are
  distinguished.
- Qualified references, unqualified references, constructors, instances,
  inherited class evidence, and designated operators all count as semantic
  uses of the module that supplied them.
- Imports needed only transitively are handled according to the module
  visibility contract rather than a textual approximation.
- Parse/elaboration failures produce no unused-import findings for the failed
  module.
- Findings are emitted once when a directory is checked as a deduplicated
  closure.

## What it assumes from elsewhere

- [[lint-roadmap]] owns profile policy and sequencing. This rule is intended
  for the conservative default once its semantic controls are clean.

## Log

- 2026-08-22: Filed as the preferred next infrastructure customer: it pays for
  a module-finalization lint phase while providing a high-confidence cleanup.
- 2026-09-16: The `pair`/`int`/`omega` imports of `docs/showcase/calc_parser.hthr` are the sharp case for this lint's semantic definition: nothing in the file names them, but each is required by the mutual `decreases` machinery, so a textual scan would wrongly flag all three. [[feature-implicit-module-dependencies]] proposes to remove the requirement; if it lands, the same three lines become genuinely unused and this lint should start flagging them.
- 2026-09-16: The inverse reading of the same module-finalization table — "what did this import contribute" rather than "did anything" — is [[explain-why-an-import-is-needed]]; if this issue lands, that one should be a presentation layer over it and not separate machinery.
