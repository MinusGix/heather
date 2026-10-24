---
title: A .hthr test corpus with inline expectations, and tests that name imports
status: open
labels: [testing,tooling,design]
area: infrastructure
created: 2026-10-24
updated: 2026-10-24
---

About 1000 of the 2528 elab integration tests are a Heather program in a
Rust string handed to an `ok(…)`-style helper. The test asserts nothing the
program doesn't already assert by checking. The wrapper costs editor, LSP and
formatter support. The lib-layout move (#145) hand-edited 1094 test lines
that `scripts/lib-paths --fix` could not reach. It also costs per-file helper
dialects and test-binary link work. Separately, 105 test files hand-maintain
library closures (891 `include_str!` lines, in dependency order, some ordered
for the image cache's sake). See `docs/test-value-audit.md` §3.3, §4.2, §4.3.

## Proposal

1. `support::library_for(&["rat"])`: resolve imports through
   `heather_cli::loader` in place of the hand-ordered `MODULES` lists. The
   prefix key becomes the root set. A library edit then stops relinking every
   binary that `include_str!`s the file
   (`docs/testing-architecture-design.md` §2.2). The sentinel's exact lane
   should see one run of it, since it touches image keys.
2. A `.hthr` corpus, `tests/hthr/<area>/*.hthr`, checked by one runner. Every
   declaration must check unless a directive above it says
   `// expect-error: <fragment>`, in which case its first error must match.
   The checker already reports every diagnostic with spans; the runner maps
   them to declarations. Precedents: rustc UI tests, Lean 4 `#guard_msgs`,
   Idris 2 `failing` blocks.
3. Migrate lazily: new elaborator-behaviour tests go to the corpus, and old
   ones move when their file is touched.

## Open question for Minus

Whether to add an in-language `failing "fragment" guards Name { … }` block later, as
Idris 2 has (without the `guards`). Minus (2026-10-24) likes it but worries about
noise next to theorems. Proposed answer (doc §4.3): blocks live in
`lib/_tests` by convention, `guards` gives the LSP a link from the theorem to
its controls, and editors fold the few that stay inline. If `guards` is all
a block adds, the comment directive can carry it instead. Either way it
reuses the corpus runner's matcher. Decide after the corpus shows how often
the directive is used.
