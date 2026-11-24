---
title: A module image moved over another world fails instead of rebuilding when the store is rewritten concurrently
status: open
labels: [tooling,infrastructure,cache]
area: infrastructure
created: 2026-11-24
updated: 2026-11-24
---

Under `scripts/test --pr`, three native test targets failed together because
a library module's image could not be moved into the world it was being
replayed in. Each target passed when run alone straight afterwards, on the
same tree (`native_cat` 11/11, `native_program` 21/21, `native_tools`
21/21). Seen 2026-11-24 on `ccr-a42b8144-7er7yg` right after merging two
branches that changed the elaborator (`claude/proof-tooling-omega`) and the
runtime generator (`claude/span-multiword`), so most library images were
being rewritten by a new build while the test binaries' children
(`write-elf`, `compile-x86`) shared the stores.

The messages, from `crates/cli/src/semantic.rs`:

```
error: module `native_structured_meaning` could not be placed in its world: `x86_64_stack`'s world has another length
error: module `native_compile_frames` could not be placed in its world: moving `native_compile_frames`: a referenced dependency binding has no counterpart in the new world
```

(the first is `delta.over_prefix(world.psi().clone())` failing in
`canonical_delta`, about line 832), beside many lines of `module … replayed
from an image of another build` and `moved from an image of the same source
over another dependency world`. Failing tests:
`native_cat::{a_program_can_carry_its_own_stack, compiled_cat_runs_as_cat}`,
`native_program::{programs_with_narrow_words_execute,
records_of_two_words_are_passed_and_returned}`,
`native_tools::compiled_yes_takes_its_line_as_gnu_yes`.

This looks like the same class as [[image-sweep-removes-planned-image]]: a
module already planned as a replay, or moved over another dependency world
(docs/infrastructure/module-interface-cutoff-design.md), meets a store that
another process changed between planning and reading, and the failure is an
error rather than an ordinary cache miss that rebuilds. Not yet reproduced
deliberately.

## Done when

A move or replay whose world no longer matches (another length, a binding
with no counterpart) falls back to elaborating the module, as a miss does,
with a one-line note; and a reproduction (two processes over one store, one
rewriting the images the other has planned) passes.
