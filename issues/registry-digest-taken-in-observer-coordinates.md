---
title: A module's registry digest depends on which world first asks for it
status: closed
labels: [tooling,caching,performance,bug]
area: infrastructure
created: 2026-11-14
updated: 2026-11-14
---

The early cutoff (`docs/module-interface-cutoff-design.md`) moves a module's
image onto a changed dependency world when the world's registries and the
names it looked up are unchanged. Each module's registry contribution enters
that comparison as a digest of its `RegistryPart` projection, which blanks
every Ψ position and appends the content hash of what the position named.

A registry part names bindings by where they sit in its module's own
canonical world. `SemanticSession::world_view` took the digest over the hashes
of the world it was building, at those positions, and kept it for every later
world. That is right only when the module's canonical world is a prefix of
the observing world (it stands on the spine). Off the spine the positions
name other bindings, so the digest depended on which world first asked for
it.

Within one process the first asker is the same before and after an edit, so
the digests agreed and the cutoff worked. The library gate builds a process
per module (`--build-jobs`), and once an earlier child has stored a moved
image, a later child loads it as a hit and meets the module first in its own
world. Its digest then differs from the one in the record, and the move is
refused with "the world's registries differ". Found on `common`, whose world
holds `string` off the spine; every module downstream of `common` then
re-elaborated.

Measured 2026-11-14 on a 4-core cloud box, release binary, self-checks off:
one trivial theorem appended to `lib/std/num/nat.hthr`, then the gate's build
step over a store matching the tree before the edit. Before the fix 523 of
553 modules cost near their cold time (301 s wall with the debug binary,
against 369 s for an empty store). After it, 190 s wall and 577 CPU-s against
316 s and 1088 CPU-s cold.

## Fix

`world_view` takes a digest over the module's own canonical world: the
observing world's hashes when the module's world is a prefix of it, and
otherwise the same per-module content hashes laid out in the module's order.
Records written before the fix can hold a digest of the old kind; a move over
one is refused once and the module is elaborated and recorded again.

Test: `a_registry_digest_is_the_same_whichever_world_asks_first`
(`crates/cli/tests/semantic.rs`), which fails without the fix.

What the same measurement shows is left:
`issues/expected-refusal-modules-never-moved.md`, and about a second per
moved module of loading its closure
(`issues/build-children-replay-their-imports.md`).
