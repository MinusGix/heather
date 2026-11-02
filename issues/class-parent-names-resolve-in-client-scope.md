---
title: Resolve a class's parent names where the class was declared, not at the client
status: open
labels: [traits,classes,modules,ergonomics]
area: language
milestone: [math-classes]
created: 2026-11-02
updated: 2026-11-02
---

A class's `extends` clause names its parents (and their index relations) by
the names in scope where the class is declared. A client that only imports the
class still has those names resolved in the client's own scope. If the client
does not also import the parent's module, the dictionary type cannot be
formed.

Seen twice in the math-classes rounds:

- `StrictOrder`/`PseudoOrder` gained a tagged `Preorder<A>(le)` parent
  (docs/strict-order-presentation-design.md §2.2). Every module that opens
  `section<A: PseudoOrder(…)>` or a class above it was then refused with
  "`Preorder` takes no type arguments (only a `fn` or `theorem` declared
  `Preorder<A, …>` does)", reported at the end of the module, once per
  declaration. Sixteen modules gained `import order;` to get past it.
- The ordered-algebra round: an instance head that names `RelId<Nat>` needs
  `import relation`, or parent lookup fails with "missing fields: rel_refl…"
  and the index is shown as `_`.

Every client of `ordered_field` already imports `relation_props` for the same
reason (`Equivalence`), which is why the rule went unnoticed.

## What is wanted

A class records its parents by resolved declaration, as an instance key's
carrier already is (docs/instance-resolved-key-design.md). Then a client that
can see the class can form its dictionary without importing the parent's
module. Two things this must preserve: a client still needs an import to
*write* the parent's name itself, and module images and the cutoff key on the
resolved names (docs/module-interface-cutoff-design.md).

Until then, the error should at least name the class whose parent failed to
resolve, and the module to import. It should not read as a misuse of
`Preorder` at a span that points at nothing.

## What it assumes from elsewhere

- **[[module-reexports]]** owns re-exporting. Assumed here: only that an
  `export` is not the fix, because a class's parents are not part of what a
  client asked to see.
