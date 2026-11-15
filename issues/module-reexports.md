---
title: Support explicit identity-preserving module reexports
status: closed
labels: [syntax,elab,cli]
created: 2026-09-15
updated: 2026-09-15
---

## Problem

The parser library is split between `lib/std/parser/parser.hthr` and six modules in
`lib/std/parser/`. Clients must import each component and qualify moved names
with its owning module. There is no explicit reexport facility to expose a
stable library interface while organizing implementation and proof files.

## Scope

Design and implement explicit module reexports, with a parser umbrella module
as the acceptance client. Ordinary imports must retain their current visibility
rules; importing a dependency must not implicitly publish its declarations.

Reexports must refer to the original checked declaration. They must preserve
nominal type and constructor identity, operation-indexed typeclass identities,
receiver-method resolution, and axiom provenance. Function wrappers and duplicate
type declarations are not equivalent substitutes.

## Design questions

- Choose surface syntax for selected exports and decide whether whole-module
  reexports belong in the initial implementation. Renaming can be a separate
  extension if it would obscure the identity and visibility rules.
- Define qualified access through a facade, listed imports from a facade, and
  bare-name ambiguity. A diamond reaching the same declaration should retain
  one identity; two different declarations sharing a name need an explicit
  disambiguation rule rather than import-order precedence.
- Decide how constructors, class methods, instances, and generated declarations
  participate while respecting existing restrictions on generated names.
- Preserve loader cycle and duplicate-module diagnostics and record reexport
  dependencies in semantic images, cache invalidation, and source diagnostics.

## Acceptance

- A client can use `import parser;`, `parser::token`, core parser types, receiver
  combinators, and their proof certificates through the facade.
- A client importing both a component and its facade can interchange values and
  certificates without conversions or duplicated declarations.
- Exercise selected imports, transitive and diamond reexports, conflicting names,
  missing/unexported names, receiver dispatch, constructor access, and dependency
  changes through both the CLI loader and semantic-image replay.
- Axiom audits report the original proof dependencies through either spelling.
- Migrate the parser to an acyclic facade layout: move the current core behind
  the umbrella so components do not import a facade that reexports them.

Hierarchical module paths and recursive directory discovery are separate design
questions; this issue does not require them to ship with reexports.

## References

- `docs/language/modules-design.md`: existing visibility and ambiguity rules.
- `lib/std/parser/README.md`: current component layout and import instructions.
- [[axiom-provenance]] owns dependency auditing; reexports must preserve it.

## Log

- 2026-09-15: Landed: `export m::{…};` as a selected, identity-preserving reexport (aliases in the visibility index only; origin resolution, by-origin ambiguity, constructor inclusion, generated-name refusal, loader edge, image field + replay validation). `lib/std/parser/parser.hthr` is now a facade over `parser_core` and the six components. Design in docs/language/modules-design.md §3.4; tests in crates/elab/tests/modules.rs and crates/cli/tests/semantic.rs. Whole-module reexport, renaming and hierarchical paths stay unbuilt by decision.
