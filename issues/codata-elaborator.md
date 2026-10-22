---
title: Codata declarations in the elaborator
status: open
labels: [codata,coinduction,elaborator,kernel]
area: interaction-trees
milestone: [it-coinductive,it-codata]
created: 2026-10-22
updated: 2026-10-22
---

`codata` declarations in the elaborator, over the kernel's `M` / `corec` /
`out` (`docs/kernel-coinduction-design.md` §10 step 4). Design and the
round's record: `docs/codata-elaborator-design.md`.

## Scope of round 1

- Surface `codata D<…>(…) { … }` with type and value parameters, plain and
  function children (dependent domains included).
- Lowering `⟦D⟧ = M(Unit; _. S; _ s. P(s); _ _ _. ⟨⟩)(⟨⟩)` with tier 1's
  shape and a position code per child.
- Constructors as the apomorphism's `in`; `match` through `out` with a
  non-dependent motive.
- Guarded corecursive functions compiled into one `corec`, with fixed and
  varying parameters.
- Declarations over codata bound at layer c, over `M`'s codes ([[codata-codes]],
  design §6). Round 1 used layer-p term definitions for this; the codes
  round removed them.

## Follow-ups

- [[codata-indexed]]: indexed codata, which `Bisim` and eutt need.
- [[codata-nested-guards]]: a constructor nested above a self-call.
- ~~[[codata-codes]]~~: done, codata declarations are bound at layer c.
- The library: the coinductive tree, `approx`, `Bisim`, eutt and the bridge
  (`docs/kernel-coinduction-design.md` §4, §6), milestone `it-coinductive`.

## Log

- 2026-10-22: Round 1 implemented on branch `claude/project-thread-lozmdm`.
  It found that `M` (with `IWf` and `DVec`) is admitted only at layers p/m,
  while every declaration is bound at c and Ψ allowed term definitions only
  at v/c. The fix is a kernel relaxation: bodied term bindings at p, with the
  elaborator choosing p for any declaration that mentions codata or a p
  binding. Minus was asked whether to do this or give `M` codes first; the
  round went ahead on the recommended option (p definitions now, codes
  filed). `crates/elab/tests/codata.rs` covers the four axes, including an
  image round trip and `approx` into the finite `ITree`, and it caught one
  encoding bug: a function child's codomain was left unshifted under its
  binder.
- 2026-10-22: With [[codata-codes]] done, codata declarations are bound at layer c; §6 rewritten, `layers_follow_codata` became `codata_declarations_are_code`, and codata works as a type argument.
