---
title: Let a member name its owner's other members bare
status: closed
labels: [frontend,elaboration,modules,ergonomics]
area: language
created: 2026-10-26
updated: 2026-10-26
---

Inside a member of `T`, the member's own name is bound (recursion) but its
siblings are not: in `fn Box::twice(self b: Box)`, bare `get` is "unbound
name `get`" although `Box::get` is declared above; `Box::get(b)` and
`b.get()` work (probe 2026-10-26). The library writes `Owner::x` inside
`Owner`'s own members 3,409 times (`scripts/signature-census`), e.g.
`List::cong_cons` throughout `list.hthr`, `Rat::…` throughout `rat.hthr`.

Proposal (docs/sections-design.md §6): inside the body of a member of `T`,
`T`'s members are candidates for a bare name at the **same rank as every
other visible name** — no precedence, not even locals-beat-imports, so that a
file's own `Rat::add` can never silently take over a bare `add` that resolves
to an imported declaration today (docs/modules-design.md §8, second
invariant). Landing it can only turn existing library text into ambiguity
errors, which the round qualifies.

Keyed on the declaration's owner, not on any block, so it is independent of
[[section-spliced-heads]].

## Acceptance

- A bare sibling resolves inside a type-owned, class-owned and
  function-owned member, in-module and for members imported from another
  module.
- A bare name that is both a sibling and an ambient (or imported) declaration
  is ambiguous, naming both; outside a member of `T`, `T`'s members are not
  candidates.
- The library still checks with identical count columns
  (`scripts/timings --diff`) before any `Owner::` is dropped; dropping them is
  a separate, opportunistic edit.

## What it assumes from elsewhere

- **[[type-owned-namespaces]]** owns how subject namespaces are reached.
  Assumed here: only that a non-receiver reach inside the owner is in its
  direction (its 2026-09-18 log names the missing non-receiver reach).

## Log

- 2026-10-26: Built (PR #191, 2026-10-26), at ambiguity rank as proposed. `owner_member` /
  `owner_rewrite` in `crates/elab/src/lib.rs` rewrite a bare variable or call
  head inside a member of `T` to `T::x` when `T::x` is a declared member and no
  binder, alias or the member's own name binds `x`; if `x` also resolves on its
  own (module-local declarations included) it is an ambiguity naming both.
  Instance-synthesized declarations have no owner. Mutual groups form by base
  name, so bare calls between members are one group. Landing made 75 bare names
  in 10 library files ambiguous (`Nat::cong`/`Int::cong` vs prelude `cong`,
  `Bisim`/`Eutt` `sym`/`trans` vs equality's, `Node::mentions` vs lowering's
  `mentions`, `Finite::NearestEven` vs the `Mode` constructor in defaults,
  `Target::At` vs the `Prog` constructor); each now spells its old reading, so no term changed. Tests
  `crates/elab/tests/owner_siblings.rs`,
  `mutual_recursion::members_calling_each_other_bare_are_one_group`. No sweep of
  the 3,409 qualified references (docs/sections-design.md §9).
