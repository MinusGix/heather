---
title: Let the datarepr form take constructor images whose laws hold on a success arm
status: open
labels: [datarepr,elaborator]
area: heather-in-heather
milestone: [nh-heap]
created: 2026-11-02
updated: 2026-11-02
---

docs/datarepr-design.md §1.3 (FINDING 1) settled that constructor images are
operations: consumption is total, construction may be guarded or carry an
outcome, and the image laws are then stated on the success arm. The v1
`datarepr` form (`crates/elab/src/datarepr.rs`) takes only total images with
unguarded laws (`Cons_abs`, `Cons_inv` under `inv` alone).

The first repr that needs more is the arena's (`lib/native/native_arena.hthr`,
docs/native-heap-arena-design.md §4.1): `ArenaRef::cons` is total as a
function, but `inv` of its result needs the arena to be within its limit, and
no `inv` can carry that, since consing onto any list can overflow it. Its laws
are theorems today (`ArenaRef::cons_abs` takes the bound as a hypothesis).

## Scope

- A clause form for a guarded image: the guard as a hypothesis of `Cons_abs`
  and `Cons_inv` (an input-determined precondition, the bag `cons` of §6.2,
  is the same shape), or an outcome-typed image whose laws are on its success
  arm.
- The arena's laws declared as a repr of `List<List<BitVec(8)>>` with it.
- What reprgen (§3) does with a guarded image: a transferred body that
  constructs inherits the guard as a precondition or bubbles the outcome
  (§2's ladder).

## Done when

`native_arena`'s representation is a `datarepr` declaration whose `Cons`
image is guarded by the arena's limit, and a negative control (an unguarded
`Cons_inv` for it) is refused with its reason.
