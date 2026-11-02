---
title: Reflect a match on a list into rt
status: open
labels: [native,runtime,frontend]
area: heather-in-heather
milestone: [nh-heap]
created: 2026-11-02
updated: 2026-11-02
---

The `rt` reflector cannot read a `match` on a `List`. The host's `Arms`
request presents only a tier-0 match, which is one kernel `Case` on a
two-constructor type (`crates/elab/src/host.rs`, `arms_request`). An
elaborated `match xs { Nil => …, Cons(h, t) => … }` on a recursive type is
not that term. The `View` of it falls through to the reflector's last arm, so
the refusal is "a form the reflected fragment does not have"
(`lib/native/runtime/rt_reflect.hthr`). Found writing `tac`'s and `sort`'s
customers ([[runtime-fn-arena-lists]], docs/native-heap-arena-design.md §7.1).
`List::bytes_before` in `lib/native/runtime/line_tools.hthr` matches on the
rest of a line.

## Scope

- `Arms` presents a `match` on `List` (and on any inductive the reflector
  lays out) with the same answer it gives for a tier-0 match: the scrutinee,
  one arm per constructor as a λ over its payloads, and the convoy's
  arguments. If the elaborated term is an eliminator application, the host
  says which argument is which arm.
- `rt` gains a list case node (`Case(xs, nil, cons)`, with the head and the
  tail bound in the cons arm) whose meaning is the match. It pins by `refl`
  against the elaborated match at `Bytes` and at `Lines`.
- Under the arena (N4), a list case lowers to a read of the cell's header:
  name 0 is `Nil`, and otherwise the next cell's name and the payload.

## Done when

The reflector reads a `match` on a `List<BitVec(8)>` and on a
`List<List<BitVec(8)>>` into the case node, each pinned by `refl` in
`lib/_tests/native/runtime/rt_tests.hthr`. A match on an unsupported
inductive still refuses, and the refusal names the type.
