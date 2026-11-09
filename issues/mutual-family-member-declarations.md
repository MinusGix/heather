---
title: A member declaration on a mutual family's member is refused: the owner is not found
status: open
labels: [elaboration,inductives,surface]
area: language
milestone: [math-metatheory]
created: 2026-11-09
updated: 2026-11-09
---

A member declaration on a member of a mutual family is refused as if its
owner did not exist:

```heather
inductive Tm { Bv(index: Nat), Node(op: Nat, args: Args) }
inductive Args { ANil, ACons(binds: Nat, head: Tm, tail: Args) }

fn Tm::size(self t: Tm) → Nat { match t { Bv(_) => 1, Node(_, ts) => Succ(ts.size()) } }
fn Args::size(self ts: Args) → Nat { match ts { ANil => 0, ACons(_, t, rest) => t.size() + rest.size() } }
```

```
error: `Tm` is not a type, a type former or a function in scope, so `Tm::size`
attaches to nothing — a member declaration is `fn <Type>::size(…)` …
```

The same two functions written free (`fn tm_size`, `fn args_size`) form a
structural group and check. A type-parameterised group (`Tm<O>`, `Args<O>`)
behaves the same way. The message comes from the owner lookup in
`crates/elab/src/lib.rs` (the "attaches to nothing" arm); the mutual
family's members are evidently not registered where that lookup reads.

Found writing a generic syntax for the heather-coq port
(`docs/heather-coq-port-assessment.md`, PR #158): a syntax with a sort of
terms and a sort of argument lists is the first thing such a development
declares, and `lib/`'s style (operations on their type as methods, dot
calls) is not available on it. The probe uses free functions throughout.

## Acceptance

`fn D::f(self x: D, …)` and `theorem D::f` on a mutual family's member
elaborate, dot calls resolve to them, and a cycle of member declarations
over the family is one structural group as a cycle of free functions is.
Probes in `lib/_tests`.

Related, from the same probe: [[mutual-group-type-valued-members]] and
[[wide-inductive-lemma-quadratic-gate]].
