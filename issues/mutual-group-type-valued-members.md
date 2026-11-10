---
title: A Type-valued function over a mutual family: calls inside connectives are not group edges, and True reads as Bool's
status: closed
labels: [elaboration,inductives,recursion]
area: language
milestone: [math-metatheory]
created: 2026-11-09
updated: 2026-11-09
---

Two refusals met by a `Type`-valued function over a mutual family, both in
the structural-group path (`crates/elab/src/mutual_rec.rs`). Each has a
workaround that only reorders spelling, so both are gaps and not limits.

**1. A sibling call inside a connective's operands is not an edge.**

```heather
fn Lc<O>(t: Tm<O>, d: Nat) → Type {
    match t { Bv(i) => i < d, Fv(_) => True, Node(_, ts) => LcArgs(ts, d) }
}
fn LcArgs<O>(ts: Args<O>, d: Nat) → Type {
    match ts { ANil => True, ACons(b, t, rest) => Lc(t, d + b) ∧ LcArgs(rest, d) }
}
```

```
error: unbound name `LcArgs`. `LcArgs` is declared below
```

`P ∧ Q` is `And<P, Q>`, so the calls to `Lc` and `LcArgs` in the second
function sit in type arguments. `callees` walks expressions for application
heads and does not reach them, so the only edge seen is `Lc → LcArgs`, there
is no cycle, and no group is formed. Spelling the conjunction as a call
(`fn both(P: Type, Q: Type) → Type { P ∧ Q }`, then `both(Lc(…), LcArgs(…))`)
forms the group. `∨` and `∃` have the same shape.

**2. `True` in a group member's arm is read as `Bool`'s constructor.**

With the group formed, `Fv(_) => True` and `ANil => True` are refused:

```
error: `True` is a constructor of `Bool`, which is not the expected type here
```

In a function that is not part of a group the same arm elaborates as the
proposition (`lib/kernel_model/kernel_reduction.hthr`, `Tm::Lc`). The
group's arms evidently reach elaboration without the result type `Type` as
the expected type that picks the reading. `fn top() → Type { True }` and
`top()` in the arm is the workaround.

Found writing a generic syntax for the heather-coq port (PR #158); a
local-closure predicate over terms and argument lists is the second
declaration such a development makes.

## Acceptance

The two functions above elaborate as written, as one structural group.
Probes in `lib/_tests`, with `∨` and `∃` forms beside `∧`.

Related, from the same probe: [[mutual-family-member-declarations]] and
[[wide-inductive-lemma-quadratic-gate]].

## Log

- 2026-11-09: Done. (1) `mutual_rec::callees` scans the expressions inside
  the types a body writes (`walk_with_types`: type arguments, so `∧`/`∨`,
  and type literals, so `∀`), and the call rewrite maps them the same way
  (`Calls::ty`); `∃` already reached its `λ` body. (2) The checker's
  universe arm reads `El(«Ty n»)` as the universe `Ty n` structurally
  (`expected_universe`, crates/elab/src/lib.rs): the group's arm is checked
  against its motive's codomain, which arrives as the decode of the code
  `Type` rather than `Type`, so `True` fell through to `Bool`'s
  constructor. Probes in lib/_tests/lang/mutual_type_valued_tests.hthr:
  `∧`, `∨`, `∃` and `∀` groups, values whose types compute through the
  group, and a theorem group (`lc_mono`) over one.
