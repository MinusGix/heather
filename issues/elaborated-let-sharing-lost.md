---
title: Elaborated bodies repeat a let-bound value at each use instead of sharing it
status: open
labels: [elaboration,sharing,native,metaprogramming]
area: language
milestone: [nh-front]
created: 2026-11-01
updated: 2026-11-01
---

Found building the `rt` reflector (`lib/native/runtime/rt_reflect.hthr`,
V5 of `docs/runtime-fn-setups-design.md` §12). The design assumed a block's
`let` is an alias whose value is one shared subterm in the kernel term
(`docs/let-and-blocks-design.md` §4.4), so the host could hand out one
handle per shared subterm and a reflector memoise on handles. The host now
does exactly that (`Run::issue_shared` in `crates/elab/src/host.rs`, keyed on
the subterm's address), but a probe of `Body(f)` for

```heather
fn chain(x: BitVec(64)) → BitVec(64) { let a = x.add(x); let b = a.bxor(a); let c = b.sub(b); c.bor(c) }
```

shows a tree: every use of `a`, `b`, `c` is its own application node (four
copies of `x.add(x)`), and only the leaf variables are pointer-shared. The
kernel's own traversals keep a DAG shared (`subst.rs`, "Keeping a shared DAG
shared"), so the copying happens before: in how the elaborator substitutes a
let's value into the block (a `Term` cloned per occurrence rather than its
`Rc`), or in a pass over the finished body.

## Consequences

- The reflector numbers values instead (as the Rust reflector does), so its
  output is right, but it still *visits* every copy: one host request per
  node of the tree, which is exponential in an SSA chain's length. R7's
  lexer is the first body where that would show.
- Every other reader of elaborated bodies pays the same: conversion of the
  pin, `.code` quotation, memo tables keyed on node identity.

## Done when

`Body(chain)` viewed node by node yields one handle per let-bound value
(the probe is in the reflector's test module's history; a `lib/_tests` probe
can count handles), and the reflector's value numbering becomes a fallback
rather than the mechanism.
