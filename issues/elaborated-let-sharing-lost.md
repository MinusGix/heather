---
title: Elaborated bodies repeat a let-bound value at each use instead of sharing it
status: open
labels: [elaboration,sharing,native,metaprogramming]
area: language
milestone: [nh-front]
created: 2026-11-01
updated: 2026-11-10
---

Found building the `rt` reflector (`lib/native/runtime/rt_reflect.hthr`,
V5 of `docs/native/runtime-fn-setups-design.md` §12). The design assumed a block's
`let` is an alias whose value is one shared subterm in the kernel term
(`docs/language/let-and-blocks-design.md` §4.4), so the host could hand out one
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

## Log

- 2026-11-05: gardener: cites a file it shares with [[runtime-reflect-list-match]] (`lib/native/runtime/rt_reflect.hthr`).
- 2026-11-10: Two more places paid this, both found certifying the scanner's automaton. (1) The x86 placement planner (`plan_block`, `plan_from` in `function_ir_lower_structured.hthr`): a `let`-bound plan read at several places was replanned at each, and under nested conditionals that compounded per level; it was the memory [[compile-x86-certificate-memory]] reported, and the planner now binds with `shared` (`nat_map.hthr`). (2) `scan_step` (`lib/lang/lexer/lexer_scan.hthr`): written as `let f = scan_family(s, b);` over a decision tree on `f`, the kernel ran `scan_family` at each of five comparisons and the evaluated lexer probes ran out of fuel, so the tree is a function of its own taking the family as an argument. In both the source says "compute once" and the kernel term does not; `shared` and an extra function are the two spellings of the workaround, and a `runtime fn` cannot use `shared` (the reflector does not read it).
