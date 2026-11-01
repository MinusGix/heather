---
title: Host requests for reading a definition's body: Body, λ and match-arm views, shared subterms
status: open
labels: [native,metaprogramming,host-interface]
area: heather-in-heather
milestone: [nh-front]
created: 2026-10-31
updated: 2026-10-31
---

Slice R5a of `docs/runtime-fn-setups-design.md` (§3.2, §13): the host
requests a `runtime fn` generator needs to read a definition's elaborated
body. `View` was built for tactics, which read goals and never a
definition's code.

## Scope

- `Body(g: GlobalRef) → Checked<Handle>`: a definition's elaborated value.
  Refused, with the reason, for a theorem, an axiom, a constructor or a
  global with no body. An `interface fn` is not refused (boxing is
  intensional analysis, not conversion in a proof).
- λ in a view (`HLam(dom)`), opened by `Open` into a host local as a
  function type's binder is today.
- `match` with its arms (`HCases(scrut, motive, arms)`): each arm's
  constructor, its fields opened as locals, and its body, as `Cases`
  presents a split goal. Equation binders (`match h: c`) appear as a local
  whose type is a proposition.
- Sharing by identity: the same handle for the same shared subterm within a
  run (or a `Same(a, b)` request), so a reflector can memoise and rebuild a
  block's aliases as lets. A block's `let` is an alias, so the kernel term
  has only a shared subterm (`docs/let-and-blocks-design.md` §4.4).
- Record the cost as a shape against the body's DAG size. If one request per
  node dominates, add a bulk `Reflect(h)` answering a tree of heads with
  shared nodes numbered.

## Done when

The prototype reflector (`runtime-fn-reflected-language`) reads every
body under `examples/x86-native/` through these requests, with a shared
subterm read once (V5 of the design note).
