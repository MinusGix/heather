---
title: The default setup's judgment, lowering and soundness theorem, proved once
status: open
labels: [native,compiler,proofs]
area: heather-in-heather
milestone: [nh-front]
created: 2026-10-31
updated: 2026-10-31
---

Slice R5b of `docs/runtime-fn-setups-design.md` (§2, §5–§7): the `Setup`
record, the default setup's judgment and lowering, and its soundness theorem
proved once (route 2 of [[in-language-certificate-emission]]).

## Scope

- `Setup { name, judge, lower, sound }` and the `Compile(f)` class in
  `lib/native/runtime/`.
- The default judgment over `rt` (§5.1), with reasons and paths.
- The lowering to a FunctionIR program (§7): the primitive table, flat
  layouts (records and enums scalar-replaced, `Bool` as a bit, `Bytes` as a
  buffer and a length), `Call` regions, and `Loop` for `Fold`, `ForIn`,
  `Measured` and fuel recursion.
- `default().sound`: induction over `Tm` under the lowering invariant
  (environment to ports, fresh ids, valuation agreeing with the encoded
  meaning). V6 first: the `Prim(add)` and `If` cases, to fix the invariant.
  Per-construct cases reuse `function_ir_compile`'s loop lemmas and the
  node equations (design §6.3's table).

## Done when

`default().sound` is proved for every N1 construct of design §7, with no
per-program proof, and a negative control: a lowering perturbed at one
construct fails the theorem, not a test.
