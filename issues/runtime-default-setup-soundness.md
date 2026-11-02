---
title: The default setup's judgment, lowering and soundness theorem, proved once
status: open
labels: [native,compiler,proofs]
area: heather-in-heather
milestone: [nh-front]
created: 2026-10-31
updated: 2026-11-01
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

## Log

**2026-11-01 (R5b, V6).** `lib/native/runtime/rt_lower.hthr`: the lowering
of variables, `Let`, `Prim(Add)` and `If` into FunctionIR regions, and
`Tm::lower_sound`, proved once by induction over `Tm`; every other node
lowers to `None` for now. What V6 fixed (design §16.5):

- **The invariant** is three things: every variable's port holds its
  value's encoding (`EnvHolds`; a word at its width, a bit as `ofBool`),
  every port is below the fresh id `next` (`Below`), and the region keeps
  every id below `next` (`Keeps`). The result port then holds the encoded
  meaning. It is stated over `StructuredRegion::eval`, so FunctionIR's
  `program_eval_computes` carries it to the relational semantics.
- **No judgment hypothesis.** The lowering asks for each equation of codes
  the meaning casts along (`Ty::check`) and refuses without it, and the
  proof carries encodings along that equation (`Ty::cast_holds`, from
  `Ty::cast_self` and `Nat::equation_self`). So `sound` assumes only that
  the lowering accepted; `judge` can stay a reporter of reasons.
- **A branch's arms take disjoint fresh ids:** the second arm's start
  above the first's, and both move their result to one port above both.

Probes: `lib/_tests/native/runtime/rt_lower_tests.hthr` (`pick`, a branch
with an `Add` arm, and `twice`, a shared sum, each agreeing with the Heather
function by instantiating the theorem; a wrong claim and an `Add` lowered
to a `Sub` node refused). Next: the remaining primitives, `Lit`, `IfEq`,
records, calls and `Fold` (§6.3's table), and the `Fun`/`Program` wrapper
from parameters bound by `Valuation::bind` to `Function::eval`.
