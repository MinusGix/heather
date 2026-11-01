---
title: The reflected language rt, its typed meaning, and the per-function pin by conversion
status: open
labels: [native,metaprogramming,compiler]
area: heather-in-heather
milestone: [nh-front]
created: 2026-10-31
updated: 2026-10-31
---

Slice R5a of `docs/runtime-fn-setups-design.md` (§4, §12): the reflected
language every setup reads, its meaning, and the per-function pin.

## Scope

- `rt::Ty`, `rt::Tm`, `rt::Fun`, `rt::Program` (§4.1), mirroring the
  elaborated forms node for node, including R3's loop shapes (`foldl` and
  `for_in` of a named step, `decreases` recursion).
- `Ty::sem` and a type-directed `Program::meaning` (§4.2), calls answered by
  a table of meanings, every cast at a closed type code.
- The verification items V1–V4 first: the pin
  `f::rt().meaning(callees)(xs…) = f(xs…)` by `refl` for straight-line code,
  a `&&` test, a call, a record (does `Rec(fs).sem` convert to the record's
  kernel lowering?), a `foldl` of a named step, a `decreases` word
  recursion, and an erased `match h:` convoy. Reflections written by hand
  until `runtime-body-reflection-requests` lands.
- The reflector itself, `rt::reflect(g) → Tac<rt::Program>`, over the host
  requests, with a path-to-handle side table for refusal spans.

## Done when

V1–V4 hold by `refl` (or the design note is corrected with the construct
that needs the certifying route), and the reflector produces the same `rt`
values from the real bodies. Stop and report if V1 or V2 refutes the
type-directed interpreter (design §15 names the fallback).
