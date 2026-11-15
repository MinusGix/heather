---
title: The reflected language rt, its typed meaning, and the per-function pin by conversion
status: open
labels: [native,metaprogramming,compiler]
area: heather-in-heather
milestone: [nh-front]
created: 2026-10-31
updated: 2026-11-14
---

Slice R5a of `docs/native/runtime-fn-setups-design.md` (§4, §12): the reflected
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

## Log

**2026-11-01 (R5a).** `lib/native/runtime/rt.hthr`. V1–V4 hold by `refl`
(`lib/_tests/native/runtime/rt_tests.hthr`), and the reflector produces the
same values from the real bodies. What implementing changed from §4.1:

- **A-normal form.** Operands are variables (de Bruijn indices); every
  intermediate is a `Let`. So `Tm` has no `List<Tm>` (nested inductives
  are not lowered yet) and a shared value is one `Let`.
- **Types by synthesis.** `Tm::ty` computes each node's code and
  `Tm::sem` lives at its semantics; casts only where two codes must agree,
  along `Ty::equation`, which evaluates to `refl` at closed codes. The
  type-directed interpreter did not need §15's fallback.
- **Records are named.** A record type's lowering carries a nominal tag no
  surface term spells, so `Rec(fs).sem` cannot be the record type. `Named(i)`
  reads the type, its constructor and its projections from a table of
  `RecInfo`s the meaning takes, as calls read callees from theirs; V2's pin is
  then `refl` with no `encode`/`decode`. Fields are flat.
- **`IfEq`** for `match h:`: its meaning is the elaborator's convoy (the
  match at the convoyed motive applied to `refl`); a plain `If` does not
  convert with it (the negative control).
- **No `Measured` node.** A `decreases` function's self-call is a `Call` of
  itself, answered by the function, so the body pins by `refl` against the
  body as written; `f = body[f]` is the generated `f_unfold`, a theorem, not
  a conversion (the proof argument of the recursor's ih is not data the
  reflection can carry). For `match h:` bodies `f_unfold` is refused today:
  [[decreases-unfold-convoy-scrutinee]].
- `ForIn` waits for R3 (`List::for_in` does not exist yet); `Enum`/`Case`
  wait for the first enum-reading runtime fn. `Bytes(cap)`'s capacity is not
  in the type, so the reflector writes `Bytes(0)` and the setup chooses.
- 2026-11-14: The span reflector's refusal of another computation called
  last rested on "no η for records", which is false; filed as
  [[reflect-tail-call-of-computation]].
