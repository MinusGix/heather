---
title: Lower signed words through the native frontend
status: closed
labels: [native]
area: heather-in-heather
created: 2026-11-03
updated: 2026-11-08
---

`i8`/`i64` are `SInt(n)`, a record over `BitVec(n)`
(docs/fixed-width-integers-design.md §3), so their operations are the word's
behind a field: `SInt::add(a, b) = SInt(a.bits.add(b.bits))`. The native
frontend and `rt` read `BitVec` words; a `runtime fn` over `i64` would meet
the record constructor and projection first.

Wanted: an `i64` parameter, local and result lower to the same 64-bit
register as a `u64`, with the signed operations (`Lt`, `div`, `shift_right`,
`extend`) lowering to their signed instructions (`JL`/`IDIV`/`SAR`/`MOVSX`).
Either the frontend sees through one-field records generally, or `SInt` gets
a `datarepr` that is its field.

## Log

### 2026-11-08 — done through the datarepr (Minus chose it over seeing through records)

`sint.hthr` states `datarepr I64 for SInt(64)` (and `I8`…`I32`); the
datarepr elaborator accepts a spec that is an inductive applied to value
arguments. The `runtime` generator asks the registry (host request `Repr`)
for each type of the function's signature, holds a repr'd type at
`Named(i)` with `RecInfo::word_repr(abs, emb, round)` as its table entry,
and the reflector reads an operation on it through its definition (host
request `Unfold`): `a + b` becomes the word's `Add(64)` between the field
and the constructor. The boundary (`Ty::OneWord`, proved in
`Fun::lower_sound`) passes the record in the 64-bit word a `u64` takes, so
`i64_add::agrees` says the program returns `x.add(y)` on words.
docs/runtime-fn-setups-design.md §16.13 has the design;
`lib/_tests/native/runtime/runtime_sint_tests.hthr` the probes.

Of the four signed ops, `lt_bit` → `Slt` (`JL`) and `shift_right` → `Ashr`
(`SAR`) reflect. Left, each filed:

- [[runtime-signed-extend-divide]]: `extend` (`MOVSX`) and `div` (`IDIV`)
  have no `rt` op.
- [[runtime-repr-calls]]: calls of runtime fns with `i64` signatures.
- [[runtime-repr-loops]]: loops whose state is `i64`.
- [[runtime-repr-inner-types]]: an `i64` the signature does not name.
- [[runtime-repr-narrow-words]]: `i8`…`i32` at the boundary.
- [[datarepr-value-parameter-telescope]]: one repr for every width.
