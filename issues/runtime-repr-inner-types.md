---
title: Reflect repr'd types that the signature does not name
status: open
labels: [native, runtime-fn]
area: heather-in-heather
milestone: [nh-front]
created: 2026-11-08
updated: 2026-11-08
---

The `runtime` generator learns which types are held by their `datarepr`
from the function's signature (`runtime_reprs`, docs/runtime-fn-setups-design.md
§16.13): an `i64` local inside a function whose parameters and result are
all `u64` is refused with "`SInt` is held by its datarepr `I64`, which the
function's signature does not name".

The reflector meets the type mid-walk (`Known::repr_ty`), but `Known` is
fixed for the walk, and its type table's indices must be settled before any
`Named(i)` is emitted. Either a first pass collects every type the body's
nodes have (one `infer` per node, which the walk already pays), or the walk
threads the reprs found so far through `RSt` and the table is the order
they were met. The second keeps one pass; `Known::ty` would then need the
state, which every call site of `ty_of` would thread.
