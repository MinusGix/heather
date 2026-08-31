---
title: FunctionIR proof-carrying validation is much slower than its graph walk
status: open
labels: [compiler,proofs,performance,function-ir]
created: 2026-08-31
updated: 2026-08-31
---

`check_region_valid` validates raw FunctionIR while constructing a
`RegionValid` certificate. Its algorithmic graph work is tiny for `sum4`, but
a cold check of the FunctionIR fixture rose from roughly 2 seconds before
validation to roughly 13 seconds with both three-node schedules certified.

The first implementation returned `P ∨ ¬P` at every recursive layer and took
roughly 33 seconds in the equivalent cold CLI probe. Replacing it with
`Option<P>` removed unused refutation trees and reduced the cold test to about
19 seconds; exporting opaque `sum4_*_valid` theorems so clients do not rerun
validation reduced it again to about 13 seconds. These are worthwhile API
fixes, but the remaining cost is still too high for compiler-sized graphs.

The likely dominant residue is proof construction for equality. A successful
lookup at width 64 reaches `nat::eq_dec(64, 64)`, whose evidence is a recursive
chain of successor congruences even though a generated certificate could emit
`refl` for the same closed equality. Stable-ID inequalities similarly carry
structural decision evidence.

## Desired direction

Keep `check_region_valid` as the in-language reference validator and dynamic
fallback, but add a certifying generator that traverses a concrete region and
emits the small proof term appropriate to the actual data:

- `refl` for definitionally equal IDs and widths;
- direct constructor paths for port lookup;
- shared freshness/uniqueness facts rather than recomputed decisions; and
- named stage certificates for large regions so client checks remain opaque.

Do not solve this by raising kernel fuel or weakening `RegionValid`.

## Acceptance

- Generated and reference validation agree on valid and invalid region corpus
  cases.
- A graph with at least 100 simple nodes validates in time suitable for an
  ordinary compiler test.
- Generated certificates are kernel-checked and contain no axiom or trusted
  validation shortcut.
- Width literals such as 64 do not create proof work linear in the represented
  Nat depth at every use.
