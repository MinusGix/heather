---
title: The bytes level's loads and stores name the view they use; the loop's back edge; the comparison again
status: open
labels: [native,function-ir,memory,ownership]
area: heather-in-heather
milestone: [nh-ownership]
created: 2026-11-26
updated: 2026-11-26
---

The bytes level's word ids have a view at every width (FunctionIR's valuation inside `Compute`), and views at different widths are independent in general. The lowering holds an id at one kind. Before this round a `Store` and a `Load` silently meant the 64-bit view and the kind `Word`. So a `ByteSwap(32)` result could not be stored by a four-byte store, and a four-byte load could not feed a `ByteSwap(32)`. That refused the four SHA-256 buffer rows and `scan_tokens` ([[bytes-level-translation]], item 4, cause 3; `docs/language/ownership-design.md` §17.8).

The coordinator's ruling, built here:
- `Store(bytes, view, place, value)` writes the low `bytes` bytes of the value's view at width `view`. The lowering asks for the value at that view's kind (`Word` at 64, `Narrow(32)` at 32).
- `Load(bytes, view, output, place)` binds the output at every width, as before, and the lowering records the stated kind.
- Validity refuses a view narrower than the access, and any view but 64 and 32.

Beside it:
- The plain loop's back edge jumps straight to the head where the continuing arm moves nothing.
- The translation drops a dead reference `Move`.
- The comparison is re-run over every export row and the gates.

## Log
