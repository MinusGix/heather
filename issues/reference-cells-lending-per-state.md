---
title: The lending threaded per state across an allocation: carved pieces in the body's invariant
status: open
labels: [ownership,native,design]
area: heather-in-heather
milestone: [nh-ownership]
created: 2026-11-25
updated: 2026-11-25
---

A block obtained after entry is a piece carved from a span the function was lent (a supply). The experiment proved that `Loan` needs no new law for it: pieces of a loan's spans, written pieces apart, are a `Loan` themselves (`Loan::carve`), and every store into a piece is a store into its parent, so the footprint stays the one stated at entry (`Stack::wrote_in_parents`; `lib/native/reference_cells/reference_cells_bridges.hthr`).

What does change is the threading. `function_ir_lower_calls` states a body's memory against one `Lending` fixed for the program (`Stack::InMemory(lending, now, memory)`, `Stack::Trail`, the contract), its `addresses` a list by buffer number. Across an allocation the blocks and where they lie grow, so the invariant must carry the current pieces (`Carved(entry_spans, pieces_now)`) and the loan it gets from `Loan::carve` at each state, with `WroteIn` still stated over the entry spans by `wrote_in_parents`. The allocator's laws (ownership-design §15.5: an answered block apart from every live one and inside the supply) are exactly what `Carved::apart` and `Carved::inside` ask.

## Done when

A body that allocates a block from a supply span, stores into it and reads it back compiles with its theorem, its contract's footprint the entry lending's; the allocator's laws stated once as what produces a `Carved`.

## What it assumes from elsewhere

- **[[ownership-reference-cells-spike]]** owns `Loan::carve` and `Stack::wrote_in_parents`. Assumed here: only those two statements.
- **[[ownership-discipline-over-code]]** owns the allocator's laws (§15.5); assumed only that a block answered is apart from every live one and inside its supply.
